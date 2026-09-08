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

noncomputable def sk0Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (1/4), kHi := (5/16) }

noncomputable def sk0LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (655351/524288) }, upper := { exponent := 0, mantissa := (21/16) } }

noncomputable def sk0LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (1) }, upper := { exponent := -2, mantissa := (5/4) } }

noncomputable def sk0LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (5210031/2621440) }, upper := { exponent := 2, mantissa := (21/16) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk0LogOuter_valid :
    sk0LogOuterCertificate.check sk0Slice.outerAD.value = true := by
  norm_num [sk0LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk0Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk0LogK_valid :
    sk0LogKCertificate.check sk0Slice.kAD.value = true := by
  norm_num [sk0LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk0Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk0LogDArg_valid :
    sk0LogDArgCertificate.check sk0Slice.dArgAD.value = true := by
  norm_num [sk0LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk0Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk0ValidityFacts : SKFacts sk0Slice
    sk0LogOuterCertificate sk0LogKCertificate
    sk0LogDArgCertificate :=
  { domain := by norm_num [sk0Slice]
    kPositive := by
      norm_num [sk0Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk0LogOuter_valid
    logK := sk0LogK_valid
    logDArg := sk0LogDArg_valid }

noncomputable def sk0RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (3743497/16777216), upper := (4562291/16777216) }
    logK := { lower := (-23258161/16777216), upper := (-304913/262144) }
    logDArg := { lower := (2894089/2097152), upper := (6955113/4194304) } }

set_option maxRecDepth 1000000 in
private theorem sk0LogOuterInput_eq :
    sk0RoundedInputs.logOuter = outerEnclosure 24
      (sk0LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk0LogKInput_eq :
    sk0RoundedInputs.logK = outerEnclosure 24
      (sk0LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk0LogDArgInput_eq :
    sk0RoundedInputs.logDArg = outerEnclosure 24
      (sk0LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk0RoundedFacts : SKRoundedFacts 8
    sk0LogOuterCertificate sk0LogKCertificate
    sk0LogDArgCertificate sk0RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk0LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk0LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk0LogDArgInput_eq }

noncomputable def sk1Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (5/16), kHi := (3/8) }

noncomputable def sk1LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (688117/524288) }, upper := { exponent := 0, mantissa := (11/8) } }

noncomputable def sk1LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (5/4) }, upper := { exponent := -2, mantissa := (3/2) } }

noncomputable def sk1LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (2282797/1310720) }, upper := { exponent := 2, mantissa := (11/10) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk1LogOuter_valid :
    sk1LogOuterCertificate.check sk1Slice.outerAD.value = true := by
  norm_num [sk1LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk1Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk1LogK_valid :
    sk1LogKCertificate.check sk1Slice.kAD.value = true := by
  norm_num [sk1LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk1Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk1LogDArg_valid :
    sk1LogDArgCertificate.check sk1Slice.dArgAD.value = true := by
  norm_num [sk1LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk1Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk1ValidityFacts : SKFacts sk1Slice
    sk1LogOuterCertificate sk1LogKCertificate
    sk1LogDArgCertificate :=
  { domain := by norm_num [sk1Slice]
    kPositive := by
      norm_num [sk1Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk1LogOuter_valid
    logK := sk1LogK_valid
    logDArg := sk1LogDArg_valid }

noncomputable def sk1RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (2281011/8388608), upper := (333923/1048576) }
    logK := { lower := (-19514433/16777216), upper := (-514237/524288) }
    logDArg := { lower := (2617187/2097152), upper := (1553575/1048576) } }

set_option maxRecDepth 1000000 in
private theorem sk1LogOuterInput_eq :
    sk1RoundedInputs.logOuter = outerEnclosure 24
      (sk1LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk1LogKInput_eq :
    sk1RoundedInputs.logK = outerEnclosure 24
      (sk1LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk1LogDArgInput_eq :
    sk1RoundedInputs.logDArg = outerEnclosure 24
      (sk1LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk1RoundedFacts : SKRoundedFacts 8
    sk1LogOuterCertificate sk1LogKCertificate
    sk1LogDArgCertificate sk1RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk1LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk1LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk1LogDArgInput_eq }

noncomputable def sk2Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (3/8), kHi := (1/2) }

noncomputable def sk2LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (360441/262144) }, upper := { exponent := 0, mantissa := (3/2) } }

noncomputable def sk2LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (3/2) }, upper := { exponent := -1, mantissa := (1) } }

noncomputable def sk2LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (709957/524288) }, upper := { exponent := 2, mantissa := (1) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk2LogOuter_valid :
    sk2LogOuterCertificate.check sk2Slice.outerAD.value = true := by
  norm_num [sk2LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk2Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk2LogK_valid :
    sk2LogKCertificate.check sk2Slice.kAD.value = true := by
  norm_num [sk2LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk2Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk2LogDArg_valid :
    sk2LogDArgCertificate.check sk2Slice.dArgAD.value = true := by
  norm_num [sk2LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk2Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk2ValidityFacts : SKFacts sk2Slice
    sk2LogOuterCertificate sk2LogKCertificate
    sk2LogDArgCertificate :=
  { domain := by norm_num [sk2Slice]
    kPositive := by
      norm_num [sk2Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk2LogOuter_valid
    logK := sk2LogK_valid
    logDArg := sk2LogDArg_valid }

noncomputable def sk2RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (5342441/16777216), upper := (425161/1048576) }
    logK := { lower := (-16455585/16777216), upper := (-11629079/16777216) }
    logDArg := { lower := (16715315/16777216), upper := (23258161/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk2LogOuterInput_eq :
    sk2RoundedInputs.logOuter = outerEnclosure 24
      (sk2LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk2LogKInput_eq :
    sk2RoundedInputs.logK = outerEnclosure 24
      (sk2LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk2LogDArgInput_eq :
    sk2RoundedInputs.logDArg = outerEnclosure 24
      (sk2LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk2RoundedFacts : SKRoundedFacts 8
    sk2LogOuterCertificate sk2LogKCertificate
    sk2LogDArgCertificate sk2RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk2LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk2LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk2LogDArgInput_eq }

noncomputable def sk3Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (3/8), kHi := (7/16) }

noncomputable def sk3LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (720883/524288) }, upper := { exponent := 0, mantissa := (23/16) } }

noncomputable def sk3LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (3/2) }, upper := { exponent := -2, mantissa := (7/4) } }

noncomputable def sk3LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (2872605/1835008) }, upper := { exponent := 1, mantissa := (23/12) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk3LogOuter_valid :
    sk3LogOuterCertificate.check sk3Slice.outerAD.value = true := by
  norm_num [sk3LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk3Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk3LogK_valid :
    sk3LogKCertificate.check sk3Slice.kAD.value = true := by
  norm_num [sk3LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk3Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk3LogDArg_valid :
    sk3LogDArgCertificate.check sk3Slice.dArgAD.value = true := by
  norm_num [sk3LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk3Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk3ValidityFacts : SKFacts sk3Slice
    sk3LogOuterCertificate sk3LogKCertificate
    sk3LogDArgCertificate :=
  { domain := by norm_num [sk3Slice]
    kPositive := by
      norm_num [sk3Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk3LogOuter_valid
    logK := sk3LogK_valid
    logDArg := sk3LogDArg_valid }

noncomputable def sk3RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (20869/65536), upper := (190267/524288) }
    logK := { lower := (-16455585/16777216), upper := (-3467341/4194304) }
    logDArg := { lower := (4787033/4194304), upper := (22544129/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk3LogOuterInput_eq :
    sk3RoundedInputs.logOuter = outerEnclosure 24
      (sk3LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk3LogKInput_eq :
    sk3RoundedInputs.logK = outerEnclosure 24
      (sk3LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk3LogDArgInput_eq :
    sk3RoundedInputs.logDArg = outerEnclosure 24
      (sk3LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk3RoundedFacts : SKRoundedFacts 8
    sk3LogOuterCertificate sk3LogKCertificate
    sk3LogDArgCertificate sk3RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk3LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk3LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk3LogDArgInput_eq }

noncomputable def sk4Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (7/16), kHi := (1/2) }

noncomputable def sk4LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (753649/524288) }, upper := { exponent := 0, mantissa := (3/2) } }

noncomputable def sk4LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (7/4) }, upper := { exponent := -1, mantissa := (1) } }

noncomputable def sk4LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (10518303/7340032) }, upper := { exponent := 1, mantissa := (12/7) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk4LogOuter_valid :
    sk4LogOuterCertificate.check sk4Slice.outerAD.value = true := by
  norm_num [sk4LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk4Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk4LogK_valid :
    sk4LogKCertificate.check sk4Slice.kAD.value = true := by
  norm_num [sk4LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk4Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk4LogDArg_valid :
    sk4LogDArgCertificate.check sk4Slice.dArgAD.value = true := by
  norm_num [sk4LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk4Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk4ValidityFacts : SKFacts sk4Slice
    sk4LogOuterCertificate sk4LogKCertificate
    sk4LogDArgCertificate :=
  { domain := by norm_num [sk4Slice]
    kPositive := by
      norm_num [sk4Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk4LogOuter_valid
    logK := sk4LogK_valid
    logDArg := sk4LogDArg_valid }

noncomputable def sk4RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (6088209/16777216), upper := (425161/1048576) }
    logK := { lower := (-6934683/8388608), upper := (-11629079/16777216) }
    logDArg := { lower := (2208135/2097152), upper := (20671941/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk4LogOuterInput_eq :
    sk4RoundedInputs.logOuter = outerEnclosure 24
      (sk4LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk4LogKInput_eq :
    sk4RoundedInputs.logK = outerEnclosure 24
      (sk4LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk4LogDArgInput_eq :
    sk4RoundedInputs.logDArg = outerEnclosure 24
      (sk4LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk4RoundedFacts : SKRoundedFacts 8
    sk4LogOuterCertificate sk4LogKCertificate
    sk4LogDArgCertificate sk4RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk4LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk4LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk4LogDArgInput_eq }

noncomputable def sk5Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (1/2), kHi := (5/8) }

noncomputable def sk5LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (393207/262144) }, upper := { exponent := 0, mantissa := (13/8) } }

noncomputable def sk5LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (1) }, upper := { exponent := -1, mantissa := (5/4) } }

noncomputable def sk5LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (3112879/2621440) }, upper := { exponent := 1, mantissa := (13/8) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk5LogOuter_valid :
    sk5LogOuterCertificate.check sk5Slice.outerAD.value = true := by
  norm_num [sk5LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk5Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk5LogK_valid :
    sk5LogKCertificate.check sk5Slice.kAD.value = true := by
  norm_num [sk5LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk5Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk5LogDArg_valid :
    sk5LogDArgCertificate.check sk5Slice.dArgAD.value = true := by
  norm_num [sk5LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk5Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk5ValidityFacts : SKFacts sk5Slice
    sk5LogOuterCertificate sk5LogKCertificate
    sk5LogDArgCertificate :=
  { domain := by norm_num [sk5Slice]
    kPositive := by
      norm_num [sk5Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk5LogOuter_valid
    logK := sk5LogK_valid
    logDArg := sk5LogDArg_valid }

noncomputable def sk5RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (6802191/16777216), upper := (4072735/8388608) }
    logK := { lower := (-11629081/16777216), upper := (-985669/2097152) }
    logDArg := { lower := (3627953/4194304), upper := (9887275/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk5LogOuterInput_eq :
    sk5RoundedInputs.logOuter = outerEnclosure 24
      (sk5LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk5LogKInput_eq :
    sk5RoundedInputs.logK = outerEnclosure 24
      (sk5LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk5LogDArgInput_eq :
    sk5RoundedInputs.logDArg = outerEnclosure 24
      (sk5LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk5RoundedFacts : SKRoundedFacts 8
    sk5LogOuterCertificate sk5LogKCertificate
    sk5LogDArgCertificate sk5RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk5LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk5LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk5LogDArgInput_eq }

noncomputable def sk6Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (1/2), kHi := (9/16) }

noncomputable def sk6LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (786415/524288) }, upper := { exponent := 0, mantissa := (25/16) } }

noncomputable def sk6LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (1) }, upper := { exponent := -1, mantissa := (9/8) } }

noncomputable def sk6LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (4183285/3145728) }, upper := { exponent := 1, mantissa := (25/16) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk6LogOuter_valid :
    sk6LogOuterCertificate.check sk6Slice.outerAD.value = true := by
  norm_num [sk6LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk6Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk6LogK_valid :
    sk6LogKCertificate.check sk6Slice.kAD.value = true := by
  norm_num [sk6LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk6Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk6LogDArg_valid :
    sk6LogDArgCertificate.check sk6Slice.dArgAD.value = true := by
  norm_num [sk6LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk6Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk6ValidityFacts : SKFacts sk6Slice
    sk6LogOuterCertificate sk6LogKCertificate
    sk6LogDArgCertificate :=
  { domain := by norm_num [sk6Slice]
    kPositive := by
      norm_num [sk6Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk6LogOuter_valid
    logK := sk6LogK_valid
    logDArg := sk6LogDArg_valid }

noncomputable def sk6RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (6802213/16777216), upper := (233983/524288) }
    logK := { lower := (-11629081/16777216), upper := (-603313/1048576) }
    logDArg := { lower := (8205725/8388608), upper := (2389567/2097152) } }

set_option maxRecDepth 1000000 in
private theorem sk6LogOuterInput_eq :
    sk6RoundedInputs.logOuter = outerEnclosure 24
      (sk6LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk6LogKInput_eq :
    sk6RoundedInputs.logK = outerEnclosure 24
      (sk6LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk6LogDArgInput_eq :
    sk6RoundedInputs.logDArg = outerEnclosure 24
      (sk6LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk6RoundedFacts : SKRoundedFacts 8
    sk6LogOuterCertificate sk6LogKCertificate
    sk6LogDArgCertificate sk6RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk6LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk6LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk6LogDArgInput_eq }

noncomputable def sk7Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (9/16), kHi := (5/8) }

noncomputable def sk7LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (819181/524288) }, upper := { exponent := 0, mantissa := (13/8) } }

noncomputable def sk7LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (9/8) }, upper := { exponent := -1, mantissa := (5/4) } }

noncomputable def sk7LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (1634719/1310720) }, upper := { exponent := 1, mantissa := (13/9) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk7LogOuter_valid :
    sk7LogOuterCertificate.check sk7Slice.outerAD.value = true := by
  norm_num [sk7LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk7Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk7LogK_valid :
    sk7LogKCertificate.check sk7Slice.kAD.value = true := by
  norm_num [sk7LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk7Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk7LogDArg_valid :
    sk7LogDArgCertificate.check sk7Slice.dArgAD.value = true := by
  norm_num [sk7LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk7Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk7ValidityFacts : SKFacts sk7Slice
    sk7LogOuterCertificate sk7LogKCertificate
    sk7LogDArgCertificate :=
  { domain := by norm_num [sk7Slice]
    kPositive := by
      norm_num [sk7Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk7LogOuter_valid
    logK := sk7LogK_valid
    logDArg := sk7LogDArg_valid }

noncomputable def sk7RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (7487065/16777216), upper := (4072735/8388608) }
    logK := { lower := (-9653009/16777216), upper := (-985669/2097152) }
    logDArg := { lower := (15335071/16777216), upper := (17798479/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk7LogOuterInput_eq :
    sk7RoundedInputs.logOuter = outerEnclosure 24
      (sk7LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk7LogKInput_eq :
    sk7RoundedInputs.logK = outerEnclosure 24
      (sk7LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk7LogDArgInput_eq :
    sk7RoundedInputs.logDArg = outerEnclosure 24
      (sk7LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk7RoundedFacts : SKRoundedFacts 8
    sk7LogOuterCertificate sk7LogKCertificate
    sk7LogDArgCertificate sk7RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk7LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk7LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk7LogDArgInput_eq }

noncomputable def sk8Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (5/8), kHi := (3/4) }

noncomputable def sk8LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (425973/262144) }, upper := { exponent := 0, mantissa := (7/4) } }

noncomputable def sk8LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (5/4) }, upper := { exponent := -1, mantissa := (3/2) } }

noncomputable def sk8LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (4226951/3932160) }, upper := { exponent := 1, mantissa := (7/5) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk8LogOuter_valid :
    sk8LogOuterCertificate.check sk8Slice.outerAD.value = true := by
  norm_num [sk8LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk8Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk8LogK_valid :
    sk8LogKCertificate.check sk8Slice.kAD.value = true := by
  norm_num [sk8LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk8Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk8LogDArg_valid :
    sk8LogDArgCertificate.check sk8Slice.dArgAD.value = true := by
  norm_num [sk8LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk8Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk8ValidityFacts : SKFacts sk8Slice
    sk8LogOuterCertificate sk8LogKCertificate
    sk8LogDArgCertificate :=
  { domain := by norm_num [sk8Slice]
    kPositive := by
      norm_num [sk8Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk8LogOuter_valid
    logK := sk8LogK_valid
    logDArg := sk8LogDArg_valid }

noncomputable def sk8RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (2036259/4194304), upper := (9388795/16777216) }
    logK := { lower := (-7885353/16777216), upper := (-603313/2097152) }
    logDArg := { lower := (12841939/16777216), upper := (4318537/4194304) } }

set_option maxRecDepth 1000000 in
private theorem sk8LogOuterInput_eq :
    sk8RoundedInputs.logOuter = outerEnclosure 24
      (sk8LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk8LogKInput_eq :
    sk8RoundedInputs.logK = outerEnclosure 24
      (sk8LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk8LogDArgInput_eq :
    sk8RoundedInputs.logDArg = outerEnclosure 24
      (sk8LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk8RoundedFacts : SKRoundedFacts 8
    sk8LogOuterCertificate sk8LogKCertificate
    sk8LogDArgCertificate sk8RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk8LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk8LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk8LogDArgInput_eq }

noncomputable def sk9Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (5/8), kHi := (11/16) }

noncomputable def sk9LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (851947/524288) }, upper := { exponent := 0, mantissa := (27/16) } }

noncomputable def sk9LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (5/4) }, upper := { exponent := -1, mantissa := (11/8) } }

noncomputable def sk9LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (17006151/14417920) }, upper := { exponent := 1, mantissa := (27/20) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk9LogOuter_valid :
    sk9LogOuterCertificate.check sk9Slice.outerAD.value = true := by
  norm_num [sk9LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk9Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk9LogK_valid :
    sk9LogKCertificate.check sk9Slice.kAD.value = true := by
  norm_num [sk9LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk9Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk9LogDArg_valid :
    sk9LogDArgCertificate.check sk9Slice.dArgAD.value = true := by
  norm_num [sk9LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk9Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk9ValidityFacts : SKFacts sk9Slice
    sk9LogOuterCertificate sk9LogKCertificate
    sk9LogDArgCertificate :=
  { domain := by norm_num [sk9Slice]
    kPositive := by
      norm_num [sk9Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk9LogOuter_valid
    logK := sk9LogK_valid
    logDArg := sk9LogDArg_valid }

noncomputable def sk9RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (8145055/16777216), upper := (1097331/2097152) }
    logK := { lower := (-7885353/16777216), upper := (-785789/2097152) }
    logDArg := { lower := (3599763/4194304), upper := (260375/262144) } }

set_option maxRecDepth 1000000 in
private theorem sk9LogOuterInput_eq :
    sk9RoundedInputs.logOuter = outerEnclosure 24
      (sk9LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk9LogKInput_eq :
    sk9RoundedInputs.logK = outerEnclosure 24
      (sk9LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk9LogDArgInput_eq :
    sk9RoundedInputs.logDArg = outerEnclosure 24
      (sk9LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk9RoundedFacts : SKRoundedFacts 8
    sk9LogOuterCertificate sk9LogKCertificate
    sk9LogDArgCertificate sk9RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk9LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk9LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk9LogDArgInput_eq }

noncomputable def sk10Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (11/16), kHi := (3/4) }

noncomputable def sk10LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (884713/524288) }, upper := { exponent := 0, mantissa := (7/4) } }

noncomputable def sk10LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (11/8) }, upper := { exponent := -1, mantissa := (3/2) } }

noncomputable def sk10LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (588815/524288) }, upper := { exponent := 1, mantissa := (14/11) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk10LogOuter_valid :
    sk10LogOuterCertificate.check sk10Slice.outerAD.value = true := by
  norm_num [sk10LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk10Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk10LogK_valid :
    sk10LogKCertificate.check sk10Slice.kAD.value = true := by
  norm_num [sk10LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk10Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk10LogDArg_valid :
    sk10LogDArgCertificate.check sk10Slice.dArgAD.value = true := by
  norm_num [sk10LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk10Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk10ValidityFacts : SKFacts sk10Slice
    sk10LogOuterCertificate sk10LogKCertificate
    sk10LogDArgCertificate :=
  { domain := by norm_num [sk10Slice]
    kPositive := by
      norm_num [sk10Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk10LogOuter_valid
    logK := sk10LogK_valid
    logDArg := sk10LogDArg_valid }

noncomputable def sk10RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (4389105/8388608), upper := (9388795/16777216) }
    logK := { lower := (-3143157/8388608), upper := (-603313/2097152) }
    logDArg := { lower := (6788213/8388608), upper := (15675109/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk10LogOuterInput_eq :
    sk10RoundedInputs.logOuter = outerEnclosure 24
      (sk10LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk10LogKInput_eq :
    sk10RoundedInputs.logK = outerEnclosure 24
      (sk10LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk10LogDArgInput_eq :
    sk10RoundedInputs.logDArg = outerEnclosure 24
      (sk10LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk10RoundedFacts : SKRoundedFacts 8
    sk10LogOuterCertificate sk10LogKCertificate
    sk10LogDArgCertificate sk10RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk10LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk10LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk10LogDArgInput_eq }

noncomputable def sk11Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (3/4), kHi := (7/8) }

noncomputable def sk11LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (458739/262144) }, upper := { exponent := 0, mantissa := (15/8) } }

noncomputable def sk11LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (3/2) }, upper := { exponent := -1, mantissa := (7/4) } }

noncomputable def sk11LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (1824029/917504) }, upper := { exponent := 1, mantissa := (5/4) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk11LogOuter_valid :
    sk11LogOuterCertificate.check sk11Slice.outerAD.value = true := by
  norm_num [sk11LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk11Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk11LogK_valid :
    sk11LogKCertificate.check sk11Slice.kAD.value = true := by
  norm_num [sk11LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk11Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk11LogDArg_valid :
    sk11LogDArgCertificate.check sk11Slice.dArgAD.value = true := by
  norm_num [sk11LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk11Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk11ValidityFacts : SKFacts sk11Slice
    sk11LogOuterCertificate sk11LogKCertificate
    sk11LogDArgCertificate :=
  { domain := by norm_num [sk11Slice]
    kPositive := by
      norm_num [sk11Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk11LogOuter_valid
    logK := sk11LogK_valid
    logDArg := sk11LogDArg_valid }

noncomputable def sk11RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (9388319/16777216), upper := (82393/131072) }
    logK := { lower := (-4826505/16777216), upper := (-560071/4194304) }
    logDArg := { lower := (11528399/16777216), upper := (1921601/2097152) } }

set_option maxRecDepth 1000000 in
private theorem sk11LogOuterInput_eq :
    sk11RoundedInputs.logOuter = outerEnclosure 24
      (sk11LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk11LogKInput_eq :
    sk11RoundedInputs.logK = outerEnclosure 24
      (sk11LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk11LogDArgInput_eq :
    sk11RoundedInputs.logDArg = outerEnclosure 24
      (sk11LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk11RoundedFacts : SKRoundedFacts 8
    sk11LogOuterCertificate sk11LogKCertificate
    sk11LogDArgCertificate sk11RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk11LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk11LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk11LogDArgInput_eq }

noncomputable def sk12Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (7/8), kHi := (1) }

noncomputable def sk12LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (491505/262144) }, upper := { exponent := 1, mantissa := (1) } }

noncomputable def sk12LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (7/4) }, upper := { exponent := 0, mantissa := (1) } }

noncomputable def sk12LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (6848287/3670016) }, upper := { exponent := 1, mantissa := (8/7) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk12LogOuter_valid :
    sk12LogOuterCertificate.check sk12Slice.outerAD.value = true := by
  norm_num [sk12LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk12Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk12LogK_valid :
    sk12LogKCertificate.check sk12Slice.kAD.value = true := by
  norm_num [sk12LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk12Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk12LogDArg_valid :
    sk12LogDArgCertificate.check sk12Slice.dArgAD.value = true := by
  norm_num [sk12LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk12Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk12ValidityFacts : SKFacts sk12Slice
    sk12LogOuterCertificate sk12LogKCertificate
    sk12LogDArgCertificate :=
  { domain := by norm_num [sk12Slice]
    kPositive := by
      norm_num [sk12Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk12LogOuter_valid
    logK := sk12LogK_valid
    logDArg := sk12LogDArg_valid }

noncomputable def sk12RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (10545791/16777216), upper := (11629081/16777216) }
    logK := { lower := (-1120143/8388608), upper := (0) }
    logDArg := { lower := (10465669/16777216), upper := (6934683/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk12LogOuterInput_eq :
    sk12RoundedInputs.logOuter = outerEnclosure 24
      (sk12LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk12LogKInput_eq :
    sk12RoundedInputs.logK = outerEnclosure 24
      (sk12LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk12LogDArgInput_eq :
    sk12RoundedInputs.logDArg = outerEnclosure 24
      (sk12LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk12RoundedFacts : SKRoundedFacts 8
    sk12LogOuterCertificate sk12LogKCertificate
    sk12LogDArgCertificate sk12RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk12LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk12LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk12LogDArgInput_eq }

noncomputable def sk13Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (7/8), kHi := (15/16) }

noncomputable def sk13LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (983011/524288) }, upper := { exponent := 0, mantissa := (31/16) } }

noncomputable def sk13LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (7/4) }, upper := { exponent := -1, mantissa := (15/8) } }

noncomputable def sk13LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (9163837/4587520) }, upper := { exponent := 1, mantissa := (31/28) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk13LogOuter_valid :
    sk13LogOuterCertificate.check sk13Slice.outerAD.value = true := by
  norm_num [sk13LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk13Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk13LogK_valid :
    sk13LogKCertificate.check sk13Slice.kAD.value = true := by
  norm_num [sk13LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk13Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk13LogDArg_valid :
    sk13LogDArgCertificate.check sk13Slice.dArgAD.value = true := by
  norm_num [sk13LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk13Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk13ValidityFacts : SKFacts sk13Slice
    sk13LogOuterCertificate sk13LogKCertificate
    sk13LogDArgCertificate :=
  { domain := by norm_num [sk13Slice]
    kPositive := by
      norm_num [sk13Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk13LogOuter_valid
    logK := sk13LogK_valid
    logDArg := sk13LogDArg_valid }

noncomputable def sk13RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (659113/1048576), upper := (5548213/8388608) }
    logK := { lower := (-1120143/8388608), upper := (-135347/2097152) }
    logDArg := { lower := (11608581/16777216), upper := (13336711/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk13LogOuterInput_eq :
    sk13RoundedInputs.logOuter = outerEnclosure 24
      (sk13LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk13LogKInput_eq :
    sk13RoundedInputs.logK = outerEnclosure 24
      (sk13LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk13LogDArgInput_eq :
    sk13RoundedInputs.logDArg = outerEnclosure 24
      (sk13LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk13RoundedFacts : SKRoundedFacts 8
    sk13LogOuterCertificate sk13LogKCertificate
    sk13LogDArgCertificate sk13RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk13LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk13LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk13LogDArgInput_eq }

noncomputable def sk14Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (15/16), kHi := (1) }

noncomputable def sk14LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (1015777/524288) }, upper := { exponent := 1, mantissa := (1) } }

noncomputable def sk14LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (15/8) }, upper := { exponent := 0, mantissa := (1) } }

noncomputable def sk14LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (10146837/5242880) }, upper := { exponent := 1, mantissa := (16/15) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk14LogOuter_valid :
    sk14LogOuterCertificate.check sk14Slice.outerAD.value = true := by
  norm_num [sk14LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk14Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk14LogK_valid :
    sk14LogKCertificate.check sk14Slice.kAD.value = true := by
  norm_num [sk14LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk14Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk14LogDArg_valid :
    sk14LogDArgCertificate.check sk14Slice.dArgAD.value = true := by
  norm_num [sk14LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk14Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk14ValidityFacts : SKFacts sk14Slice
    sk14LogOuterCertificate sk14LogKCertificate
    sk14LogDArgCertificate :=
  { domain := by norm_num [sk14Slice]
    kPositive := by
      norm_num [sk14Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk14LogOuter_valid
    logK := sk14LogK_valid
    logDArg := sk14LogDArg_valid }

noncomputable def sk14RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (11095913/16777216), upper := (11629081/16777216) }
    logK := { lower := (-1082777/16777216), upper := (0) }
    logDArg := { lower := (11077845/16777216), upper := (12711857/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk14LogOuterInput_eq :
    sk14RoundedInputs.logOuter = outerEnclosure 24
      (sk14LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk14LogKInput_eq :
    sk14RoundedInputs.logK = outerEnclosure 24
      (sk14LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk14LogDArgInput_eq :
    sk14RoundedInputs.logDArg = outerEnclosure 24
      (sk14LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk14RoundedFacts : SKRoundedFacts 8
    sk14LogOuterCertificate sk14LogKCertificate
    sk14LogDArgCertificate sk14RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk14LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk14LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk14LogDArgInput_eq }

noncomputable def sk15Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (3/4), kHi := (13/16) }

noncomputable def sk15LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (917479/524288) }, upper := { exponent := 0, mantissa := (29/16) } }

noncomputable def sk15LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (3/2) }, upper := { exponent := -1, mantissa := (13/8) } }

noncomputable def sk15LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (7328901/6815744) }, upper := { exponent := 1, mantissa := (29/24) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk15LogOuter_valid :
    sk15LogOuterCertificate.check sk15Slice.outerAD.value = true := by
  norm_num [sk15LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk15Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk15LogK_valid :
    sk15LogKCertificate.check sk15Slice.kAD.value = true := by
  norm_num [sk15LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk15Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk15LogDArg_valid :
    sk15LogDArgCertificate.check sk15Slice.dArgAD.value = true := by
  norm_num [sk15LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk15Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk15ValidityFacts : SKFacts sk15Slice
    sk15LogOuterCertificate sk15LogKCertificate
    sk15LogDArgCertificate :=
  { domain := by norm_num [sk15Slice]
    kPositive := by
      norm_num [sk15Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk15LogOuter_valid
    logK := sk15LogK_valid
    logDArg := sk15LogDArg_valid }

noncomputable def sk15RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (9388337/16777216), upper := (4988765/8388608) }
    logK := { lower := (-4826505/16777216), upper := (-1741805/8388608) }
    logDArg := { lower := (12846943/16777216), upper := (14804035/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk15LogOuterInput_eq :
    sk15RoundedInputs.logOuter = outerEnclosure 24
      (sk15LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk15LogKInput_eq :
    sk15RoundedInputs.logK = outerEnclosure 24
      (sk15LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk15LogDArgInput_eq :
    sk15RoundedInputs.logDArg = outerEnclosure 24
      (sk15LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk15RoundedFacts : SKRoundedFacts 8
    sk15LogOuterCertificate sk15LogKCertificate
    sk15LogDArgCertificate sk15RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk15LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk15LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk15LogDArgInput_eq }

noncomputable def sk16Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (13/16), kHi := (7/8) }

noncomputable def sk16LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (950245/524288) }, upper := { exponent := 0, mantissa := (15/8) } }

noncomputable def sk16LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (13/8) }, upper := { exponent := -1, mantissa := (7/4) } }

noncomputable def sk16LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (24673575/23855104) }, upper := { exponent := 1, mantissa := (15/13) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk16LogOuter_valid :
    sk16LogOuterCertificate.check sk16Slice.outerAD.value = true := by
  norm_num [sk16LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk16Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk16LogK_valid :
    sk16LogKCertificate.check sk16Slice.kAD.value = true := by
  norm_num [sk16LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk16Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk16LogDArg_valid :
    sk16LogDArgCertificate.check sk16Slice.dArgAD.value = true := by
  norm_num [sk16LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk16Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk16ValidityFacts : SKFacts sk16Slice
    sk16LogOuterCertificate sk16LogKCertificate
    sk16LogDArgCertificate :=
  { domain := by norm_num [sk16Slice]
    kPositive := by
      norm_num [sk16Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk16LogOuter_valid
    logK := sk16LogK_valid
    logDArg := sk16LogDArg_valid }

noncomputable def sk16RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (2494263/4194304), upper := (82393/131072) }
    logK := { lower := (-3483611/16777216), upper := (-560071/4194304) }
    logDArg := { lower := (12195053/16777216), upper := (14029915/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk16LogOuterInput_eq :
    sk16RoundedInputs.logOuter = outerEnclosure 24
      (sk16LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk16LogKInput_eq :
    sk16RoundedInputs.logK = outerEnclosure 24
      (sk16LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk16LogDArgInput_eq :
    sk16RoundedInputs.logDArg = outerEnclosure 24
      (sk16LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk16RoundedFacts : SKRoundedFacts 8
    sk16LogOuterCertificate sk16LogKCertificate
    sk16LogDArgCertificate sk16RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk16LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk16LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk16LogDArgInput_eq }

noncomputable def sk17Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (9/8) }

noncomputable def sk17LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (524271/262144) }, upper := { exponent := 1, mantissa := (17/16) } }

noncomputable def sk17LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (1) }, upper := { exponent := 0, mantissa := (9/8) } }

noncomputable def sk17LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (8355551/4718592) }, upper := { exponent := 1, mantissa := (17/16) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk17LogOuter_valid :
    sk17LogOuterCertificate.check sk17Slice.outerAD.value = true := by
  norm_num [sk17LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk17Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk17LogK_valid :
    sk17LogKCertificate.check sk17Slice.kAD.value = true := by
  norm_num [sk17LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk17Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk17LogDArg_valid :
    sk17LogDArgCertificate.check sk17Slice.dArgAD.value = true := by
  norm_num [sk17LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk17Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk17ValidityFacts : SKFacts sk17Slice
    sk17LogOuterCertificate sk17LogKCertificate
    sk17LogDArgCertificate :=
  { domain := by norm_num [sk17Slice]
    kPositive := by
      norm_num [sk17Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk17LogOuter_valid
    logK := sk17LogK_valid
    logDArg := sk17LogDArg_valid }

noncomputable def sk17RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (11628535/16777216), upper := (12646193/16777216) }
    logK := { lower := (0), upper := (247009/2097152) }
    logDArg := { lower := (9586763/16777216), upper := (12646193/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk17LogOuterInput_eq :
    sk17RoundedInputs.logOuter = outerEnclosure 24
      (sk17LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk17LogKInput_eq :
    sk17RoundedInputs.logK = outerEnclosure 24
      (sk17LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk17LogDArgInput_eq :
    sk17RoundedInputs.logDArg = outerEnclosure 24
      (sk17LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk17RoundedFacts : SKRoundedFacts 8
    sk17LogOuterCertificate sk17LogKCertificate
    sk17LogDArgCertificate sk17RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk17LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk17LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk17LogDArgInput_eq }

noncomputable def sk18Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (17/16) }

noncomputable def sk18LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (1048543/524288) }, upper := { exponent := 1, mantissa := (33/32) } }

noncomputable def sk18LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (1) }, upper := { exponent := 0, mantissa := (17/16) } }

noncomputable def sk18LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (33520575/17825792) }, upper := { exponent := 1, mantissa := (33/32) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk18LogOuter_valid :
    sk18LogOuterCertificate.check sk18Slice.outerAD.value = true := by
  norm_num [sk18LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk18Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk18LogK_valid :
    sk18LogKCertificate.check sk18Slice.kAD.value = true := by
  norm_num [sk18LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk18Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk18LogDArg_valid :
    sk18LogDArgCertificate.check sk18Slice.dArgAD.value = true := by
  norm_num [sk18LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk18Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk18ValidityFacts : SKFacts sk18Slice
    sk18LogOuterCertificate sk18LogKCertificate
    sk18LogDArgCertificate :=
  { domain := by norm_num [sk18Slice]
    kPositive := by
      norm_num [sk18Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk18LogOuter_valid
    logK := sk18LogK_valid
    logDArg := sk18LogDArg_valid }

noncomputable def sk18RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (11628551/16777216), upper := (189771/262144) }
    logK := { lower := (0), upper := (1017113/16777216) }
    logDArg := { lower := (5297515/8388608), upper := (189771/262144) } }

set_option maxRecDepth 1000000 in
private theorem sk18LogOuterInput_eq :
    sk18RoundedInputs.logOuter = outerEnclosure 24
      (sk18LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk18LogKInput_eq :
    sk18RoundedInputs.logK = outerEnclosure 24
      (sk18LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk18LogDArgInput_eq :
    sk18RoundedInputs.logDArg = outerEnclosure 24
      (sk18LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk18RoundedFacts : SKRoundedFacts 8
    sk18LogOuterCertificate sk18LogKCertificate
    sk18LogDArgCertificate sk18RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk18LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk18LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk18LogDArgInput_eq }

noncomputable def sk19Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (17/16), kHi := (9/8) }

noncomputable def sk19LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (1081309/1048576) }, upper := { exponent := 1, mantissa := (17/16) } }

noncomputable def sk19LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (17/16) }, upper := { exponent := 0, mantissa := (9/8) } }

noncomputable def sk19LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (12243901/6684672) }, upper := { exponent := 1, mantissa := (1) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk19LogOuter_valid :
    sk19LogOuterCertificate.check sk19Slice.outerAD.value = true := by
  norm_num [sk19LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk19Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk19LogK_valid :
    sk19LogKCertificate.check sk19Slice.kAD.value = true := by
  norm_num [sk19LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk19Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk19LogDArg_valid :
    sk19LogDArgCertificate.check sk19Slice.dArgAD.value = true := by
  norm_num [sk19LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk19Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk19ValidityFacts : SKFacts sk19Slice
    sk19LogOuterCertificate sk19LogKCertificate
    sk19LogDArgCertificate :=
  { domain := by norm_num [sk19Slice]
    kPositive := by
      norm_num [sk19Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk19LogOuter_valid
    logK := sk19LogK_valid
    logDArg := sk19LogDArg_valid }

noncomputable def sk19RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (12144799/16777216), upper := (12646193/16777216) }
    logK := { lower := (127139/2097152), upper := (247009/2097152) }
    logDArg := { lower := (1269219/2097152), upper := (11629081/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk19LogOuterInput_eq :
    sk19RoundedInputs.logOuter = outerEnclosure 24
      (sk19LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk19LogKInput_eq :
    sk19RoundedInputs.logK = outerEnclosure 24
      (sk19LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk19LogDArgInput_eq :
    sk19RoundedInputs.logDArg = outerEnclosure 24
      (sk19LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk19RoundedFacts : SKRoundedFacts 8
    sk19LogOuterCertificate sk19LogKCertificate
    sk19LogDArgCertificate sk19RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk19LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk19LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk19LogDArgInput_eq }

noncomputable def sk20Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (9/8), kHi := (5/4) }

noncomputable def sk20LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (557037/524288) }, upper := { exponent := 1, mantissa := (9/8) } }

noncomputable def sk20LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (9/8) }, upper := { exponent := 0, mantissa := (5/4) } }

noncomputable def sk20LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (1110431/655360) }, upper := { exponent := 1, mantissa := (1) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk20LogOuter_valid :
    sk20LogOuterCertificate.check sk20Slice.outerAD.value = true := by
  norm_num [sk20LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk20Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk20LogK_valid :
    sk20LogKCertificate.check sk20Slice.kAD.value = true := by
  norm_num [sk20LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk20Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk20LogDArg_valid :
    sk20LogDArgCertificate.check sk20Slice.dArgAD.value = true := by
  norm_num [sk20LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk20Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk20ValidityFacts : SKFacts sk20Slice
    sk20LogOuterCertificate sk20LogKCertificate
    sk20LogDArgCertificate :=
  { domain := by norm_num [sk20Slice]
    kPositive := by
      norm_num [sk20Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk20LogOuter_valid
    logK := sk20LogK_valid
    logDArg := sk20LogDArg_valid }

noncomputable def sk20RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (3161405/4194304), upper := (425161/524288) }
    logK := { lower := (1976071/16777216), upper := (233983/1048576) }
    logDArg := { lower := (8846941/16777216), upper := (11629081/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk20LogOuterInput_eq :
    sk20RoundedInputs.logOuter = outerEnclosure 24
      (sk20LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk20LogKInput_eq :
    sk20RoundedInputs.logK = outerEnclosure 24
      (sk20LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk20LogDArgInput_eq :
    sk20RoundedInputs.logDArg = outerEnclosure 24
      (sk20LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk20RoundedFacts : SKRoundedFacts 8
    sk20LogOuterCertificate sk20LogKCertificate
    sk20LogDArgCertificate sk20RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk20LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk20LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk20LogDArgInput_eq }

noncomputable def sk21Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (9/8), kHi := (19/16) }

noncomputable def sk21LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (1114075/1048576) }, upper := { exponent := 1, mantissa := (35/32) } }

noncomputable def sk21LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (9/8) }, upper := { exponent := 0, mantissa := (19/16) } }

noncomputable def sk21LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (4452655/2490368) }, upper := { exponent := 0, mantissa := (35/18) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk21LogOuter_valid :
    sk21LogOuterCertificate.check sk21Slice.outerAD.value = true := by
  norm_num [sk21LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk21Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk21LogK_valid :
    sk21LogKCertificate.check sk21Slice.kAD.value = true := by
  norm_num [sk21LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk21Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk21LogDArg_valid :
    sk21LogDArgCertificate.check sk21Slice.dArgAD.value = true := by
  norm_num [sk21LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk21Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk21ValidityFacts : SKFacts sk21Slice
    sk21LogOuterCertificate sk21LogKCertificate
    sk21LogDArgCertificate :=
  { domain := by norm_num [sk21Slice]
    kPositive := by
      norm_num [sk21Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk21LogOuter_valid
    logK := sk21LogK_valid
    logDArg := sk21LogDArg_valid }

noncomputable def sk21RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (12645635/16777216), upper := (13132523/16777216) }
    logK := { lower := (1976071/16777216), upper := (2883169/16777216) }
    logDArg := { lower := (9748737/16777216), upper := (2789113/4194304) } }

set_option maxRecDepth 1000000 in
private theorem sk21LogOuterInput_eq :
    sk21RoundedInputs.logOuter = outerEnclosure 24
      (sk21LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk21LogKInput_eq :
    sk21RoundedInputs.logK = outerEnclosure 24
      (sk21LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk21LogDArgInput_eq :
    sk21RoundedInputs.logDArg = outerEnclosure 24
      (sk21LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk21RoundedFacts : SKRoundedFacts 8
    sk21LogOuterCertificate sk21LogKCertificate
    sk21LogDArgCertificate sk21RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk21LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk21LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk21LogDArgInput_eq }

noncomputable def sk22Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (19/16), kHi := (5/4) }

noncomputable def sk22LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (1146841/1048576) }, upper := { exponent := 1, mantissa := (9/8) } }

noncomputable def sk22LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (19/16) }, upper := { exponent := 0, mantissa := (5/4) } }

noncomputable def sk22LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (43547151/24903680) }, upper := { exponent := 0, mantissa := (36/19) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk22LogOuter_valid :
    sk22LogOuterCertificate.check sk22Slice.outerAD.value = true := by
  norm_num [sk22LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk22Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk22LogK_valid :
    sk22LogKCertificate.check sk22Slice.kAD.value = true := by
  norm_num [sk22LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk22Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk22LogDArg_valid :
    sk22LogDArgCertificate.check sk22Slice.dArgAD.value = true := by
  norm_num [sk22LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk22Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk22ValidityFacts : SKFacts sk22Slice
    sk22LogOuterCertificate sk22LogKCertificate
    sk22LogDArgCertificate :=
  { domain := by norm_num [sk22Slice]
    kPositive := by
      norm_num [sk22Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk22LogOuter_valid
    logK := sk22LogK_valid
    logDArg := sk22LogDArg_valid }

noncomputable def sk22RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (13131951/16777216), upper := (425161/524288) }
    logK := { lower := (90099/524288), upper := (233983/1048576) }
    logDArg := { lower := (9375589/16777216), upper := (10721983/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk22LogOuterInput_eq :
    sk22RoundedInputs.logOuter = outerEnclosure 24
      (sk22LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk22LogKInput_eq :
    sk22RoundedInputs.logK = outerEnclosure 24
      (sk22LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk22LogDArgInput_eq :
    sk22RoundedInputs.logDArg = outerEnclosure 24
      (sk22LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk22RoundedFacts : SKRoundedFacts 8
    sk22LogOuterCertificate sk22LogKCertificate
    sk22LogDArgCertificate sk22RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk22LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk22LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk22LogDArgInput_eq }

noncomputable def sk23Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (11/8) }

noncomputable def sk23LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (589803/524288) }, upper := { exponent := 1, mantissa := (19/16) } }

noncomputable def sk23LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (5/4) }, upper := { exponent := 0, mantissa := (11/8) } }

noncomputable def sk23LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (11763271/7208960) }, upper := { exponent := 0, mantissa := (19/10) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk23LogOuter_valid :
    sk23LogOuterCertificate.check sk23Slice.outerAD.value = true := by
  norm_num [sk23LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk23Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk23LogK_valid :
    sk23LogKCertificate.check sk23Slice.kAD.value = true := by
  norm_num [sk23LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk23Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk23LogDArg_valid :
    sk23LogDArgCertificate.check sk23Slice.dArgAD.value = true := by
  norm_num [sk23LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk23Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk23ValidityFacts : SKFacts sk23Slice
    sk23LogOuterCertificate sk23LogKCertificate
    sk23LogDArgCertificate :=
  { domain := by norm_num [sk23Slice]
    kPositive := by
      norm_num [sk23Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk23LogOuter_valid
    logK := sk23LogK_valid
    logDArg := sk23LogDArg_valid }

noncomputable def sk23RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (6802277/8388608), upper := (7256125/8388608) }
    logK := { lower := (3743727/16777216), upper := (333923/1048576) }
    logDArg := { lower := (8215087/16777216), upper := (5384261/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk23LogOuterInput_eq :
    sk23RoundedInputs.logOuter = outerEnclosure 24
      (sk23LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk23LogKInput_eq :
    sk23RoundedInputs.logK = outerEnclosure 24
      (sk23LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk23LogDArgInput_eq :
    sk23RoundedInputs.logDArg = outerEnclosure 24
      (sk23LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk23RoundedFacts : SKRoundedFacts 8
    sk23LogOuterCertificate sk23LogKCertificate
    sk23LogDArgCertificate sk23RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk23LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk23LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk23LogDArgInput_eq }

noncomputable def sk24Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (3/2) }

noncomputable def sk24LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (622569/524288) }, upper := { exponent := 1, mantissa := (5/4) } }

noncomputable def sk24LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (11/8) }, upper := { exponent := 0, mantissa := (3/2) } }

noncomputable def sk24LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (1242157/786432) }, upper := { exponent := 0, mantissa := (20/11) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk24LogOuter_valid :
    sk24LogOuterCertificate.check sk24Slice.outerAD.value = true := by
  norm_num [sk24LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk24Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk24LogK_valid :
    sk24LogKCertificate.check sk24Slice.kAD.value = true := by
  norm_num [sk24LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk24Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk24LogDArg_valid :
    sk24LogDArgCertificate.check sk24Slice.dArgAD.value = true := by
  norm_num [sk24LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk24Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk24ValidityFacts : SKFacts sk24Slice
    sk24LogOuterCertificate sk24LogKCertificate
    sk24LogDArgCertificate :=
  { domain := by norm_num [sk24Slice]
    kPositive := by
      norm_num [sk24Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk24LogOuter_valid
    logK := sk24LogK_valid
    logDArg := sk24LogDArg_valid }

noncomputable def sk24RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (14511629/16777216), upper := (1921601/2097152) }
    logK := { lower := (5342767/16777216), upper := (425161/1048576) }
    logDArg := { lower := (3834419/8388608), upper := (10030041/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk24LogOuterInput_eq :
    sk24RoundedInputs.logOuter = outerEnclosure 24
      (sk24LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk24LogKInput_eq :
    sk24RoundedInputs.logK = outerEnclosure 24
      (sk24LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk24LogDArgInput_eq :
    sk24RoundedInputs.logDArg = outerEnclosure 24
      (sk24LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk24RoundedFacts : SKRoundedFacts 8
    sk24LogOuterCertificate sk24LogKCertificate
    sk24LogDArgCertificate sk24RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk24LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk24LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk24LogDArgInput_eq }

noncomputable def sk25Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (21/16) }

noncomputable def sk25LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (1179607/1048576) }, upper := { exponent := 1, mantissa := (37/32) } }

noncomputable def sk25LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (5/4) }, upper := { exponent := 0, mantissa := (21/16) } }

noncomputable def sk25LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (15717157/9175040) }, upper := { exponent := 0, mantissa := (37/20) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk25LogOuter_valid :
    sk25LogOuterCertificate.check sk25Slice.outerAD.value = true := by
  norm_num [sk25LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk25Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk25LogK_valid :
    sk25LogKCertificate.check sk25Slice.kAD.value = true := by
  norm_num [sk25LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk25Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk25LogDArg_valid :
    sk25LogDArgCertificate.check sk25Slice.dArgAD.value = true := by
  norm_num [sk25LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk25Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk25ValidityFacts : SKFacts sk25Slice
    sk25LogOuterCertificate sk25LogKCertificate
    sk25LogDArgCertificate :=
  { domain := by norm_num [sk25Slice]
    kPositive := by
      norm_num [sk25Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk25LogOuter_valid
    logK := sk25LogK_valid
    logDArg := sk25LogDArg_valid }

noncomputable def sk25RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (1700571/2097152), upper := (14064831/16777216) }
    logK := { lower := (3743727/16777216), upper := (4562291/16777216) }
    logDArg := { lower := (9030607/16777216), upper := (10321103/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk25LogOuterInput_eq :
    sk25RoundedInputs.logOuter = outerEnclosure 24
      (sk25LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk25LogKInput_eq :
    sk25RoundedInputs.logK = outerEnclosure 24
      (sk25LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk25LogDArgInput_eq :
    sk25RoundedInputs.logDArg = outerEnclosure 24
      (sk25LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk25RoundedFacts : SKRoundedFacts 8
    sk25LogOuterCertificate sk25LogKCertificate
    sk25LogDArgCertificate sk25RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk25LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk25LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk25LogDArgInput_eq }

noncomputable def sk26Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (21/16), kHi := (11/8) }

noncomputable def sk26LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (1212373/1048576) }, upper := { exponent := 1, mantissa := (19/16) } }

noncomputable def sk26LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (21/16) }, upper := { exponent := 0, mantissa := (11/8) } }

noncomputable def sk26LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (16962285/10092544) }, upper := { exponent := 0, mantissa := (38/21) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk26LogOuter_valid :
    sk26LogOuterCertificate.check sk26Slice.outerAD.value = true := by
  norm_num [sk26LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk26Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk26LogK_valid :
    sk26LogKCertificate.check sk26Slice.kAD.value = true := by
  norm_num [sk26LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk26Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk26LogDArg_valid :
    sk26LogDArgCertificate.check sk26Slice.dArgAD.value = true := by
  norm_num [sk26LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk26Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk26ValidityFacts : SKFacts sk26Slice
    sk26LogOuterCertificate sk26LogKCertificate
    sk26LogDArgCertificate :=
  { domain := by norm_num [sk26Slice]
    kPositive := by
      norm_num [sk26Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk26LogOuter_valid
    logK := sk26LogK_valid
    logDArg := sk26LogDArg_valid }

noncomputable def sk26RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (7032117/8388608), upper := (7256125/8388608) }
    logK := { lower := (2281145/8388608), upper := (333923/1048576) }
    logDArg := { lower := (8710653/16777216), upper := (9949959/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk26LogOuterInput_eq :
    sk26RoundedInputs.logOuter = outerEnclosure 24
      (sk26LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk26LogKInput_eq :
    sk26RoundedInputs.logK = outerEnclosure 24
      (sk26LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk26LogDArgInput_eq :
    sk26RoundedInputs.logDArg = outerEnclosure 24
      (sk26LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk26RoundedFacts : SKRoundedFacts 8
    sk26LogOuterCertificate sk26LogKCertificate
    sk26LogDArgCertificate sk26RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk26LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk26LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk26LogDArgInput_eq }

noncomputable def sk27Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (23/16) }

noncomputable def sk27LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (1245139/1048576) }, upper := { exponent := 1, mantissa := (39/32) } }

noncomputable def sk27LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (11/8) }, upper := { exponent := 0, mantissa := (23/16) } }

noncomputable def sk27LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (4977573/3014656) }, upper := { exponent := 0, mantissa := (39/22) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk27LogOuter_valid :
    sk27LogOuterCertificate.check sk27Slice.outerAD.value = true := by
  norm_num [sk27LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk27Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk27LogK_valid :
    sk27LogKCertificate.check sk27Slice.kAD.value = true := by
  norm_num [sk27LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk27Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk27LogDArg_valid :
    sk27LogDArgCertificate.check sk27Slice.dArgAD.value = true := by
  norm_num [sk27LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk27Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk27ValidityFacts : SKFacts sk27Slice
    sk27LogOuterCertificate sk27LogKCertificate
    sk27LogDArgCertificate :=
  { domain := by norm_num [sk27Slice]
    kPositive := by
      norm_num [sk27Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk27LogOuter_valid
    logK := sk27LogK_valid
    logDArg := sk27LogDArg_valid }

noncomputable def sk27RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (7255821/8388608), upper := (7474023/8388608) }
    logK := { lower := (5342767/16777216), upper := (190267/524288) }
    logDArg := { lower := (8413047/16777216), upper := (9605279/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk27LogOuterInput_eq :
    sk27RoundedInputs.logOuter = outerEnclosure 24
      (sk27LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk27LogKInput_eq :
    sk27RoundedInputs.logK = outerEnclosure 24
      (sk27LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk27LogDArgInput_eq :
    sk27RoundedInputs.logDArg = outerEnclosure 24
      (sk27LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk27RoundedFacts : SKRoundedFacts 8
    sk27LogOuterCertificate sk27LogKCertificate
    sk27LogDArgCertificate sk27RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk27LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk27LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk27LogDArgInput_eq }

noncomputable def sk28Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (23/16), kHi := (3/2) }

noncomputable def sk28LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (1277905/1048576) }, upper := { exponent := 1, mantissa := (5/4) } }

noncomputable def sk28LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (23/16) }, upper := { exponent := 0, mantissa := (3/2) } }

noncomputable def sk28LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (19583605/12058624) }, upper := { exponent := 0, mantissa := (40/23) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk28LogOuter_valid :
    sk28LogOuterCertificate.check sk28Slice.outerAD.value = true := by
  norm_num [sk28LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk28Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk28LogK_valid :
    sk28LogKCertificate.check sk28Slice.kAD.value = true := by
  norm_num [sk28LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk28Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk28LogDArg_valid :
    sk28LogDArgCertificate.check sk28Slice.dArgAD.value = true := by
  norm_num [sk28LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk28Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk28ValidityFacts : SKFacts sk28Slice
    sk28LogOuterCertificate sk28LogKCertificate
    sk28LogDArgCertificate :=
  { domain := by norm_num [sk28Slice]
    kPositive := by
      norm_num [sk28Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk28LogOuter_valid
    logK := sk28LogK_valid
    logDArg := sk28LogDArg_valid }

noncomputable def sk28RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (3736857/4194304), upper := (1921601/2097152) }
    logK := { lower := (6088543/16777216), upper := (425161/1048576) }
    logDArg := { lower := (2033871/4194304), upper := (1160533/2097152) } }

set_option maxRecDepth 1000000 in
private theorem sk28LogOuterInput_eq :
    sk28RoundedInputs.logOuter = outerEnclosure 24
      (sk28LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk28LogKInput_eq :
    sk28RoundedInputs.logK = outerEnclosure 24
      (sk28LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk28LogDArgInput_eq :
    sk28RoundedInputs.logDArg = outerEnclosure 24
      (sk28LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk28RoundedFacts : SKRoundedFacts 8
    sk28LogOuterCertificate sk28LogKCertificate
    sk28LogDArgCertificate sk28RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk28LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk28LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk28LogDArgInput_eq }

noncomputable def sk29Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (23/16), kHi := (47/32) }

noncomputable def sk29LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (2555811/2097152) }, upper := { exponent := 1, mantissa := (79/64) } }

noncomputable def sk29LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (23/16) }, upper := { exponent := 0, mantissa := (47/32) } }

noncomputable def sk29LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (235101751/141688832) }, upper := { exponent := 0, mantissa := (79/46) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk29LogOuter_valid :
    sk29LogOuterCertificate.check sk29Slice.outerAD.value = true := by
  norm_num [sk29LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk29Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk29LogK_valid :
    sk29LogKCertificate.check sk29Slice.kAD.value = true := by
  norm_num [sk29LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk29Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk29LogDArg_valid :
    sk29LogDArgCertificate.check sk29Slice.dArgAD.value = true := by
  norm_num [sk29LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk29Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk29ValidityFacts : SKFacts sk29Slice
    sk29LogOuterCertificate sk29LogKCertificate
    sk29LogDArgCertificate :=
  { domain := by norm_num [sk29Slice]
    kPositive := by
      norm_num [sk29Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk29LogOuter_valid
    logK := sk29LogK_valid
    logDArg := sk29LogDArg_valid }

noncomputable def sk29RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (7473717/8388608), upper := (15161771/16777216) }
    logK := { lower := (6088543/16777216), upper := (6449359/16777216) }
    logDArg := { lower := (8495731/16777216), upper := (9073227/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk29LogOuterInput_eq :
    sk29RoundedInputs.logOuter = outerEnclosure 24
      (sk29LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk29LogKInput_eq :
    sk29RoundedInputs.logK = outerEnclosure 24
      (sk29LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk29LogDArgInput_eq :
    sk29RoundedInputs.logDArg = outerEnclosure 24
      (sk29LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk29RoundedFacts : SKRoundedFacts 8
    sk29LogOuterCertificate sk29LogKCertificate
    sk29LogDArgCertificate sk29RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk29LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk29LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk29LogDArgInput_eq }

noncomputable def sk30Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (47/32), kHi := (3/2) }

noncomputable def sk30LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (2588577/2097152) }, upper := { exponent := 1, mantissa := (5/4) } }

noncomputable def sk30LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (47/32) }, upper := { exponent := 0, mantissa := (3/2) } }

noncomputable def sk30LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (243293375/147849216) }, upper := { exponent := 0, mantissa := (80/47) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk30LogOuter_valid :
    sk30LogOuterCertificate.check sk30Slice.outerAD.value = true := by
  norm_num [sk30LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk30Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk30LogK_valid :
    sk30LogKCertificate.check sk30Slice.kAD.value = true := by
  norm_num [sk30LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk30Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk30LogDArg_valid :
    sk30LogDArgCertificate.check sk30Slice.dArgAD.value = true := by
  norm_num [sk30LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk30Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk30ValidityFacts : SKFacts sk30Slice
    sk30LogOuterCertificate sk30LogKCertificate
    sk30LogDArgCertificate :=
  { domain := by norm_num [sk30Slice]
    kPositive := by
      norm_num [sk30Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk30LogOuter_valid
    logK := sk30LogK_valid
    logDArg := sk30LogDArg_valid }

noncomputable def sk30RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (7580577/8388608), upper := (1921601/2097152) }
    logK := { lower := (3224679/8388608), upper := (425161/1048576) }
    logDArg := { lower := (8356313/16777216), upper := (4461725/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk30LogOuterInput_eq :
    sk30RoundedInputs.logOuter = outerEnclosure 24
      (sk30LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk30LogKInput_eq :
    sk30RoundedInputs.logK = outerEnclosure 24
      (sk30LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk30LogDArgInput_eq :
    sk30RoundedInputs.logDArg = outerEnclosure 24
      (sk30LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk30RoundedFacts : SKRoundedFacts 8
    sk30LogOuterCertificate sk30LogKCertificate
    sk30LogDArgCertificate sk30RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk30LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk30LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk30LogDArgInput_eq }

noncomputable def sk31Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (13/8) }

noncomputable def sk31LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (655335/524288) }, upper := { exponent := 1, mantissa := (21/16) } }

noncomputable def sk31LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (3/2) }, upper := { exponent := 0, mantissa := (13/8) } }

noncomputable def sk31LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (5231749/3407872) }, upper := { exponent := 0, mantissa := (7/4) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk31LogOuter_valid :
    sk31LogOuterCertificate.check sk31Slice.outerAD.value = true := by
  norm_num [sk31LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk31Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk31LogK_valid :
    sk31LogKCertificate.check sk31Slice.kAD.value = true := by
  norm_num [sk31LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk31Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk31LogDArg_valid :
    sk31LogDArgCertificate.check sk31Slice.dArgAD.value = true := by
  norm_num [sk31LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk31Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk31ValidityFacts : SKFacts sk31Slice
    sk31LogOuterCertificate sk31LogKCertificate
    sk31LogDArgCertificate :=
  { domain := by norm_num [sk31Slice]
    kPositive := by
      norm_num [sk31Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk31LogOuter_valid
    logK := sk31LogK_valid
    logDArg := sk31LogDArg_valid }

noncomputable def sk31RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (15372167/16777216), upper := (16191371/16777216) }
    logK := { lower := (6802575/16777216), upper := (4072735/8388608) }
    logDArg := { lower := (56185/131072), upper := (9388795/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk31LogOuterInput_eq :
    sk31RoundedInputs.logOuter = outerEnclosure 24
      (sk31LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk31LogKInput_eq :
    sk31RoundedInputs.logK = outerEnclosure 24
      (sk31LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk31LogDArgInput_eq :
    sk31RoundedInputs.logDArg = outerEnclosure 24
      (sk31LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk31RoundedFacts : SKRoundedFacts 8
    sk31LogOuterCertificate sk31LogKCertificate
    sk31LogDArgCertificate sk31RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk31LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk31LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk31LogDArgInput_eq }

noncomputable def sk32Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (7/4) }

noncomputable def sk32LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (688101/524288) }, upper := { exponent := 1, mantissa := (11/8) } }

noncomputable def sk32LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (13/8) }, upper := { exponent := 0, mantissa := (7/4) } }

noncomputable def sk32LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (17857831/11927552) }, upper := { exponent := 0, mantissa := (22/13) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk32LogOuter_valid :
    sk32LogOuterCertificate.check sk32Slice.outerAD.value = true := by
  norm_num [sk32LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk32Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk32LogK_valid :
    sk32LogKCertificate.check sk32Slice.kAD.value = true := by
  norm_num [sk32LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk32Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk32LogDArg_valid :
    sk32LogDArgCertificate.check sk32Slice.dArgAD.value = true := by
  norm_num [sk32LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk32Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk32ValidityFacts : SKFacts sk32Slice
    sk32LogOuterCertificate sk32LogKCertificate
    sk32LogDArgCertificate :=
  { domain := by norm_num [sk32Slice]
    kPositive := by
      norm_num [sk32Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk32LogOuter_valid
    logK := sk32LogK_valid
    logDArg := sk32LogDArg_valid }

noncomputable def sk32RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (2023839/2097152), upper := (2121481/2097152) }
    logK := { lower := (8145469/16777216), upper := (9388795/16777216) }
    logDArg := { lower := (6771135/16777216), upper := (4413189/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk32LogOuterInput_eq :
    sk32RoundedInputs.logOuter = outerEnclosure 24
      (sk32LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk32LogKInput_eq :
    sk32RoundedInputs.logK = outerEnclosure 24
      (sk32LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk32LogDArgInput_eq :
    sk32RoundedInputs.logDArg = outerEnclosure 24
      (sk32LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk32RoundedFacts : SKRoundedFacts 8
    sk32LogOuterCertificate sk32LogKCertificate
    sk32LogDArgCertificate sk32RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk32LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk32LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk32LogDArgInput_eq }

noncomputable def sk33Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (27/16) }

noncomputable def sk33LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (1376203/1048576) }, upper := { exponent := 1, mantissa := (43/32) } }

noncomputable def sk33LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (13/8) }, upper := { exponent := 0, mantissa := (27/16) } }

noncomputable def sk33LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (23843245/15335424) }, upper := { exponent := 0, mantissa := (43/26) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk33LogOuter_valid :
    sk33LogOuterCertificate.check sk33Slice.outerAD.value = true := by
  norm_num [sk33LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk33Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk33LogK_valid :
    sk33LogKCertificate.check sk33Slice.kAD.value = true := by
  norm_num [sk33LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk33Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk33LogDArg_valid :
    sk33LogDArgCertificate.check sk33Slice.dArgAD.value = true := by
  norm_num [sk33LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk33Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk33ValidityFacts : SKFacts sk33Slice
    sk33LogOuterCertificate sk33LogKCertificate
    sk33LogDArgCertificate :=
  { domain := by norm_num [sk33Slice]
    kPositive := by
      norm_num [sk33Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk33LogOuter_valid
    logK := sk33LogK_valid
    logDArg := sk33LogDArg_valid }

noncomputable def sk33RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (4047681/4194304), upper := (4146537/4194304) }
    logK := { lower := (8145469/16777216), upper := (1097331/2097152) }
    logDArg := { lower := (7404381/16777216), upper := (4220339/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk33LogOuterInput_eq :
    sk33RoundedInputs.logOuter = outerEnclosure 24
      (sk33LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk33LogKInput_eq :
    sk33RoundedInputs.logK = outerEnclosure 24
      (sk33LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk33LogDArgInput_eq :
    sk33RoundedInputs.logDArg = outerEnclosure 24
      (sk33LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk33RoundedFacts : SKRoundedFacts 8
    sk33LogOuterCertificate sk33LogKCertificate
    sk33LogDArgCertificate sk33RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk33LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk33LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk33LogDArgInput_eq }

noncomputable def sk34Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (27/16), kHi := (7/4) }

noncomputable def sk34LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (1408969/1048576) }, upper := { exponent := 1, mantissa := (11/8) } }

noncomputable def sk34LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (27/16) }, upper := { exponent := 0, mantissa := (7/4) } }

noncomputable def sk34LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (8450167/5505024) }, upper := { exponent := 0, mantissa := (44/27) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk34LogOuter_valid :
    sk34LogOuterCertificate.check sk34Slice.outerAD.value = true := by
  norm_num [sk34LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk34Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk34LogK_valid :
    sk34LogKCertificate.check sk34Slice.kAD.value = true := by
  norm_num [sk34LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk34Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk34LogDArg_valid :
    sk34LogDArgCertificate.check sk34Slice.dArgAD.value = true := by
  norm_num [sk34LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk34Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk34ValidityFacts : SKFacts sk34Slice
    sk34LogOuterCertificate sk34LogKCertificate
    sk34LogDArgCertificate :=
  { domain := by norm_num [sk34Slice]
    kPositive := by
      norm_num [sk34Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk34LogOuter_valid
    logK := sk34LogK_valid
    logDArg := sk34LogDArg_valid }

noncomputable def sk34RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (16585491/16777216), upper := (2121481/2097152) }
    logK := { lower := (8778647/16777216), upper := (9388795/16777216) }
    logDArg := { lower := (7189457/16777216), upper := (512075/1048576) } }

set_option maxRecDepth 1000000 in
private theorem sk34LogOuterInput_eq :
    sk34RoundedInputs.logOuter = outerEnclosure 24
      (sk34LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk34LogKInput_eq :
    sk34RoundedInputs.logK = outerEnclosure 24
      (sk34LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk34LogDArgInput_eq :
    sk34RoundedInputs.logDArg = outerEnclosure 24
      (sk34LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk34RoundedFacts : SKRoundedFacts 8
    sk34LogOuterCertificate sk34LogKCertificate
    sk34LogDArgCertificate sk34RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk34LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk34LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk34LogDArgInput_eq }

noncomputable def sk35Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (25/16) }

noncomputable def sk35LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (1310671/1048576) }, upper := { exponent := 1, mantissa := (41/32) } }

noncomputable def sk35LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (3/2) }, upper := { exponent := 0, mantissa := (25/16) } }

noncomputable def sk35LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (20959797/13107200) }, upper := { exponent := 0, mantissa := (41/24) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk35LogOuter_valid :
    sk35LogOuterCertificate.check sk35Slice.outerAD.value = true := by
  norm_num [sk35LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk35Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk35LogK_valid :
    sk35LogKCertificate.check sk35Slice.kAD.value = true := by
  norm_num [sk35LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk35Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk35LogDArg_valid :
    sk35LogDArgCertificate.check sk35Slice.dArgAD.value = true := by
  norm_num [sk35LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk35Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk35ValidityFacts : SKFacts sk35Slice
    sk35LogOuterCertificate sk35LogKCertificate
    sk35LogDArgCertificate :=
  { domain := by norm_num [sk35Slice]
    kPositive := by
      norm_num [sk35Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk35LogOuter_valid
    logK := sk35LogK_valid
    logDArg := sk35LogDArg_valid }

noncomputable def sk35RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (3843045/4194304), upper := (7893541/8388608) }
    logK := { lower := (6802575/16777216), upper := (233983/524288) }
    logDArg := { lower := (7875971/16777216), upper := (4492253/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk35LogOuterInput_eq :
    sk35RoundedInputs.logOuter = outerEnclosure 24
      (sk35LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk35LogKInput_eq :
    sk35RoundedInputs.logK = outerEnclosure 24
      (sk35LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk35LogDArgInput_eq :
    sk35RoundedInputs.logDArg = outerEnclosure 24
      (sk35LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk35RoundedFacts : SKRoundedFacts 8
    sk35LogOuterCertificate sk35LogKCertificate
    sk35LogDArgCertificate sk35RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk35LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk35LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk35LogDArgInput_eq }

noncomputable def sk36Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (25/16), kHi := (13/8) }

noncomputable def sk36LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (1343437/1048576) }, upper := { exponent := 1, mantissa := (21/16) } }

noncomputable def sk36LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (25/16) }, upper := { exponent := 0, mantissa := (13/8) } }

noncomputable def sk36LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (67139031/42598400) }, upper := { exponent := 0, mantissa := (42/25) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk36LogOuter_valid :
    sk36LogOuterCertificate.check sk36Slice.outerAD.value = true := by
  norm_num [sk36LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk36Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk36LogK_valid :
    sk36LogKCertificate.check sk36Slice.kAD.value = true := by
  norm_num [sk36LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk36Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk36LogDArg_valid :
    sk36LogDArgCertificate.check sk36Slice.dArgAD.value = true := by
  norm_num [sk36LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk36Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk36ValidityFacts : SKFacts sk36Slice
    sk36LogOuterCertificate sk36LogKCertificate
    sk36LogDArgCertificate :=
  { domain := by norm_num [sk36Slice]
    kPositive := by
      norm_num [sk36Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk36LogOuter_valid
    logK := sk36LogK_valid
    logDArg := sk36LogDArg_valid }

noncomputable def sk36RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (15786443/16777216), upper := (16191371/16777216) }
    logK := { lower := (7487455/16777216), upper := (4072735/8388608) }
    logDArg := { lower := (7632775/16777216), upper := (2175979/4194304) } }

set_option maxRecDepth 1000000 in
private theorem sk36LogOuterInput_eq :
    sk36RoundedInputs.logOuter = outerEnclosure 24
      (sk36LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk36LogKInput_eq :
    sk36RoundedInputs.logK = outerEnclosure 24
      (sk36LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk36LogDArgInput_eq :
    sk36RoundedInputs.logDArg = outerEnclosure 24
      (sk36LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk36RoundedFacts : SKRoundedFacts 8
    sk36LogOuterCertificate sk36LogKCertificate
    sk36LogDArgCertificate sk36RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk36LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk36LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk36LogDArgInput_eq }

noncomputable def sk37Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (15/8) }

noncomputable def sk37LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (720867/524288) }, upper := { exponent := 1, mantissa := (23/16) } }

noncomputable def sk37LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (7/4) }, upper := { exponent := 0, mantissa := (15/8) } }

noncomputable def sk37LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (20151479/13762560) }, upper := { exponent := 0, mantissa := (23/14) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk37LogOuter_valid :
    sk37LogOuterCertificate.check sk37Slice.outerAD.value = true := by
  norm_num [sk37LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk37Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk37LogK_valid :
    sk37LogKCertificate.check sk37Slice.kAD.value = true := by
  norm_num [sk37LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk37Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk37LogDArg_valid :
    sk37LogDArgCertificate.check sk37Slice.dArgAD.value = true := by
  norm_num [sk37LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk37Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk37ValidityFacts : SKFacts sk37Slice
    sk37LogOuterCertificate sk37LogKCertificate
    sk37LogDArgCertificate :=
  { domain := by norm_num [sk37Slice]
    kPositive := by
      norm_num [sk37Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk37LogOuter_valid
    logK := sk37LogK_valid
    logDArg := sk37LogDArg_valid }

noncomputable def sk37RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (4242793/4194304), upper := (17717625/16777216) }
    logK := { lower := (4694397/8388608), upper := (82393/131072) }
    logDArg := { lower := (6397585/16777216), upper := (8328829/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk37LogOuterInput_eq :
    sk37RoundedInputs.logOuter = outerEnclosure 24
      (sk37LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk37LogKInput_eq :
    sk37RoundedInputs.logK = outerEnclosure 24
      (sk37LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk37LogDArgInput_eq :
    sk37RoundedInputs.logDArg = outerEnclosure 24
      (sk37LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk37RoundedFacts : SKRoundedFacts 8
    sk37LogOuterCertificate sk37LogKCertificate
    sk37LogDArgCertificate sk37RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk37LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk37LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk37LogDArgInput_eq }

noncomputable def sk38Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (2) }

noncomputable def sk38LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (753633/524288) }, upper := { exponent := 1, mantissa := (3/2) } }

noncomputable def sk38LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (15/8) }, upper := { exponent := 1, mantissa := (1) } }

noncomputable def sk38LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (7525397/5242880) }, upper := { exponent := 0, mantissa := (8/5) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk38LogOuter_valid :
    sk38LogOuterCertificate.check sk38Slice.outerAD.value = true := by
  norm_num [sk38LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk38Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk38LogK_valid :
    sk38LogKCertificate.check sk38Slice.kAD.value = true := by
  norm_num [sk38LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk38Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk38LogDArg_valid :
    sk38LogDArgCertificate.check sk38Slice.dArgAD.value = true := by
  norm_num [sk38LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk38Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk38ValidityFacts : SKFacts sk38Slice
    sk38LogOuterCertificate sk38LogKCertificate
    sk38LogDArgCertificate :=
  { domain := by norm_num [sk38Slice]
    kPositive := by
      norm_num [sk38Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk38LogOuter_valid
    logK := sk38LogK_valid
    logDArg := sk38LogDArg_valid }

noncomputable def sk38RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (17716933/16777216), upper := (2303957/2097152) }
    logK := { lower := (10546303/16777216), upper := (11629081/16777216) }
    logDArg := { lower := (6063497/16777216), upper := (7885353/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk38LogOuterInput_eq :
    sk38RoundedInputs.logOuter = outerEnclosure 24
      (sk38LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk38LogKInput_eq :
    sk38RoundedInputs.logK = outerEnclosure 24
      (sk38LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk38LogDArgInput_eq :
    sk38RoundedInputs.logDArg = outerEnclosure 24
      (sk38LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk38RoundedFacts : SKRoundedFacts 8
    sk38LogOuterCertificate sk38LogKCertificate
    sk38LogDArgCertificate sk38RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk38LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk38LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk38LogDArgInput_eq }

noncomputable def sk39Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (29/16) }

noncomputable def sk39LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (1441735/1048576) }, upper := { exponent := 1, mantissa := (45/32) } }

noncomputable def sk39LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (7/4) }, upper := { exponent := 0, mantissa := (29/16) } }

noncomputable def sk39LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (80704335/53215232) }, upper := { exponent := 0, mantissa := (45/28) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk39LogOuter_valid :
    sk39LogOuterCertificate.check sk39Slice.outerAD.value = true := by
  norm_num [sk39LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk39Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk39LogK_valid :
    sk39LogKCertificate.check sk39Slice.kAD.value = true := by
  norm_num [sk39LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk39Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk39LogDArg_valid :
    sk39LogDArgCertificate.check sk39Slice.dArgAD.value = true := by
  norm_num [sk39LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk39Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk39ValidityFacts : SKFacts sk39Slice
    sk39LogOuterCertificate sk39LogKCertificate
    sk39LogDArgCertificate :=
  { domain := by norm_num [sk39Slice]
    kPositive := by
      norm_num [sk39Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk39LogOuter_valid
    logK := sk39LogK_valid
    logDArg := sk39LogDArg_valid }

noncomputable def sk39RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (16971183/16777216), upper := (1084305/1048576) }
    logK := { lower := (4694397/8388608), upper := (4988765/8388608) }
    logDArg := { lower := (6986831/16777216), upper := (7960085/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk39LogOuterInput_eq :
    sk39RoundedInputs.logOuter = outerEnclosure 24
      (sk39LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk39LogKInput_eq :
    sk39RoundedInputs.logK = outerEnclosure 24
      (sk39LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk39LogDArgInput_eq :
    sk39RoundedInputs.logDArg = outerEnclosure 24
      (sk39LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk39RoundedFacts : SKRoundedFacts 8
    sk39LogOuterCertificate sk39LogKCertificate
    sk39LogDArgCertificate sk39RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk39LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk39LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk39LogDArgInput_eq }

noncomputable def sk40Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (15/8) }

noncomputable def sk40LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (1474501/1048576) }, upper := { exponent := 1, mantissa := (23/16) } }

noncomputable def sk40LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (29/16) }, upper := { exponent := 0, mantissa := (15/8) } }

noncomputable def sk40LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (28496077/19005440) }, upper := { exponent := 0, mantissa := (46/29) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk40LogOuter_valid :
    sk40LogOuterCertificate.check sk40Slice.outerAD.value = true := by
  norm_num [sk40LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk40Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk40LogK_valid :
    sk40LogKCertificate.check sk40Slice.kAD.value = true := by
  norm_num [sk40LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk40Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk40LogDArg_valid :
    sk40LogDArgCertificate.check sk40Slice.dArgAD.value = true := by
  norm_num [sk40LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk40Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk40ValidityFacts : SKFacts sk40Slice
    sk40LogOuterCertificate sk40LogKCertificate
    sk40LogDArgCertificate :=
  { domain := by norm_num [sk40Slice]
    kPositive := by
      norm_num [sk40Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk40LogOuter_valid
    logK := sk40LogK_valid
    logDArg := sk40LogDArg_valid }

noncomputable def sk40RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (17348207/16777216), upper := (17717625/16777216) }
    logK := { lower := (9977529/16777216), upper := (82393/131072) }
    logDArg := { lower := (6795463/16777216), upper := (7740095/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk40LogOuterInput_eq :
    sk40RoundedInputs.logOuter = outerEnclosure 24
      (sk40LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk40LogKInput_eq :
    sk40RoundedInputs.logK = outerEnclosure 24
      (sk40LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk40LogDArgInput_eq :
    sk40RoundedInputs.logDArg = outerEnclosure 24
      (sk40LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk40RoundedFacts : SKRoundedFacts 8
    sk40LogOuterCertificate sk40LogKCertificate
    sk40LogDArgCertificate sk40RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk40LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk40LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk40LogDArgInput_eq }

noncomputable def sk41Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (31/16) }

noncomputable def sk41LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (1507267/1048576) }, upper := { exponent := 1, mantissa := (47/32) } }

noncomputable def sk41LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (15/8) }, upper := { exponent := 0, mantissa := (31/16) } }

noncomputable def sk41LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (30134397/20316160) }, upper := { exponent := 0, mantissa := (47/30) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk41LogOuter_valid :
    sk41LogOuterCertificate.check sk41Slice.outerAD.value = true := by
  norm_num [sk41LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk41Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk41LogK_valid :
    sk41LogKCertificate.check sk41Slice.kAD.value = true := by
  norm_num [sk41LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk41Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk41LogDArg_valid :
    sk41LogDArgCertificate.check sk41Slice.dArgAD.value = true := by
  norm_num [sk41LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk41Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk41ValidityFacts : SKFacts sk41Slice
    sk41LogOuterCertificate sk41LogKCertificate
    sk41LogDArgCertificate :=
  { domain := by norm_num [sk41Slice]
    kPositive := by
      norm_num [sk41Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk41LogOuter_valid
    logK := sk41LogK_valid
    logDArg := sk41LogDArg_valid }

noncomputable def sk41RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (1107309/1048576), upper := (18078439/16777216) }
    logK := { lower := (10546303/16777216), upper := (5548213/8388608) }
    logDArg := { lower := (1653607/4194304), upper := (7532135/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk41LogOuterInput_eq :
    sk41RoundedInputs.logOuter = outerEnclosure 24
      (sk41LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk41LogKInput_eq :
    sk41RoundedInputs.logK = outerEnclosure 24
      (sk41LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk41LogDArgInput_eq :
    sk41RoundedInputs.logDArg = outerEnclosure 24
      (sk41LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk41RoundedFacts : SKRoundedFacts 8
    sk41LogOuterCertificate sk41LogKCertificate
    sk41LogDArgCertificate sk41RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk41LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk41LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk41LogDArgInput_eq }

noncomputable def sk42Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2) }

noncomputable def sk42LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (1540033/1048576) }, upper := { exponent := 1, mantissa := (3/2) } }

noncomputable def sk42LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (31/16) }, upper := { exponent := 1, mantissa := (1) } }

noncomputable def sk42LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (95449215/65011712) }, upper := { exponent := 0, mantissa := (48/31) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk42LogOuter_valid :
    sk42LogOuterCertificate.check sk42Slice.outerAD.value = true := by
  norm_num [sk42LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk42Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk42LogK_valid :
    sk42LogKCertificate.check sk42Slice.kAD.value = true := by
  norm_num [sk42LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk42Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk42LogDArg_valid :
    sk42LogDArgCertificate.check sk42Slice.dArgAD.value = true := by
  norm_num [sk42LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk42Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk42ValidityFacts : SKFacts sk42Slice
    sk42LogOuterCertificate sk42LogKCertificate
    sk42LogDArgCertificate :=
  { domain := by norm_num [sk42Slice]
    kPositive := by
      norm_num [sk42Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk42LogOuter_valid
    logK := sk42LogK_valid
    logDArg := sk42LogDArg_valid }

noncomputable def sk42RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (18077751/16777216), upper := (2303957/2097152) }
    logK := { lower := (11096425/16777216), upper := (11629081/16777216) }
    logDArg := { lower := (3221451/8388608), upper := (7335231/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk42LogOuterInput_eq :
    sk42RoundedInputs.logOuter = outerEnclosure 24
      (sk42LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk42LogKInput_eq :
    sk42RoundedInputs.logK = outerEnclosure 24
      (sk42LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk42LogDArgInput_eq :
    sk42RoundedInputs.logDArg = outerEnclosure 24
      (sk42LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk42RoundedFacts : SKRoundedFacts 8
    sk42LogOuterCertificate sk42LogKCertificate
    sk42LogDArgCertificate sk42RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk42LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk42LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk42LogDArgInput_eq }

noncomputable def sk43Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (49/32) }

noncomputable def sk43LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (2621343/2097152) }, upper := { exponent := 1, mantissa := (81/64) } }

noncomputable def sk43LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (3/2) }, upper := { exponent := 0, mantissa := (49/32) } }

noncomputable def sk43LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (83872021/51380224) }, upper := { exponent := 0, mantissa := (27/16) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk43LogOuter_valid :
    sk43LogOuterCertificate.check sk43Slice.outerAD.value = true := by
  norm_num [sk43LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk43Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk43LogK_valid :
    sk43LogKCertificate.check sk43Slice.kAD.value = true := by
  norm_num [sk43LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk43Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk43LogDArg_valid :
    sk43LogDArgCertificate.check sk43Slice.dArgAD.value = true := by
  norm_num [sk43LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk43Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk43ValidityFacts : SKFacts sk43Slice
    sk43LogOuterCertificate sk43LogKCertificate
    sk43LogDArgCertificate :=
  { domain := by norm_num [sk43Slice]
    kPositive := by
      norm_num [sk43Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk43LogOuter_valid
    logK := sk43LogK_valid
    logDArg := sk43LogDArg_valid }

noncomputable def sk43RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (7686093/8388608), upper := (1947653/2097152) }
    logK := { lower := (6802575/16777216), upper := (3574255/8388608) }
    logDArg := { lower := (8221485/16777216), upper := (1097331/2097152) } }

set_option maxRecDepth 1000000 in
private theorem sk43LogOuterInput_eq :
    sk43RoundedInputs.logOuter = outerEnclosure 24
      (sk43LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk43LogKInput_eq :
    sk43RoundedInputs.logK = outerEnclosure 24
      (sk43LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk43LogDArgInput_eq :
    sk43RoundedInputs.logDArg = outerEnclosure 24
      (sk43LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk43RoundedFacts : SKRoundedFacts 8
    sk43LogOuterCertificate sk43LogKCertificate
    sk43LogDArgCertificate sk43RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk43LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk43LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk43LogDArgInput_eq }

noncomputable def sk44Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (49/32), kHi := (25/16) }

noncomputable def sk44LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (2654109/2097152) }, upper := { exponent := 1, mantissa := (41/32) } }

noncomputable def sk44LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (49/32) }, upper := { exponent := 0, mantissa := (25/16) } }

noncomputable def sk44LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (52013963/32112640) }, upper := { exponent := 0, mantissa := (82/49) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk44LogOuter_valid :
    sk44LogOuterCertificate.check sk44Slice.outerAD.value = true := by
  norm_num [sk44LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk44Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk44LogK_valid :
    sk44LogKCertificate.check sk44Slice.kAD.value = true := by
  norm_num [sk44LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk44Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk44LogDArg_valid :
    sk44LogDArgCertificate.check sk44Slice.dArgAD.value = true := by
  norm_num [sk44LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk44Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk44ValidityFacts : SKFacts sk44Slice
    sk44LogOuterCertificate sk44LogKCertificate
    sk44LogDArgCertificate :=
  { domain := by norm_num [sk44Slice]
    kPositive := by
      norm_num [sk44Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk44LogOuter_valid
    logK := sk44LogK_valid
    logDArg := sk44LogDArg_valid }

noncomputable def sk44RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (15580597/16777216), upper := (7893541/8388608) }
    logK := { lower := (7148509/16777216), upper := (233983/524288) }
    logDArg := { lower := (8091021/16777216), upper := (8638571/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk44LogOuterInput_eq :
    sk44RoundedInputs.logOuter = outerEnclosure 24
      (sk44LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk44LogKInput_eq :
    sk44RoundedInputs.logK = outerEnclosure 24
      (sk44LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk44LogDArgInput_eq :
    sk44RoundedInputs.logDArg = outerEnclosure 24
      (sk44LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk44RoundedFacts : SKRoundedFacts 8
    sk44LogOuterCertificate sk44LogKCertificate
    sk44LogDArgCertificate sk44RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk44LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk44LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk44LogDArgInput_eq }

noncomputable def sk45Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (25/16), kHi := (51/32) }

noncomputable def sk45LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (2686875/2097152) }, upper := { exponent := 1, mantissa := (83/64) } }

noncomputable def sk45LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (25/16) }, upper := { exponent := 0, mantissa := (51/32) } }

noncomputable def sk45LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (268654631/167116800) }, upper := { exponent := 0, mantissa := (83/50) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk45LogOuter_valid :
    sk45LogOuterCertificate.check sk45Slice.outerAD.value = true := by
  norm_num [sk45LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk45Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk45LogK_valid :
    sk45LogKCertificate.check sk45Slice.kAD.value = true := by
  norm_num [sk45LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk45Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk45LogDArg_valid :
    sk45LogDArgCertificate.check sk45Slice.dArgAD.value = true := by
  norm_num [sk45LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk45Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk45ValidityFacts : SKFacts sk45Slice
    sk45LogOuterCertificate sk45LogKCertificate
    sk45LogDArgCertificate :=
  { domain := by norm_num [sk45Slice]
    kPositive := by
      norm_num [sk45Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk45LogOuter_valid
    logK := sk45LogK_valid
    logDArg := sk45LogDArg_valid }

noncomputable def sk45RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (7893225/8388608), upper := (3997611/4194304) }
    logK := { lower := (7487455/16777216), upper := (7819689/16777216) }
    logDArg := { lower := (7964709/16777216), upper := (8502989/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk45LogOuterInput_eq :
    sk45RoundedInputs.logOuter = outerEnclosure 24
      (sk45LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk45LogKInput_eq :
    sk45RoundedInputs.logK = outerEnclosure 24
      (sk45LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk45LogDArgInput_eq :
    sk45RoundedInputs.logDArg = outerEnclosure 24
      (sk45LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk45RoundedFacts : SKRoundedFacts 8
    sk45LogOuterCertificate sk45LogKCertificate
    sk45LogDArgCertificate sk45RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk45LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk45LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk45LogDArgInput_eq }

noncomputable def sk46Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (51/32), kHi := (13/8) }

noncomputable def sk46LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (2719641/2097152) }, upper := { exponent := 1, mantissa := (21/16) } }

noncomputable def sk46LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (51/32) }, upper := { exponent := 0, mantissa := (13/8) } }

noncomputable def sk46LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (92456837/57933824) }, upper := { exponent := 0, mantissa := (28/17) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk46LogOuter_valid :
    sk46LogOuterCertificate.check sk46Slice.outerAD.value = true := by
  norm_num [sk46LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk46Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk46LogK_valid :
    sk46LogKCertificate.check sk46Slice.kAD.value = true := by
  norm_num [sk46LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk46Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk46LogDArg_valid :
    sk46LogDArgCertificate.check sk46Slice.dArgAD.value = true := by
  norm_num [sk46LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk46Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk46ValidityFacts : SKFacts sk46Slice
    sk46LogOuterCertificate sk46LogKCertificate
    sk46LogDArgCertificate :=
  { domain := by norm_num [sk46Slice]
    kPositive := by
      norm_num [sk46Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk46LogOuter_valid
    logK := sk46LogK_valid
    logDArg := sk46LogDArg_valid }

noncomputable def sk46RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (999363/1048576), upper := (16191371/16777216) }
    logK := { lower := (977461/2097152), upper := (4072735/8388608) }
    logDArg := { lower := (3921175/8388608), upper := (8371683/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk46LogOuterInput_eq :
    sk46RoundedInputs.logOuter = outerEnclosure 24
      (sk46LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk46LogKInput_eq :
    sk46RoundedInputs.logK = outerEnclosure 24
      (sk46LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk46LogDArgInput_eq :
    sk46RoundedInputs.logDArg = outerEnclosure 24
      (sk46LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk46RoundedFacts : SKRoundedFacts 8
    sk46LogOuterCertificate sk46LogKCertificate
    sk46LogDArgCertificate sk46RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk46LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk46LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk46LogDArgInput_eq }

noncomputable def sk47Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (63/32) }

noncomputable def sk47LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (3080067/2097152) }, upper := { exponent := 1, mantissa := (95/64) } }

noncomputable def sk47LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (31/16) }, upper := { exponent := 0, mantissa := (63/32) } }

noncomputable def sk47LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (381895415/255983616) }, upper := { exponent := 0, mantissa := (95/62) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk47LogOuter_valid :
    sk47LogOuterCertificate.check sk47Slice.outerAD.value = true := by
  norm_num [sk47LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk47Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk47LogK_valid :
    sk47LogKCertificate.check sk47Slice.kAD.value = true := by
  norm_num [sk47LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk47Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk47LogDArg_valid :
    sk47LogDArgCertificate.check sk47Slice.dArgAD.value = true := by
  norm_num [sk47LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk47Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk47ValidityFacts : SKFacts sk47Slice
    sk47LogOuterCertificate sk47LogKCertificate
    sk47LogDArgCertificate :=
  { domain := by norm_num [sk47Slice]
    kPositive := by
      norm_num [sk47Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk47LogOuter_valid
    logK := sk47LogK_valid
    logDArg := sk47LogDArg_valid }

noncomputable def sk47RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (18077757/16777216), upper := (18255977/16777216) }
    logK := { lower := (11096425/16777216), upper := (11364867/16777216) }
    logDArg := { lower := (6711445/16777216), upper := (27967/65536) } }

set_option maxRecDepth 1000000 in
private theorem sk47LogOuterInput_eq :
    sk47RoundedInputs.logOuter = outerEnclosure 24
      (sk47LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk47LogKInput_eq :
    sk47RoundedInputs.logK = outerEnclosure 24
      (sk47LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk47LogDArgInput_eq :
    sk47RoundedInputs.logDArg = outerEnclosure 24
      (sk47LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk47RoundedFacts : SKRoundedFacts 8
    sk47LogOuterCertificate sk47LogKCertificate
    sk47LogDArgCertificate sk47RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk47LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk47LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk47LogDArgInput_eq }

noncomputable def sk48Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (63/32), kHi := (2) }

noncomputable def sk48LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (3112833/2097152) }, upper := { exponent := 1, mantissa := (3/2) } }

noncomputable def sk48LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (63/32) }, upper := { exponent := 1, mantissa := (1) } }

noncomputable def sk48LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (43576007/29360128) }, upper := { exponent := 0, mantissa := (32/21) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk48LogOuter_valid :
    sk48LogOuterCertificate.check sk48Slice.outerAD.value = true := by
  norm_num [sk48LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk48Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk48LogK_valid :
    sk48LogKCertificate.check sk48Slice.kAD.value = true := by
  norm_num [sk48LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk48Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk48LogDArg_valid :
    sk48LogDArgCertificate.check sk48Slice.dArgAD.value = true := by
  norm_num [sk48LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk48Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk48ValidityFacts : SKFacts sk48Slice
    sk48LogOuterCertificate sk48LogKCertificate
    sk48LogDArgCertificate :=
  { domain := by norm_num [sk48Slice]
    kPositive := by
      norm_num [sk48Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk48LogOuter_valid
    logK := sk48LogK_valid
    logDArg := sk48LogDArg_valid }

noncomputable def sk48RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (18255291/16777216), upper := (2303957/2097152) }
    logK := { lower := (5682433/8388608), upper := (11629081/16777216) }
    logDArg := { lower := (1656201/4194304), upper := (3533395/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk48LogOuterInput_eq :
    sk48RoundedInputs.logOuter = outerEnclosure 24
      (sk48LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk48LogKInput_eq :
    sk48RoundedInputs.logK = outerEnclosure 24
      (sk48LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk48LogDArgInput_eq :
    sk48RoundedInputs.logDArg = outerEnclosure 24
      (sk48LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk48RoundedFacts : SKRoundedFacts 8
    sk48LogOuterCertificate sk48LogKCertificate
    sk48LogDArgCertificate sk48RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk48LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk48LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk48LogDArgInput_eq }

noncomputable def sk49Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (61/32) }

noncomputable def sk49LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (3014535/2097152) }, upper := { exponent := 1, mantissa := (93/64) } }

noncomputable def sk49LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (15/8) }, upper := { exponent := 0, mantissa := (61/32) } }

noncomputable def sk49LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (120570437/79953920) }, upper := { exponent := 0, mantissa := (31/20) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk49LogOuter_valid :
    sk49LogOuterCertificate.check sk49Slice.outerAD.value = true := by
  norm_num [sk49LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk49Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk49LogK_valid :
    sk49LogKCertificate.check sk49Slice.kAD.value = true := by
  norm_num [sk49LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk49Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk49LogDArg_valid :
    sk49LogDArgCertificate.check sk49Slice.dArgAD.value = true := by
  norm_num [sk49LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk49Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk49ValidityFacts : SKFacts sk49Slice
    sk49LogOuterCertificate sk49LogKCertificate
    sk49LogDArgCertificate :=
  { domain := by norm_num [sk49Slice]
    kPositive := by
      norm_num [sk49Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk49LogOuter_valid
    logK := sk49LogK_valid
    logDArg := sk49LogDArg_valid }

noncomputable def sk49RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (8858475/8388608), upper := (8949501/8388608) }
    logK := { lower := (10546303/16777216), upper := (2705905/4194304) }
    logDArg := { lower := (3445903/8388608), upper := (3676349/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk49LogOuterInput_eq :
    sk49RoundedInputs.logOuter = outerEnclosure 24
      (sk49LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk49LogKInput_eq :
    sk49RoundedInputs.logK = outerEnclosure 24
      (sk49LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk49LogDArgInput_eq :
    sk49RoundedInputs.logDArg = outerEnclosure 24
      (sk49LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk49RoundedFacts : SKRoundedFacts 8
    sk49LogOuterCertificate sk49LogKCertificate
    sk49LogDArgCertificate sk49RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk49LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk49LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk49LogDArgInput_eq }

noncomputable def sk50Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (61/32), kHi := (31/16) }

noncomputable def sk50LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (3047301/2097152) }, upper := { exponent := 1, mantissa := (47/32) } }

noncomputable def sk50LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (61/32) }, upper := { exponent := 0, mantissa := (31/16) } }

noncomputable def sk50LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (371737831/247857152) }, upper := { exponent := 0, mantissa := (94/61) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk50LogOuter_valid :
    sk50LogOuterCertificate.check sk50Slice.outerAD.value = true := by
  norm_num [sk50LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk50Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk50LogK_valid :
    sk50LogKCertificate.check sk50Slice.kAD.value = true := by
  norm_num [sk50LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk50Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk50LogDArg_valid :
    sk50LogDArgCertificate.check sk50Slice.dArgAD.value = true := by
  norm_num [sk50LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk50Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk50ValidityFacts : SKFacts sk50Slice
    sk50LogOuterCertificate sk50LogKCertificate
    sk50LogDArgCertificate :=
  { domain := by norm_num [sk50Slice]
    kPositive := by
      norm_num [sk50Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk50LogOuter_valid
    logK := sk50LogK_valid
    logDArg := sk50LogDArg_valid }

noncomputable def sk50RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (17898323/16777216), upper := (18078439/16777216) }
    logK := { lower := (5411809/8388608), upper := (5548213/8388608) }
    logDArg := { lower := (3400207/8388608), upper := (1813705/4194304) } }

set_option maxRecDepth 1000000 in
private theorem sk50LogOuterInput_eq :
    sk50RoundedInputs.logOuter = outerEnclosure 24
      (sk50LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk50LogKInput_eq :
    sk50RoundedInputs.logK = outerEnclosure 24
      (sk50LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk50LogDArgInput_eq :
    sk50RoundedInputs.logDArg = outerEnclosure 24
      (sk50LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk50RoundedFacts : SKRoundedFacts 8
    sk50LogOuterCertificate sk50LogKCertificate
    sk50LogDArgCertificate sk50RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk50LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk50LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk50LogDArgInput_eq }

noncomputable def sk51Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (59/32) }

noncomputable def sk51LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (2949003/2097152) }, upper := { exponent := 1, mantissa := (91/64) } }

noncomputable def sk51LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (29/16) }, upper := { exponent := 0, mantissa := (59/32) } }

noncomputable def sk51LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (342051463/224264192) }, upper := { exponent := 0, mantissa := (91/58) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk51LogOuter_valid :
    sk51LogOuterCertificate.check sk51Slice.outerAD.value = true := by
  norm_num [sk51LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk51Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk51LogK_valid :
    sk51LogKCertificate.check sk51Slice.kAD.value = true := by
  norm_num [sk51LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk51Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk51LogDArg_valid :
    sk51LogDArgCertificate.check sk51Slice.dArgAD.value = true := by
  norm_num [sk51LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk51Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk51ValidityFacts : SKFacts sk51Slice
    sk51LogOuterCertificate sk51LogKCertificate
    sk51LogDArgCertificate :=
  { domain := by norm_num [sk51Slice]
    kPositive := by
      norm_num [sk51Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk51LogOuter_valid
    logK := sk51LogK_valid
    logDArg := sk51LogDArg_valid }

noncomputable def sk51RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (17348213/16777216), upper := (17534265/16777216) }
    logK := { lower := (9977529/16777216), upper := (10264327/16777216) }
    logDArg := { lower := (7082273/16777216), upper := (7556735/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk51LogOuterInput_eq :
    sk51RoundedInputs.logOuter = outerEnclosure 24
      (sk51LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk51LogKInput_eq :
    sk51RoundedInputs.logK = outerEnclosure 24
      (sk51LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk51LogDArgInput_eq :
    sk51RoundedInputs.logDArg = outerEnclosure 24
      (sk51LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk51RoundedFacts : SKRoundedFacts 8
    sk51LogOuterCertificate sk51LogKCertificate
    sk51LogDArgCertificate sk51RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk51LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk51LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk51LogDArgInput_eq }

noncomputable def sk52Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (59/32), kHi := (15/8) }

noncomputable def sk52LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (2981769/2097152) }, upper := { exponent := 1, mantissa := (23/16) } }

noncomputable def sk52LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (59/32) }, upper := { exponent := 0, mantissa := (15/8) } }

noncomputable def sk52LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (70363171/46399488) }, upper := { exponent := 0, mantissa := (92/59) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk52LogOuter_valid :
    sk52LogOuterCertificate.check sk52Slice.outerAD.value = true := by
  norm_num [sk52LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk52Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk52LogK_valid :
    sk52LogKCertificate.check sk52Slice.kAD.value = true := by
  norm_num [sk52LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk52Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk52LogDArg_valid :
    sk52LogDArgCertificate.check sk52Slice.dArgAD.value = true := by
  norm_num [sk52LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk52Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk52ValidityFacts : SKFacts sk52Slice
    sk52LogOuterCertificate sk52LogKCertificate
    sk52LogDArgCertificate :=
  { domain := by norm_num [sk52Slice]
    kPositive := by
      norm_num [sk52Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk52LogOuter_valid
    logK := sk52LogK_valid
    logDArg := sk52LogDArg_valid }

noncomputable def sk52RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (8766797/8388608), upper := (17717625/16777216) }
    logK := { lower := (5132163/8388608), upper := (82393/131072) }
    logDArg := { lower := (6985723/16777216), upper := (3726649/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk52LogOuterInput_eq :
    sk52RoundedInputs.logOuter = outerEnclosure 24
      (sk52LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk52LogKInput_eq :
    sk52RoundedInputs.logK = outerEnclosure 24
      (sk52LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk52LogDArgInput_eq :
    sk52RoundedInputs.logDArg = outerEnclosure 24
      (sk52LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk52RoundedFacts : SKRoundedFacts 8
    sk52LogOuterCertificate sk52LogKCertificate
    sk52LogDArgCertificate sk52RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk52LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk52LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk52LogDArgInput_eq }

noncomputable def sk53Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (45/32) }

noncomputable def sk53LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (2490279/2097152) }, upper := { exponent := 1, mantissa := (77/64) } }

noncomputable def sk53LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (11/8) }, upper := { exponent := 0, mantissa := (45/32) } }

noncomputable def sk53LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (3983849/2359296) }, upper := { exponent := 0, mantissa := (7/4) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk53LogOuter_valid :
    sk53LogOuterCertificate.check sk53Slice.outerAD.value = true := by
  norm_num [sk53LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk53Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk53LogK_valid :
    sk53LogKCertificate.check sk53Slice.kAD.value = true := by
  norm_num [sk53LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk53Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk53LogDArg_valid :
    sk53LogDArgCertificate.check sk53Slice.dArgAD.value = true := by
  norm_num [sk53LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk53Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk53ValidityFacts : SKFacts sk53Slice
    sk53LogOuterCertificate sk53LogKCertificate
    sk53LogDArgCertificate :=
  { domain := by norm_num [sk53Slice]
    kPositive := by
      norm_num [sk53Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk53LogOuter_valid
    logK := sk53LogK_valid
    logDArg := sk53LogDArg_valid }

noncomputable def sk53RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (14511649/16777216), upper := (14731563/16777216) }
    logK := { lower := (5342767/16777216), upper := (5719799/16777216) }
    logDArg := { lower := (4394667/8388608), upper := (9388795/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk53LogOuterInput_eq :
    sk53RoundedInputs.logOuter = outerEnclosure 24
      (sk53LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk53LogKInput_eq :
    sk53RoundedInputs.logK = outerEnclosure 24
      (sk53LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk53LogDArgInput_eq :
    sk53RoundedInputs.logDArg = outerEnclosure 24
      (sk53LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk53RoundedFacts : SKRoundedFacts 8
    sk53LogOuterCertificate sk53LogKCertificate
    sk53LogDArgCertificate sk53RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk53LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk53LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk53LogDArgInput_eq }

noncomputable def sk54Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (45/32), kHi := (23/16) }

noncomputable def sk54LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (2523045/2097152) }, upper := { exponent := 1, mantissa := (39/32) } }

noncomputable def sk54LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (45/32) }, upper := { exponent := 0, mantissa := (23/16) } }

noncomputable def sk54LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (25226799/15073280) }, upper := { exponent := 0, mantissa := (26/15) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk54LogOuter_valid :
    sk54LogOuterCertificate.check sk54Slice.outerAD.value = true := by
  norm_num [sk54LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk54Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk54LogK_valid :
    sk54LogKCertificate.check sk54Slice.kAD.value = true := by
  norm_num [sk54LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk54Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk54LogDArg_valid :
    sk54LogDArgCertificate.check sk54Slice.dArgAD.value = true := by
  norm_num [sk54LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk54Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk54ValidityFacts : SKFacts sk54Slice
    sk54LogOuterCertificate sk54LogKCertificate
    sk54LogDArgCertificate :=
  { domain := by norm_num [sk54Slice]
    kPositive := by
      norm_num [sk54Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk54LogOuter_valid
    logK := sk54LogK_valid
    logDArg := sk54LogDArg_valid }

noncomputable def sk54RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (3682739/4194304), upper := (7474023/8388608) }
    logK := { lower := (2859899/8388608), upper := (190267/524288) }
    logDArg := { lower := (8639985/16777216), upper := (9228247/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk54LogOuterInput_eq :
    sk54RoundedInputs.logOuter = outerEnclosure 24
      (sk54LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk54LogKInput_eq :
    sk54RoundedInputs.logK = outerEnclosure 24
      (sk54LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk54LogDArgInput_eq :
    sk54RoundedInputs.logDArg = outerEnclosure 24
      (sk54LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk54RoundedFacts : SKRoundedFacts 8
    sk54LogOuterCertificate sk54LogKCertificate
    sk54LogDArgCertificate sk54RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk54LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk54LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk54LogDArgInput_eq }

noncomputable def sk55Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (53/32) }

noncomputable def sk55LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (2752407/2097152) }, upper := { exponent := 1, mantissa := (85/64) } }

noncomputable def sk55LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (13/8) }, upper := { exponent := 0, mantissa := (53/32) } }

noncomputable def sk55LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (286217455/180617216) }, upper := { exponent := 0, mantissa := (85/52) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk55LogOuter_valid :
    sk55LogOuterCertificate.check sk55Slice.outerAD.value = true := by
  norm_num [sk55LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk55Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk55LogK_valid :
    sk55LogKCertificate.check sk55Slice.kAD.value = true := by
  norm_num [sk55LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk55Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk55LogDArg_valid :
    sk55LogDArgCertificate.check sk55Slice.dArgAD.value = true := by
  norm_num [sk55LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk55Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk55ValidityFacts : SKFacts sk55Slice
    sk55LogOuterCertificate sk55LogKCertificate
    sk55LogDArgCertificate :=
  { domain := by norm_num [sk55Slice]
    kPositive := by
      norm_num [sk55Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk55LogOuter_valid
    logK := sk55LogK_valid
    logDArg := sk55LogDArg_valid }

noncomputable def sk55RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (8095365/8388608), upper := (16389921/16777216) }
    logK := { lower := (8145469/16777216), upper := (4232523/8388608) }
    logDArg := { lower := (3861879/8388608), upper := (8244451/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk55LogOuterInput_eq :
    sk55RoundedInputs.logOuter = outerEnclosure 24
      (sk55LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk55LogKInput_eq :
    sk55RoundedInputs.logK = outerEnclosure 24
      (sk55LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk55LogDArgInput_eq :
    sk55RoundedInputs.logDArg = outerEnclosure 24
      (sk55LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk55RoundedFacts : SKRoundedFacts 8
    sk55LogOuterCertificate sk55LogKCertificate
    sk55LogDArgCertificate sk55RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk55LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk55LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk55LogDArgInput_eq }

noncomputable def sk56Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (53/32), kHi := (27/16) }

noncomputable def sk56LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (2785173/2097152) }, upper := { exponent := 1, mantissa := (43/32) } }

noncomputable def sk56LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (53/32) }, upper := { exponent := 0, mantissa := (27/16) } }

noncomputable def sk56LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (295195463/187564032) }, upper := { exponent := 0, mantissa := (86/53) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk56LogOuter_valid :
    sk56LogOuterCertificate.check sk56Slice.outerAD.value = true := by
  norm_num [sk56LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk56Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk56LogK_valid :
    sk56LogKCertificate.check sk56Slice.kAD.value = true := by
  norm_num [sk56LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk56Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk56LogDArg_valid :
    sk56LogDArgCertificate.check sk56Slice.dArgAD.value = true := by
  norm_num [sk56LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk56Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk56ValidityFacts : SKFacts sk56Slice
    sk56LogOuterCertificate sk56LogKCertificate
    sk56LogDArgCertificate :=
  { domain := by norm_num [sk56Slice]
    kPositive := by
      norm_num [sk56Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk56LogOuter_valid
    logK := sk56LogK_valid
    logDArg := sk56LogDArg_valid }

noncomputable def sk56RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (16389275/16777216), upper := (4146537/4194304) }
    logK := { lower := (8465045/16777216), upper := (1097331/2097152) }
    logDArg := { lower := (7608759/16777216), upper := (4060551/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk56LogOuterInput_eq :
    sk56RoundedInputs.logOuter = outerEnclosure 24
      (sk56LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk56LogKInput_eq :
    sk56RoundedInputs.logK = outerEnclosure 24
      (sk56LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk56LogDArgInput_eq :
    sk56RoundedInputs.logDArg = outerEnclosure 24
      (sk56LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk56RoundedFacts : SKRoundedFacts 8
    sk56LogOuterCertificate sk56LogKCertificate
    sk56LogDArgCertificate sk56RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk56LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk56LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk56LogDArgInput_eq }

noncomputable def sk57Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (57/32) }

noncomputable def sk57LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (2883471/2097152) }, upper := { exponent := 1, mantissa := (89/64) } }

noncomputable def sk57LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (7/4) }, upper := { exponent := 0, mantissa := (57/32) } }

noncomputable def sk57LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (322915871/209190912) }, upper := { exponent := 0, mantissa := (89/56) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk57LogOuter_valid :
    sk57LogOuterCertificate.check sk57Slice.outerAD.value = true := by
  norm_num [sk57LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk57Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk57LogK_valid :
    sk57LogKCertificate.check sk57Slice.kAD.value = true := by
  norm_num [sk57LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk57Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk57LogDArg_valid :
    sk57LogDArgCertificate.check sk57Slice.dArgAD.value = true := by
  norm_num [sk57LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk57Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk57ValidityFacts : SKFacts sk57Slice
    sk57LogOuterCertificate sk57LogKCertificate
    sk57LogDArgCertificate :=
  { domain := by norm_num [sk57Slice]
    kPositive := by
      norm_num [sk57Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk57LogOuter_valid
    logK := sk57LogK_valid
    logDArg := sk57LogDArg_valid }

noncomputable def sk57RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (16971189/16777216), upper := (17161423/16777216) }
    logK := { lower := (4694397/8388608), upper := (9685745/16777216) }
    logDArg := { lower := (910467/2097152), upper := (1943157/4194304) } }

set_option maxRecDepth 1000000 in
private theorem sk57LogOuterInput_eq :
    sk57RoundedInputs.logOuter = outerEnclosure 24
      (sk57LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk57LogKInput_eq :
    sk57RoundedInputs.logK = outerEnclosure 24
      (sk57LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk57LogDArgInput_eq :
    sk57RoundedInputs.logDArg = outerEnclosure 24
      (sk57LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk57RoundedFacts : SKRoundedFacts 8
    sk57LogOuterCertificate sk57LogKCertificate
    sk57LogDArgCertificate sk57RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk57LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk57LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk57LogDArgInput_eq }

noncomputable def sk58Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (57/32), kHi := (29/16) }

noncomputable def sk58LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (2916237/2097152) }, upper := { exponent := 1, mantissa := (45/32) } }

noncomputable def sk58LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (57/32) }, upper := { exponent := 0, mantissa := (29/16) } }

noncomputable def sk58LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (110806045/72220672) }, upper := { exponent := 0, mantissa := (30/19) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk58LogOuter_valid :
    sk58LogOuterCertificate.check sk58Slice.outerAD.value = true := by
  norm_num [sk58LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk58Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk58LogK_valid :
    sk58LogKCertificate.check sk58Slice.kAD.value = true := by
  norm_num [sk58LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk58Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk58LogDArg_valid :
    sk58LogDArgCertificate.check sk58Slice.dArgAD.value = true := by
  norm_num [sk58LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk58Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk58ValidityFacts : SKFacts sk58Slice
    sk58LogOuterCertificate sk58LogKCertificate
    sk58LogDArgCertificate :=
  { domain := by norm_num [sk58Slice]
    kPositive := by
      norm_num [sk58Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk58LogOuter_valid
    logK := sk58LogK_valid
    logDArg := sk58LogDArg_valid }

noncomputable def sk58RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (2145095/2097152), upper := (1084305/1048576) }
    logK := { lower := (605359/1048576), upper := (4988765/8388608) }
    logDArg := { lower := (7181571/16777216), upper := (7663135/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk58LogOuterInput_eq :
    sk58RoundedInputs.logOuter = outerEnclosure 24
      (sk58LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk58LogKInput_eq :
    sk58RoundedInputs.logK = outerEnclosure 24
      (sk58LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk58LogDArgInput_eq :
    sk58RoundedInputs.logDArg = outerEnclosure 24
      (sk58LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk58RoundedFacts : SKRoundedFacts 8
    sk58LogOuterCertificate sk58LogKCertificate
    sk58LogDArgCertificate sk58RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk58LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk58LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk58LogDArgInput_eq }

noncomputable def sk59Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (17/8) }

noncomputable def sk59LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (786399/524288) }, upper := { exponent := 1, mantissa := (25/16) } }

noncomputable def sk59LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (1) }, upper := { exponent := 1, mantissa := (17/16) } }

noncomputable def sk59LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (1478351/1048576) }, upper := { exponent := 0, mantissa := (25/16) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk59LogOuter_valid :
    sk59LogOuterCertificate.check sk59Slice.outerAD.value = true := by
  norm_num [sk59LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk59Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk59LogK_valid :
    sk59LogKCertificate.check sk59Slice.kAD.value = true := by
  norm_num [sk59LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk59Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk59LogDArg_valid :
    sk59LogDArgCertificate.check sk59Slice.dArgAD.value = true := by
  norm_num [sk59LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk59Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk59ValidityFacts : SKFacts sk59Slice
    sk59LogOuterCertificate sk59LogKCertificate
    sk59LogDArgCertificate :=
  { domain := by norm_num [sk59Slice]
    kPositive := by
      norm_num [sk59Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk59LogOuter_valid
    logK := sk59LogK_valid
    logDArg := sk59LogDArg_valid }

noncomputable def sk59RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (18430951/16777216), upper := (2389567/2097152) }
    logK := { lower := (11629079/16777216), upper := (12646193/16777216) }
    logDArg := { lower := (1440719/4194304), upper := (233983/524288) } }

set_option maxRecDepth 1000000 in
private theorem sk59LogOuterInput_eq :
    sk59RoundedInputs.logOuter = outerEnclosure 24
      (sk59LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk59LogKInput_eq :
    sk59RoundedInputs.logK = outerEnclosure 24
      (sk59LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk59LogDArgInput_eq :
    sk59RoundedInputs.logDArg = outerEnclosure 24
      (sk59LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk59RoundedFacts : SKRoundedFacts 8
    sk59LogOuterCertificate sk59LogKCertificate
    sk59LogDArgCertificate sk59RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk59LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk59LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk59LogDArgInput_eq }

noncomputable def sk60Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (9/4) }

noncomputable def sk60LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (819165/524288) }, upper := { exponent := 1, mantissa := (13/8) } }

noncomputable def sk60LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (17/16) }, upper := { exponent := 1, mantissa := (9/8) } }

noncomputable def sk60LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (27818807/20054016) }, upper := { exponent := 0, mantissa := (26/17) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk60LogOuter_valid :
    sk60LogOuterCertificate.check sk60Slice.outerAD.value = true := by
  norm_num [sk60LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk60Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk60LogK_valid :
    sk60LogKCertificate.check sk60Slice.kAD.value = true := by
  norm_num [sk60LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk60Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk60LogDArg_valid :
    sk60LogDArgCertificate.check sk60Slice.dArgAD.value = true := by
  norm_num [sk60LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk60Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk60ValidityFacts : SKFacts sk60Slice
    sk60LogOuterCertificate sk60LogKCertificate
    sk60LogDArgCertificate :=
  { domain := by norm_num [sk60Slice]
    kPositive := by
      norm_num [sk60Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk60LogOuter_valid
    logK := sk60LogK_valid
    logDArg := sk60LogDArg_valid }

noncomputable def sk60RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (9557909/8388608), upper := (9887275/8388608) }
    logK := { lower := (790387/1048576), upper := (425161/524288) }
    logDArg := { lower := (5490895/16777216), upper := (3564179/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk60LogOuterInput_eq :
    sk60RoundedInputs.logOuter = outerEnclosure 24
      (sk60LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk60LogKInput_eq :
    sk60RoundedInputs.logK = outerEnclosure 24
      (sk60LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk60LogDArgInput_eq :
    sk60RoundedInputs.logDArg = outerEnclosure 24
      (sk60LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk60RoundedFacts : SKRoundedFacts 8
    sk60LogOuterCertificate sk60LogKCertificate
    sk60LogDArgCertificate sk60RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk60LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk60LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk60LogDArgInput_eq }

noncomputable def sk61Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16) }

noncomputable def sk61LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (1572799/1048576) }, upper := { exponent := 1, mantissa := (49/32) } }

noncomputable def sk61LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (1) }, upper := { exponent := 1, mantissa := (33/32) } }

noncomputable def sk61LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (33542101/23068672) }, upper := { exponent := 0, mantissa := (49/32) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk61LogOuter_valid :
    sk61LogOuterCertificate.check sk61Slice.outerAD.value = true := by
  norm_num [sk61LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk61Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk61LogK_valid :
    sk61LogKCertificate.check sk61Slice.kAD.value = true := by
  norm_num [sk61LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk61Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk61LogDArg_valid :
    sk61LogDArgCertificate.check sk61Slice.dArgAD.value = true := by
  norm_num [sk61LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk61Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk61ValidityFacts : SKFacts sk61Slice
    sk61LogOuterCertificate sk61LogKCertificate
    sk61LogDArgCertificate :=
  { domain := by norm_num [sk61Slice]
    kPositive := by
      norm_num [sk61Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk61LogOuter_valid
    logK := sk61LogK_valid
    logDArg := sk61LogDArg_valid }

noncomputable def sk61RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (9215481/8388608), upper := (18777591/16777216) }
    logK := { lower := (11629079/16777216), upper := (189771/262144) }
    logDArg := { lower := (3140073/8388608), upper := (3574255/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk61LogOuterInput_eq :
    sk61RoundedInputs.logOuter = outerEnclosure 24
      (sk61LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk61LogKInput_eq :
    sk61RoundedInputs.logK = outerEnclosure 24
      (sk61LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk61LogDArgInput_eq :
    sk61RoundedInputs.logDArg = outerEnclosure 24
      (sk61LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk61RoundedFacts : SKRoundedFacts 8
    sk61LogOuterCertificate sk61LogKCertificate
    sk61LogDArgCertificate sk61RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk61LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk61LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk61LogDArgInput_eq }

noncomputable def sk62Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8) }

noncomputable def sk62LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (1605565/1048576) }, upper := { exponent := 1, mantissa := (25/16) } }

noncomputable def sk62LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (33/32) }, upper := { exponent := 1, mantissa := (17/16) } }

noncomputable def sk62LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (3210135/2228224) }, upper := { exponent := 0, mantissa := (50/33) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk62LogOuter_valid :
    sk62LogOuterCertificate.check sk62Slice.outerAD.value = true := by
  norm_num [sk62LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk62Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk62LogK_valid :
    sk62LogKCertificate.check sk62Slice.kAD.value = true := by
  norm_num [sk62LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk62Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk62LogDArg_valid :
    sk62LogDArgCertificate.check sk62Slice.dArgAD.value = true := by
  norm_num [sk62LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk62Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk62ValidityFacts : SKFacts sk62Slice
    sk62LogOuterCertificate sk62LogKCertificate
    sk62LogDArgCertificate :=
  { domain := by norm_num [sk62Slice]
    kPositive := by
      norm_num [sk62Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk62LogOuter_valid
    logK := sk62LogK_valid
    logDArg := sk62LogDArg_valid }

noncomputable def sk62RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (18776889/16777216), upper := (2389567/2097152) }
    logK := { lower := (6072671/8388608), upper := (12646193/16777216) }
    logDArg := { lower := (3062749/8388608), upper := (6971193/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk62LogOuterInput_eq :
    sk62RoundedInputs.logOuter = outerEnclosure 24
      (sk62LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk62LogKInput_eq :
    sk62RoundedInputs.logK = outerEnclosure 24
      (sk62LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk62LogDArgInput_eq :
    sk62RoundedInputs.logDArg = outerEnclosure 24
      (sk62LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk62RoundedFacts : SKRoundedFacts 8
    sk62LogOuterCertificate sk62LogKCertificate
    sk62LogDArgCertificate sk62RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk62LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk62LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk62LogDArgInput_eq }

noncomputable def sk63Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16) }

noncomputable def sk63LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (1638331/1048576) }, upper := { exponent := 1, mantissa := (51/32) } }

noncomputable def sk63LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (17/16) }, upper := { exponent := 1, mantissa := (35/32) } }

noncomputable def sk63LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (111373671/77987840) }, upper := { exponent := 0, mantissa := (3/2) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk63LogOuter_valid :
    sk63LogOuterCertificate.check sk63Slice.outerAD.value = true := by
  norm_num [sk63LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk63Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk63LogK_valid :
    sk63LogKCertificate.check sk63Slice.kAD.value = true := by
  norm_num [sk63LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk63Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk63LogDArg_valid :
    sk63LogDArgCertificate.check sk63Slice.dArgAD.value = true := by
  norm_num [sk63LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk63Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk63ValidityFacts : SKFacts sk63Slice
    sk63LogOuterCertificate sk63LogKCertificate
    sk63LogDArgCertificate :=
  { domain := by norm_num [sk63Slice]
    kPositive := by
      norm_num [sk63Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk63LogOuter_valid
    logK := sk63LogK_valid
    logDArg := sk63LogDArg_valid }

noncomputable def sk63RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (4778957/4194304), upper := (19448769/16777216) }
    logK := { lower := (790387/1048576), upper := (13132523/16777216) }
    logDArg := { lower := (747295/2097152), upper := (425161/1048576) } }

set_option maxRecDepth 1000000 in
private theorem sk63LogOuterInput_eq :
    sk63RoundedInputs.logOuter = outerEnclosure 24
      (sk63LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk63LogKInput_eq :
    sk63RoundedInputs.logK = outerEnclosure 24
      (sk63LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk63LogDArgInput_eq :
    sk63RoundedInputs.logDArg = outerEnclosure 24
      (sk63LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk63RoundedFacts : SKRoundedFacts 8
    sk63LogOuterCertificate sk63LogKCertificate
    sk63LogDArgCertificate sk63RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk63LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk63LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk63LogDArgInput_eq }

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
