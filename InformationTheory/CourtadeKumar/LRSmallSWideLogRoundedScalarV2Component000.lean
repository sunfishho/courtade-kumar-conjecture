import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch0
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

private noncomputable def leaf0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1/4), kHi := (5/16), chiLo := (0), chiHi := (1/4) }

private noncomputable def leaf0Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (4194315/4194304) }, vSqrt := { lower := (65535/65536), upper := (1048578/1048571) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := -1, mantissa := (4161527/2097152) }, upper := { exponent := 0, mantissa := (69/64) } }, logOuter := sk0LogOuterCertificate, logK := sk0LogKCertificate, logChi := chi0LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131071/65536) }, upper := { exponent := 1, mantissa := (2097149/2097142) } }, logDArg := sk0LogDArgCertificate }

private noncomputable def leaf0InnerLog : WideLogData :=
  innerPair0Data

set_option maxRecDepth 1000000 in
private theorem leaf0LocalValidity :
    LeafFacts leaf0Box leaf0Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf0Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65535/65536), upper := (1048578/1048571) }) = true
      norm_num [leaf0Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf0CertificateValid :
    WideCertificateValid leaf0Box leaf0Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk0ValidityFacts chi0ValidityFacts
    leaf0LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf0CoverageChecked :
    coverageCheck (innerAD leaf0Box) leaf0InnerLog = true := by
  rfl'

private theorem leaf0InnerLogValid :
    leaf0InnerLog.Valid 8 (innerAD leaf0Box) :=
  wideLogDataValid_of_cachedCheck endpoint0PositiveFacts
    endpoint1PositiveFacts.valid leaf0CoverageChecked

private noncomputable def leaf0InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628951/16777216), upper := (11629137/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf0InputLogOnePlusV_eq :
    leaf0InputLogOnePlusV = outerEnclosure 24
      (leaf0Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf0RoundedFacts : LeafRoundedFacts 8
    leaf0Certificate.logOnePlusV leaf0InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf0InputLogOnePlusV_eq }

private noncomputable def leaf0Inputs : Inputs :=
  inputsOfCaches globalInput sk0RoundedInputs
    chi0InputQChi innerPair0Input
    leaf0InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf0LowerChecked :
    lowerCheck 24 leaf0Box leaf0Inputs = true := by
  rfl'

private theorem leaf0CoversExact : CoversExact 8
    leaf0Box leaf0Certificate leaf0InnerLog leaf0Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk0RoundedFacts chi0RoundedFacts
    innerPair0RoundedFacts leaf0RoundedFacts (by rfl)

private theorem leaf0FlatSound : Sound leaf0Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf0CertificateValid
    leaf0InnerLogValid leaf0CoversExact leaf0LowerChecked

private noncomputable def leaf1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/16), kHi := (3/8), chiLo := (0), chiHi := (1/4) }

private noncomputable def leaf1Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (4194317/4194304) }, vSqrt := { lower := (65535/65536), upper := (524289/524285) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := -1, mantissa := (4161525/2097152) }, upper := { exponent := 0, mantissa := (35/32) } }, logOuter := sk1LogOuterCertificate, logK := sk1LogKCertificate, logChi := chi0LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131071/65536) }, upper := { exponent := 1, mantissa := (524287/524285) } }, logDArg := sk1LogDArgCertificate }

private noncomputable def leaf1InnerLog : WideLogData :=
  innerPair0Data

set_option maxRecDepth 1000000 in
private theorem leaf1LocalValidity :
    LeafFacts leaf1Box leaf1Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65535/65536), upper := (524289/524285) }) = true
      norm_num [leaf1Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1CertificateValid :
    WideCertificateValid leaf1Box leaf1Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk1ValidityFacts chi0ValidityFacts
    leaf1LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1CoverageChecked :
    coverageCheck (innerAD leaf1Box) leaf1InnerLog = true := by
  rfl'

private theorem leaf1InnerLogValid :
    leaf1InnerLog.Valid 8 (innerAD leaf1Box) :=
  wideLogDataValid_of_cachedCheck endpoint0PositiveFacts
    endpoint1PositiveFacts.valid leaf1CoverageChecked

private noncomputable def leaf1InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628951/16777216), upper := (11629145/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1InputLogOnePlusV_eq :
    leaf1InputLogOnePlusV = outerEnclosure 24
      (leaf1Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1RoundedFacts : LeafRoundedFacts 8
    leaf1Certificate.logOnePlusV leaf1InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1InputLogOnePlusV_eq }

private noncomputable def leaf1Inputs : Inputs :=
  inputsOfCaches globalInput sk1RoundedInputs
    chi0InputQChi innerPair0Input
    leaf1InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1LowerChecked :
    lowerCheck 24 leaf1Box leaf1Inputs = true := by
  rfl'

private theorem leaf1CoversExact : CoversExact 8
    leaf1Box leaf1Certificate leaf1InnerLog leaf1Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk1RoundedFacts chi0RoundedFacts
    innerPair0RoundedFacts leaf1RoundedFacts (by rfl)

private theorem leaf1FlatSound : Sound leaf1Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1CertificateValid
    leaf1InnerLogValid leaf1CoversExact leaf1LowerChecked

private noncomputable def leaf2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/8), kHi := (1/2), chiLo := (0), chiHi := (1/8) }

private noncomputable def leaf2Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (4194313/4194304) }, vSqrt := { lower := (32767/32768), upper := (262145/262143) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := -1, mantissa := (4161529/2097152) }, upper := { exponent := 0, mantissa := (17/16) } }, logOuter := sk2LogOuterCertificate, logK := sk2LogKCertificate, logChi := chi1LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (262144/262143) } }, logDArg := sk2LogDArgCertificate }

private noncomputable def leaf2InnerLog : WideLogData :=
  innerPair1Data

set_option maxRecDepth 1000000 in
private theorem leaf2LocalValidity :
    LeafFacts leaf2Box leaf2Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (262145/262143) }) = true
      norm_num [leaf2Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2CertificateValid :
    WideCertificateValid leaf2Box leaf2Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk2ValidityFacts chi1ValidityFacts
    leaf2LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2CoverageChecked :
    coverageCheck (innerAD leaf2Box) leaf2InnerLog = true := by
  rfl'

private theorem leaf2InnerLogValid :
    leaf2InnerLog.Valid 8 (innerAD leaf2Box) :=
  wideLogDataValid_of_cachedCheck endpoint0PositiveFacts
    endpoint2PositiveFacts.valid leaf2CoverageChecked

private noncomputable def leaf2InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629145/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2InputLogOnePlusV_eq :
    leaf2InputLogOnePlusV = outerEnclosure 24
      (leaf2Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2RoundedFacts : LeafRoundedFacts 8
    leaf2Certificate.logOnePlusV leaf2InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2InputLogOnePlusV_eq }

private noncomputable def leaf2Inputs : Inputs :=
  inputsOfCaches globalInput sk2RoundedInputs
    chi1InputQChi innerPair1Input
    leaf2InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2LowerChecked :
    lowerCheck 24 leaf2Box leaf2Inputs = true := by
  rfl'

private theorem leaf2CoversExact : CoversExact 8
    leaf2Box leaf2Certificate leaf2InnerLog leaf2Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk2RoundedFacts chi1RoundedFacts
    innerPair1RoundedFacts leaf2RoundedFacts (by rfl)

private theorem leaf2FlatSound : Sound leaf2Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2CertificateValid
    leaf2InnerLogValid leaf2CoversExact leaf2LowerChecked

private noncomputable def leaf3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/8), kHi := (7/16), chiLo := (1/8), chiHi := (1/4) }

private noncomputable def leaf3Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (8388625/8388608) }, vSqrt := { lower := (65535/65536), upper := (349526/349523) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (8749017/8388608) }, upper := { exponent := 0, mantissa := (71/64) } }, logOuter := sk3LogOuterCertificate, logK := sk3LogKCertificate, logChi := chi2LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131071/65536) }, upper := { exponent := 1, mantissa := (699049/699046) } }, logDArg := sk3LogDArgCertificate }

private noncomputable def leaf3InnerLog : WideLogData :=
  innerPair9Data

set_option maxRecDepth 1000000 in
private theorem leaf3LocalValidity :
    LeafFacts leaf3Box leaf3Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65535/65536), upper := (349526/349523) }) = true
      norm_num [leaf3Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3CertificateValid :
    WideCertificateValid leaf3Box leaf3Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk3ValidityFacts chi2ValidityFacts
    leaf3LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3CoverageChecked :
    coverageCheck (innerAD leaf3Box) leaf3InnerLog = true := by
  rfl'

private theorem leaf3InnerLogValid :
    leaf3InnerLog.Valid 8 (innerAD leaf3Box) :=
  wideLogDataValid_of_cachedCheck endpoint3PositiveFacts
    endpoint1PositiveFacts.valid leaf3CoverageChecked

private noncomputable def leaf3InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628951/16777216), upper := (11629153/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3InputLogOnePlusV_eq :
    leaf3InputLogOnePlusV = outerEnclosure 24
      (leaf3Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3RoundedFacts : LeafRoundedFacts 8
    leaf3Certificate.logOnePlusV leaf3InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3InputLogOnePlusV_eq }

private noncomputable def leaf3Inputs : Inputs :=
  inputsOfCaches globalInput sk3RoundedInputs
    chi2InputQChi innerPair9Input
    leaf3InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3LowerChecked :
    lowerCheck 24 leaf3Box leaf3Inputs = true := by
  rfl'

private theorem leaf3CoversExact : CoversExact 8
    leaf3Box leaf3Certificate leaf3InnerLog leaf3Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk3RoundedFacts chi2RoundedFacts
    innerPair9RoundedFacts leaf3RoundedFacts (by rfl)

private theorem leaf3FlatSound : Sound leaf3Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3CertificateValid
    leaf3InnerLogValid leaf3CoversExact leaf3LowerChecked

private noncomputable def leaf4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/16), kHi := (1/2), chiLo := (1/8), chiHi := (1/4) }

private noncomputable def leaf4Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (8388627/8388608) }, vSqrt := { lower := (32767/32768), upper := (524289/524284) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (8814547/8388608) }, upper := { exponent := 0, mantissa := (9/8) } }, logOuter := sk4LogOuterCertificate, logK := sk4LogKCertificate, logChi := chi2LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (1048573/1048568) } }, logDArg := sk4LogDArgCertificate }

private noncomputable def leaf4InnerLog : WideLogData :=
  innerPair9Data

set_option maxRecDepth 1000000 in
private theorem leaf4LocalValidity :
    LeafFacts leaf4Box leaf4Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (524289/524284) }) = true
      norm_num [leaf4Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4CertificateValid :
    WideCertificateValid leaf4Box leaf4Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk4ValidityFacts chi2ValidityFacts
    leaf4LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4CoverageChecked :
    coverageCheck (innerAD leaf4Box) leaf4InnerLog = true := by
  rfl'

private theorem leaf4InnerLogValid :
    leaf4InnerLog.Valid 8 (innerAD leaf4Box) :=
  wideLogDataValid_of_cachedCheck endpoint3PositiveFacts
    endpoint1PositiveFacts.valid leaf4CoverageChecked

private noncomputable def leaf4InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629161/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4InputLogOnePlusV_eq :
    leaf4InputLogOnePlusV = outerEnclosure 24
      (leaf4Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4RoundedFacts : LeafRoundedFacts 8
    leaf4Certificate.logOnePlusV leaf4InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4InputLogOnePlusV_eq }

private noncomputable def leaf4Inputs : Inputs :=
  inputsOfCaches globalInput sk4RoundedInputs
    chi2InputQChi innerPair9Input
    leaf4InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4LowerChecked :
    lowerCheck 24 leaf4Box leaf4Inputs = true := by
  rfl'

private theorem leaf4CoversExact : CoversExact 8
    leaf4Box leaf4Certificate leaf4InnerLog leaf4Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk4RoundedFacts chi2RoundedFacts
    innerPair9RoundedFacts leaf4RoundedFacts (by rfl)

private theorem leaf4FlatSound : Sound leaf4Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4CertificateValid
    leaf4InnerLogValid leaf4CoversExact leaf4LowerChecked

private noncomputable def leaf5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1/4), kHi := (5/16), chiLo := (1/4), chiHi := (1/2) }

private noncomputable def leaf5Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (4194317/4194304) }, vSqrt := { lower := (65535/65536), upper := (174763/174761) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (4423653/4194304) }, upper := { exponent := 0, mantissa := (37/32) } }, logOuter := sk0LogOuterCertificate, logK := sk0LogKCertificate, logChi := chi3LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131071/65536) }, upper := { exponent := 1, mantissa := (174762/174761) } }, logDArg := sk0LogDArgCertificate }

private noncomputable def leaf5InnerLog : WideLogData :=
  innerPair11Data

set_option maxRecDepth 1000000 in
private theorem leaf5LocalValidity :
    LeafFacts leaf5Box leaf5Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65535/65536), upper := (174763/174761) }) = true
      norm_num [leaf5Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5CertificateValid :
    WideCertificateValid leaf5Box leaf5Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk0ValidityFacts chi3ValidityFacts
    leaf5LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5CoverageChecked :
    coverageCheck (innerAD leaf5Box) leaf5InnerLog = true := by
  rfl'

private theorem leaf5InnerLogValid :
    leaf5InnerLog.Valid 8 (innerAD leaf5Box) :=
  wideLogDataValid_of_cachedCheck endpoint3PositiveFacts
    endpoint4PositiveFacts.valid leaf5CoverageChecked

private noncomputable def leaf5InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628951/16777216), upper := (11629177/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5InputLogOnePlusV_eq :
    leaf5InputLogOnePlusV = outerEnclosure 24
      (leaf5Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5RoundedFacts : LeafRoundedFacts 8
    leaf5Certificate.logOnePlusV leaf5InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5InputLogOnePlusV_eq }

private noncomputable def leaf5Inputs : Inputs :=
  inputsOfCaches globalInput sk0RoundedInputs
    chi3InputQChi innerPair11Input
    leaf5InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5LowerChecked :
    lowerCheck 24 leaf5Box leaf5Inputs = true := by
  rfl'

private theorem leaf5CoversExact : CoversExact 8
    leaf5Box leaf5Certificate leaf5InnerLog leaf5Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk0RoundedFacts chi3RoundedFacts
    innerPair11RoundedFacts leaf5RoundedFacts (by rfl)

private theorem leaf5FlatSound : Sound leaf5Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5CertificateValid
    leaf5InnerLogValid leaf5CoversExact leaf5LowerChecked

private noncomputable def leaf6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/16), kHi := (3/8), chiLo := (1/4), chiHi := (3/8) }

private noncomputable def leaf6Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (8388625/8388608) }, vSqrt := { lower := (65535/65536), upper := (1048578/1048567) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (9011145/8388608) }, upper := { exponent := 0, mantissa := (73/64) } }, logOuter := sk1LogOuterCertificate, logK := sk1LogKCertificate, logChi := chi4LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131071/65536) }, upper := { exponent := 1, mantissa := (2097145/2097134) } }, logDArg := sk1LogDArgCertificate }

private noncomputable def leaf6InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf6LocalValidity :
    LeafFacts leaf6Box leaf6Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65535/65536), upper := (1048578/1048567) }) = true
      norm_num [leaf6Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6CertificateValid :
    WideCertificateValid leaf6Box leaf6Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk1ValidityFacts chi4ValidityFacts
    leaf6LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6CoverageChecked :
    coverageCheck (innerAD leaf6Box) leaf6InnerLog = true := by
  rfl'

private theorem leaf6InnerLogValid :
    leaf6InnerLog.Valid 8 (innerAD leaf6Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf6CoverageChecked

private noncomputable def leaf6InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628951/16777216), upper := (11629169/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6InputLogOnePlusV_eq :
    leaf6InputLogOnePlusV = outerEnclosure 24
      (leaf6Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6RoundedFacts : LeafRoundedFacts 8
    leaf6Certificate.logOnePlusV leaf6InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6InputLogOnePlusV_eq }

private noncomputable def leaf6Inputs : Inputs :=
  inputsOfCaches globalInput sk1RoundedInputs
    chi4InputQChi innerPair6Input
    leaf6InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6LowerChecked :
    lowerCheck 24 leaf6Box leaf6Inputs = true := by
  rfl'

private theorem leaf6CoversExact : CoversExact 8
    leaf6Box leaf6Certificate leaf6InnerLog leaf6Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk1RoundedFacts chi4RoundedFacts
    innerPair6RoundedFacts leaf6RoundedFacts (by rfl)

private theorem leaf6FlatSound : Sound leaf6Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6CertificateValid
    leaf6InnerLogValid leaf6CoversExact leaf6LowerChecked

private noncomputable def leaf7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/16), kHi := (3/8), chiLo := (3/8), chiHi := (1/2) }

private noncomputable def leaf7Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (8388627/8388608) }, vSqrt := { lower := (65535/65536), upper := (524289/524282) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (9338803/8388608) }, upper := { exponent := 0, mantissa := (19/16) } }, logOuter := sk1LogOuterCertificate, logK := sk1LogKCertificate, logChi := chi5LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131071/65536) }, upper := { exponent := 1, mantissa := (1048571/1048564) } }, logDArg := sk1LogDArgCertificate }

private noncomputable def leaf7InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf7LocalValidity :
    LeafFacts leaf7Box leaf7Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65535/65536), upper := (524289/524282) }) = true
      norm_num [leaf7Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7CertificateValid :
    WideCertificateValid leaf7Box leaf7Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk1ValidityFacts chi5ValidityFacts
    leaf7LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7CoverageChecked :
    coverageCheck (innerAD leaf7Box) leaf7InnerLog = true := by
  rfl'

private theorem leaf7InnerLogValid :
    leaf7InnerLog.Valid 8 (innerAD leaf7Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf7CoverageChecked

private noncomputable def leaf7InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628951/16777216), upper := (11629193/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7InputLogOnePlusV_eq :
    leaf7InputLogOnePlusV = outerEnclosure 24
      (leaf7Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7RoundedFacts : LeafRoundedFacts 8
    leaf7Certificate.logOnePlusV leaf7InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7InputLogOnePlusV_eq }

private noncomputable def leaf7Inputs : Inputs :=
  inputsOfCaches globalInput sk1RoundedInputs
    chi5InputQChi innerPair6Input
    leaf7InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7LowerChecked :
    lowerCheck 24 leaf7Box leaf7Inputs = true := by
  rfl'

private theorem leaf7CoversExact : CoversExact 8
    leaf7Box leaf7Certificate leaf7InnerLog leaf7Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk1RoundedFacts chi5RoundedFacts
    innerPair6RoundedFacts leaf7RoundedFacts (by rfl)

private theorem leaf7FlatSound : Sound leaf7Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7CertificateValid
    leaf7InnerLogValid leaf7CoversExact leaf7LowerChecked

private noncomputable def leaf8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/8), kHi := (7/16), chiLo := (1/4), chiHi := (3/8) }

private noncomputable def leaf8Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (8388627/8388608) }, vSqrt := { lower := (65535/65536), upper := (2097156/2097131) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (9142207/8388608) }, upper := { exponent := 0, mantissa := (149/128) } }, logOuter := sk3LogOuterCertificate, logK := sk3LogKCertificate, logChi := chi4LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131071/65536) }, upper := { exponent := 1, mantissa := (4194287/4194262) } }, logDArg := sk3LogDArgCertificate }

private noncomputable def leaf8InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf8LocalValidity :
    LeafFacts leaf8Box leaf8Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf8Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65535/65536), upper := (2097156/2097131) }) = true
      norm_num [leaf8Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf8CertificateValid :
    WideCertificateValid leaf8Box leaf8Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk3ValidityFacts chi4ValidityFacts
    leaf8LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf8CoverageChecked :
    coverageCheck (innerAD leaf8Box) leaf8InnerLog = true := by
  rfl'

private theorem leaf8InnerLogValid :
    leaf8InnerLog.Valid 8 (innerAD leaf8Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf8CoverageChecked

private noncomputable def leaf8InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628951/16777216), upper := (11629181/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf8InputLogOnePlusV_eq :
    leaf8InputLogOnePlusV = outerEnclosure 24
      (leaf8Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf8RoundedFacts : LeafRoundedFacts 8
    leaf8Certificate.logOnePlusV leaf8InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf8InputLogOnePlusV_eq }

private noncomputable def leaf8Inputs : Inputs :=
  inputsOfCaches globalInput sk3RoundedInputs
    chi4InputQChi innerPair6Input
    leaf8InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf8LowerChecked :
    lowerCheck 24 leaf8Box leaf8Inputs = true := by
  rfl'

private theorem leaf8CoversExact : CoversExact 8
    leaf8Box leaf8Certificate leaf8InnerLog leaf8Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk3RoundedFacts chi4RoundedFacts
    innerPair6RoundedFacts leaf8RoundedFacts (by rfl)

private theorem leaf8FlatSound : Sound leaf8Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf8CertificateValid
    leaf8InnerLogValid leaf8CoversExact leaf8LowerChecked

private noncomputable def leaf9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/16), kHi := (1/2), chiLo := (1/4), chiHi := (3/8) }

private noncomputable def leaf9Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (8388629/8388608) }, vSqrt := { lower := (32767/32768), upper := (524289/524282) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (9273269/8388608) }, upper := { exponent := 0, mantissa := (19/16) } }, logOuter := sk4LogOuterCertificate, logK := sk4LogKCertificate, logChi := chi4LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (1048571/1048564) } }, logDArg := sk4LogDArgCertificate }

private noncomputable def leaf9InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf9LocalValidity :
    LeafFacts leaf9Box leaf9Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf9Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (524289/524282) }) = true
      norm_num [leaf9Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf9CertificateValid :
    WideCertificateValid leaf9Box leaf9Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk4ValidityFacts chi4ValidityFacts
    leaf9LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf9CoverageChecked :
    coverageCheck (innerAD leaf9Box) leaf9InnerLog = true := by
  rfl'

private theorem leaf9InnerLogValid :
    leaf9InnerLog.Valid 8 (innerAD leaf9Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf9CoverageChecked

private noncomputable def leaf9InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629193/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf9InputLogOnePlusV_eq :
    leaf9InputLogOnePlusV = outerEnclosure 24
      (leaf9Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf9RoundedFacts : LeafRoundedFacts 8
    leaf9Certificate.logOnePlusV leaf9InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf9InputLogOnePlusV_eq }

private noncomputable def leaf9Inputs : Inputs :=
  inputsOfCaches globalInput sk4RoundedInputs
    chi4InputQChi innerPair6Input
    leaf9InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf9LowerChecked :
    lowerCheck 24 leaf9Box leaf9Inputs = true := by
  rfl'

private theorem leaf9CoversExact : CoversExact 8
    leaf9Box leaf9Certificate leaf9InnerLog leaf9Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk4RoundedFacts chi4RoundedFacts
    innerPair6RoundedFacts leaf9RoundedFacts (by rfl)

private theorem leaf9FlatSound : Sound leaf9Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf9CertificateValid
    leaf9InnerLogValid leaf9CoversExact leaf9LowerChecked

private noncomputable def leaf10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/8), kHi := (7/16), chiLo := (3/8), chiHi := (1/2) }

private noncomputable def leaf10Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (8388629/8388608) }, vSqrt := { lower := (65535/65536), upper := (524289/524281) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (9535397/8388608) }, upper := { exponent := 0, mantissa := (39/32) } }, logOuter := sk3LogOuterCertificate, logK := sk3LogKCertificate, logChi := chi5LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131071/65536) }, upper := { exponent := 1, mantissa := (524285/524281) } }, logDArg := sk3LogDArgCertificate }

private noncomputable def leaf10InnerLog : WideLogData :=
  innerPair3Data

set_option maxRecDepth 1000000 in
private theorem leaf10LocalValidity :
    LeafFacts leaf10Box leaf10Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf10Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65535/65536), upper := (524289/524281) }) = true
      norm_num [leaf10Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf10CertificateValid :
    WideCertificateValid leaf10Box leaf10Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk3ValidityFacts chi5ValidityFacts
    leaf10LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf10CoverageChecked :
    coverageCheck (innerAD leaf10Box) leaf10InnerLog = true := by
  rfl'

private theorem leaf10InnerLogValid :
    leaf10InnerLog.Valid 8 (innerAD leaf10Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint5PositiveFacts.valid leaf10CoverageChecked

private noncomputable def leaf10InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628951/16777216), upper := (11629209/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf10InputLogOnePlusV_eq :
    leaf10InputLogOnePlusV = outerEnclosure 24
      (leaf10Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf10RoundedFacts : LeafRoundedFacts 8
    leaf10Certificate.logOnePlusV leaf10InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf10InputLogOnePlusV_eq }

private noncomputable def leaf10Inputs : Inputs :=
  inputsOfCaches globalInput sk3RoundedInputs
    chi5InputQChi innerPair3Input
    leaf10InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf10LowerChecked :
    lowerCheck 24 leaf10Box leaf10Inputs = true := by
  rfl'

private theorem leaf10CoversExact : CoversExact 8
    leaf10Box leaf10Certificate leaf10InnerLog leaf10Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk3RoundedFacts chi5RoundedFacts
    innerPair3RoundedFacts leaf10RoundedFacts (by rfl)

private theorem leaf10FlatSound : Sound leaf10Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf10CertificateValid
    leaf10InnerLogValid leaf10CoversExact leaf10LowerChecked

private noncomputable def leaf11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/16), kHi := (1/2), chiLo := (3/8), chiHi := (1/2) }

private noncomputable def leaf11Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (8388631/8388608) }, vSqrt := { lower := (32767/32768), upper := (174763/174760) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (9731991/8388608) }, upper := { exponent := 0, mantissa := (5/4) } }, logOuter := sk4LogOuterCertificate, logK := sk4LogKCertificate, logChi := chi5LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (349523/349520) } }, logDArg := sk4LogDArgCertificate }

private noncomputable def leaf11InnerLog : WideLogData :=
  innerPair3Data

set_option maxRecDepth 1000000 in
private theorem leaf11LocalValidity :
    LeafFacts leaf11Box leaf11Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf11Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (174763/174760) }) = true
      norm_num [leaf11Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf11CertificateValid :
    WideCertificateValid leaf11Box leaf11Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk4ValidityFacts chi5ValidityFacts
    leaf11LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf11CoverageChecked :
    coverageCheck (innerAD leaf11Box) leaf11InnerLog = true := by
  rfl'

private theorem leaf11InnerLogValid :
    leaf11InnerLog.Valid 8 (innerAD leaf11Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint5PositiveFacts.valid leaf11CoverageChecked

private noncomputable def leaf11InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629225/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf11InputLogOnePlusV_eq :
    leaf11InputLogOnePlusV = outerEnclosure 24
      (leaf11Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf11RoundedFacts : LeafRoundedFacts 8
    leaf11Certificate.logOnePlusV leaf11InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf11InputLogOnePlusV_eq }

private noncomputable def leaf11Inputs : Inputs :=
  inputsOfCaches globalInput sk4RoundedInputs
    chi5InputQChi innerPair3Input
    leaf11InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf11LowerChecked :
    lowerCheck 24 leaf11Box leaf11Inputs = true := by
  rfl'

private theorem leaf11CoversExact : CoversExact 8
    leaf11Box leaf11Certificate leaf11InnerLog leaf11Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk4RoundedFacts chi5RoundedFacts
    innerPair3RoundedFacts leaf11RoundedFacts (by rfl)

private theorem leaf11FlatSound : Sound leaf11Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf11CertificateValid
    leaf11InnerLogValid leaf11CoversExact leaf11LowerChecked

private noncomputable def leaf12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1/4), kHi := (5/16), chiLo := (1/2), chiHi := (3/4) }

private noncomputable def leaf12Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (4194319/4194304) }, vSqrt := { lower := (65535/65536), upper := (1048578/1048561) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (4685779/4194304) }, upper := { exponent := 0, mantissa := (79/64) } }, logOuter := sk0LogOuterCertificate, logK := sk0LogKCertificate, logChi := chi6LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131071/65536) }, upper := { exponent := 1, mantissa := (2097139/2097122) } }, logDArg := sk0LogDArgCertificate }

private noncomputable def leaf12InnerLog : WideLogData :=
  innerPair7Data

set_option maxRecDepth 1000000 in
private theorem leaf12LocalValidity :
    LeafFacts leaf12Box leaf12Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf12Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65535/65536), upper := (1048578/1048561) }) = true
      norm_num [leaf12Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf12CertificateValid :
    WideCertificateValid leaf12Box leaf12Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk0ValidityFacts chi6ValidityFacts
    leaf12LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf12CoverageChecked :
    coverageCheck (innerAD leaf12Box) leaf12InnerLog = true := by
  rfl'

private theorem leaf12InnerLogValid :
    leaf12InnerLog.Valid 8 (innerAD leaf12Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint5PositiveFacts.valid leaf12CoverageChecked

private noncomputable def leaf12InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628951/16777216), upper := (11629217/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf12InputLogOnePlusV_eq :
    leaf12InputLogOnePlusV = outerEnclosure 24
      (leaf12Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf12RoundedFacts : LeafRoundedFacts 8
    leaf12Certificate.logOnePlusV leaf12InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf12InputLogOnePlusV_eq }

private noncomputable def leaf12Inputs : Inputs :=
  inputsOfCaches globalInput sk0RoundedInputs
    chi6InputQChi innerPair7Input
    leaf12InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf12LowerChecked :
    lowerCheck 24 leaf12Box leaf12Inputs = true := by
  rfl'

private theorem leaf12CoversExact : CoversExact 8
    leaf12Box leaf12Certificate leaf12InnerLog leaf12Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk0RoundedFacts chi6RoundedFacts
    innerPair7RoundedFacts leaf12RoundedFacts (by rfl)

private theorem leaf12FlatSound : Sound leaf12Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf12CertificateValid
    leaf12InnerLogValid leaf12CoversExact leaf12LowerChecked

private noncomputable def leaf13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/16), kHi := (3/8), chiLo := (1/2), chiHi := (3/4) }

private noncomputable def leaf13Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (4194321/4194304) }, vSqrt := { lower := (65535/65536), upper := (524289/524279) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (4816841/4194304) }, upper := { exponent := 0, mantissa := (41/32) } }, logOuter := sk1LogOuterCertificate, logK := sk1LogKCertificate, logChi := chi6LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131071/65536) }, upper := { exponent := 1, mantissa := (524284/524279) } }, logDArg := sk1LogDArgCertificate }

private noncomputable def leaf13InnerLog : WideLogData :=
  innerPair4Data

set_option maxRecDepth 1000000 in
private theorem leaf13LocalValidity :
    LeafFacts leaf13Box leaf13Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf13Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65535/65536), upper := (524289/524279) }) = true
      norm_num [leaf13Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf13CertificateValid :
    WideCertificateValid leaf13Box leaf13Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk1ValidityFacts chi6ValidityFacts
    leaf13LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf13CoverageChecked :
    coverageCheck (innerAD leaf13Box) leaf13InnerLog = true := by
  rfl'

private theorem leaf13InnerLogValid :
    leaf13InnerLog.Valid 8 (innerAD leaf13Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint6PositiveFacts.valid leaf13CoverageChecked

private noncomputable def leaf13InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628951/16777216), upper := (11629241/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf13InputLogOnePlusV_eq :
    leaf13InputLogOnePlusV = outerEnclosure 24
      (leaf13Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf13RoundedFacts : LeafRoundedFacts 8
    leaf13Certificate.logOnePlusV leaf13InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf13InputLogOnePlusV_eq }

private noncomputable def leaf13Inputs : Inputs :=
  inputsOfCaches globalInput sk1RoundedInputs
    chi6InputQChi innerPair4Input
    leaf13InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf13LowerChecked :
    lowerCheck 24 leaf13Box leaf13Inputs = true := by
  rfl'

private theorem leaf13CoversExact : CoversExact 8
    leaf13Box leaf13Certificate leaf13InnerLog leaf13Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk1RoundedFacts chi6RoundedFacts
    innerPair4RoundedFacts leaf13RoundedFacts (by rfl)

private theorem leaf13FlatSound : Sound leaf13Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf13CertificateValid
    leaf13InnerLogValid leaf13CoversExact leaf13LowerChecked

private noncomputable def leaf14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1/4), kHi := (5/16), chiLo := (3/4), chiHi := (1) }

private noncomputable def leaf14Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (4194321/4194304) }, vSqrt := { lower := (65535/65536), upper := (524289/524278) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (4947905/4194304) }, upper := { exponent := 0, mantissa := (21/16) } }, logOuter := sk0LogOuterCertificate, logK := sk0LogKCertificate, logChi := chi7LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131071/65536) }, upper := { exponent := 1, mantissa := (1048567/1048556) } }, logDArg := sk0LogDArgCertificate }

private noncomputable def leaf14InnerLog : WideLogData :=
  innerPair4Data

set_option maxRecDepth 1000000 in
private theorem leaf14LocalValidity :
    LeafFacts leaf14Box leaf14Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf14Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65535/65536), upper := (524289/524278) }) = true
      norm_num [leaf14Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf14CertificateValid :
    WideCertificateValid leaf14Box leaf14Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk0ValidityFacts chi7ValidityFacts
    leaf14LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf14CoverageChecked :
    coverageCheck (innerAD leaf14Box) leaf14InnerLog = true := by
  rfl'

private theorem leaf14InnerLogValid :
    leaf14InnerLog.Valid 8 (innerAD leaf14Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint6PositiveFacts.valid leaf14CoverageChecked

private noncomputable def leaf14InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628951/16777216), upper := (11629257/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf14InputLogOnePlusV_eq :
    leaf14InputLogOnePlusV = outerEnclosure 24
      (leaf14Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf14RoundedFacts : LeafRoundedFacts 8
    leaf14Certificate.logOnePlusV leaf14InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf14InputLogOnePlusV_eq }

private noncomputable def leaf14Inputs : Inputs :=
  inputsOfCaches globalInput sk0RoundedInputs
    chi7InputQChi innerPair4Input
    leaf14InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf14LowerChecked :
    lowerCheck 24 leaf14Box leaf14Inputs = true := by
  rfl'

private theorem leaf14CoversExact : CoversExact 8
    leaf14Box leaf14Certificate leaf14InnerLog leaf14Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk0RoundedFacts chi7RoundedFacts
    innerPair4RoundedFacts leaf14RoundedFacts (by rfl)

private theorem leaf14FlatSound : Sound leaf14Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf14CertificateValid
    leaf14InnerLogValid leaf14CoversExact leaf14LowerChecked

private noncomputable def leaf15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/16), kHi := (3/8), chiLo := (3/4), chiHi := (1) }

private noncomputable def leaf15Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (4194323/4194304) }, vSqrt := { lower := (65535/65536), upper := (524289/524276) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (5144499/4194304) }, upper := { exponent := 0, mantissa := (11/8) } }, logOuter := sk1LogOuterCertificate, logK := sk1LogKCertificate, logChi := chi7LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131071/65536) }, upper := { exponent := 1, mantissa := (1048565/1048552) } }, logDArg := sk1LogDArgCertificate }

private noncomputable def leaf15InnerLog : WideLogData :=
  innerPair14Data

set_option maxRecDepth 1000000 in
private theorem leaf15LocalValidity :
    LeafFacts leaf15Box leaf15Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf15Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65535/65536), upper := (524289/524276) }) = true
      norm_num [leaf15Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf15CertificateValid :
    WideCertificateValid leaf15Box leaf15Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk1ValidityFacts chi7ValidityFacts
    leaf15LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf15CoverageChecked :
    coverageCheck (innerAD leaf15Box) leaf15InnerLog = true := by
  rfl'

private theorem leaf15InnerLogValid :
    leaf15InnerLog.Valid 8 (innerAD leaf15Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint7PositiveFacts.valid leaf15CoverageChecked

private noncomputable def leaf15InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628951/16777216), upper := (11629289/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf15InputLogOnePlusV_eq :
    leaf15InputLogOnePlusV = outerEnclosure 24
      (leaf15Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf15RoundedFacts : LeafRoundedFacts 8
    leaf15Certificate.logOnePlusV leaf15InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf15InputLogOnePlusV_eq }

private noncomputable def leaf15Inputs : Inputs :=
  inputsOfCaches globalInput sk1RoundedInputs
    chi7InputQChi innerPair14Input
    leaf15InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf15LowerChecked :
    lowerCheck 24 leaf15Box leaf15Inputs = true := by
  rfl'

private theorem leaf15CoversExact : CoversExact 8
    leaf15Box leaf15Certificate leaf15InnerLog leaf15Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk1RoundedFacts chi7RoundedFacts
    innerPair14RoundedFacts leaf15RoundedFacts (by rfl)

private theorem leaf15FlatSound : Sound leaf15Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf15CertificateValid
    leaf15InnerLogValid leaf15CoversExact leaf15LowerChecked

private noncomputable def leaf16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/8), kHi := (7/16), chiLo := (1/2), chiHi := (3/4) }

private noncomputable def leaf16Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (4194323/4194304) }, vSqrt := { lower := (32767/32768), upper := (1048578/1048555) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (4947903/4194304) }, upper := { exponent := 0, mantissa := (85/64) } }, logOuter := sk3LogOuterCertificate, logK := sk3LogKCertificate, logChi := chi6LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (2097133/2097110) } }, logDArg := sk3LogDArgCertificate }

private noncomputable def leaf16InnerLog : WideLogData :=
  innerPair31Data

set_option maxRecDepth 1000000 in
private theorem leaf16LocalValidity :
    LeafFacts leaf16Box leaf16Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf16Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (1048578/1048555) }) = true
      norm_num [leaf16Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf16CertificateValid :
    WideCertificateValid leaf16Box leaf16Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk3ValidityFacts chi6ValidityFacts
    leaf16LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf16CoverageChecked :
    coverageCheck (innerAD leaf16Box) leaf16InnerLog = true := by
  rfl'

private theorem leaf16InnerLogValid :
    leaf16InnerLog.Valid 8 (innerAD leaf16Box) :=
  wideLogDataValid_of_cachedCheck endpoint8PositiveFacts
    endpoint9PositiveFacts.valid leaf16CoverageChecked

private noncomputable def leaf16InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629265/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf16InputLogOnePlusV_eq :
    leaf16InputLogOnePlusV = outerEnclosure 24
      (leaf16Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf16RoundedFacts : LeafRoundedFacts 8
    leaf16Certificate.logOnePlusV leaf16InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf16InputLogOnePlusV_eq }

private noncomputable def leaf16Inputs : Inputs :=
  inputsOfCaches globalInput sk3RoundedInputs
    chi6InputQChi innerPair31Input
    leaf16InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf16LowerChecked :
    lowerCheck 24 leaf16Box leaf16Inputs = true := by
  rfl'

private theorem leaf16CoversExact : CoversExact 8
    leaf16Box leaf16Certificate leaf16InnerLog leaf16Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk3RoundedFacts chi6RoundedFacts
    innerPair31RoundedFacts leaf16RoundedFacts (by rfl)

private theorem leaf16FlatSound : Sound leaf16Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf16CertificateValid
    leaf16InnerLogValid leaf16CoversExact leaf16LowerChecked

private noncomputable def leaf17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/16), kHi := (1/2), chiLo := (1/2), chiHi := (5/8) }

private noncomputable def leaf17Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (8388633/8388608) }, vSqrt := { lower := (32767/32768), upper := (524289/524278) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (10190713/8388608) }, upper := { exponent := 0, mantissa := (21/16) } }, logOuter := sk4LogOuterCertificate, logK := sk4LogKCertificate, logChi := chi8LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (1048567/1048556) } }, logDArg := sk4LogDArgCertificate }

private noncomputable def leaf17InnerLog : WideLogData :=
  innerPair13Data

set_option maxRecDepth 1000000 in
private theorem leaf17LocalValidity :
    LeafFacts leaf17Box leaf17Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf17Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (524289/524278) }) = true
      norm_num [leaf17Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf17CertificateValid :
    WideCertificateValid leaf17Box leaf17Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk4ValidityFacts chi8ValidityFacts
    leaf17LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf17CoverageChecked :
    coverageCheck (innerAD leaf17Box) leaf17InnerLog = true := by
  rfl'

private theorem leaf17InnerLogValid :
    leaf17InnerLog.Valid 8 (innerAD leaf17Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint6PositiveFacts.valid leaf17CoverageChecked

private noncomputable def leaf17InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629257/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf17InputLogOnePlusV_eq :
    leaf17InputLogOnePlusV = outerEnclosure 24
      (leaf17Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf17RoundedFacts : LeafRoundedFacts 8
    leaf17Certificate.logOnePlusV leaf17InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf17InputLogOnePlusV_eq }

private noncomputable def leaf17Inputs : Inputs :=
  inputsOfCaches globalInput sk4RoundedInputs
    chi8InputQChi innerPair13Input
    leaf17InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf17LowerChecked :
    lowerCheck 24 leaf17Box leaf17Inputs = true := by
  rfl'

private theorem leaf17CoversExact : CoversExact 8
    leaf17Box leaf17Certificate leaf17InnerLog leaf17Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk4RoundedFacts chi8RoundedFacts
    innerPair13RoundedFacts leaf17RoundedFacts (by rfl)

private theorem leaf17FlatSound : Sound leaf17Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf17CertificateValid
    leaf17InnerLogValid leaf17CoversExact leaf17LowerChecked

private noncomputable def leaf18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/16), kHi := (1/2), chiLo := (5/8), chiHi := (3/4) }

private noncomputable def leaf18Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (8388635/8388608) }, vSqrt := { lower := (32767/32768), upper := (524289/524276) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (10649435/8388608) }, upper := { exponent := 0, mantissa := (11/8) } }, logOuter := sk4LogOuterCertificate, logK := sk4LogKCertificate, logChi := chi9LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (1048565/1048552) } }, logDArg := sk4LogDArgCertificate }

private noncomputable def leaf18InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf18LocalValidity :
    LeafFacts leaf18Box leaf18Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf18Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (524289/524276) }) = true
      norm_num [leaf18Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf18CertificateValid :
    WideCertificateValid leaf18Box leaf18Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk4ValidityFacts chi9ValidityFacts
    leaf18LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf18CoverageChecked :
    coverageCheck (innerAD leaf18Box) leaf18InnerLog = true := by
  rfl'

private theorem leaf18InnerLogValid :
    leaf18InnerLog.Valid 8 (innerAD leaf18Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf18CoverageChecked

private noncomputable def leaf18InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629289/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf18InputLogOnePlusV_eq :
    leaf18InputLogOnePlusV = outerEnclosure 24
      (leaf18Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf18RoundedFacts : LeafRoundedFacts 8
    leaf18Certificate.logOnePlusV leaf18InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf18InputLogOnePlusV_eq }

private noncomputable def leaf18Inputs : Inputs :=
  inputsOfCaches globalInput sk4RoundedInputs
    chi9InputQChi innerPair17Input
    leaf18InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf18LowerChecked :
    lowerCheck 24 leaf18Box leaf18Inputs = true := by
  rfl'

private theorem leaf18CoversExact : CoversExact 8
    leaf18Box leaf18Certificate leaf18InnerLog leaf18Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk4RoundedFacts chi9RoundedFacts
    innerPair17RoundedFacts leaf18RoundedFacts (by rfl)

private theorem leaf18FlatSound : Sound leaf18Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf18CertificateValid
    leaf18InnerLogValid leaf18CoversExact leaf18LowerChecked

private noncomputable def leaf19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/8), kHi := (7/16), chiLo := (3/4), chiHi := (1) }

private noncomputable def leaf19Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (4194325/4194304) }, vSqrt := { lower := (32767/32768), upper := (174763/174758) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (5341093/4194304) }, upper := { exponent := 0, mantissa := (23/16) } }, logOuter := sk3LogOuterCertificate, logK := sk3LogKCertificate, logChi := chi7LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (349521/349516) } }, logDArg := sk3LogDArgCertificate }

private noncomputable def leaf19InnerLog : WideLogData :=
  innerPair19Data

set_option maxRecDepth 1000000 in
private theorem leaf19LocalValidity :
    LeafFacts leaf19Box leaf19Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf19Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (174763/174758) }) = true
      norm_num [leaf19Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf19CertificateValid :
    WideCertificateValid leaf19Box leaf19Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk3ValidityFacts chi7ValidityFacts
    leaf19LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf19CoverageChecked :
    coverageCheck (innerAD leaf19Box) leaf19InnerLog = true := by
  rfl'

private theorem leaf19InnerLogValid :
    leaf19InnerLog.Valid 8 (innerAD leaf19Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint10PositiveFacts.valid leaf19CoverageChecked

private noncomputable def leaf19InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629321/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf19InputLogOnePlusV_eq :
    leaf19InputLogOnePlusV = outerEnclosure 24
      (leaf19Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf19RoundedFacts : LeafRoundedFacts 8
    leaf19Certificate.logOnePlusV leaf19InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf19InputLogOnePlusV_eq }

private noncomputable def leaf19Inputs : Inputs :=
  inputsOfCaches globalInput sk3RoundedInputs
    chi7InputQChi innerPair19Input
    leaf19InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf19LowerChecked :
    lowerCheck 24 leaf19Box leaf19Inputs = true := by
  rfl'

private theorem leaf19CoversExact : CoversExact 8
    leaf19Box leaf19Certificate leaf19InnerLog leaf19Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk3RoundedFacts chi7RoundedFacts
    innerPair19RoundedFacts leaf19RoundedFacts (by rfl)

private theorem leaf19FlatSound : Sound leaf19Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf19CertificateValid
    leaf19InnerLogValid leaf19CoversExact leaf19LowerChecked

private noncomputable def leaf20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/16), kHi := (1/2), chiLo := (3/4), chiHi := (1) }

private noncomputable def leaf20Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (4194327/4194304) }, vSqrt := { lower := (32767/32768), upper := (34359279615/34358689792) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (5537687/4194304) }, upper := { exponent := 0, mantissa := (3/2) } }, logOuter := sk4LogOuterCertificate, logK := sk4LogKCertificate, logChi := chi7LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (68717969407/68717379584) } }, logDArg := sk4LogDArgCertificate }

private noncomputable def leaf20InnerLog : WideLogData :=
  innerPair23Data

set_option maxRecDepth 1000000 in
private theorem leaf20LocalValidity :
    LeafFacts leaf20Box leaf20Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf20Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (34359279615/34358689792) }) = true
      norm_num [leaf20Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf20CertificateValid :
    WideCertificateValid leaf20Box leaf20Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk4ValidityFacts chi7ValidityFacts
    leaf20LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf20CoverageChecked :
    coverageCheck (innerAD leaf20Box) leaf20InnerLog = true := by
  rfl'

private theorem leaf20InnerLogValid :
    leaf20InnerLog.Valid 8 (innerAD leaf20Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint11PositiveFacts.valid leaf20CoverageChecked

private noncomputable def leaf20InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629225/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf20InputLogOnePlusV_eq :
    leaf20InputLogOnePlusV = outerEnclosure 24
      (leaf20Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf20RoundedFacts : LeafRoundedFacts 8
    leaf20Certificate.logOnePlusV leaf20InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf20InputLogOnePlusV_eq }

private noncomputable def leaf20Inputs : Inputs :=
  inputsOfCaches globalInput sk4RoundedInputs
    chi7InputQChi innerPair23Input
    leaf20InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf20LowerChecked :
    lowerCheck 24 leaf20Box leaf20Inputs = true := by
  rfl'

private theorem leaf20CoversExact : CoversExact 8
    leaf20Box leaf20Certificate leaf20InnerLog leaf20Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk4RoundedFacts chi7RoundedFacts
    innerPair23RoundedFacts leaf20RoundedFacts (by rfl)

private theorem leaf20FlatSound : Sound leaf20Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf20CertificateValid
    leaf20InnerLogValid leaf20CoversExact leaf20LowerChecked

private noncomputable def component0Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1/4), kHi := (3/8), chiLo := (0), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component0Node0_sound : Sound component0Node0Box :=
  sound_of_literal_split component0Node0Box leaf0Box leaf1Box
    .k (5/16) (by rfl) (by rfl)
    leaf0FlatSound leaf1FlatSound

private noncomputable def component0Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/8), kHi := (1/2), chiLo := (1/8), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component0Node1_sound : Sound component0Node1Box :=
  sound_of_literal_split component0Node1Box leaf3Box leaf4Box
    .k (7/16) (by rfl) (by rfl)
    leaf3FlatSound leaf4FlatSound

private noncomputable def component0Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/8), kHi := (1/2), chiLo := (0), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component0Node2_sound : Sound component0Node2Box :=
  sound_of_literal_split component0Node2Box leaf2Box component0Node1Box
    .chi (1/8) (by rfl) (by rfl)
    leaf2FlatSound component0Node1_sound

private noncomputable def component0Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1/4), kHi := (1/2), chiLo := (0), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component0Node3_sound : Sound component0Node3Box :=
  sound_of_literal_split component0Node3Box component0Node0Box component0Node2Box
    .k (3/8) (by rfl) (by rfl)
    component0Node0_sound component0Node2_sound

private noncomputable def component0Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/16), kHi := (3/8), chiLo := (1/4), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component0Node4_sound : Sound component0Node4Box :=
  sound_of_literal_split component0Node4Box leaf6Box leaf7Box
    .chi (3/8) (by rfl) (by rfl)
    leaf6FlatSound leaf7FlatSound

private noncomputable def component0Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1/4), kHi := (3/8), chiLo := (1/4), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component0Node5_sound : Sound component0Node5Box :=
  sound_of_literal_split component0Node5Box leaf5Box component0Node4Box
    .k (5/16) (by rfl) (by rfl)
    leaf5FlatSound component0Node4_sound

private noncomputable def component0Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/8), kHi := (1/2), chiLo := (1/4), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component0Node6_sound : Sound component0Node6Box :=
  sound_of_literal_split component0Node6Box leaf8Box leaf9Box
    .k (7/16) (by rfl) (by rfl)
    leaf8FlatSound leaf9FlatSound

private noncomputable def component0Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/8), kHi := (1/2), chiLo := (3/8), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component0Node7_sound : Sound component0Node7Box :=
  sound_of_literal_split component0Node7Box leaf10Box leaf11Box
    .k (7/16) (by rfl) (by rfl)
    leaf10FlatSound leaf11FlatSound

private noncomputable def component0Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/8), kHi := (1/2), chiLo := (1/4), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component0Node8_sound : Sound component0Node8Box :=
  sound_of_literal_split component0Node8Box component0Node6Box component0Node7Box
    .chi (3/8) (by rfl) (by rfl)
    component0Node6_sound component0Node7_sound

private noncomputable def component0Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1/4), kHi := (1/2), chiLo := (1/4), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component0Node9_sound : Sound component0Node9Box :=
  sound_of_literal_split component0Node9Box component0Node5Box component0Node8Box
    .k (3/8) (by rfl) (by rfl)
    component0Node5_sound component0Node8_sound

private noncomputable def component0Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1/4), kHi := (1/2), chiLo := (0), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component0Node10_sound : Sound component0Node10Box :=
  sound_of_literal_split component0Node10Box component0Node3Box component0Node9Box
    .chi (1/4) (by rfl) (by rfl)
    component0Node3_sound component0Node9_sound

private noncomputable def component0Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1/4), kHi := (3/8), chiLo := (1/2), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component0Node11_sound : Sound component0Node11Box :=
  sound_of_literal_split component0Node11Box leaf12Box leaf13Box
    .k (5/16) (by rfl) (by rfl)
    leaf12FlatSound leaf13FlatSound

private noncomputable def component0Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1/4), kHi := (3/8), chiLo := (3/4), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component0Node12_sound : Sound component0Node12Box :=
  sound_of_literal_split component0Node12Box leaf14Box leaf15Box
    .k (5/16) (by rfl) (by rfl)
    leaf14FlatSound leaf15FlatSound

private noncomputable def component0Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1/4), kHi := (3/8), chiLo := (1/2), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component0Node13_sound : Sound component0Node13Box :=
  sound_of_literal_split component0Node13Box component0Node11Box component0Node12Box
    .chi (3/4) (by rfl) (by rfl)
    component0Node11_sound component0Node12_sound

private noncomputable def component0Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/16), kHi := (1/2), chiLo := (1/2), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component0Node14_sound : Sound component0Node14Box :=
  sound_of_literal_split component0Node14Box leaf17Box leaf18Box
    .chi (5/8) (by rfl) (by rfl)
    leaf17FlatSound leaf18FlatSound

private noncomputable def component0Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/8), kHi := (1/2), chiLo := (1/2), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component0Node15_sound : Sound component0Node15Box :=
  sound_of_literal_split component0Node15Box leaf16Box component0Node14Box
    .k (7/16) (by rfl) (by rfl)
    leaf16FlatSound component0Node14_sound

private noncomputable def component0Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/8), kHi := (1/2), chiLo := (3/4), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component0Node16_sound : Sound component0Node16Box :=
  sound_of_literal_split component0Node16Box leaf19Box leaf20Box
    .k (7/16) (by rfl) (by rfl)
    leaf19FlatSound leaf20FlatSound

private noncomputable def component0Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/8), kHi := (1/2), chiLo := (1/2), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component0Node17_sound : Sound component0Node17Box :=
  sound_of_literal_split component0Node17Box component0Node15Box component0Node16Box
    .chi (3/4) (by rfl) (by rfl)
    component0Node15_sound component0Node16_sound

private noncomputable def component0Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1/4), kHi := (1/2), chiLo := (1/2), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component0Node18_sound : Sound component0Node18Box :=
  sound_of_literal_split component0Node18Box component0Node13Box component0Node17Box
    .k (3/8) (by rfl) (by rfl)
    component0Node13_sound component0Node17_sound

noncomputable def component0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1/4), kHi := (1/2), chiLo := (0), chiHi := (1) }

set_option maxRecDepth 1000000 in
theorem component0_sound : Sound component0Box :=
  sound_of_literal_split component0Box component0Node10Box component0Node18Box
    .chi (1/2) (by rfl) (by rfl)
    component0Node10_sound component0Node18_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
