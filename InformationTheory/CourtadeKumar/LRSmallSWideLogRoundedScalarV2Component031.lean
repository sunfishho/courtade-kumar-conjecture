import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch6
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheSKBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheSKBatch2

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

private noncomputable def leaf1330Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (0), chiHi := (1/128) }

private noncomputable def leaf1330Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108915/67108864) }, vSqrt := { lower := (65529/65536), upper := (16777280/16777191) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := -1, mantissa := (67076047/33554432) }, upper := { exponent := 0, mantissa := (1049/1024) } }, logOuter := sk121LogOuterCertificate, logK := sk121LogKCertificate, logChi := chi137LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (33554471/33554382) } }, logDArg := sk121LogDArgCertificate }

private noncomputable def leaf1330InnerLog : WideLogData :=
  innerPair1Data

set_option maxRecDepth 1000000 in
private theorem leaf1330LocalValidity :
    LeafFacts leaf1330Box leaf1330Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1330Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (16777280/16777191) }) = true
      norm_num [leaf1330Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1330CertificateValid :
    WideCertificateValid leaf1330Box leaf1330Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk121ValidityFacts chi137ValidityFacts
    leaf1330LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1330CoverageChecked :
    coverageCheck (innerAD leaf1330Box) leaf1330InnerLog = true := by
  rfl'

private theorem leaf1330InnerLogValid :
    leaf1330InnerLog.Valid 8 (innerAD leaf1330Box) :=
  wideLogDataValid_of_cachedCheck endpoint0PositiveFacts
    endpoint2PositiveFacts.valid leaf1330CoverageChecked

private noncomputable def leaf1330InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629125/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1330InputLogOnePlusV_eq :
    leaf1330InputLogOnePlusV = outerEnclosure 24
      (leaf1330Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1330RoundedFacts : LeafRoundedFacts 8
    leaf1330Certificate.logOnePlusV leaf1330InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1330InputLogOnePlusV_eq }

private noncomputable def leaf1330Inputs : Inputs :=
  inputsOfCaches globalInput sk121RoundedInputs
    chi137InputQChi innerPair1Input
    leaf1330InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1330LowerChecked :
    lowerCheck 24 leaf1330Box leaf1330Inputs = true := by
  rfl'

private theorem leaf1330CoversExact : CoversExact 8
    leaf1330Box leaf1330Certificate leaf1330InnerLog leaf1330Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk121RoundedFacts chi137RoundedFacts
    innerPair1RoundedFacts leaf1330RoundedFacts (by rfl)

private theorem leaf1330FlatSound : Sound leaf1330Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1330CertificateValid
    leaf1330InnerLogValid leaf1330CoversExact leaf1330LowerChecked

private noncomputable def leaf1331Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (0), chiHi := (1/128) }

private noncomputable def leaf1331Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108917/67108864) }, vSqrt := { lower := (65529/65536), upper := (1677728/1677719) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := -1, mantissa := (67076045/33554432) }, upper := { exponent := 0, mantissa := (525/512) } }, logOuter := sk122LogOuterCertificate, logK := sk122LogKCertificate, logChi := chi137LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (3355447/3355438) } }, logDArg := sk122LogDArgCertificate }

private noncomputable def leaf1331InnerLog : WideLogData :=
  innerPair1Data

set_option maxRecDepth 1000000 in
private theorem leaf1331LocalValidity :
    LeafFacts leaf1331Box leaf1331Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1331Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (1677728/1677719) }) = true
      norm_num [leaf1331Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1331CertificateValid :
    WideCertificateValid leaf1331Box leaf1331Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk122ValidityFacts chi137ValidityFacts
    leaf1331LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1331CoverageChecked :
    coverageCheck (innerAD leaf1331Box) leaf1331InnerLog = true := by
  rfl'

private theorem leaf1331InnerLogValid :
    leaf1331InnerLog.Valid 8 (innerAD leaf1331Box) :=
  wideLogDataValid_of_cachedCheck endpoint0PositiveFacts
    endpoint2PositiveFacts.valid leaf1331CoverageChecked

private noncomputable def leaf1331InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814563/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1331InputLogOnePlusV_eq :
    leaf1331InputLogOnePlusV = outerEnclosure 24
      (leaf1331Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1331RoundedFacts : LeafRoundedFacts 8
    leaf1331Certificate.logOnePlusV leaf1331InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1331InputLogOnePlusV_eq }

private noncomputable def leaf1331Inputs : Inputs :=
  inputsOfCaches globalInput sk122RoundedInputs
    chi137InputQChi innerPair1Input
    leaf1331InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1331LowerChecked :
    lowerCheck 24 leaf1331Box leaf1331Inputs = true := by
  rfl'

private theorem leaf1331CoversExact : CoversExact 8
    leaf1331Box leaf1331Certificate leaf1331InnerLog leaf1331Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk122RoundedFacts chi137RoundedFacts
    innerPair1RoundedFacts leaf1331RoundedFacts (by rfl)

private theorem leaf1331FlatSound : Sound leaf1331Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1331CertificateValid
    leaf1331InnerLogValid leaf1331CoversExact leaf1331LowerChecked

private noncomputable def leaf1332Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (1/128), chiHi := (1/64) }

private noncomputable def leaf1332Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108917/67108864) }, vSqrt := { lower := (65529/65536), upper := (8388640/8388583) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (68648813/67108864) }, upper := { exponent := 0, mantissa := (537/512) } }, logOuter := sk121LogOuterCertificate, logK := sk121LogKCertificate, logChi := chi138LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (16777223/16777166) } }, logDArg := sk121LogDArgCertificate }

private noncomputable def leaf1332InnerLog : WideLogData :=
  innerPair10Data

set_option maxRecDepth 1000000 in
private theorem leaf1332LocalValidity :
    LeafFacts leaf1332Box leaf1332Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1332Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8388640/8388583) }) = true
      norm_num [leaf1332Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1332CertificateValid :
    WideCertificateValid leaf1332Box leaf1332Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk121ValidityFacts chi138ValidityFacts
    leaf1332LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1332CoverageChecked :
    coverageCheck (innerAD leaf1332Box) leaf1332InnerLog = true := by
  rfl'

private theorem leaf1332InnerLogValid :
    leaf1332InnerLog.Valid 8 (innerAD leaf1332Box) :=
  wideLogDataValid_of_cachedCheck endpoint3PositiveFacts
    endpoint2PositiveFacts.valid leaf1332CoverageChecked

private noncomputable def leaf1332InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814569/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1332InputLogOnePlusV_eq :
    leaf1332InputLogOnePlusV = outerEnclosure 24
      (leaf1332Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1332RoundedFacts : LeafRoundedFacts 8
    leaf1332Certificate.logOnePlusV leaf1332InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1332InputLogOnePlusV_eq }

private noncomputable def leaf1332Inputs : Inputs :=
  inputsOfCaches globalInput sk121RoundedInputs
    chi138InputQChi innerPair10Input
    leaf1332InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1332LowerChecked :
    lowerCheck 24 leaf1332Box leaf1332Inputs = true := by
  rfl'

private theorem leaf1332CoversExact : CoversExact 8
    leaf1332Box leaf1332Certificate leaf1332InnerLog leaf1332Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk121RoundedFacts chi138RoundedFacts
    innerPair10RoundedFacts leaf1332RoundedFacts (by rfl)

private theorem leaf1332FlatSound : Sound leaf1332Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1332CertificateValid
    leaf1332InnerLogValid leaf1332CoversExact leaf1332LowerChecked

private noncomputable def leaf1333Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (1/128), chiHi := (1/64) }

private noncomputable def leaf1333Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108919/67108864) }, vSqrt := { lower := (65529/65536), upper := (4194320/4194291) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (68714343/67108864) }, upper := { exponent := 0, mantissa := (269/256) } }, logOuter := sk122LogOuterCertificate, logK := sk122LogKCertificate, logChi := chi138LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (8388611/8388582) } }, logDArg := sk122LogDArgCertificate }

private noncomputable def leaf1333InnerLog : WideLogData :=
  innerPair10Data

set_option maxRecDepth 1000000 in
private theorem leaf1333LocalValidity :
    LeafFacts leaf1333Box leaf1333Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1333Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4194320/4194291) }) = true
      norm_num [leaf1333Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1333CertificateValid :
    WideCertificateValid leaf1333Box leaf1333Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk122ValidityFacts chi138ValidityFacts
    leaf1333LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1333CoverageChecked :
    coverageCheck (innerAD leaf1333Box) leaf1333InnerLog = true := by
  rfl'

private theorem leaf1333InnerLogValid :
    leaf1333InnerLog.Valid 8 (innerAD leaf1333Box) :=
  wideLogDataValid_of_cachedCheck endpoint3PositiveFacts
    endpoint2PositiveFacts.valid leaf1333CoverageChecked

private noncomputable def leaf1333InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629139/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1333InputLogOnePlusV_eq :
    leaf1333InputLogOnePlusV = outerEnclosure 24
      (leaf1333Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1333RoundedFacts : LeafRoundedFacts 8
    leaf1333Certificate.logOnePlusV leaf1333InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1333InputLogOnePlusV_eq }

private noncomputable def leaf1333Inputs : Inputs :=
  inputsOfCaches globalInput sk122RoundedInputs
    chi138InputQChi innerPair10Input
    leaf1333InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1333LowerChecked :
    lowerCheck 24 leaf1333Box leaf1333Inputs = true := by
  rfl'

private theorem leaf1333CoversExact : CoversExact 8
    leaf1333Box leaf1333Certificate leaf1333InnerLog leaf1333Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk122RoundedFacts chi138RoundedFacts
    innerPair10RoundedFacts leaf1333RoundedFacts (by rfl)

private theorem leaf1333FlatSound : Sound leaf1333Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1333CertificateValid
    leaf1333InnerLogValid leaf1333CoversExact leaf1333LowerChecked

private noncomputable def leaf1334Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (1/64), chiHi := (3/128) }

private noncomputable def leaf1334Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108919/67108864) }, vSqrt := { lower := (65529/65536), upper := (16777280/16777141) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (70221579/67108864) }, upper := { exponent := 0, mantissa := (1099/1024) } }, logOuter := sk121LogOuterCertificate, logK := sk121LogKCertificate, logChi := chi101LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (33554421/33554282) } }, logDArg := sk121LogDArgCertificate }

private noncomputable def leaf1334InnerLog : WideLogData :=
  innerPair9Data

set_option maxRecDepth 1000000 in
private theorem leaf1334LocalValidity :
    LeafFacts leaf1334Box leaf1334Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1334Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (16777280/16777141) }) = true
      norm_num [leaf1334Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1334CertificateValid :
    WideCertificateValid leaf1334Box leaf1334Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk121ValidityFacts chi101ValidityFacts
    leaf1334LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1334CoverageChecked :
    coverageCheck (innerAD leaf1334Box) leaf1334InnerLog = true := by
  rfl'

private theorem leaf1334InnerLogValid :
    leaf1334InnerLog.Valid 8 (innerAD leaf1334Box) :=
  wideLogDataValid_of_cachedCheck endpoint3PositiveFacts
    endpoint1PositiveFacts.valid leaf1334CoverageChecked

private noncomputable def leaf1334InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814575/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1334InputLogOnePlusV_eq :
    leaf1334InputLogOnePlusV = outerEnclosure 24
      (leaf1334Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1334RoundedFacts : LeafRoundedFacts 8
    leaf1334Certificate.logOnePlusV leaf1334InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1334InputLogOnePlusV_eq }

private noncomputable def leaf1334Inputs : Inputs :=
  inputsOfCaches globalInput sk121RoundedInputs
    chi101InputQChi innerPair9Input
    leaf1334InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1334LowerChecked :
    lowerCheck 24 leaf1334Box leaf1334Inputs = true := by
  rfl'

private theorem leaf1334CoversExact : CoversExact 8
    leaf1334Box leaf1334Certificate leaf1334InnerLog leaf1334Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk121RoundedFacts chi101RoundedFacts
    innerPair9RoundedFacts leaf1334RoundedFacts (by rfl)

private theorem leaf1334FlatSound : Sound leaf1334Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1334CertificateValid
    leaf1334InnerLogValid leaf1334CoversExact leaf1334LowerChecked

private noncomputable def leaf1335Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (1/64), chiHi := (3/128) }

private noncomputable def leaf1335Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108921/67108864) }, vSqrt := { lower := (65529/65536), upper := (8388640/8388569) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (70352641/67108864) }, upper := { exponent := 0, mantissa := (551/512) } }, logOuter := sk122LogOuterCertificate, logK := sk122LogKCertificate, logChi := chi101LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (16777209/16777138) } }, logDArg := sk122LogDArgCertificate }

private noncomputable def leaf1335InnerLog : WideLogData :=
  innerPair9Data

set_option maxRecDepth 1000000 in
private theorem leaf1335LocalValidity :
    LeafFacts leaf1335Box leaf1335Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1335Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8388640/8388569) }) = true
      norm_num [leaf1335Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1335CertificateValid :
    WideCertificateValid leaf1335Box leaf1335Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk122ValidityFacts chi101ValidityFacts
    leaf1335LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1335CoverageChecked :
    coverageCheck (innerAD leaf1335Box) leaf1335InnerLog = true := by
  rfl'

private theorem leaf1335InnerLogValid :
    leaf1335InnerLog.Valid 8 (innerAD leaf1335Box) :=
  wideLogDataValid_of_cachedCheck endpoint3PositiveFacts
    endpoint1PositiveFacts.valid leaf1335CoverageChecked

private noncomputable def leaf1335InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (363411/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf1335InputLogOnePlusV_eq :
    leaf1335InputLogOnePlusV = outerEnclosure 24
      (leaf1335Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1335RoundedFacts : LeafRoundedFacts 8
    leaf1335Certificate.logOnePlusV leaf1335InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1335InputLogOnePlusV_eq }

private noncomputable def leaf1335Inputs : Inputs :=
  inputsOfCaches globalInput sk122RoundedInputs
    chi101InputQChi innerPair9Input
    leaf1335InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1335LowerChecked :
    lowerCheck 24 leaf1335Box leaf1335Inputs = true := by
  rfl'

private theorem leaf1335CoversExact : CoversExact 8
    leaf1335Box leaf1335Certificate leaf1335InnerLog leaf1335Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk122RoundedFacts chi101RoundedFacts
    innerPair9RoundedFacts leaf1335RoundedFacts (by rfl)

private theorem leaf1335FlatSound : Sound leaf1335Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1335CertificateValid
    leaf1335InnerLogValid leaf1335CoversExact leaf1335LowerChecked

private noncomputable def leaf1336Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (3/128), chiHi := (7/256) }

private noncomputable def leaf1336Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217791/134217728) }, vSqrt := { lower := (65529/65536), upper := (33554560/33554257) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (143621507/134217728) }, upper := { exponent := 0, mantissa := (2223/2048) } }, logOuter := sk121LogOuterCertificate, logK := sk121LogKCertificate, logChi := chi123LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (67108817/67108514) } }, logDArg := sk121LogDArgCertificate }

private noncomputable def leaf1336InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf1336LocalValidity :
    LeafFacts leaf1336Box leaf1336Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1336Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (33554560/33554257) }) = true
      norm_num [leaf1336Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1336CertificateValid :
    WideCertificateValid leaf1336Box leaf1336Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk121ValidityFacts chi123ValidityFacts
    leaf1336LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1336CoverageChecked :
    coverageCheck (innerAD leaf1336Box) leaf1336InnerLog = true := by
  rfl'

private theorem leaf1336InnerLogValid :
    leaf1336InnerLog.Valid 8 (innerAD leaf1336Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf1336CoverageChecked

private noncomputable def leaf1336InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907289/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1336InputLogOnePlusV_eq :
    leaf1336InputLogOnePlusV = outerEnclosure 24
      (leaf1336Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1336RoundedFacts : LeafRoundedFacts 8
    leaf1336Certificate.logOnePlusV leaf1336InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1336InputLogOnePlusV_eq }

private noncomputable def leaf1336Inputs : Inputs :=
  inputsOfCaches globalInput sk121RoundedInputs
    chi123InputQChi innerPair5Input
    leaf1336InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1336LowerChecked :
    lowerCheck 24 leaf1336Box leaf1336Inputs = true := by
  rfl'

private theorem leaf1336CoversExact : CoversExact 8
    leaf1336Box leaf1336Certificate leaf1336InnerLog leaf1336Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk121RoundedFacts chi123RoundedFacts
    innerPair5RoundedFacts leaf1336RoundedFacts (by rfl)

private theorem leaf1336FlatSound : Sound leaf1336Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1336CertificateValid
    leaf1336InnerLogValid leaf1336CoversExact leaf1336LowerChecked

private noncomputable def leaf1337Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (7/256), chiHi := (1/32) }

private noncomputable def leaf1337Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217793/134217728) }, vSqrt := { lower := (65529/65536), upper := (4194320/4194279) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (145194273/134217728) }, upper := { exponent := 0, mantissa := (281/256) } }, logOuter := sk121LogOuterCertificate, logK := sk121LogKCertificate, logChi := chi124LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (8388599/8388558) } }, logDArg := sk121LogDArgCertificate }

private noncomputable def leaf1337InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf1337LocalValidity :
    LeafFacts leaf1337Box leaf1337Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1337Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4194320/4194279) }) = true
      norm_num [leaf1337Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1337CertificateValid :
    WideCertificateValid leaf1337Box leaf1337Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk121ValidityFacts chi124ValidityFacts
    leaf1337LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1337CoverageChecked :
    coverageCheck (innerAD leaf1337Box) leaf1337InnerLog = true := by
  rfl'

private theorem leaf1337InnerLogValid :
    leaf1337InnerLog.Valid 8 (innerAD leaf1337Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf1337CoverageChecked

private noncomputable def leaf1337InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629163/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1337InputLogOnePlusV_eq :
    leaf1337InputLogOnePlusV = outerEnclosure 24
      (leaf1337Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1337RoundedFacts : LeafRoundedFacts 8
    leaf1337Certificate.logOnePlusV leaf1337InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1337InputLogOnePlusV_eq }

private noncomputable def leaf1337Inputs : Inputs :=
  inputsOfCaches globalInput sk121RoundedInputs
    chi124InputQChi innerPair5Input
    leaf1337InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1337LowerChecked :
    lowerCheck 24 leaf1337Box leaf1337Inputs = true := by
  rfl'

private theorem leaf1337CoversExact : CoversExact 8
    leaf1337Box leaf1337Certificate leaf1337InnerLog leaf1337Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk121RoundedFacts chi124RoundedFacts
    innerPair5RoundedFacts leaf1337RoundedFacts (by rfl)

private theorem leaf1337FlatSound : Sound leaf1337Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1337CertificateValid
    leaf1337InnerLogValid leaf1337CoversExact leaf1337LowerChecked

private noncomputable def leaf1338Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (3/128), chiHi := (7/256) }

private noncomputable def leaf1338Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217793/134217728) }, vSqrt := { lower := (65529/65536), upper := (3355456/3355425) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (144014697/134217728) }, upper := { exponent := 0, mantissa := (1115/1024) } }, logOuter := sk122LogOuterCertificate, logK := sk122LogKCertificate, logChi := chi123LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (6710881/6710850) } }, logDArg := sk122LogDArgCertificate }

private noncomputable def leaf1338InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf1338LocalValidity :
    LeafFacts leaf1338Box leaf1338Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1338Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (3355456/3355425) }) = true
      norm_num [leaf1338Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1338CertificateValid :
    WideCertificateValid leaf1338Box leaf1338Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk122ValidityFacts chi123ValidityFacts
    leaf1338LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1338CoverageChecked :
    coverageCheck (innerAD leaf1338Box) leaf1338InnerLog = true := by
  rfl'

private theorem leaf1338InnerLogValid :
    leaf1338InnerLog.Valid 8 (innerAD leaf1338Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf1338CoverageChecked

private noncomputable def leaf1338InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814579/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1338InputLogOnePlusV_eq :
    leaf1338InputLogOnePlusV = outerEnclosure 24
      (leaf1338Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1338RoundedFacts : LeafRoundedFacts 8
    leaf1338Certificate.logOnePlusV leaf1338InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1338InputLogOnePlusV_eq }

private noncomputable def leaf1338Inputs : Inputs :=
  inputsOfCaches globalInput sk122RoundedInputs
    chi123InputQChi innerPair5Input
    leaf1338InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1338LowerChecked :
    lowerCheck 24 leaf1338Box leaf1338Inputs = true := by
  rfl'

private theorem leaf1338CoversExact : CoversExact 8
    leaf1338Box leaf1338Certificate leaf1338InnerLog leaf1338Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk122RoundedFacts chi123RoundedFacts
    innerPair5RoundedFacts leaf1338RoundedFacts (by rfl)

private theorem leaf1338FlatSound : Sound leaf1338Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1338CertificateValid
    leaf1338InnerLogValid leaf1338CoversExact leaf1338LowerChecked

private noncomputable def leaf1339Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (7/256), chiHi := (1/32) }

private noncomputable def leaf1339Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217795/134217728) }, vSqrt := { lower := (65529/65536), upper := (2097160/2097139) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (145652995/134217728) }, upper := { exponent := 0, mantissa := (141/128) } }, logOuter := sk122LogOuterCertificate, logK := sk122LogKCertificate, logChi := chi124LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (4194299/4194278) } }, logDArg := sk122LogDArgCertificate }

private noncomputable def leaf1339InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf1339LocalValidity :
    LeafFacts leaf1339Box leaf1339Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1339Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (2097160/2097139) }) = true
      norm_num [leaf1339Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1339CertificateValid :
    WideCertificateValid leaf1339Box leaf1339Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk122ValidityFacts chi124ValidityFacts
    leaf1339LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1339CoverageChecked :
    coverageCheck (innerAD leaf1339Box) leaf1339InnerLog = true := by
  rfl'

private theorem leaf1339InnerLogValid :
    leaf1339InnerLog.Valid 8 (innerAD leaf1339Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf1339CoverageChecked

private noncomputable def leaf1339InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629165/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1339InputLogOnePlusV_eq :
    leaf1339InputLogOnePlusV = outerEnclosure 24
      (leaf1339Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1339RoundedFacts : LeafRoundedFacts 8
    leaf1339Certificate.logOnePlusV leaf1339InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1339InputLogOnePlusV_eq }

private noncomputable def leaf1339Inputs : Inputs :=
  inputsOfCaches globalInput sk122RoundedInputs
    chi124InputQChi innerPair5Input
    leaf1339InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1339LowerChecked :
    lowerCheck 24 leaf1339Box leaf1339Inputs = true := by
  rfl'

private theorem leaf1339CoversExact : CoversExact 8
    leaf1339Box leaf1339Certificate leaf1339InnerLog leaf1339Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk122RoundedFacts chi124RoundedFacts
    innerPair5RoundedFacts leaf1339RoundedFacts (by rfl)

private theorem leaf1339FlatSound : Sound leaf1339Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1339CertificateValid
    leaf1339InnerLogValid leaf1339CoversExact leaf1339LowerChecked

private noncomputable def leaf1340Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (1/32), chiHi := (9/256) }

private noncomputable def leaf1340Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217795/134217728) }, vSqrt := { lower := (65529/65536), upper := (33554560/33554207) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (146767039/134217728) }, upper := { exponent := 0, mantissa := (2273/2048) } }, logOuter := sk121LogOuterCertificate, logK := sk121LogKCertificate, logChi := chi139LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (67108767/67108414) } }, logDArg := sk121LogDArgCertificate }

private noncomputable def leaf1340InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf1340LocalValidity :
    LeafFacts leaf1340Box leaf1340Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1340Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (33554560/33554207) }) = true
      norm_num [leaf1340Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1340CertificateValid :
    WideCertificateValid leaf1340Box leaf1340Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk121ValidityFacts chi139ValidityFacts
    leaf1340LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1340CoverageChecked :
    coverageCheck (innerAD leaf1340Box) leaf1340InnerLog = true := by
  rfl'

private theorem leaf1340InnerLogValid :
    leaf1340InnerLog.Valid 8 (innerAD leaf1340Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf1340CoverageChecked

private noncomputable def leaf1340InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629169/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1340InputLogOnePlusV_eq :
    leaf1340InputLogOnePlusV = outerEnclosure 24
      (leaf1340Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1340RoundedFacts : LeafRoundedFacts 8
    leaf1340Certificate.logOnePlusV leaf1340InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1340InputLogOnePlusV_eq }

private noncomputable def leaf1340Inputs : Inputs :=
  inputsOfCaches globalInput sk121RoundedInputs
    chi139InputQChi innerPair5Input
    leaf1340InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1340LowerChecked :
    lowerCheck 24 leaf1340Box leaf1340Inputs = true := by
  rfl'

private theorem leaf1340CoversExact : CoversExact 8
    leaf1340Box leaf1340Certificate leaf1340InnerLog leaf1340Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk121RoundedFacts chi139RoundedFacts
    innerPair5RoundedFacts leaf1340RoundedFacts (by rfl)

private theorem leaf1340FlatSound : Sound leaf1340Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1340CertificateValid
    leaf1340InnerLogValid leaf1340CoversExact leaf1340LowerChecked

private noncomputable def leaf1341Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (9/256), chiHi := (5/128) }

private noncomputable def leaf1341Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435573/268435456) }, vSqrt := { lower := (65529/65536), upper := (11184832/11184729) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (296712397/268435456) }, upper := { exponent := 0, mantissa := (2293/2048) } }, logOuter := sk123LogOuterCertificate, logK := sk123LogKCertificate, logChi := chi140LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (22369561/22369458) } }, logDArg := sk123LogDArgCertificate }

private noncomputable def leaf1341InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf1341LocalValidity :
    LeafFacts leaf1341Box leaf1341Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1341Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (11184832/11184729) }) = true
      norm_num [leaf1341Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1341CertificateValid :
    WideCertificateValid leaf1341Box leaf1341Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk123ValidityFacts chi140ValidityFacts
    leaf1341LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1341CoverageChecked :
    coverageCheck (innerAD leaf1341Box) leaf1341InnerLog = true := by
  rfl'

private theorem leaf1341InnerLogValid :
    leaf1341InnerLog.Valid 8 (innerAD leaf1341Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf1341CoverageChecked

private noncomputable def leaf1341InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814579/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1341InputLogOnePlusV_eq :
    leaf1341InputLogOnePlusV = outerEnclosure 24
      (leaf1341Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1341RoundedFacts : LeafRoundedFacts 8
    leaf1341Certificate.logOnePlusV leaf1341InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1341InputLogOnePlusV_eq }

private noncomputable def leaf1341Inputs : Inputs :=
  inputsOfCaches globalInput sk123RoundedInputs
    chi140InputQChi innerPair5Input
    leaf1341InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1341LowerChecked :
    lowerCheck 24 leaf1341Box leaf1341Inputs = true := by
  rfl'

private theorem leaf1341CoversExact : CoversExact 8
    leaf1341Box leaf1341Certificate leaf1341InnerLog leaf1341Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk123RoundedFacts chi140RoundedFacts
    innerPair5RoundedFacts leaf1341RoundedFacts (by rfl)

private theorem leaf1341FlatSound : Sound leaf1341Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1341CertificateValid
    leaf1341InnerLogValid leaf1341CoversExact leaf1341LowerChecked

private noncomputable def leaf1342Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (9/256), chiHi := (5/128) }

private noncomputable def leaf1342Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435575/268435456) }, vSqrt := { lower := (65529/65536), upper := (16777248/16777091) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (297302183/268435456) }, upper := { exponent := 0, mantissa := (1149/1024) } }, logOuter := sk124LogOuterCertificate, logK := sk124LogKCertificate, logChi := chi140LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (33554339/33554182) } }, logDArg := sk124LogDArgCertificate }

private noncomputable def leaf1342InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf1342LocalValidity :
    LeafFacts leaf1342Box leaf1342Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1342Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (16777248/16777091) }) = true
      norm_num [leaf1342Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1342CertificateValid :
    WideCertificateValid leaf1342Box leaf1342Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk124ValidityFacts chi140ValidityFacts
    leaf1342LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1342CoverageChecked :
    coverageCheck (innerAD leaf1342Box) leaf1342InnerLog = true := by
  rfl'

private theorem leaf1342InnerLogValid :
    leaf1342InnerLog.Valid 8 (innerAD leaf1342Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf1342CoverageChecked

private noncomputable def leaf1342InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629159/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1342InputLogOnePlusV_eq :
    leaf1342InputLogOnePlusV = outerEnclosure 24
      (leaf1342Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1342RoundedFacts : LeafRoundedFacts 8
    leaf1342Certificate.logOnePlusV leaf1342InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1342InputLogOnePlusV_eq }

private noncomputable def leaf1342Inputs : Inputs :=
  inputsOfCaches globalInput sk124RoundedInputs
    chi140InputQChi innerPair5Input
    leaf1342InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1342LowerChecked :
    lowerCheck 24 leaf1342Box leaf1342Inputs = true := by
  rfl'

private theorem leaf1342CoversExact : CoversExact 8
    leaf1342Box leaf1342Certificate leaf1342InnerLog leaf1342Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk124RoundedFacts chi140RoundedFacts
    innerPair5RoundedFacts leaf1342RoundedFacts (by rfl)

private theorem leaf1342FlatSound : Sound leaf1342Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1342CertificateValid
    leaf1342InnerLogValid leaf1342CoversExact leaf1342LowerChecked

private noncomputable def leaf1343Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (5/128), chiHi := (3/64) }

private noncomputable def leaf1343Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217837/134217728) }, vSqrt := { lower := (65529/65536), upper := (16777248/16777069) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (149912533/134217728) }, upper := { exponent := 0, mantissa := (1171/1024) } }, logOuter := sk123LogOuterCertificate, logK := sk123LogKCertificate, logChi := chi39LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (33554317/33554138) } }, logDArg := sk123LogDArgCertificate }

private noncomputable def leaf1343InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf1343LocalValidity :
    LeafFacts leaf1343Box leaf1343Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1343Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (16777248/16777069) }) = true
      norm_num [leaf1343Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1343CertificateValid :
    WideCertificateValid leaf1343Box leaf1343Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk123ValidityFacts chi39ValidityFacts
    leaf1343LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1343CoverageChecked :
    coverageCheck (innerAD leaf1343Box) leaf1343InnerLog = true := by
  rfl'

private theorem leaf1343InnerLogValid :
    leaf1343InnerLog.Valid 8 (innerAD leaf1343Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf1343CoverageChecked

private noncomputable def leaf1343InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814585/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1343InputLogOnePlusV_eq :
    leaf1343InputLogOnePlusV = outerEnclosure 24
      (leaf1343Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1343RoundedFacts : LeafRoundedFacts 8
    leaf1343Certificate.logOnePlusV leaf1343InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1343InputLogOnePlusV_eq }

private noncomputable def leaf1343Inputs : Inputs :=
  inputsOfCaches globalInput sk123RoundedInputs
    chi39InputQChi innerPair6Input
    leaf1343InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1343LowerChecked :
    lowerCheck 24 leaf1343Box leaf1343Inputs = true := by
  rfl'

private theorem leaf1343CoversExact : CoversExact 8
    leaf1343Box leaf1343Certificate leaf1343InnerLog leaf1343Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk123RoundedFacts chi39RoundedFacts
    innerPair6RoundedFacts leaf1343RoundedFacts (by rfl)

private theorem leaf1343FlatSound : Sound leaf1343Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1343CertificateValid
    leaf1343InnerLogValid leaf1343CoversExact leaf1343LowerChecked

private noncomputable def leaf1344Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (5/128), chiHi := (3/64) }

private noncomputable def leaf1344Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217839/134217728) }, vSqrt := { lower := (65529/65536), upper := (8388624/8388533) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (150240191/134217728) }, upper := { exponent := 0, mantissa := (587/512) } }, logOuter := sk124LogOuterCertificate, logK := sk124LogKCertificate, logChi := chi39LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (16777157/16777066) } }, logDArg := sk124LogDArgCertificate }

private noncomputable def leaf1344InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf1344LocalValidity :
    LeafFacts leaf1344Box leaf1344Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1344Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8388624/8388533) }) = true
      norm_num [leaf1344Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1344CertificateValid :
    WideCertificateValid leaf1344Box leaf1344Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk124ValidityFacts chi39ValidityFacts
    leaf1344LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1344CoverageChecked :
    coverageCheck (innerAD leaf1344Box) leaf1344InnerLog = true := by
  rfl'

private theorem leaf1344InnerLogValid :
    leaf1344InnerLog.Valid 8 (innerAD leaf1344Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf1344CoverageChecked

private noncomputable def leaf1344InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907293/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1344InputLogOnePlusV_eq :
    leaf1344InputLogOnePlusV = outerEnclosure 24
      (leaf1344Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1344RoundedFacts : LeafRoundedFacts 8
    leaf1344Certificate.logOnePlusV leaf1344InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1344InputLogOnePlusV_eq }

private noncomputable def leaf1344Inputs : Inputs :=
  inputsOfCaches globalInput sk124RoundedInputs
    chi39InputQChi innerPair6Input
    leaf1344InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1344LowerChecked :
    lowerCheck 24 leaf1344Box leaf1344Inputs = true := by
  rfl'

private theorem leaf1344CoversExact : CoversExact 8
    leaf1344Box leaf1344Certificate leaf1344InnerLog leaf1344Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk124RoundedFacts chi39RoundedFacts
    innerPair6RoundedFacts leaf1344RoundedFacts (by rfl)

private theorem leaf1344FlatSound : Sound leaf1344Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1344CertificateValid
    leaf1344InnerLogValid leaf1344CoversExact leaf1344LowerChecked

private noncomputable def leaf1345Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (1/32), chiHi := (9/256) }

private noncomputable def leaf1345Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435575/268435456) }, vSqrt := { lower := (65529/65536), upper := (67108992/67108405) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (294615371/268435456) }, upper := { exponent := 0, mantissa := (4555/4096) } }, logOuter := sk125LogOuterCertificate, logK := sk125LogKCertificate, logChi := chi139LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (134217397/134216810) } }, logDArg := sk125LogDArgCertificate }

private noncomputable def leaf1345InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf1345LocalValidity :
    LeafFacts leaf1345Box leaf1345Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1345Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (67108992/67108405) }) = true
      norm_num [leaf1345Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1345CertificateValid :
    WideCertificateValid leaf1345Box leaf1345Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk125ValidityFacts chi139ValidityFacts
    leaf1345LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1345CoverageChecked :
    coverageCheck (innerAD leaf1345Box) leaf1345InnerLog = true := by
  rfl'

private theorem leaf1345InnerLogValid :
    leaf1345InnerLog.Valid 8 (innerAD leaf1345Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf1345CoverageChecked

private noncomputable def leaf1345InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814577/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1345InputLogOnePlusV_eq :
    leaf1345InputLogOnePlusV = outerEnclosure 24
      (leaf1345Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1345RoundedFacts : LeafRoundedFacts 8
    leaf1345Certificate.logOnePlusV leaf1345InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1345InputLogOnePlusV_eq }

private noncomputable def leaf1345Inputs : Inputs :=
  inputsOfCaches globalInput sk125RoundedInputs
    chi139InputQChi innerPair5Input
    leaf1345InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1345LowerChecked :
    lowerCheck 24 leaf1345Box leaf1345Inputs = true := by
  rfl'

private theorem leaf1345CoversExact : CoversExact 8
    leaf1345Box leaf1345Certificate leaf1345InnerLog leaf1345Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk125RoundedFacts chi139RoundedFacts
    innerPair5RoundedFacts leaf1345RoundedFacts (by rfl)

private theorem leaf1345FlatSound : Sound leaf1345Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1345CertificateValid
    leaf1345InnerLogValid leaf1345CoversExact leaf1345LowerChecked

private noncomputable def leaf1346Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (1/32), chiHi := (9/256) }

private noncomputable def leaf1346Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435577/268435456) }, vSqrt := { lower := (65529/65536), upper := (16777248/16777099) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (295139625/268435456) }, upper := { exponent := 0, mantissa := (1141/1024) } }, logOuter := sk126LogOuterCertificate, logK := sk126LogKCertificate, logChi := chi139LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (33554347/33554198) } }, logDArg := sk126LogDArgCertificate }

private noncomputable def leaf1346InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf1346LocalValidity :
    LeafFacts leaf1346Box leaf1346Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1346Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (16777248/16777099) }) = true
      norm_num [leaf1346Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1346CertificateValid :
    WideCertificateValid leaf1346Box leaf1346Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk126ValidityFacts chi139ValidityFacts
    leaf1346LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1346CoverageChecked :
    coverageCheck (innerAD leaf1346Box) leaf1346InnerLog = true := by
  rfl'

private theorem leaf1346InnerLogValid :
    leaf1346InnerLog.Valid 8 (innerAD leaf1346Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf1346CoverageChecked

private noncomputable def leaf1346InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629155/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1346InputLogOnePlusV_eq :
    leaf1346InputLogOnePlusV = outerEnclosure 24
      (leaf1346Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1346RoundedFacts : LeafRoundedFacts 8
    leaf1346Certificate.logOnePlusV leaf1346InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1346InputLogOnePlusV_eq }

private noncomputable def leaf1346Inputs : Inputs :=
  inputsOfCaches globalInput sk126RoundedInputs
    chi139InputQChi innerPair5Input
    leaf1346InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1346LowerChecked :
    lowerCheck 24 leaf1346Box leaf1346Inputs = true := by
  rfl'

private theorem leaf1346CoversExact : CoversExact 8
    leaf1346Box leaf1346Certificate leaf1346InnerLog leaf1346Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk126RoundedFacts chi139RoundedFacts
    innerPair5RoundedFacts leaf1346RoundedFacts (by rfl)

private theorem leaf1346FlatSound : Sound leaf1346Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1346CertificateValid
    leaf1346InnerLogValid leaf1346CoversExact leaf1346LowerChecked

private noncomputable def leaf1347Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (9/256), chiHi := (5/128) }

private noncomputable def leaf1347Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435577/268435456) }, vSqrt := { lower := (65529/65536), upper := (33554496/33554177) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (297891969/268435456) }, upper := { exponent := 0, mantissa := (2303/2048) } }, logOuter := sk125LogOuterCertificate, logK := sk125LogKCertificate, logChi := chi140LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (67108673/67108354) } }, logDArg := sk125LogDArgCertificate }

private noncomputable def leaf1347InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf1347LocalValidity :
    LeafFacts leaf1347Box leaf1347Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1347Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (33554496/33554177) }) = true
      norm_num [leaf1347Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1347CertificateValid :
    WideCertificateValid leaf1347Box leaf1347Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk125ValidityFacts chi140ValidityFacts
    leaf1347LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1347CoverageChecked :
    coverageCheck (innerAD leaf1347Box) leaf1347InnerLog = true := by
  rfl'

private theorem leaf1347InnerLogValid :
    leaf1347InnerLog.Valid 8 (innerAD leaf1347Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf1347CoverageChecked

private noncomputable def leaf1347InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453645/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf1347InputLogOnePlusV_eq :
    leaf1347InputLogOnePlusV = outerEnclosure 24
      (leaf1347Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1347RoundedFacts : LeafRoundedFacts 8
    leaf1347Certificate.logOnePlusV leaf1347InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1347InputLogOnePlusV_eq }

private noncomputable def leaf1347Inputs : Inputs :=
  inputsOfCaches globalInput sk125RoundedInputs
    chi140InputQChi innerPair5Input
    leaf1347InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1347LowerChecked :
    lowerCheck 24 leaf1347Box leaf1347Inputs = true := by
  rfl'

private theorem leaf1347CoversExact : CoversExact 8
    leaf1347Box leaf1347Certificate leaf1347InnerLog leaf1347Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk125RoundedFacts chi140RoundedFacts
    innerPair5RoundedFacts leaf1347RoundedFacts (by rfl)

private theorem leaf1347FlatSound : Sound leaf1347Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1347CertificateValid
    leaf1347InnerLogValid leaf1347CoversExact leaf1347LowerChecked

private noncomputable def leaf1348Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (9/256), chiHi := (5/128) }

private noncomputable def leaf1348Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435579/268435456) }, vSqrt := { lower := (65529/65536), upper := (2796208/2796181) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (298481755/268435456) }, upper := { exponent := 0, mantissa := (577/512) } }, logOuter := sk126LogOuterCertificate, logK := sk126LogKCertificate, logChi := chi140LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (5592389/5592362) } }, logDArg := sk126LogDArgCertificate }

private noncomputable def leaf1348InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf1348LocalValidity :
    LeafFacts leaf1348Box leaf1348Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1348Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (2796208/2796181) }) = true
      norm_num [leaf1348Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1348CertificateValid :
    WideCertificateValid leaf1348Box leaf1348Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk126ValidityFacts chi140ValidityFacts
    leaf1348LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1348CoverageChecked :
    coverageCheck (innerAD leaf1348Box) leaf1348InnerLog = true := by
  rfl'

private theorem leaf1348InnerLogValid :
    leaf1348InnerLog.Valid 8 (innerAD leaf1348Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf1348CoverageChecked

private noncomputable def leaf1348InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814581/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1348InputLogOnePlusV_eq :
    leaf1348InputLogOnePlusV = outerEnclosure 24
      (leaf1348Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1348RoundedFacts : LeafRoundedFacts 8
    leaf1348Certificate.logOnePlusV leaf1348InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1348InputLogOnePlusV_eq }

private noncomputable def leaf1348Inputs : Inputs :=
  inputsOfCaches globalInput sk126RoundedInputs
    chi140InputQChi innerPair6Input
    leaf1348InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1348LowerChecked :
    lowerCheck 24 leaf1348Box leaf1348Inputs = true := by
  rfl'

private theorem leaf1348CoversExact : CoversExact 8
    leaf1348Box leaf1348Certificate leaf1348InnerLog leaf1348Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk126RoundedFacts chi140RoundedFacts
    innerPair6RoundedFacts leaf1348RoundedFacts (by rfl)

private theorem leaf1348FlatSound : Sound leaf1348Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1348CertificateValid
    leaf1348InnerLogValid leaf1348CoversExact leaf1348LowerChecked

private noncomputable def leaf1349Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (5/128), chiHi := (3/64) }

private noncomputable def leaf1349Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217841/134217728) }, vSqrt := { lower := (65529/65536), upper := (16777248/16777063) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (150567849/134217728) }, upper := { exponent := 0, mantissa := (1177/1024) } }, logOuter := sk125LogOuterCertificate, logK := sk125LogKCertificate, logChi := chi39LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (33554311/33554126) } }, logDArg := sk125LogDArgCertificate }

private noncomputable def leaf1349InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf1349LocalValidity :
    LeafFacts leaf1349Box leaf1349Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1349Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (16777248/16777063) }) = true
      norm_num [leaf1349Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1349CertificateValid :
    WideCertificateValid leaf1349Box leaf1349Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk125ValidityFacts chi39ValidityFacts
    leaf1349LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1349CoverageChecked :
    coverageCheck (innerAD leaf1349Box) leaf1349InnerLog = true := by
  rfl'

private theorem leaf1349InnerLogValid :
    leaf1349InnerLog.Valid 8 (innerAD leaf1349Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf1349CoverageChecked

private noncomputable def leaf1349InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629173/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1349InputLogOnePlusV_eq :
    leaf1349InputLogOnePlusV = outerEnclosure 24
      (leaf1349Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1349RoundedFacts : LeafRoundedFacts 8
    leaf1349Certificate.logOnePlusV leaf1349InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1349InputLogOnePlusV_eq }

private noncomputable def leaf1349Inputs : Inputs :=
  inputsOfCaches globalInput sk125RoundedInputs
    chi39InputQChi innerPair6Input
    leaf1349InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1349LowerChecked :
    lowerCheck 24 leaf1349Box leaf1349Inputs = true := by
  rfl'

private theorem leaf1349CoversExact : CoversExact 8
    leaf1349Box leaf1349Certificate leaf1349InnerLog leaf1349Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk125RoundedFacts chi39RoundedFacts
    innerPair6RoundedFacts leaf1349RoundedFacts (by rfl)

private theorem leaf1349FlatSound : Sound leaf1349Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1349CertificateValid
    leaf1349InnerLogValid leaf1349CoversExact leaf1349LowerChecked

private noncomputable def leaf1350Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (5/128), chiHi := (3/64) }

private noncomputable def leaf1350Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217843/134217728) }, vSqrt := { lower := (65529/65536), upper := (4194312/4194265) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (150895507/134217728) }, upper := { exponent := 0, mantissa := (295/256) } }, logOuter := sk126LogOuterCertificate, logK := sk126LogKCertificate, logChi := chi39LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (8388577/8388530) } }, logDArg := sk126LogDArgCertificate }

private noncomputable def leaf1350InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf1350LocalValidity :
    LeafFacts leaf1350Box leaf1350Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1350Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4194312/4194265) }) = true
      norm_num [leaf1350Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1350CertificateValid :
    WideCertificateValid leaf1350Box leaf1350Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk126ValidityFacts chi39ValidityFacts
    leaf1350LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1350CoverageChecked :
    coverageCheck (innerAD leaf1350Box) leaf1350InnerLog = true := by
  rfl'

private theorem leaf1350InnerLogValid :
    leaf1350InnerLog.Valid 8 (innerAD leaf1350Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf1350CoverageChecked

private noncomputable def leaf1350InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629175/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1350InputLogOnePlusV_eq :
    leaf1350InputLogOnePlusV = outerEnclosure 24
      (leaf1350Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1350RoundedFacts : LeafRoundedFacts 8
    leaf1350Certificate.logOnePlusV leaf1350InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1350InputLogOnePlusV_eq }

private noncomputable def leaf1350Inputs : Inputs :=
  inputsOfCaches globalInput sk126RoundedInputs
    chi39InputQChi innerPair6Input
    leaf1350InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1350LowerChecked :
    lowerCheck 24 leaf1350Box leaf1350Inputs = true := by
  rfl'

private theorem leaf1350CoversExact : CoversExact 8
    leaf1350Box leaf1350Certificate leaf1350InnerLog leaf1350Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk126RoundedFacts chi39RoundedFacts
    innerPair6RoundedFacts leaf1350RoundedFacts (by rfl)

private theorem leaf1350FlatSound : Sound leaf1350Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1350CertificateValid
    leaf1350InnerLogValid leaf1350CoversExact leaf1350LowerChecked

private noncomputable def leaf1351Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (3/64), chiHi := (7/128) }

private noncomputable def leaf1351Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217839/134217728) }, vSqrt := { lower := (65529/65536), upper := (33554496/33554089) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (153058067/134217728) }, upper := { exponent := 0, mantissa := (2391/2048) } }, logOuter := sk123LogOuterCertificate, logK := sk123LogKCertificate, logChi := chi96LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (67108585/67108178) } }, logDArg := sk123LogDArgCertificate }

private noncomputable def leaf1351InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf1351LocalValidity :
    LeafFacts leaf1351Box leaf1351Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1351Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (33554496/33554089) }) = true
      norm_num [leaf1351Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1351CertificateValid :
    WideCertificateValid leaf1351Box leaf1351Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk123ValidityFacts chi96ValidityFacts
    leaf1351LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1351CoverageChecked :
    coverageCheck (innerAD leaf1351Box) leaf1351InnerLog = true := by
  rfl'

private theorem leaf1351InnerLogValid :
    leaf1351InnerLog.Valid 8 (innerAD leaf1351Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf1351CoverageChecked

private noncomputable def leaf1351InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814591/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1351InputLogOnePlusV_eq :
    leaf1351InputLogOnePlusV = outerEnclosure 24
      (leaf1351Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1351RoundedFacts : LeafRoundedFacts 8
    leaf1351Certificate.logOnePlusV leaf1351InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1351InputLogOnePlusV_eq }

private noncomputable def leaf1351Inputs : Inputs :=
  inputsOfCaches globalInput sk123RoundedInputs
    chi96InputQChi innerPair2Input
    leaf1351InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1351LowerChecked :
    lowerCheck 24 leaf1351Box leaf1351Inputs = true := by
  rfl'

private theorem leaf1351CoversExact : CoversExact 8
    leaf1351Box leaf1351Certificate leaf1351InnerLog leaf1351Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk123RoundedFacts chi96RoundedFacts
    innerPair2RoundedFacts leaf1351RoundedFacts (by rfl)

private theorem leaf1351FlatSound : Sound leaf1351Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1351CertificateValid
    leaf1351InnerLogValid leaf1351CoversExact leaf1351LowerChecked

private noncomputable def leaf1352Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (3/64), chiHi := (7/128) }

private noncomputable def leaf1352Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217841/134217728) }, vSqrt := { lower := (65529/65536), upper := (5592416/5592347) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (153451257/134217728) }, upper := { exponent := 0, mantissa := (1199/1024) } }, logOuter := sk124LogOuterCertificate, logK := sk124LogKCertificate, logChi := chi96LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (11184763/11184694) } }, logDArg := sk124LogDArgCertificate }

private noncomputable def leaf1352InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf1352LocalValidity :
    LeafFacts leaf1352Box leaf1352Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1352Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (5592416/5592347) }) = true
      norm_num [leaf1352Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1352CertificateValid :
    WideCertificateValid leaf1352Box leaf1352Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk124ValidityFacts chi96ValidityFacts
    leaf1352LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1352CoverageChecked :
    coverageCheck (innerAD leaf1352Box) leaf1352InnerLog = true := by
  rfl'

private theorem leaf1352InnerLogValid :
    leaf1352InnerLog.Valid 8 (innerAD leaf1352Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf1352CoverageChecked

private noncomputable def leaf1352InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (90853/131072) }

set_option maxRecDepth 1000000 in
private theorem leaf1352InputLogOnePlusV_eq :
    leaf1352InputLogOnePlusV = outerEnclosure 24
      (leaf1352Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1352RoundedFacts : LeafRoundedFacts 8
    leaf1352Certificate.logOnePlusV leaf1352InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1352InputLogOnePlusV_eq }

private noncomputable def leaf1352Inputs : Inputs :=
  inputsOfCaches globalInput sk124RoundedInputs
    chi96InputQChi innerPair2Input
    leaf1352InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1352LowerChecked :
    lowerCheck 24 leaf1352Box leaf1352Inputs = true := by
  rfl'

private theorem leaf1352CoversExact : CoversExact 8
    leaf1352Box leaf1352Certificate leaf1352InnerLog leaf1352Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk124RoundedFacts chi96RoundedFacts
    innerPair2RoundedFacts leaf1352RoundedFacts (by rfl)

private theorem leaf1352FlatSound : Sound leaf1352Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1352CertificateValid
    leaf1352InnerLogValid leaf1352CoversExact leaf1352LowerChecked

private noncomputable def leaf1353Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (7/128), chiHi := (1/16) }

private noncomputable def leaf1353Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217841/134217728) }, vSqrt := { lower := (65529/65536), upper := (1398104/1398085) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (156203601/134217728) }, upper := { exponent := 0, mantissa := (305/256) } }, logOuter := sk123LogOuterCertificate, logK := sk123LogKCertificate, logChi := chi97LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (2796189/2796170) } }, logDArg := sk123LogDArgCertificate }

private noncomputable def leaf1353InnerLog : WideLogData :=
  innerPair3Data

set_option maxRecDepth 1000000 in
private theorem leaf1353LocalValidity :
    LeafFacts leaf1353Box leaf1353Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1353Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (1398104/1398085) }) = true
      norm_num [leaf1353Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1353CertificateValid :
    WideCertificateValid leaf1353Box leaf1353Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk123ValidityFacts chi97ValidityFacts
    leaf1353LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1353CoverageChecked :
    coverageCheck (innerAD leaf1353Box) leaf1353InnerLog = true := by
  rfl'

private theorem leaf1353InnerLogValid :
    leaf1353InnerLog.Valid 8 (innerAD leaf1353Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint5PositiveFacts.valid leaf1353CoverageChecked

private noncomputable def leaf1353InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629195/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1353InputLogOnePlusV_eq :
    leaf1353InputLogOnePlusV = outerEnclosure 24
      (leaf1353Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1353RoundedFacts : LeafRoundedFacts 8
    leaf1353Certificate.logOnePlusV leaf1353InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1353InputLogOnePlusV_eq }

private noncomputable def leaf1353Inputs : Inputs :=
  inputsOfCaches globalInput sk123RoundedInputs
    chi97InputQChi innerPair3Input
    leaf1353InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1353LowerChecked :
    lowerCheck 24 leaf1353Box leaf1353Inputs = true := by
  rfl'

private theorem leaf1353CoversExact : CoversExact 8
    leaf1353Box leaf1353Certificate leaf1353InnerLog leaf1353Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk123RoundedFacts chi97RoundedFacts
    innerPair3RoundedFacts leaf1353RoundedFacts (by rfl)

private theorem leaf1353FlatSound : Sound leaf1353Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1353CertificateValid
    leaf1353InnerLogValid leaf1353CoversExact leaf1353LowerChecked

private noncomputable def leaf1354Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (7/128), chiHi := (1/16) }

private noncomputable def leaf1354Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217843/134217728) }, vSqrt := { lower := (65529/65536), upper := (2097156/2097127) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (156662323/134217728) }, upper := { exponent := 0, mantissa := (153/128) } }, logOuter := sk124LogOuterCertificate, logK := sk124LogKCertificate, logChi := chi97LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (4194283/4194254) } }, logDArg := sk124LogDArgCertificate }

private noncomputable def leaf1354InnerLog : WideLogData :=
  innerPair3Data

set_option maxRecDepth 1000000 in
private theorem leaf1354LocalValidity :
    LeafFacts leaf1354Box leaf1354Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1354Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (2097156/2097127) }) = true
      norm_num [leaf1354Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1354CertificateValid :
    WideCertificateValid leaf1354Box leaf1354Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk124ValidityFacts chi97ValidityFacts
    leaf1354LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1354CoverageChecked :
    coverageCheck (innerAD leaf1354Box) leaf1354InnerLog = true := by
  rfl'

private theorem leaf1354InnerLogValid :
    leaf1354InnerLog.Valid 8 (innerAD leaf1354Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint5PositiveFacts.valid leaf1354CoverageChecked

private noncomputable def leaf1354InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629197/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1354InputLogOnePlusV_eq :
    leaf1354InputLogOnePlusV = outerEnclosure 24
      (leaf1354Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1354RoundedFacts : LeafRoundedFacts 8
    leaf1354Certificate.logOnePlusV leaf1354InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1354InputLogOnePlusV_eq }

private noncomputable def leaf1354Inputs : Inputs :=
  inputsOfCaches globalInput sk124RoundedInputs
    chi97InputQChi innerPair3Input
    leaf1354InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1354LowerChecked :
    lowerCheck 24 leaf1354Box leaf1354Inputs = true := by
  rfl'

private theorem leaf1354CoversExact : CoversExact 8
    leaf1354Box leaf1354Certificate leaf1354InnerLog leaf1354Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk124RoundedFacts chi97RoundedFacts
    innerPair3RoundedFacts leaf1354RoundedFacts (by rfl)

private theorem leaf1354FlatSound : Sound leaf1354Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1354CertificateValid
    leaf1354InnerLogValid leaf1354CoversExact leaf1354LowerChecked

private noncomputable def leaf1355Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (3/64), chiHi := (7/128) }

private noncomputable def leaf1355Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217843/134217728) }, vSqrt := { lower := (65529/65536), upper := (33554496/33554075) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (153844447/134217728) }, upper := { exponent := 0, mantissa := (2405/2048) } }, logOuter := sk125LogOuterCertificate, logK := sk125LogKCertificate, logChi := chi96LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (67108571/67108150) } }, logDArg := sk125LogDArgCertificate }

private noncomputable def leaf1355InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf1355LocalValidity :
    LeafFacts leaf1355Box leaf1355Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1355Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (33554496/33554075) }) = true
      norm_num [leaf1355Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1355CertificateValid :
    WideCertificateValid leaf1355Box leaf1355Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk125ValidityFacts chi96ValidityFacts
    leaf1355LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1355CoverageChecked :
    coverageCheck (innerAD leaf1355Box) leaf1355InnerLog = true := by
  rfl'

private theorem leaf1355InnerLogValid :
    leaf1355InnerLog.Valid 8 (innerAD leaf1355Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf1355CoverageChecked

private noncomputable def leaf1355InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814593/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1355InputLogOnePlusV_eq :
    leaf1355InputLogOnePlusV = outerEnclosure 24
      (leaf1355Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1355RoundedFacts : LeafRoundedFacts 8
    leaf1355Certificate.logOnePlusV leaf1355InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1355InputLogOnePlusV_eq }

private noncomputable def leaf1355Inputs : Inputs :=
  inputsOfCaches globalInput sk125RoundedInputs
    chi96InputQChi innerPair2Input
    leaf1355InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1355LowerChecked :
    lowerCheck 24 leaf1355Box leaf1355Inputs = true := by
  rfl'

private theorem leaf1355CoversExact : CoversExact 8
    leaf1355Box leaf1355Certificate leaf1355InnerLog leaf1355Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk125RoundedFacts chi96RoundedFacts
    innerPair2RoundedFacts leaf1355RoundedFacts (by rfl)

private theorem leaf1355FlatSound : Sound leaf1355Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1355CertificateValid
    leaf1355InnerLogValid leaf1355CoversExact leaf1355LowerChecked

private noncomputable def leaf1356Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (3/64), chiHi := (7/128) }

private noncomputable def leaf1356Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217845/134217728) }, vSqrt := { lower := (65529/65536), upper := (8388624/8388517) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (154237637/134217728) }, upper := { exponent := 0, mantissa := (603/512) } }, logOuter := sk126LogOuterCertificate, logK := sk126LogKCertificate, logChi := chi96LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (16777141/16777034) } }, logDArg := sk126LogDArgCertificate }

private noncomputable def leaf1356InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf1356LocalValidity :
    LeafFacts leaf1356Box leaf1356Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1356Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8388624/8388517) }) = true
      norm_num [leaf1356Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1356CertificateValid :
    WideCertificateValid leaf1356Box leaf1356Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk126ValidityFacts chi96ValidityFacts
    leaf1356LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1356CoverageChecked :
    coverageCheck (innerAD leaf1356Box) leaf1356InnerLog = true := by
  rfl'

private theorem leaf1356InnerLogValid :
    leaf1356InnerLog.Valid 8 (innerAD leaf1356Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf1356CoverageChecked

private noncomputable def leaf1356InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907297/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1356InputLogOnePlusV_eq :
    leaf1356InputLogOnePlusV = outerEnclosure 24
      (leaf1356Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1356RoundedFacts : LeafRoundedFacts 8
    leaf1356Certificate.logOnePlusV leaf1356InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1356InputLogOnePlusV_eq }

private noncomputable def leaf1356Inputs : Inputs :=
  inputsOfCaches globalInput sk126RoundedInputs
    chi96InputQChi innerPair2Input
    leaf1356InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1356LowerChecked :
    lowerCheck 24 leaf1356Box leaf1356Inputs = true := by
  rfl'

private theorem leaf1356CoversExact : CoversExact 8
    leaf1356Box leaf1356Certificate leaf1356InnerLog leaf1356Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk126RoundedFacts chi96RoundedFacts
    innerPair2RoundedFacts leaf1356RoundedFacts (by rfl)

private theorem leaf1356FlatSound : Sound leaf1356Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1356CertificateValid
    leaf1356InnerLogValid leaf1356CoversExact leaf1356LowerChecked

private noncomputable def leaf1357Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (7/128), chiHi := (1/16) }

private noncomputable def leaf1357Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217845/134217728) }, vSqrt := { lower := (65529/65536), upper := (4194312/4194253) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (157121045/134217728) }, upper := { exponent := 0, mantissa := (307/256) } }, logOuter := sk125LogOuterCertificate, logK := sk125LogKCertificate, logChi := chi97LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (8388565/8388506) } }, logDArg := sk125LogDArgCertificate }

private noncomputable def leaf1357InnerLog : WideLogData :=
  innerPair3Data

set_option maxRecDepth 1000000 in
private theorem leaf1357LocalValidity :
    LeafFacts leaf1357Box leaf1357Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1357Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4194312/4194253) }) = true
      norm_num [leaf1357Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1357CertificateValid :
    WideCertificateValid leaf1357Box leaf1357Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk125ValidityFacts chi97ValidityFacts
    leaf1357LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1357CoverageChecked :
    coverageCheck (innerAD leaf1357Box) leaf1357InnerLog = true := by
  rfl'

private theorem leaf1357InnerLogValid :
    leaf1357InnerLog.Valid 8 (innerAD leaf1357Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint5PositiveFacts.valid leaf1357CoverageChecked

private noncomputable def leaf1357InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629199/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1357InputLogOnePlusV_eq :
    leaf1357InputLogOnePlusV = outerEnclosure 24
      (leaf1357Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1357RoundedFacts : LeafRoundedFacts 8
    leaf1357Certificate.logOnePlusV leaf1357InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1357InputLogOnePlusV_eq }

private noncomputable def leaf1357Inputs : Inputs :=
  inputsOfCaches globalInput sk125RoundedInputs
    chi97InputQChi innerPair3Input
    leaf1357InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1357LowerChecked :
    lowerCheck 24 leaf1357Box leaf1357Inputs = true := by
  rfl'

private theorem leaf1357CoversExact : CoversExact 8
    leaf1357Box leaf1357Certificate leaf1357InnerLog leaf1357Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk125RoundedFacts chi97RoundedFacts
    innerPair3RoundedFacts leaf1357RoundedFacts (by rfl)

private theorem leaf1357FlatSound : Sound leaf1357Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1357CertificateValid
    leaf1357InnerLogValid leaf1357CoversExact leaf1357LowerChecked

private noncomputable def leaf1358Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (7/128), chiHi := (1/16) }

private noncomputable def leaf1358Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217847/134217728) }, vSqrt := { lower := (65529/65536), upper := (349526/349521) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (157579767/134217728) }, upper := { exponent := 0, mantissa := (77/64) } }, logOuter := sk126LogOuterCertificate, logK := sk126LogKCertificate, logChi := chi97LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (699047/699042) } }, logDArg := sk126LogDArgCertificate }

private noncomputable def leaf1358InnerLog : WideLogData :=
  innerPair3Data

set_option maxRecDepth 1000000 in
private theorem leaf1358LocalValidity :
    LeafFacts leaf1358Box leaf1358Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1358Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (349526/349521) }) = true
      norm_num [leaf1358Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1358CertificateValid :
    WideCertificateValid leaf1358Box leaf1358Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk126ValidityFacts chi97ValidityFacts
    leaf1358LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1358CoverageChecked :
    coverageCheck (innerAD leaf1358Box) leaf1358InnerLog = true := by
  rfl'

private theorem leaf1358InnerLogValid :
    leaf1358InnerLog.Valid 8 (innerAD leaf1358Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint5PositiveFacts.valid leaf1358CoverageChecked

private noncomputable def leaf1358InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629201/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1358InputLogOnePlusV_eq :
    leaf1358InputLogOnePlusV = outerEnclosure 24
      (leaf1358Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1358RoundedFacts : LeafRoundedFacts 8
    leaf1358Certificate.logOnePlusV leaf1358InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1358InputLogOnePlusV_eq }

private noncomputable def leaf1358Inputs : Inputs :=
  inputsOfCaches globalInput sk126RoundedInputs
    chi97InputQChi innerPair3Input
    leaf1358InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1358LowerChecked :
    lowerCheck 24 leaf1358Box leaf1358Inputs = true := by
  rfl'

private theorem leaf1358CoversExact : CoversExact 8
    leaf1358Box leaf1358Certificate leaf1358InnerLog leaf1358Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk126RoundedFacts chi97RoundedFacts
    innerPair3RoundedFacts leaf1358RoundedFacts (by rfl)

private theorem leaf1358FlatSound : Sound leaf1358Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1358CertificateValid
    leaf1358InnerLogValid leaf1358CoversExact leaf1358LowerChecked

private noncomputable def leaf1359Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (0), chiHi := (1/128) }

private noncomputable def leaf1359Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108919/67108864) }, vSqrt := { lower := (65529/65536), upper := (1290560/1290553) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := -1, mantissa := (67076043/33554432) }, upper := { exponent := 0, mantissa := (1051/1024) } }, logOuter := sk127LogOuterCertificate, logK := sk127LogKCertificate, logChi := chi137LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (2581113/2581106) } }, logDArg := sk127LogDArgCertificate }

private noncomputable def leaf1359InnerLog : WideLogData :=
  innerPair1Data

set_option maxRecDepth 1000000 in
private theorem leaf1359LocalValidity :
    LeafFacts leaf1359Box leaf1359Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1359Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (1290560/1290553) }) = true
      norm_num [leaf1359Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1359CertificateValid :
    WideCertificateValid leaf1359Box leaf1359Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk127ValidityFacts chi137ValidityFacts
    leaf1359LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1359CoverageChecked :
    coverageCheck (innerAD leaf1359Box) leaf1359InnerLog = true := by
  rfl'

private theorem leaf1359InnerLogValid :
    leaf1359InnerLog.Valid 8 (innerAD leaf1359Box) :=
  wideLogDataValid_of_cachedCheck endpoint0PositiveFacts
    endpoint2PositiveFacts.valid leaf1359CoverageChecked

private noncomputable def leaf1359InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814563/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1359InputLogOnePlusV_eq :
    leaf1359InputLogOnePlusV = outerEnclosure 24
      (leaf1359Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1359RoundedFacts : LeafRoundedFacts 8
    leaf1359Certificate.logOnePlusV leaf1359InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1359InputLogOnePlusV_eq }

private noncomputable def leaf1359Inputs : Inputs :=
  inputsOfCaches globalInput sk127RoundedInputs
    chi137InputQChi innerPair1Input
    leaf1359InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1359LowerChecked :
    lowerCheck 24 leaf1359Box leaf1359Inputs = true := by
  rfl'

private theorem leaf1359CoversExact : CoversExact 8
    leaf1359Box leaf1359Certificate leaf1359InnerLog leaf1359Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk127RoundedFacts chi137RoundedFacts
    innerPair1RoundedFacts leaf1359RoundedFacts (by rfl)

private theorem leaf1359FlatSound : Sound leaf1359Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1359CertificateValid
    leaf1359InnerLogValid leaf1359CoversExact leaf1359LowerChecked

private noncomputable def leaf1360Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (0), chiHi := (1/128) }

private noncomputable def leaf1360Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108921/67108864) }, vSqrt := { lower := (8191/8192), upper := (4194320/4194297) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := -1, mantissa := (67076041/33554432) }, upper := { exponent := 0, mantissa := (263/256) } }, logOuter := sk128LogOuterCertificate, logK := sk128LogKCertificate, logChi := chi137LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (8388617/8388594) } }, logDArg := sk128LogDArgCertificate }

private noncomputable def leaf1360InnerLog : WideLogData :=
  innerPair1Data

set_option maxRecDepth 1000000 in
private theorem leaf1360LocalValidity :
    LeafFacts leaf1360Box leaf1360Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1360Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4194320/4194297) }) = true
      norm_num [leaf1360Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1360CertificateValid :
    WideCertificateValid leaf1360Box leaf1360Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk128ValidityFacts chi137ValidityFacts
    leaf1360LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1360CoverageChecked :
    coverageCheck (innerAD leaf1360Box) leaf1360InnerLog = true := by
  rfl'

private theorem leaf1360InnerLogValid :
    leaf1360InnerLog.Valid 8 (innerAD leaf1360Box) :=
  wideLogDataValid_of_cachedCheck endpoint0PositiveFacts
    endpoint2PositiveFacts.valid leaf1360CoverageChecked

private noncomputable def leaf1360InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629127/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1360InputLogOnePlusV_eq :
    leaf1360InputLogOnePlusV = outerEnclosure 24
      (leaf1360Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1360RoundedFacts : LeafRoundedFacts 8
    leaf1360Certificate.logOnePlusV leaf1360InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1360InputLogOnePlusV_eq }

private noncomputable def leaf1360Inputs : Inputs :=
  inputsOfCaches globalInput sk128RoundedInputs
    chi137InputQChi innerPair1Input
    leaf1360InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1360LowerChecked :
    lowerCheck 24 leaf1360Box leaf1360Inputs = true := by
  rfl'

private theorem leaf1360CoversExact : CoversExact 8
    leaf1360Box leaf1360Certificate leaf1360InnerLog leaf1360Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk128RoundedFacts chi137RoundedFacts
    innerPair1RoundedFacts leaf1360RoundedFacts (by rfl)

private theorem leaf1360FlatSound : Sound leaf1360Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1360CertificateValid
    leaf1360InnerLogValid leaf1360CoversExact leaf1360LowerChecked

private noncomputable def leaf1361Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (1/128), chiHi := (1/64) }

private noncomputable def leaf1361Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108921/67108864) }, vSqrt := { lower := (65529/65536), upper := (8388640/8388581) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (68779873/67108864) }, upper := { exponent := 0, mantissa := (539/512) } }, logOuter := sk127LogOuterCertificate, logK := sk127LogKCertificate, logChi := chi138LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (16777221/16777162) } }, logDArg := sk127LogDArgCertificate }

private noncomputable def leaf1361InnerLog : WideLogData :=
  innerPair10Data

set_option maxRecDepth 1000000 in
private theorem leaf1361LocalValidity :
    LeafFacts leaf1361Box leaf1361Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1361Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8388640/8388581) }) = true
      norm_num [leaf1361Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1361CertificateValid :
    WideCertificateValid leaf1361Box leaf1361Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk127ValidityFacts chi138ValidityFacts
    leaf1361LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1361CoverageChecked :
    coverageCheck (innerAD leaf1361Box) leaf1361InnerLog = true := by
  rfl'

private theorem leaf1361InnerLogValid :
    leaf1361InnerLog.Valid 8 (innerAD leaf1361Box) :=
  wideLogDataValid_of_cachedCheck endpoint3PositiveFacts
    endpoint2PositiveFacts.valid leaf1361CoverageChecked

private noncomputable def leaf1361InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907285/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1361InputLogOnePlusV_eq :
    leaf1361InputLogOnePlusV = outerEnclosure 24
      (leaf1361Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1361RoundedFacts : LeafRoundedFacts 8
    leaf1361Certificate.logOnePlusV leaf1361InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1361InputLogOnePlusV_eq }

private noncomputable def leaf1361Inputs : Inputs :=
  inputsOfCaches globalInput sk127RoundedInputs
    chi138InputQChi innerPair10Input
    leaf1361InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1361LowerChecked :
    lowerCheck 24 leaf1361Box leaf1361Inputs = true := by
  rfl'

private theorem leaf1361CoversExact : CoversExact 8
    leaf1361Box leaf1361Certificate leaf1361InnerLog leaf1361Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk127RoundedFacts chi138RoundedFacts
    innerPair10RoundedFacts leaf1361RoundedFacts (by rfl)

private theorem leaf1361FlatSound : Sound leaf1361Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1361CertificateValid
    leaf1361InnerLogValid leaf1361CoversExact leaf1361LowerChecked

private noncomputable def leaf1362Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (1/128), chiHi := (1/64) }

private noncomputable def leaf1362Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108923/67108864) }, vSqrt := { lower := (8191/8192), upper := (419432/419429) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (68845403/67108864) }, upper := { exponent := 0, mantissa := (135/128) } }, logOuter := sk128LogOuterCertificate, logK := sk128LogKCertificate, logChi := chi138LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (838861/838858) } }, logDArg := sk128LogDArgCertificate }

private noncomputable def leaf1362InnerLog : WideLogData :=
  innerPair10Data

set_option maxRecDepth 1000000 in
private theorem leaf1362LocalValidity :
    LeafFacts leaf1362Box leaf1362Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1362Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (419432/419429) }) = true
      norm_num [leaf1362Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1362CertificateValid :
    WideCertificateValid leaf1362Box leaf1362Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk128ValidityFacts chi138ValidityFacts
    leaf1362LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1362CoverageChecked :
    coverageCheck (innerAD leaf1362Box) leaf1362InnerLog = true := by
  rfl'

private theorem leaf1362InnerLogValid :
    leaf1362InnerLog.Valid 8 (innerAD leaf1362Box) :=
  wideLogDataValid_of_cachedCheck endpoint3PositiveFacts
    endpoint2PositiveFacts.valid leaf1362CoverageChecked

private noncomputable def leaf1362InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629141/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1362InputLogOnePlusV_eq :
    leaf1362InputLogOnePlusV = outerEnclosure 24
      (leaf1362Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1362RoundedFacts : LeafRoundedFacts 8
    leaf1362Certificate.logOnePlusV leaf1362InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1362InputLogOnePlusV_eq }

private noncomputable def leaf1362Inputs : Inputs :=
  inputsOfCaches globalInput sk128RoundedInputs
    chi138InputQChi innerPair10Input
    leaf1362InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1362LowerChecked :
    lowerCheck 24 leaf1362Box leaf1362Inputs = true := by
  rfl'

private theorem leaf1362CoversExact : CoversExact 8
    leaf1362Box leaf1362Certificate leaf1362InnerLog leaf1362Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk128RoundedFacts chi138RoundedFacts
    innerPair10RoundedFacts leaf1362RoundedFacts (by rfl)

private theorem leaf1362FlatSound : Sound leaf1362Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1362CertificateValid
    leaf1362InnerLogValid leaf1362CoversExact leaf1362LowerChecked

private noncomputable def leaf1363Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (1/64), chiHi := (3/128) }

private noncomputable def leaf1363Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108923/67108864) }, vSqrt := { lower := (65529/65536), upper := (3355456/3355427) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (70483703/67108864) }, upper := { exponent := 0, mantissa := (1105/1024) } }, logOuter := sk127LogOuterCertificate, logK := sk127LogKCertificate, logChi := chi101LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (6710883/6710854) } }, logDArg := sk127LogDArgCertificate }

private noncomputable def leaf1363InnerLog : WideLogData :=
  innerPair434Data

set_option maxRecDepth 1000000 in
private theorem leaf1363LocalValidity :
    LeafFacts leaf1363Box leaf1363Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1363Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (3355456/3355427) }) = true
      norm_num [leaf1363Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1363CertificateValid :
    WideCertificateValid leaf1363Box leaf1363Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk127ValidityFacts chi101ValidityFacts
    leaf1363LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1363CoverageChecked :
    coverageCheck (innerAD leaf1363Box) leaf1363InnerLog = true := by
  rfl'

private theorem leaf1363InnerLogValid :
    leaf1363InnerLog.Valid 8 (innerAD leaf1363Box) :=
  wideLogDataValid_of_cachedCheck endpoint140PositiveFacts
    endpoint141PositiveFacts.valid leaf1363CoverageChecked

private noncomputable def leaf1363InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629153/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1363InputLogOnePlusV_eq :
    leaf1363InputLogOnePlusV = outerEnclosure 24
      (leaf1363Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1363RoundedFacts : LeafRoundedFacts 8
    leaf1363Certificate.logOnePlusV leaf1363InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1363InputLogOnePlusV_eq }

private noncomputable def leaf1363Inputs : Inputs :=
  inputsOfCaches globalInput sk127RoundedInputs
    chi101InputQChi innerPair434Input
    leaf1363InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1363LowerChecked :
    lowerCheck 24 leaf1363Box leaf1363Inputs = true := by
  rfl'

private theorem leaf1363CoversExact : CoversExact 8
    leaf1363Box leaf1363Certificate leaf1363InnerLog leaf1363Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk127RoundedFacts chi101RoundedFacts
    innerPair434RoundedFacts leaf1363RoundedFacts (by rfl)

private theorem leaf1363FlatSound : Sound leaf1363Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1363CertificateValid
    leaf1363InnerLogValid leaf1363CoversExact leaf1363LowerChecked

private noncomputable def leaf1364Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (1/64), chiHi := (5/256) }

private noncomputable def leaf1364Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217793/134217728) }, vSqrt := { lower := (8191/8192), upper := (8388640/8388573) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (141262353/134217728) }, upper := { exponent := 0, mantissa := (547/512) } }, logOuter := sk128LogOuterCertificate, logK := sk128LogKCertificate, logChi := chi141LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16777213/16777146) } }, logDArg := sk128LogDArgCertificate }

private noncomputable def leaf1364InnerLog : WideLogData :=
  innerPair9Data

set_option maxRecDepth 1000000 in
private theorem leaf1364LocalValidity :
    LeafFacts leaf1364Box leaf1364Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1364Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8388640/8388573) }) = true
      norm_num [leaf1364Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1364CertificateValid :
    WideCertificateValid leaf1364Box leaf1364Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk128ValidityFacts chi141ValidityFacts
    leaf1364LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1364CoverageChecked :
    coverageCheck (innerAD leaf1364Box) leaf1364InnerLog = true := by
  rfl'

private theorem leaf1364InnerLogValid :
    leaf1364InnerLog.Valid 8 (innerAD leaf1364Box) :=
  wideLogDataValid_of_cachedCheck endpoint3PositiveFacts
    endpoint1PositiveFacts.valid leaf1364CoverageChecked

private noncomputable def leaf1364InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907287/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1364InputLogOnePlusV_eq :
    leaf1364InputLogOnePlusV = outerEnclosure 24
      (leaf1364Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1364RoundedFacts : LeafRoundedFacts 8
    leaf1364Certificate.logOnePlusV leaf1364InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1364InputLogOnePlusV_eq }

private noncomputable def leaf1364Inputs : Inputs :=
  inputsOfCaches globalInput sk128RoundedInputs
    chi141InputQChi innerPair9Input
    leaf1364InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1364LowerChecked :
    lowerCheck 24 leaf1364Box leaf1364Inputs = true := by
  rfl'

private theorem leaf1364CoversExact : CoversExact 8
    leaf1364Box leaf1364Certificate leaf1364InnerLog leaf1364Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk128RoundedFacts chi141RoundedFacts
    innerPair9RoundedFacts leaf1364RoundedFacts (by rfl)

private theorem leaf1364FlatSound : Sound leaf1364Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1364CertificateValid
    leaf1364InnerLogValid leaf1364CoversExact leaf1364LowerChecked

private noncomputable def leaf1365Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (5/256), chiHi := (3/128) }

private noncomputable def leaf1365Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217795/134217728) }, vSqrt := { lower := (8191/8192), upper := (113360/113359) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (143031715/134217728) }, upper := { exponent := 0, mantissa := (277/256) } }, logOuter := sk128LogOuterCertificate, logK := sk128LogKCertificate, logChi := chi142LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (226719/226718) } }, logDArg := sk128LogDArgCertificate }

private noncomputable def leaf1365InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf1365LocalValidity :
    LeafFacts leaf1365Box leaf1365Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1365Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (113360/113359) }) = true
      norm_num [leaf1365Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1365CertificateValid :
    WideCertificateValid leaf1365Box leaf1365Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk128ValidityFacts chi142ValidityFacts
    leaf1365LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1365CoverageChecked :
    coverageCheck (innerAD leaf1365Box) leaf1365InnerLog = true := by
  rfl'

private theorem leaf1365InnerLogValid :
    leaf1365InnerLog.Valid 8 (innerAD leaf1365Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf1365CoverageChecked

private noncomputable def leaf1365InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629155/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1365InputLogOnePlusV_eq :
    leaf1365InputLogOnePlusV = outerEnclosure 24
      (leaf1365Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1365RoundedFacts : LeafRoundedFacts 8
    leaf1365Certificate.logOnePlusV leaf1365InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1365InputLogOnePlusV_eq }

private noncomputable def leaf1365Inputs : Inputs :=
  inputsOfCaches globalInput sk128RoundedInputs
    chi142InputQChi innerPair5Input
    leaf1365InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1365LowerChecked :
    lowerCheck 24 leaf1365Box leaf1365Inputs = true := by
  rfl'

private theorem leaf1365CoversExact : CoversExact 8
    leaf1365Box leaf1365Certificate leaf1365InnerLog leaf1365Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk128RoundedFacts chi142RoundedFacts
    innerPair5RoundedFacts leaf1365RoundedFacts (by rfl)

private theorem leaf1365FlatSound : Sound leaf1365Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1365CertificateValid
    leaf1365InnerLogValid leaf1365CoversExact leaf1365LowerChecked

private noncomputable def leaf1366Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (3/128), chiHi := (7/256) }

private noncomputable def leaf1366Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217795/134217728) }, vSqrt := { lower := (65529/65536), upper := (33554560/33554243) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (144407887/134217728) }, upper := { exponent := 0, mantissa := (2237/2048) } }, logOuter := sk127LogOuterCertificate, logK := sk127LogKCertificate, logChi := chi123LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (67108803/67108486) } }, logDArg := sk127LogDArgCertificate }

private noncomputable def leaf1366InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf1366LocalValidity :
    LeafFacts leaf1366Box leaf1366Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1366Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (33554560/33554243) }) = true
      norm_num [leaf1366Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1366CertificateValid :
    WideCertificateValid leaf1366Box leaf1366Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk127ValidityFacts chi123ValidityFacts
    leaf1366LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1366CoverageChecked :
    coverageCheck (innerAD leaf1366Box) leaf1366InnerLog = true := by
  rfl'

private theorem leaf1366InnerLogValid :
    leaf1366InnerLog.Valid 8 (innerAD leaf1366Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf1366CoverageChecked

private noncomputable def leaf1366InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453645/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf1366InputLogOnePlusV_eq :
    leaf1366InputLogOnePlusV = outerEnclosure 24
      (leaf1366Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1366RoundedFacts : LeafRoundedFacts 8
    leaf1366Certificate.logOnePlusV leaf1366InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1366InputLogOnePlusV_eq }

private noncomputable def leaf1366Inputs : Inputs :=
  inputsOfCaches globalInput sk127RoundedInputs
    chi123InputQChi innerPair5Input
    leaf1366InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1366LowerChecked :
    lowerCheck 24 leaf1366Box leaf1366Inputs = true := by
  rfl'

private theorem leaf1366CoversExact : CoversExact 8
    leaf1366Box leaf1366Certificate leaf1366InnerLog leaf1366Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk127RoundedFacts chi123RoundedFacts
    innerPair5RoundedFacts leaf1366RoundedFacts (by rfl)

private theorem leaf1366FlatSound : Sound leaf1366Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1366CertificateValid
    leaf1366InnerLogValid leaf1366CoversExact leaf1366LowerChecked

private noncomputable def leaf1367Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (7/256), chiHi := (1/32) }

private noncomputable def leaf1367Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217797/134217728) }, vSqrt := { lower := (65529/65536), upper := (4194320/4194277) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (146111717/134217728) }, upper := { exponent := 0, mantissa := (283/256) } }, logOuter := sk127LogOuterCertificate, logK := sk127LogKCertificate, logChi := chi124LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (8388597/8388554) } }, logDArg := sk127LogDArgCertificate }

private noncomputable def leaf1367InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf1367LocalValidity :
    LeafFacts leaf1367Box leaf1367Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1367Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4194320/4194277) }) = true
      norm_num [leaf1367Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1367CertificateValid :
    WideCertificateValid leaf1367Box leaf1367Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk127ValidityFacts chi124ValidityFacts
    leaf1367LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1367CoverageChecked :
    coverageCheck (innerAD leaf1367Box) leaf1367InnerLog = true := by
  rfl'

private theorem leaf1367InnerLogValid :
    leaf1367InnerLog.Valid 8 (innerAD leaf1367Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf1367CoverageChecked

private noncomputable def leaf1367InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629167/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1367InputLogOnePlusV_eq :
    leaf1367InputLogOnePlusV = outerEnclosure 24
      (leaf1367Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1367RoundedFacts : LeafRoundedFacts 8
    leaf1367Certificate.logOnePlusV leaf1367InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1367InputLogOnePlusV_eq }

private noncomputable def leaf1367Inputs : Inputs :=
  inputsOfCaches globalInput sk127RoundedInputs
    chi124InputQChi innerPair5Input
    leaf1367InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1367LowerChecked :
    lowerCheck 24 leaf1367Box leaf1367Inputs = true := by
  rfl'

private theorem leaf1367CoversExact : CoversExact 8
    leaf1367Box leaf1367Certificate leaf1367InnerLog leaf1367Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk127RoundedFacts chi124RoundedFacts
    innerPair5RoundedFacts leaf1367RoundedFacts (by rfl)

private theorem leaf1367FlatSound : Sound leaf1367Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1367CertificateValid
    leaf1367InnerLogValid leaf1367CoversExact leaf1367LowerChecked

private noncomputable def leaf1368Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (3/128), chiHi := (7/256) }

private noncomputable def leaf1368Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217797/134217728) }, vSqrt := { lower := (8191/8192), upper := (8388640/8388559) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (144801077/134217728) }, upper := { exponent := 0, mantissa := (561/512) } }, logOuter := sk128LogOuterCertificate, logK := sk128LogKCertificate, logChi := chi123LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16777199/16777118) } }, logDArg := sk128LogDArgCertificate }

private noncomputable def leaf1368InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf1368LocalValidity :
    LeafFacts leaf1368Box leaf1368Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1368Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8388640/8388559) }) = true
      norm_num [leaf1368Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1368CertificateValid :
    WideCertificateValid leaf1368Box leaf1368Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk128ValidityFacts chi123ValidityFacts
    leaf1368LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1368CoverageChecked :
    coverageCheck (innerAD leaf1368Box) leaf1368InnerLog = true := by
  rfl'

private theorem leaf1368InnerLogValid :
    leaf1368InnerLog.Valid 8 (innerAD leaf1368Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf1368CoverageChecked

private noncomputable def leaf1368InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814581/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1368InputLogOnePlusV_eq :
    leaf1368InputLogOnePlusV = outerEnclosure 24
      (leaf1368Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1368RoundedFacts : LeafRoundedFacts 8
    leaf1368Certificate.logOnePlusV leaf1368InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1368InputLogOnePlusV_eq }

private noncomputable def leaf1368Inputs : Inputs :=
  inputsOfCaches globalInput sk128RoundedInputs
    chi123InputQChi innerPair5Input
    leaf1368InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1368LowerChecked :
    lowerCheck 24 leaf1368Box leaf1368Inputs = true := by
  rfl'

private theorem leaf1368CoversExact : CoversExact 8
    leaf1368Box leaf1368Certificate leaf1368InnerLog leaf1368Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk128RoundedFacts chi123RoundedFacts
    innerPair5RoundedFacts leaf1368RoundedFacts (by rfl)

private theorem leaf1368FlatSound : Sound leaf1368Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1368CertificateValid
    leaf1368InnerLogValid leaf1368CoversExact leaf1368LowerChecked

private noncomputable def leaf1369Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (7/256), chiHi := (1/32) }

private noncomputable def leaf1369Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435581/268435456) }, vSqrt := { lower := (65529/65536), upper := (8388624/8388553) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (293173661/268435456) }, upper := { exponent := 0, mantissa := (567/512) } }, logOuter := sk129LogOuterCertificate, logK := sk129LogKCertificate, logChi := chi124LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (16777177/16777106) } }, logDArg := sk129LogDArgCertificate }

private noncomputable def leaf1369InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf1369LocalValidity :
    LeafFacts leaf1369Box leaf1369Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1369Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8388624/8388553) }) = true
      norm_num [leaf1369Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1369CertificateValid :
    WideCertificateValid leaf1369Box leaf1369Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk129ValidityFacts chi124ValidityFacts
    leaf1369LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1369CoverageChecked :
    coverageCheck (innerAD leaf1369Box) leaf1369InnerLog = true := by
  rfl'

private theorem leaf1369InnerLogValid :
    leaf1369InnerLog.Valid 8 (innerAD leaf1369Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf1369CoverageChecked

private noncomputable def leaf1369InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (363411/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf1369InputLogOnePlusV_eq :
    leaf1369InputLogOnePlusV = outerEnclosure 24
      (leaf1369Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1369RoundedFacts : LeafRoundedFacts 8
    leaf1369Certificate.logOnePlusV leaf1369InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1369InputLogOnePlusV_eq }

private noncomputable def leaf1369Inputs : Inputs :=
  inputsOfCaches globalInput sk129RoundedInputs
    chi124InputQChi innerPair5Input
    leaf1369InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1369LowerChecked :
    lowerCheck 24 leaf1369Box leaf1369Inputs = true := by
  rfl'

private theorem leaf1369CoversExact : CoversExact 8
    leaf1369Box leaf1369Certificate leaf1369InnerLog leaf1369Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk129RoundedFacts chi124RoundedFacts
    innerPair5RoundedFacts leaf1369RoundedFacts (by rfl)

private theorem leaf1369FlatSound : Sound leaf1369Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1369CertificateValid
    leaf1369InnerLogValid leaf1369CoversExact leaf1369LowerChecked

private noncomputable def leaf1370Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (7/256), chiHi := (1/32) }

private noncomputable def leaf1370Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435583/268435456) }, vSqrt := { lower := (8191/8192), upper := (349526/349523) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (293632383/268435456) }, upper := { exponent := 0, mantissa := (71/64) } }, logOuter := sk130LogOuterCertificate, logK := sk130LogKCertificate, logChi := chi124LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (699049/699046) } }, logDArg := sk130LogDArgCertificate }

private noncomputable def leaf1370InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf1370LocalValidity :
    LeafFacts leaf1370Box leaf1370Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1370Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (349526/349523) }) = true
      norm_num [leaf1370Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1370CertificateValid :
    WideCertificateValid leaf1370Box leaf1370Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk130ValidityFacts chi124ValidityFacts
    leaf1370LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1370CoverageChecked :
    coverageCheck (innerAD leaf1370Box) leaf1370InnerLog = true := by
  rfl'

private theorem leaf1370InnerLogValid :
    leaf1370InnerLog.Valid 8 (innerAD leaf1370Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf1370CoverageChecked

private noncomputable def leaf1370InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629153/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1370InputLogOnePlusV_eq :
    leaf1370InputLogOnePlusV = outerEnclosure 24
      (leaf1370Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1370RoundedFacts : LeafRoundedFacts 8
    leaf1370Certificate.logOnePlusV leaf1370InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1370InputLogOnePlusV_eq }

private noncomputable def leaf1370Inputs : Inputs :=
  inputsOfCaches globalInput sk130RoundedInputs
    chi124InputQChi innerPair5Input
    leaf1370InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1370LowerChecked :
    lowerCheck 24 leaf1370Box leaf1370Inputs = true := by
  rfl'

private theorem leaf1370CoversExact : CoversExact 8
    leaf1370Box leaf1370Certificate leaf1370InnerLog leaf1370Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk130RoundedFacts chi124RoundedFacts
    innerPair5RoundedFacts leaf1370RoundedFacts (by rfl)

private theorem leaf1370FlatSound : Sound leaf1370Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1370CertificateValid
    leaf1370InnerLogValid leaf1370CoversExact leaf1370LowerChecked

private noncomputable def leaf1371Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (1/32), chiHi := (9/256) }

private noncomputable def leaf1371Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435579/268435456) }, vSqrt := { lower := (65529/65536), upper := (67108992/67108387) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (295663879/268435456) }, upper := { exponent := 0, mantissa := (4573/4096) } }, logOuter := sk131LogOuterCertificate, logK := sk131LogKCertificate, logChi := chi139LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (134217379/134216774) } }, logDArg := sk131LogDArgCertificate }

private noncomputable def leaf1371InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf1371LocalValidity :
    LeafFacts leaf1371Box leaf1371Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1371Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (67108992/67108387) }) = true
      norm_num [leaf1371Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1371CertificateValid :
    WideCertificateValid leaf1371Box leaf1371Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk131ValidityFacts chi139ValidityFacts
    leaf1371LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1371CoverageChecked :
    coverageCheck (innerAD leaf1371Box) leaf1371InnerLog = true := by
  rfl'

private theorem leaf1371InnerLogValid :
    leaf1371InnerLog.Valid 8 (innerAD leaf1371Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf1371CoverageChecked

private noncomputable def leaf1371InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907289/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1371InputLogOnePlusV_eq :
    leaf1371InputLogOnePlusV = outerEnclosure 24
      (leaf1371Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1371RoundedFacts : LeafRoundedFacts 8
    leaf1371Certificate.logOnePlusV leaf1371InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1371InputLogOnePlusV_eq }

private noncomputable def leaf1371Inputs : Inputs :=
  inputsOfCaches globalInput sk131RoundedInputs
    chi139InputQChi innerPair5Input
    leaf1371InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1371LowerChecked :
    lowerCheck 24 leaf1371Box leaf1371Inputs = true := by
  rfl'

private theorem leaf1371CoversExact : CoversExact 8
    leaf1371Box leaf1371Certificate leaf1371InnerLog leaf1371Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk131RoundedFacts chi139RoundedFacts
    innerPair5RoundedFacts leaf1371RoundedFacts (by rfl)

private theorem leaf1371FlatSound : Sound leaf1371Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1371CertificateValid
    leaf1371InnerLogValid leaf1371CoversExact leaf1371LowerChecked

private noncomputable def leaf1372Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (1/32), chiHi := (9/256) }

private noncomputable def leaf1372Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435581/268435456) }, vSqrt := { lower := (65529/65536), upper := (33554496/33554189) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (296188133/268435456) }, upper := { exponent := 0, mantissa := (2291/2048) } }, logOuter := sk132LogOuterCertificate, logK := sk132LogKCertificate, logChi := chi139LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (67108685/67108378) } }, logDArg := sk132LogDArgCertificate }

private noncomputable def leaf1372InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf1372LocalValidity :
    LeafFacts leaf1372Box leaf1372Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1372Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (33554496/33554189) }) = true
      norm_num [leaf1372Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1372CertificateValid :
    WideCertificateValid leaf1372Box leaf1372Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk132ValidityFacts chi139ValidityFacts
    leaf1372LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1372CoverageChecked :
    coverageCheck (innerAD leaf1372Box) leaf1372InnerLog = true := by
  rfl'

private theorem leaf1372InnerLogValid :
    leaf1372InnerLog.Valid 8 (innerAD leaf1372Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf1372CoverageChecked

private noncomputable def leaf1372InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629157/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1372InputLogOnePlusV_eq :
    leaf1372InputLogOnePlusV = outerEnclosure 24
      (leaf1372Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1372RoundedFacts : LeafRoundedFacts 8
    leaf1372Certificate.logOnePlusV leaf1372InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1372InputLogOnePlusV_eq }

private noncomputable def leaf1372Inputs : Inputs :=
  inputsOfCaches globalInput sk132RoundedInputs
    chi139InputQChi innerPair5Input
    leaf1372InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1372LowerChecked :
    lowerCheck 24 leaf1372Box leaf1372Inputs = true := by
  rfl'

private theorem leaf1372CoversExact : CoversExact 8
    leaf1372Box leaf1372Certificate leaf1372InnerLog leaf1372Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk132RoundedFacts chi139RoundedFacts
    innerPair5RoundedFacts leaf1372RoundedFacts (by rfl)

private theorem leaf1372FlatSound : Sound leaf1372Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1372CertificateValid
    leaf1372InnerLogValid leaf1372CoversExact leaf1372LowerChecked

private noncomputable def leaf1373Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (9/256), chiHi := (5/128) }

private noncomputable def leaf1373Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435581/268435456) }, vSqrt := { lower := (65529/65536), upper := (33554496/33554167) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (299071541/268435456) }, upper := { exponent := 0, mantissa := (2313/2048) } }, logOuter := sk131LogOuterCertificate, logK := sk131LogKCertificate, logChi := chi140LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (67108663/67108334) } }, logDArg := sk131LogDArgCertificate }

private noncomputable def leaf1373InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf1373LocalValidity :
    LeafFacts leaf1373Box leaf1373Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1373Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (33554496/33554167) }) = true
      norm_num [leaf1373Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1373CertificateValid :
    WideCertificateValid leaf1373Box leaf1373Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk131ValidityFacts chi140ValidityFacts
    leaf1373LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1373CoverageChecked :
    coverageCheck (innerAD leaf1373Box) leaf1373InnerLog = true := by
  rfl'

private theorem leaf1373InnerLogValid :
    leaf1373InnerLog.Valid 8 (innerAD leaf1373Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf1373CoverageChecked

private noncomputable def leaf1373InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629163/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1373InputLogOnePlusV_eq :
    leaf1373InputLogOnePlusV = outerEnclosure 24
      (leaf1373Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1373RoundedFacts : LeafRoundedFacts 8
    leaf1373Certificate.logOnePlusV leaf1373InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1373InputLogOnePlusV_eq }

private noncomputable def leaf1373Inputs : Inputs :=
  inputsOfCaches globalInput sk131RoundedInputs
    chi140InputQChi innerPair6Input
    leaf1373InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1373LowerChecked :
    lowerCheck 24 leaf1373Box leaf1373Inputs = true := by
  rfl'

private theorem leaf1373CoversExact : CoversExact 8
    leaf1373Box leaf1373Certificate leaf1373InnerLog leaf1373Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk131RoundedFacts chi140RoundedFacts
    innerPair6RoundedFacts leaf1373RoundedFacts (by rfl)

private theorem leaf1373FlatSound : Sound leaf1373Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1373CertificateValid
    leaf1373InnerLogValid leaf1373CoversExact leaf1373LowerChecked

private noncomputable def leaf1374Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (9/256), chiHi := (5/128) }

private noncomputable def leaf1374Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435583/268435456) }, vSqrt := { lower := (65529/65536), upper := (16777248/16777081) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (299661327/268435456) }, upper := { exponent := 0, mantissa := (1159/1024) } }, logOuter := sk132LogOuterCertificate, logK := sk132LogKCertificate, logChi := chi140LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (33554329/33554162) } }, logDArg := sk132LogDArgCertificate }

private noncomputable def leaf1374InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf1374LocalValidity :
    LeafFacts leaf1374Box leaf1374Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1374Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (16777248/16777081) }) = true
      norm_num [leaf1374Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1374CertificateValid :
    WideCertificateValid leaf1374Box leaf1374Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk132ValidityFacts chi140ValidityFacts
    leaf1374LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1374CoverageChecked :
    coverageCheck (innerAD leaf1374Box) leaf1374InnerLog = true := by
  rfl'

private theorem leaf1374InnerLogValid :
    leaf1374InnerLog.Valid 8 (innerAD leaf1374Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf1374CoverageChecked

private noncomputable def leaf1374InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907291/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1374InputLogOnePlusV_eq :
    leaf1374InputLogOnePlusV = outerEnclosure 24
      (leaf1374Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1374RoundedFacts : LeafRoundedFacts 8
    leaf1374Certificate.logOnePlusV leaf1374InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1374InputLogOnePlusV_eq }

private noncomputable def leaf1374Inputs : Inputs :=
  inputsOfCaches globalInput sk132RoundedInputs
    chi140InputQChi innerPair6Input
    leaf1374InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1374LowerChecked :
    lowerCheck 24 leaf1374Box leaf1374Inputs = true := by
  rfl'

private theorem leaf1374CoversExact : CoversExact 8
    leaf1374Box leaf1374Certificate leaf1374InnerLog leaf1374Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk132RoundedFacts chi140RoundedFacts
    innerPair6RoundedFacts leaf1374RoundedFacts (by rfl)

private theorem leaf1374FlatSound : Sound leaf1374Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1374CertificateValid
    leaf1374InnerLogValid leaf1374CoversExact leaf1374LowerChecked

private noncomputable def leaf1375Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (5/128), chiHi := (3/64) }

private noncomputable def leaf1375Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217845/134217728) }, vSqrt := { lower := (65529/65536), upper := (16777248/16777057) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (151223165/134217728) }, upper := { exponent := 0, mantissa := (1183/1024) } }, logOuter := sk131LogOuterCertificate, logK := sk131LogKCertificate, logChi := chi39LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (33554305/33554114) } }, logDArg := sk131LogDArgCertificate }

private noncomputable def leaf1375InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf1375LocalValidity :
    LeafFacts leaf1375Box leaf1375Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1375Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (16777248/16777057) }) = true
      norm_num [leaf1375Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1375CertificateValid :
    WideCertificateValid leaf1375Box leaf1375Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk131ValidityFacts chi39ValidityFacts
    leaf1375LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1375CoverageChecked :
    coverageCheck (innerAD leaf1375Box) leaf1375InnerLog = true := by
  rfl'

private theorem leaf1375InnerLogValid :
    leaf1375InnerLog.Valid 8 (innerAD leaf1375Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf1375CoverageChecked

private noncomputable def leaf1375InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453647/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf1375InputLogOnePlusV_eq :
    leaf1375InputLogOnePlusV = outerEnclosure 24
      (leaf1375Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1375RoundedFacts : LeafRoundedFacts 8
    leaf1375Certificate.logOnePlusV leaf1375InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1375InputLogOnePlusV_eq }

private noncomputable def leaf1375Inputs : Inputs :=
  inputsOfCaches globalInput sk131RoundedInputs
    chi39InputQChi innerPair2Input
    leaf1375InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1375LowerChecked :
    lowerCheck 24 leaf1375Box leaf1375Inputs = true := by
  rfl'

private theorem leaf1375CoversExact : CoversExact 8
    leaf1375Box leaf1375Certificate leaf1375InnerLog leaf1375Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk131RoundedFacts chi39RoundedFacts
    innerPair2RoundedFacts leaf1375RoundedFacts (by rfl)

private theorem leaf1375FlatSound : Sound leaf1375Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1375CertificateValid
    leaf1375InnerLogValid leaf1375CoversExact leaf1375LowerChecked

private noncomputable def leaf1376Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (5/128), chiHi := (3/64) }

private noncomputable def leaf1376Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217847/134217728) }, vSqrt := { lower := (65529/65536), upper := (8388624/8388527) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (151550823/134217728) }, upper := { exponent := 0, mantissa := (593/512) } }, logOuter := sk132LogOuterCertificate, logK := sk132LogKCertificate, logChi := chi39LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (16777151/16777054) } }, logDArg := sk132LogDArgCertificate }

private noncomputable def leaf1376InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf1376LocalValidity :
    LeafFacts leaf1376Box leaf1376Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1376Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8388624/8388527) }) = true
      norm_num [leaf1376Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1376CertificateValid :
    WideCertificateValid leaf1376Box leaf1376Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk132ValidityFacts chi39ValidityFacts
    leaf1376LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1376CoverageChecked :
    coverageCheck (innerAD leaf1376Box) leaf1376InnerLog = true := by
  rfl'

private theorem leaf1376InnerLogValid :
    leaf1376InnerLog.Valid 8 (innerAD leaf1376Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf1376CoverageChecked

private noncomputable def leaf1376InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814589/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1376InputLogOnePlusV_eq :
    leaf1376InputLogOnePlusV = outerEnclosure 24
      (leaf1376Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1376RoundedFacts : LeafRoundedFacts 8
    leaf1376Certificate.logOnePlusV leaf1376InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1376InputLogOnePlusV_eq }

private noncomputable def leaf1376Inputs : Inputs :=
  inputsOfCaches globalInput sk132RoundedInputs
    chi39InputQChi innerPair2Input
    leaf1376InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1376LowerChecked :
    lowerCheck 24 leaf1376Box leaf1376Inputs = true := by
  rfl'

private theorem leaf1376CoversExact : CoversExact 8
    leaf1376Box leaf1376Certificate leaf1376InnerLog leaf1376Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk132RoundedFacts chi39RoundedFacts
    innerPair2RoundedFacts leaf1376RoundedFacts (by rfl)

private theorem leaf1376FlatSound : Sound leaf1376Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1376CertificateValid
    leaf1376InnerLogValid leaf1376CoversExact leaf1376LowerChecked

private noncomputable def leaf1377Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (1/32), chiHi := (9/256) }

private noncomputable def leaf1377Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435583/268435456) }, vSqrt := { lower := (65529/65536), upper := (67108992/67108369) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (296712387/268435456) }, upper := { exponent := 0, mantissa := (4591/4096) } }, logOuter := sk129LogOuterCertificate, logK := sk129LogKCertificate, logChi := chi139LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (134217361/134216738) } }, logDArg := sk129LogDArgCertificate }

private noncomputable def leaf1377InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf1377LocalValidity :
    LeafFacts leaf1377Box leaf1377Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1377Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (67108992/67108369) }) = true
      norm_num [leaf1377Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1377CertificateValid :
    WideCertificateValid leaf1377Box leaf1377Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk129ValidityFacts chi139ValidityFacts
    leaf1377LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1377CoverageChecked :
    coverageCheck (innerAD leaf1377Box) leaf1377InnerLog = true := by
  rfl'

private theorem leaf1377InnerLogValid :
    leaf1377InnerLog.Valid 8 (innerAD leaf1377Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf1377CoverageChecked

private noncomputable def leaf1377InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629159/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1377InputLogOnePlusV_eq :
    leaf1377InputLogOnePlusV = outerEnclosure 24
      (leaf1377Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1377RoundedFacts : LeafRoundedFacts 8
    leaf1377Certificate.logOnePlusV leaf1377InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1377InputLogOnePlusV_eq }

private noncomputable def leaf1377Inputs : Inputs :=
  inputsOfCaches globalInput sk129RoundedInputs
    chi139InputQChi innerPair5Input
    leaf1377InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1377LowerChecked :
    lowerCheck 24 leaf1377Box leaf1377Inputs = true := by
  rfl'

private theorem leaf1377CoversExact : CoversExact 8
    leaf1377Box leaf1377Certificate leaf1377InnerLog leaf1377Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk129RoundedFacts chi139RoundedFacts
    innerPair5RoundedFacts leaf1377RoundedFacts (by rfl)

private theorem leaf1377FlatSound : Sound leaf1377Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1377CertificateValid
    leaf1377InnerLogValid leaf1377CoversExact leaf1377LowerChecked

private noncomputable def leaf1378Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (1/32), chiHi := (9/256) }

private noncomputable def leaf1378Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435585/268435456) }, vSqrt := { lower := (8191/8192), upper := (8388624/8388545) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (297236641/268435456) }, upper := { exponent := 0, mantissa := (575/512) } }, logOuter := sk130LogOuterCertificate, logK := sk130LogKCertificate, logChi := chi139LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16777169/16777090) } }, logDArg := sk130LogDArgCertificate }

private noncomputable def leaf1378InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf1378LocalValidity :
    LeafFacts leaf1378Box leaf1378Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1378Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8388624/8388545) }) = true
      norm_num [leaf1378Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1378CertificateValid :
    WideCertificateValid leaf1378Box leaf1378Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk130ValidityFacts chi139ValidityFacts
    leaf1378LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1378CoverageChecked :
    coverageCheck (innerAD leaf1378Box) leaf1378InnerLog = true := by
  rfl'

private theorem leaf1378InnerLogValid :
    leaf1378InnerLog.Valid 8 (innerAD leaf1378Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf1378CoverageChecked

private noncomputable def leaf1378InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453645/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf1378InputLogOnePlusV_eq :
    leaf1378InputLogOnePlusV = outerEnclosure 24
      (leaf1378Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1378RoundedFacts : LeafRoundedFacts 8
    leaf1378Certificate.logOnePlusV leaf1378InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1378InputLogOnePlusV_eq }

private noncomputable def leaf1378Inputs : Inputs :=
  inputsOfCaches globalInput sk130RoundedInputs
    chi139InputQChi innerPair5Input
    leaf1378InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1378LowerChecked :
    lowerCheck 24 leaf1378Box leaf1378Inputs = true := by
  rfl'

private theorem leaf1378CoversExact : CoversExact 8
    leaf1378Box leaf1378Certificate leaf1378InnerLog leaf1378Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk130RoundedFacts chi139RoundedFacts
    innerPair5RoundedFacts leaf1378RoundedFacts (by rfl)

private theorem leaf1378FlatSound : Sound leaf1378Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1378CertificateValid
    leaf1378InnerLogValid leaf1378CoversExact leaf1378LowerChecked

private noncomputable def leaf1379Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (9/256), chiHi := (5/128) }

private noncomputable def leaf1379Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435585/268435456) }, vSqrt := { lower := (65529/65536), upper := (11184832/11184719) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (300251113/268435456) }, upper := { exponent := 0, mantissa := (2323/2048) } }, logOuter := sk129LogOuterCertificate, logK := sk129LogKCertificate, logChi := chi140LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (22369551/22369438) } }, logDArg := sk129LogDArgCertificate }

private noncomputable def leaf1379InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf1379LocalValidity :
    LeafFacts leaf1379Box leaf1379Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1379Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (11184832/11184719) }) = true
      norm_num [leaf1379Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1379CertificateValid :
    WideCertificateValid leaf1379Box leaf1379Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk129ValidityFacts chi140ValidityFacts
    leaf1379LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1379CoverageChecked :
    coverageCheck (innerAD leaf1379Box) leaf1379InnerLog = true := by
  rfl'

private theorem leaf1379InnerLogValid :
    leaf1379InnerLog.Valid 8 (innerAD leaf1379Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf1379CoverageChecked

private noncomputable def leaf1379InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629165/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1379InputLogOnePlusV_eq :
    leaf1379InputLogOnePlusV = outerEnclosure 24
      (leaf1379Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1379RoundedFacts : LeafRoundedFacts 8
    leaf1379Certificate.logOnePlusV leaf1379InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1379InputLogOnePlusV_eq }

private noncomputable def leaf1379Inputs : Inputs :=
  inputsOfCaches globalInput sk129RoundedInputs
    chi140InputQChi innerPair6Input
    leaf1379InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1379LowerChecked :
    lowerCheck 24 leaf1379Box leaf1379Inputs = true := by
  rfl'

private theorem leaf1379CoversExact : CoversExact 8
    leaf1379Box leaf1379Certificate leaf1379InnerLog leaf1379Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk129RoundedFacts chi140RoundedFacts
    innerPair6RoundedFacts leaf1379RoundedFacts (by rfl)

private theorem leaf1379FlatSound : Sound leaf1379Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1379CertificateValid
    leaf1379InnerLogValid leaf1379CoversExact leaf1379LowerChecked

private noncomputable def leaf1380Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (9/256), chiHi := (5/128) }

private noncomputable def leaf1380Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435587/268435456) }, vSqrt := { lower := (8191/8192), upper := (4194312/4194269) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (300840899/268435456) }, upper := { exponent := 0, mantissa := (291/256) } }, logOuter := sk130LogOuterCertificate, logK := sk130LogKCertificate, logChi := chi140LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (8388581/8388538) } }, logDArg := sk130LogDArgCertificate }

private noncomputable def leaf1380InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf1380LocalValidity :
    LeafFacts leaf1380Box leaf1380Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1380Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4194312/4194269) }) = true
      norm_num [leaf1380Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1380CertificateValid :
    WideCertificateValid leaf1380Box leaf1380Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk130ValidityFacts chi140ValidityFacts
    leaf1380LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1380CoverageChecked :
    coverageCheck (innerAD leaf1380Box) leaf1380InnerLog = true := by
  rfl'

private theorem leaf1380InnerLogValid :
    leaf1380InnerLog.Valid 8 (innerAD leaf1380Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf1380CoverageChecked

private noncomputable def leaf1380InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629167/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1380InputLogOnePlusV_eq :
    leaf1380InputLogOnePlusV = outerEnclosure 24
      (leaf1380Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1380RoundedFacts : LeafRoundedFacts 8
    leaf1380Certificate.logOnePlusV leaf1380InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1380InputLogOnePlusV_eq }

private noncomputable def leaf1380Inputs : Inputs :=
  inputsOfCaches globalInput sk130RoundedInputs
    chi140InputQChi innerPair6Input
    leaf1380InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1380LowerChecked :
    lowerCheck 24 leaf1380Box leaf1380Inputs = true := by
  rfl'

private theorem leaf1380CoversExact : CoversExact 8
    leaf1380Box leaf1380Certificate leaf1380InnerLog leaf1380Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk130RoundedFacts chi140RoundedFacts
    innerPair6RoundedFacts leaf1380RoundedFacts (by rfl)

private theorem leaf1380FlatSound : Sound leaf1380Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1380CertificateValid
    leaf1380InnerLogValid leaf1380CoversExact leaf1380LowerChecked

private noncomputable def leaf1381Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (5/128), chiHi := (11/256) }

private noncomputable def leaf1381Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435587/268435456) }, vSqrt := { lower := (65529/65536), upper := (67108992/67108259) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (303789839/268435456) }, upper := { exponent := 0, mantissa := (4701/4096) } }, logOuter := sk129LogOuterCertificate, logK := sk129LogKCertificate, logChi := chi143LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (134217251/134216518) } }, logDArg := sk129LogDArgCertificate }

private noncomputable def leaf1381InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf1381LocalValidity :
    LeafFacts leaf1381Box leaf1381Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1381Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (67108992/67108259) }) = true
      norm_num [leaf1381Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1381CertificateValid :
    WideCertificateValid leaf1381Box leaf1381Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk129ValidityFacts chi143ValidityFacts
    leaf1381LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1381CoverageChecked :
    coverageCheck (innerAD leaf1381Box) leaf1381InnerLog = true := by
  rfl'

private theorem leaf1381InnerLogValid :
    leaf1381InnerLog.Valid 8 (innerAD leaf1381Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf1381CoverageChecked

private noncomputable def leaf1381InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907293/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1381InputLogOnePlusV_eq :
    leaf1381InputLogOnePlusV = outerEnclosure 24
      (leaf1381Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1381RoundedFacts : LeafRoundedFacts 8
    leaf1381Certificate.logOnePlusV leaf1381InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1381InputLogOnePlusV_eq }

private noncomputable def leaf1381Inputs : Inputs :=
  inputsOfCaches globalInput sk129RoundedInputs
    chi143InputQChi innerPair2Input
    leaf1381InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1381LowerChecked :
    lowerCheck 24 leaf1381Box leaf1381Inputs = true := by
  rfl'

private theorem leaf1381CoversExact : CoversExact 8
    leaf1381Box leaf1381Certificate leaf1381InnerLog leaf1381Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk129RoundedFacts chi143RoundedFacts
    innerPair2RoundedFacts leaf1381RoundedFacts (by rfl)

private theorem leaf1381FlatSound : Sound leaf1381Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1381CertificateValid
    leaf1381InnerLogValid leaf1381CoversExact leaf1381LowerChecked

private noncomputable def leaf1382Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (5/128), chiHi := (11/256) }

private noncomputable def leaf1382Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435589/268435456) }, vSqrt := { lower := (8191/8192), upper := (2796208/2796177) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (304445157/268435456) }, upper := { exponent := 0, mantissa := (589/512) } }, logOuter := sk130LogOuterCertificate, logK := sk130LogKCertificate, logChi := chi143LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (5592385/5592354) } }, logDArg := sk130LogDArgCertificate }

private noncomputable def leaf1382InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf1382LocalValidity :
    LeafFacts leaf1382Box leaf1382Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1382Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (2796208/2796177) }) = true
      norm_num [leaf1382Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1382CertificateValid :
    WideCertificateValid leaf1382Box leaf1382Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk130ValidityFacts chi143ValidityFacts
    leaf1382LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1382CoverageChecked :
    coverageCheck (innerAD leaf1382Box) leaf1382InnerLog = true := by
  rfl'

private theorem leaf1382InnerLogValid :
    leaf1382InnerLog.Valid 8 (innerAD leaf1382Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf1382CoverageChecked

private noncomputable def leaf1382InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814587/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1382InputLogOnePlusV_eq :
    leaf1382InputLogOnePlusV = outerEnclosure 24
      (leaf1382Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1382RoundedFacts : LeafRoundedFacts 8
    leaf1382Certificate.logOnePlusV leaf1382InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1382InputLogOnePlusV_eq }

private noncomputable def leaf1382Inputs : Inputs :=
  inputsOfCaches globalInput sk130RoundedInputs
    chi143InputQChi innerPair2Input
    leaf1382InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1382LowerChecked :
    lowerCheck 24 leaf1382Box leaf1382Inputs = true := by
  rfl'

private theorem leaf1382CoversExact : CoversExact 8
    leaf1382Box leaf1382Certificate leaf1382InnerLog leaf1382Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk130RoundedFacts chi143RoundedFacts
    innerPair2RoundedFacts leaf1382RoundedFacts (by rfl)

private theorem leaf1382FlatSound : Sound leaf1382Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1382CertificateValid
    leaf1382InnerLogValid leaf1382CoversExact leaf1382LowerChecked

private noncomputable def leaf1383Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (11/256), chiHi := (3/64) }

private noncomputable def leaf1383Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435589/268435456) }, vSqrt := { lower := (65529/65536), upper := (16777248/16777051) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (307328565/268435456) }, upper := { exponent := 0, mantissa := (1189/1024) } }, logOuter := sk129LogOuterCertificate, logK := sk129LogKCertificate, logChi := chi144LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (33554299/33554102) } }, logDArg := sk129LogDArgCertificate }

private noncomputable def leaf1383InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf1383LocalValidity :
    LeafFacts leaf1383Box leaf1383Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1383Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (16777248/16777051) }) = true
      norm_num [leaf1383Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1383CertificateValid :
    WideCertificateValid leaf1383Box leaf1383Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk129ValidityFacts chi144ValidityFacts
    leaf1383LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1383CoverageChecked :
    coverageCheck (innerAD leaf1383Box) leaf1383InnerLog = true := by
  rfl'

private theorem leaf1383InnerLogValid :
    leaf1383InnerLog.Valid 8 (innerAD leaf1383Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf1383CoverageChecked

private noncomputable def leaf1383InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629179/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1383InputLogOnePlusV_eq :
    leaf1383InputLogOnePlusV = outerEnclosure 24
      (leaf1383Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1383RoundedFacts : LeafRoundedFacts 8
    leaf1383Certificate.logOnePlusV leaf1383InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1383InputLogOnePlusV_eq }

private noncomputable def leaf1383Inputs : Inputs :=
  inputsOfCaches globalInput sk129RoundedInputs
    chi144InputQChi innerPair2Input
    leaf1383InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1383LowerChecked :
    lowerCheck 24 leaf1383Box leaf1383Inputs = true := by
  rfl'

private theorem leaf1383CoversExact : CoversExact 8
    leaf1383Box leaf1383Certificate leaf1383InnerLog leaf1383Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk129RoundedFacts chi144RoundedFacts
    innerPair2RoundedFacts leaf1383RoundedFacts (by rfl)

private theorem leaf1383FlatSound : Sound leaf1383Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1383CertificateValid
    leaf1383InnerLogValid leaf1383CoversExact leaf1383LowerChecked

private noncomputable def leaf1384Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (11/256), chiHi := (3/64) }

private noncomputable def leaf1384Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435591/268435456) }, vSqrt := { lower := (8191/8192), upper := (2097156/2097131) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (308049415/268435456) }, upper := { exponent := 0, mantissa := (149/128) } }, logOuter := sk130LogOuterCertificate, logK := sk130LogKCertificate, logChi := chi144LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (4194287/4194262) } }, logDArg := sk130LogDArgCertificate }

private noncomputable def leaf1384InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf1384LocalValidity :
    LeafFacts leaf1384Box leaf1384Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1384Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (2097156/2097131) }) = true
      norm_num [leaf1384Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1384CertificateValid :
    WideCertificateValid leaf1384Box leaf1384Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk130ValidityFacts chi144ValidityFacts
    leaf1384LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1384CoverageChecked :
    coverageCheck (innerAD leaf1384Box) leaf1384InnerLog = true := by
  rfl'

private theorem leaf1384InnerLogValid :
    leaf1384InnerLog.Valid 8 (innerAD leaf1384Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf1384CoverageChecked

private noncomputable def leaf1384InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629181/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1384InputLogOnePlusV_eq :
    leaf1384InputLogOnePlusV = outerEnclosure 24
      (leaf1384Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1384RoundedFacts : LeafRoundedFacts 8
    leaf1384Certificate.logOnePlusV leaf1384InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1384InputLogOnePlusV_eq }

private noncomputable def leaf1384Inputs : Inputs :=
  inputsOfCaches globalInput sk130RoundedInputs
    chi144InputQChi innerPair2Input
    leaf1384InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1384LowerChecked :
    lowerCheck 24 leaf1384Box leaf1384Inputs = true := by
  rfl'

private theorem leaf1384CoversExact : CoversExact 8
    leaf1384Box leaf1384Certificate leaf1384InnerLog leaf1384Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk130RoundedFacts chi144RoundedFacts
    innerPair2RoundedFacts leaf1384RoundedFacts (by rfl)

private theorem leaf1384FlatSound : Sound leaf1384Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1384CertificateValid
    leaf1384InnerLogValid leaf1384CoversExact leaf1384LowerChecked

private noncomputable def leaf1385Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (3/64), chiHi := (7/128) }

private noncomputable def leaf1385Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217847/134217728) }, vSqrt := { lower := (65529/65536), upper := (11184832/11184687) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (154630827/134217728) }, upper := { exponent := 0, mantissa := (2419/2048) } }, logOuter := sk131LogOuterCertificate, logK := sk131LogKCertificate, logChi := chi96LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (22369519/22369374) } }, logDArg := sk131LogDArgCertificate }

private noncomputable def leaf1385InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf1385LocalValidity :
    LeafFacts leaf1385Box leaf1385Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1385Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (11184832/11184687) }) = true
      norm_num [leaf1385Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1385CertificateValid :
    WideCertificateValid leaf1385Box leaf1385Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk131ValidityFacts chi96ValidityFacts
    leaf1385LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1385CoverageChecked :
    coverageCheck (innerAD leaf1385Box) leaf1385InnerLog = true := by
  rfl'

private theorem leaf1385InnerLogValid :
    leaf1385InnerLog.Valid 8 (innerAD leaf1385Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf1385CoverageChecked

private noncomputable def leaf1385InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629189/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1385InputLogOnePlusV_eq :
    leaf1385InputLogOnePlusV = outerEnclosure 24
      (leaf1385Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1385RoundedFacts : LeafRoundedFacts 8
    leaf1385Certificate.logOnePlusV leaf1385InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1385InputLogOnePlusV_eq }

private noncomputable def leaf1385Inputs : Inputs :=
  inputsOfCaches globalInput sk131RoundedInputs
    chi96InputQChi innerPair2Input
    leaf1385InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1385LowerChecked :
    lowerCheck 24 leaf1385Box leaf1385Inputs = true := by
  rfl'

private theorem leaf1385CoversExact : CoversExact 8
    leaf1385Box leaf1385Certificate leaf1385InnerLog leaf1385Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk131RoundedFacts chi96RoundedFacts
    innerPair2RoundedFacts leaf1385RoundedFacts (by rfl)

private theorem leaf1385FlatSound : Sound leaf1385Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1385CertificateValid
    leaf1385InnerLogValid leaf1385CoversExact leaf1385LowerChecked

private noncomputable def leaf1386Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (3/64), chiHi := (7/128) }

private noncomputable def leaf1386Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217849/134217728) }, vSqrt := { lower := (65529/65536), upper := (16777248/16777027) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (155024017/134217728) }, upper := { exponent := 0, mantissa := (1213/1024) } }, logOuter := sk132LogOuterCertificate, logK := sk132LogKCertificate, logChi := chi96LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (33554275/33554054) } }, logDArg := sk132LogDArgCertificate }

private noncomputable def leaf1386InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf1386LocalValidity :
    LeafFacts leaf1386Box leaf1386Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1386Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (16777248/16777027) }) = true
      norm_num [leaf1386Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1386CertificateValid :
    WideCertificateValid leaf1386Box leaf1386Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk132ValidityFacts chi96ValidityFacts
    leaf1386LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1386CoverageChecked :
    coverageCheck (innerAD leaf1386Box) leaf1386InnerLog = true := by
  rfl'

private theorem leaf1386InnerLogValid :
    leaf1386InnerLog.Valid 8 (innerAD leaf1386Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf1386CoverageChecked

private noncomputable def leaf1386InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629191/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1386InputLogOnePlusV_eq :
    leaf1386InputLogOnePlusV = outerEnclosure 24
      (leaf1386Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1386RoundedFacts : LeafRoundedFacts 8
    leaf1386Certificate.logOnePlusV leaf1386InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1386InputLogOnePlusV_eq }

private noncomputable def leaf1386Inputs : Inputs :=
  inputsOfCaches globalInput sk132RoundedInputs
    chi96InputQChi innerPair2Input
    leaf1386InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1386LowerChecked :
    lowerCheck 24 leaf1386Box leaf1386Inputs = true := by
  rfl'

private theorem leaf1386CoversExact : CoversExact 8
    leaf1386Box leaf1386Certificate leaf1386InnerLog leaf1386Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk132RoundedFacts chi96RoundedFacts
    innerPair2RoundedFacts leaf1386RoundedFacts (by rfl)

private theorem leaf1386FlatSound : Sound leaf1386Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1386CertificateValid
    leaf1386InnerLogValid leaf1386CoversExact leaf1386LowerChecked

private noncomputable def leaf1387Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (7/128), chiHi := (1/16) }

private noncomputable def leaf1387Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217849/134217728) }, vSqrt := { lower := (65529/65536), upper := (4194312/4194251) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (158038489/134217728) }, upper := { exponent := 0, mantissa := (309/256) } }, logOuter := sk131LogOuterCertificate, logK := sk131LogKCertificate, logChi := chi97LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (8388563/8388502) } }, logDArg := sk131LogDArgCertificate }

private noncomputable def leaf1387InnerLog : WideLogData :=
  innerPair3Data

set_option maxRecDepth 1000000 in
private theorem leaf1387LocalValidity :
    LeafFacts leaf1387Box leaf1387Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1387Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4194312/4194251) }) = true
      norm_num [leaf1387Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1387CertificateValid :
    WideCertificateValid leaf1387Box leaf1387Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk131ValidityFacts chi97ValidityFacts
    leaf1387LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1387CoverageChecked :
    coverageCheck (innerAD leaf1387Box) leaf1387InnerLog = true := by
  rfl'

private theorem leaf1387InnerLogValid :
    leaf1387InnerLog.Valid 8 (innerAD leaf1387Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint5PositiveFacts.valid leaf1387CoverageChecked

private noncomputable def leaf1387InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629203/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1387InputLogOnePlusV_eq :
    leaf1387InputLogOnePlusV = outerEnclosure 24
      (leaf1387Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1387RoundedFacts : LeafRoundedFacts 8
    leaf1387Certificate.logOnePlusV leaf1387InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1387InputLogOnePlusV_eq }

private noncomputable def leaf1387Inputs : Inputs :=
  inputsOfCaches globalInput sk131RoundedInputs
    chi97InputQChi innerPair3Input
    leaf1387InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1387LowerChecked :
    lowerCheck 24 leaf1387Box leaf1387Inputs = true := by
  rfl'

private theorem leaf1387CoversExact : CoversExact 8
    leaf1387Box leaf1387Certificate leaf1387InnerLog leaf1387Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk131RoundedFacts chi97RoundedFacts
    innerPair3RoundedFacts leaf1387RoundedFacts (by rfl)

private theorem leaf1387FlatSound : Sound leaf1387Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1387CertificateValid
    leaf1387InnerLogValid leaf1387CoversExact leaf1387LowerChecked

private noncomputable def leaf1388Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (7/128), chiHi := (1/16) }

private noncomputable def leaf1388Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217851/134217728) }, vSqrt := { lower := (65529/65536), upper := (2097156/2097125) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (158497211/134217728) }, upper := { exponent := 0, mantissa := (155/128) } }, logOuter := sk132LogOuterCertificate, logK := sk132LogKCertificate, logChi := chi97LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (4194281/4194250) } }, logDArg := sk132LogDArgCertificate }

private noncomputable def leaf1388InnerLog : WideLogData :=
  innerPair3Data

set_option maxRecDepth 1000000 in
private theorem leaf1388LocalValidity :
    LeafFacts leaf1388Box leaf1388Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1388Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (2097156/2097125) }) = true
      norm_num [leaf1388Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1388CertificateValid :
    WideCertificateValid leaf1388Box leaf1388Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk132ValidityFacts chi97ValidityFacts
    leaf1388LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1388CoverageChecked :
    coverageCheck (innerAD leaf1388Box) leaf1388InnerLog = true := by
  rfl'

private theorem leaf1388InnerLogValid :
    leaf1388InnerLog.Valid 8 (innerAD leaf1388Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint5PositiveFacts.valid leaf1388CoverageChecked

private noncomputable def leaf1388InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629205/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1388InputLogOnePlusV_eq :
    leaf1388InputLogOnePlusV = outerEnclosure 24
      (leaf1388Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1388RoundedFacts : LeafRoundedFacts 8
    leaf1388Certificate.logOnePlusV leaf1388InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1388InputLogOnePlusV_eq }

private noncomputable def leaf1388Inputs : Inputs :=
  inputsOfCaches globalInput sk132RoundedInputs
    chi97InputQChi innerPair3Input
    leaf1388InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1388LowerChecked :
    lowerCheck 24 leaf1388Box leaf1388Inputs = true := by
  rfl'

private theorem leaf1388CoversExact : CoversExact 8
    leaf1388Box leaf1388Certificate leaf1388InnerLog leaf1388Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk132RoundedFacts chi97RoundedFacts
    innerPair3RoundedFacts leaf1388RoundedFacts (by rfl)

private theorem leaf1388FlatSound : Sound leaf1388Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1388CertificateValid
    leaf1388InnerLogValid leaf1388CoversExact leaf1388LowerChecked

private noncomputable def leaf1389Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (3/64), chiHi := (7/128) }

private noncomputable def leaf1389Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217851/134217728) }, vSqrt := { lower := (65529/65536), upper := (33554496/33554047) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (155417207/134217728) }, upper := { exponent := 0, mantissa := (2433/2048) } }, logOuter := sk129LogOuterCertificate, logK := sk129LogKCertificate, logChi := chi96LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (67108543/67108094) } }, logDArg := sk129LogDArgCertificate }

private noncomputable def leaf1389InnerLog : WideLogData :=
  innerPair3Data

set_option maxRecDepth 1000000 in
private theorem leaf1389LocalValidity :
    LeafFacts leaf1389Box leaf1389Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1389Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (33554496/33554047) }) = true
      norm_num [leaf1389Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1389CertificateValid :
    WideCertificateValid leaf1389Box leaf1389Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk129ValidityFacts chi96ValidityFacts
    leaf1389LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1389CoverageChecked :
    coverageCheck (innerAD leaf1389Box) leaf1389InnerLog = true := by
  rfl'

private theorem leaf1389InnerLogValid :
    leaf1389InnerLog.Valid 8 (innerAD leaf1389Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint5PositiveFacts.valid leaf1389CoverageChecked

private noncomputable def leaf1389InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629193/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1389InputLogOnePlusV_eq :
    leaf1389InputLogOnePlusV = outerEnclosure 24
      (leaf1389Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1389RoundedFacts : LeafRoundedFacts 8
    leaf1389Certificate.logOnePlusV leaf1389InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1389InputLogOnePlusV_eq }

private noncomputable def leaf1389Inputs : Inputs :=
  inputsOfCaches globalInput sk129RoundedInputs
    chi96InputQChi innerPair3Input
    leaf1389InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1389LowerChecked :
    lowerCheck 24 leaf1389Box leaf1389Inputs = true := by
  rfl'

private theorem leaf1389CoversExact : CoversExact 8
    leaf1389Box leaf1389Certificate leaf1389InnerLog leaf1389Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk129RoundedFacts chi96RoundedFacts
    innerPair3RoundedFacts leaf1389RoundedFacts (by rfl)

private theorem leaf1389FlatSound : Sound leaf1389Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1389CertificateValid
    leaf1389InnerLogValid leaf1389CoversExact leaf1389LowerChecked

private noncomputable def leaf1390Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (3/64), chiHi := (7/128) }

private noncomputable def leaf1390Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217853/134217728) }, vSqrt := { lower := (8191/8192), upper := (1398104/1398085) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (155810397/134217728) }, upper := { exponent := 0, mantissa := (305/256) } }, logOuter := sk130LogOuterCertificate, logK := sk130LogKCertificate, logChi := chi96LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (2796189/2796170) } }, logDArg := sk130LogDArgCertificate }

private noncomputable def leaf1390InnerLog : WideLogData :=
  innerPair3Data

set_option maxRecDepth 1000000 in
private theorem leaf1390LocalValidity :
    LeafFacts leaf1390Box leaf1390Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1390Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (1398104/1398085) }) = true
      norm_num [leaf1390Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1390CertificateValid :
    WideCertificateValid leaf1390Box leaf1390Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk130ValidityFacts chi96ValidityFacts
    leaf1390LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1390CoverageChecked :
    coverageCheck (innerAD leaf1390Box) leaf1390InnerLog = true := by
  rfl'

private theorem leaf1390InnerLogValid :
    leaf1390InnerLog.Valid 8 (innerAD leaf1390Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint5PositiveFacts.valid leaf1390CoverageChecked

private noncomputable def leaf1390InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629195/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1390InputLogOnePlusV_eq :
    leaf1390InputLogOnePlusV = outerEnclosure 24
      (leaf1390Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1390RoundedFacts : LeafRoundedFacts 8
    leaf1390Certificate.logOnePlusV leaf1390InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1390InputLogOnePlusV_eq }

private noncomputable def leaf1390Inputs : Inputs :=
  inputsOfCaches globalInput sk130RoundedInputs
    chi96InputQChi innerPair3Input
    leaf1390InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1390LowerChecked :
    lowerCheck 24 leaf1390Box leaf1390Inputs = true := by
  rfl'

private theorem leaf1390CoversExact : CoversExact 8
    leaf1390Box leaf1390Certificate leaf1390InnerLog leaf1390Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk130RoundedFacts chi96RoundedFacts
    innerPair3RoundedFacts leaf1390RoundedFacts (by rfl)

private theorem leaf1390FlatSound : Sound leaf1390Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1390CertificateValid
    leaf1390InnerLogValid leaf1390CoversExact leaf1390LowerChecked

private noncomputable def leaf1391Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (7/128), chiHi := (1/16) }

private noncomputable def leaf1391Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217853/134217728) }, vSqrt := { lower := (65529/65536), upper := (1398104/1398083) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (158955933/134217728) }, upper := { exponent := 0, mantissa := (311/256) } }, logOuter := sk129LogOuterCertificate, logK := sk129LogKCertificate, logChi := chi97LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (2796187/2796166) } }, logDArg := sk129LogDArgCertificate }

private noncomputable def leaf1391InnerLog : WideLogData :=
  innerPair32Data

set_option maxRecDepth 1000000 in
private theorem leaf1391LocalValidity :
    LeafFacts leaf1391Box leaf1391Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1391Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (1398104/1398083) }) = true
      norm_num [leaf1391Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1391CertificateValid :
    WideCertificateValid leaf1391Box leaf1391Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk129ValidityFacts chi97ValidityFacts
    leaf1391LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1391CoverageChecked :
    coverageCheck (innerAD leaf1391Box) leaf1391InnerLog = true := by
  rfl'

private theorem leaf1391InnerLogValid :
    leaf1391InnerLog.Valid 8 (innerAD leaf1391Box) :=
  wideLogDataValid_of_cachedCheck endpoint8PositiveFacts
    endpoint27PositiveFacts.valid leaf1391CoverageChecked

private noncomputable def leaf1391InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629207/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1391InputLogOnePlusV_eq :
    leaf1391InputLogOnePlusV = outerEnclosure 24
      (leaf1391Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1391RoundedFacts : LeafRoundedFacts 8
    leaf1391Certificate.logOnePlusV leaf1391InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1391InputLogOnePlusV_eq }

private noncomputable def leaf1391Inputs : Inputs :=
  inputsOfCaches globalInput sk129RoundedInputs
    chi97InputQChi innerPair32Input
    leaf1391InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1391LowerChecked :
    lowerCheck 24 leaf1391Box leaf1391Inputs = true := by
  rfl'

private theorem leaf1391CoversExact : CoversExact 8
    leaf1391Box leaf1391Certificate leaf1391InnerLog leaf1391Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk129RoundedFacts chi97RoundedFacts
    innerPair32RoundedFacts leaf1391RoundedFacts (by rfl)

private theorem leaf1391FlatSound : Sound leaf1391Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1391CertificateValid
    leaf1391InnerLogValid leaf1391CoversExact leaf1391LowerChecked

private noncomputable def leaf1392Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (7/128), chiHi := (15/256) }

private noncomputable def leaf1392Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435597/268435456) }, vSqrt := { lower := (8191/8192), upper := (8388624/8388503) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (318862189/268435456) }, upper := { exponent := 0, mantissa := (617/512) } }, logOuter := sk130LogOuterCertificate, logK := sk130LogKCertificate, logChi := chi145LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16777127/16777006) } }, logDArg := sk130LogDArgCertificate }

private noncomputable def leaf1392InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf1392LocalValidity :
    LeafFacts leaf1392Box leaf1392Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1392Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8388624/8388503) }) = true
      norm_num [leaf1392Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1392CertificateValid :
    WideCertificateValid leaf1392Box leaf1392Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk130ValidityFacts chi145ValidityFacts
    leaf1392LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1392CoverageChecked :
    coverageCheck (innerAD leaf1392Box) leaf1392InnerLog = true := by
  rfl'

private theorem leaf1392InnerLogValid :
    leaf1392InnerLog.Valid 8 (innerAD leaf1392Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf1392CoverageChecked

private noncomputable def leaf1392InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814601/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1392InputLogOnePlusV_eq :
    leaf1392InputLogOnePlusV = outerEnclosure 24
      (leaf1392Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1392RoundedFacts : LeafRoundedFacts 8
    leaf1392Certificate.logOnePlusV leaf1392InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1392InputLogOnePlusV_eq }

private noncomputable def leaf1392Inputs : Inputs :=
  inputsOfCaches globalInput sk130RoundedInputs
    chi145InputQChi innerPair12Input
    leaf1392InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1392LowerChecked :
    lowerCheck 24 leaf1392Box leaf1392Inputs = true := by
  rfl'

private theorem leaf1392CoversExact : CoversExact 8
    leaf1392Box leaf1392Certificate leaf1392InnerLog leaf1392Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk130RoundedFacts chi145RoundedFacts
    innerPair12RoundedFacts leaf1392RoundedFacts (by rfl)

private theorem leaf1392FlatSound : Sound leaf1392Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1392CertificateValid
    leaf1392InnerLogValid leaf1392CoversExact leaf1392LowerChecked

private noncomputable def leaf1393Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (15/256), chiHi := (1/16) }

private noncomputable def leaf1393Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435599/268435456) }, vSqrt := { lower := (8191/8192), upper := (524289/524281) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (322466447/268435456) }, upper := { exponent := 0, mantissa := (39/32) } }, logOuter := sk130LogOuterCertificate, logK := sk130LogKCertificate, logChi := chi146LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (524285/524281) } }, logDArg := sk130LogDArgCertificate }

private noncomputable def leaf1393InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf1393LocalValidity :
    LeafFacts leaf1393Box leaf1393Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1393Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (524289/524281) }) = true
      norm_num [leaf1393Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1393CertificateValid :
    WideCertificateValid leaf1393Box leaf1393Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk130ValidityFacts chi146ValidityFacts
    leaf1393LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1393CoverageChecked :
    coverageCheck (innerAD leaf1393Box) leaf1393InnerLog = true := by
  rfl'

private theorem leaf1393InnerLogValid :
    leaf1393InnerLog.Valid 8 (innerAD leaf1393Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf1393CoverageChecked

private noncomputable def leaf1393InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629209/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1393InputLogOnePlusV_eq :
    leaf1393InputLogOnePlusV = outerEnclosure 24
      (leaf1393Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1393RoundedFacts : LeafRoundedFacts 8
    leaf1393Certificate.logOnePlusV leaf1393InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1393InputLogOnePlusV_eq }

private noncomputable def leaf1393Inputs : Inputs :=
  inputsOfCaches globalInput sk130RoundedInputs
    chi146InputQChi innerPair12Input
    leaf1393InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1393LowerChecked :
    lowerCheck 24 leaf1393Box leaf1393Inputs = true := by
  rfl'

private theorem leaf1393CoversExact : CoversExact 8
    leaf1393Box leaf1393Certificate leaf1393InnerLog leaf1393Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk130RoundedFacts chi146RoundedFacts
    innerPair12RoundedFacts leaf1393RoundedFacts (by rfl)

private theorem leaf1393FlatSound : Sound leaf1393Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1393CertificateValid
    leaf1393InnerLogValid leaf1393CoversExact leaf1393LowerChecked

private noncomputable def component31Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (13/4), chiLo := (0), chiHi := (1/128) }

set_option maxRecDepth 1000000 in
private theorem component31Node0_sound : Sound component31Node0Box :=
  sound_of_literal_split component31Node0Box leaf1330Box leaf1331Box
    .k (25/8) (by rfl) (by rfl)
    leaf1330FlatSound leaf1331FlatSound

private noncomputable def component31Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (13/4), chiLo := (1/128), chiHi := (1/64) }

set_option maxRecDepth 1000000 in
private theorem component31Node1_sound : Sound component31Node1Box :=
  sound_of_literal_split component31Node1Box leaf1332Box leaf1333Box
    .k (25/8) (by rfl) (by rfl)
    leaf1332FlatSound leaf1333FlatSound

private noncomputable def component31Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (13/4), chiLo := (0), chiHi := (1/64) }

set_option maxRecDepth 1000000 in
private theorem component31Node2_sound : Sound component31Node2Box :=
  sound_of_literal_split component31Node2Box component31Node0Box component31Node1Box
    .chi (1/128) (by rfl) (by rfl)
    component31Node0_sound component31Node1_sound

private noncomputable def component31Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (13/4), chiLo := (1/64), chiHi := (3/128) }

set_option maxRecDepth 1000000 in
private theorem component31Node3_sound : Sound component31Node3Box :=
  sound_of_literal_split component31Node3Box leaf1334Box leaf1335Box
    .k (25/8) (by rfl) (by rfl)
    leaf1334FlatSound leaf1335FlatSound

private noncomputable def component31Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (3/128), chiHi := (1/32) }

set_option maxRecDepth 1000000 in
private theorem component31Node4_sound : Sound component31Node4Box :=
  sound_of_literal_split component31Node4Box leaf1336Box leaf1337Box
    .chi (7/256) (by rfl) (by rfl)
    leaf1336FlatSound leaf1337FlatSound

private noncomputable def component31Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (3/128), chiHi := (1/32) }

set_option maxRecDepth 1000000 in
private theorem component31Node5_sound : Sound component31Node5Box :=
  sound_of_literal_split component31Node5Box leaf1338Box leaf1339Box
    .chi (7/256) (by rfl) (by rfl)
    leaf1338FlatSound leaf1339FlatSound

private noncomputable def component31Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (13/4), chiLo := (3/128), chiHi := (1/32) }

set_option maxRecDepth 1000000 in
private theorem component31Node6_sound : Sound component31Node6Box :=
  sound_of_literal_split component31Node6Box component31Node4Box component31Node5Box
    .k (25/8) (by rfl) (by rfl)
    component31Node4_sound component31Node5_sound

private noncomputable def component31Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (13/4), chiLo := (1/64), chiHi := (1/32) }

set_option maxRecDepth 1000000 in
private theorem component31Node7_sound : Sound component31Node7Box :=
  sound_of_literal_split component31Node7Box component31Node3Box component31Node6Box
    .chi (3/128) (by rfl) (by rfl)
    component31Node3_sound component31Node6_sound

private noncomputable def component31Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (13/4), chiLo := (0), chiHi := (1/32) }

set_option maxRecDepth 1000000 in
private theorem component31Node8_sound : Sound component31Node8Box :=
  sound_of_literal_split component31Node8Box component31Node2Box component31Node7Box
    .chi (1/64) (by rfl) (by rfl)
    component31Node2_sound component31Node7_sound

private noncomputable def component31Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (9/256), chiHi := (5/128) }

set_option maxRecDepth 1000000 in
private theorem component31Node9_sound : Sound component31Node9Box :=
  sound_of_literal_split component31Node9Box leaf1341Box leaf1342Box
    .k (49/16) (by rfl) (by rfl)
    leaf1341FlatSound leaf1342FlatSound

private noncomputable def component31Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (1/32), chiHi := (5/128) }

set_option maxRecDepth 1000000 in
private theorem component31Node10_sound : Sound component31Node10Box :=
  sound_of_literal_split component31Node10Box leaf1340Box component31Node9Box
    .chi (9/256) (by rfl) (by rfl)
    leaf1340FlatSound component31Node9_sound

private noncomputable def component31Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (5/128), chiHi := (3/64) }

set_option maxRecDepth 1000000 in
private theorem component31Node11_sound : Sound component31Node11Box :=
  sound_of_literal_split component31Node11Box leaf1343Box leaf1344Box
    .k (49/16) (by rfl) (by rfl)
    leaf1343FlatSound leaf1344FlatSound

private noncomputable def component31Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (1/32), chiHi := (3/64) }

set_option maxRecDepth 1000000 in
private theorem component31Node12_sound : Sound component31Node12Box :=
  sound_of_literal_split component31Node12Box component31Node10Box component31Node11Box
    .chi (5/128) (by rfl) (by rfl)
    component31Node10_sound component31Node11_sound

private noncomputable def component31Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (1/32), chiHi := (9/256) }

set_option maxRecDepth 1000000 in
private theorem component31Node13_sound : Sound component31Node13Box :=
  sound_of_literal_split component31Node13Box leaf1345Box leaf1346Box
    .k (51/16) (by rfl) (by rfl)
    leaf1345FlatSound leaf1346FlatSound

private noncomputable def component31Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (9/256), chiHi := (5/128) }

set_option maxRecDepth 1000000 in
private theorem component31Node14_sound : Sound component31Node14Box :=
  sound_of_literal_split component31Node14Box leaf1347Box leaf1348Box
    .k (51/16) (by rfl) (by rfl)
    leaf1347FlatSound leaf1348FlatSound

private noncomputable def component31Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (1/32), chiHi := (5/128) }

set_option maxRecDepth 1000000 in
private theorem component31Node15_sound : Sound component31Node15Box :=
  sound_of_literal_split component31Node15Box component31Node13Box component31Node14Box
    .chi (9/256) (by rfl) (by rfl)
    component31Node13_sound component31Node14_sound

private noncomputable def component31Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (5/128), chiHi := (3/64) }

set_option maxRecDepth 1000000 in
private theorem component31Node16_sound : Sound component31Node16Box :=
  sound_of_literal_split component31Node16Box leaf1349Box leaf1350Box
    .k (51/16) (by rfl) (by rfl)
    leaf1349FlatSound leaf1350FlatSound

private noncomputable def component31Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (1/32), chiHi := (3/64) }

set_option maxRecDepth 1000000 in
private theorem component31Node17_sound : Sound component31Node17Box :=
  sound_of_literal_split component31Node17Box component31Node15Box component31Node16Box
    .chi (5/128) (by rfl) (by rfl)
    component31Node15_sound component31Node16_sound

private noncomputable def component31Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (13/4), chiLo := (1/32), chiHi := (3/64) }

set_option maxRecDepth 1000000 in
private theorem component31Node18_sound : Sound component31Node18Box :=
  sound_of_literal_split component31Node18Box component31Node12Box component31Node17Box
    .k (25/8) (by rfl) (by rfl)
    component31Node12_sound component31Node17_sound

private noncomputable def component31Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (3/64), chiHi := (7/128) }

set_option maxRecDepth 1000000 in
private theorem component31Node19_sound : Sound component31Node19Box :=
  sound_of_literal_split component31Node19Box leaf1351Box leaf1352Box
    .k (49/16) (by rfl) (by rfl)
    leaf1351FlatSound leaf1352FlatSound

private noncomputable def component31Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (7/128), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component31Node20_sound : Sound component31Node20Box :=
  sound_of_literal_split component31Node20Box leaf1353Box leaf1354Box
    .k (49/16) (by rfl) (by rfl)
    leaf1353FlatSound leaf1354FlatSound

private noncomputable def component31Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (3/64), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component31Node21_sound : Sound component31Node21Box :=
  sound_of_literal_split component31Node21Box component31Node19Box component31Node20Box
    .chi (7/128) (by rfl) (by rfl)
    component31Node19_sound component31Node20_sound

private noncomputable def component31Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (3/64), chiHi := (7/128) }

set_option maxRecDepth 1000000 in
private theorem component31Node22_sound : Sound component31Node22Box :=
  sound_of_literal_split component31Node22Box leaf1355Box leaf1356Box
    .k (51/16) (by rfl) (by rfl)
    leaf1355FlatSound leaf1356FlatSound

private noncomputable def component31Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (7/128), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component31Node23_sound : Sound component31Node23Box :=
  sound_of_literal_split component31Node23Box leaf1357Box leaf1358Box
    .k (51/16) (by rfl) (by rfl)
    leaf1357FlatSound leaf1358FlatSound

private noncomputable def component31Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (3/64), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component31Node24_sound : Sound component31Node24Box :=
  sound_of_literal_split component31Node24Box component31Node22Box component31Node23Box
    .chi (7/128) (by rfl) (by rfl)
    component31Node22_sound component31Node23_sound

private noncomputable def component31Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (13/4), chiLo := (3/64), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component31Node25_sound : Sound component31Node25Box :=
  sound_of_literal_split component31Node25Box component31Node21Box component31Node24Box
    .k (25/8) (by rfl) (by rfl)
    component31Node21_sound component31Node24_sound

private noncomputable def component31Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (13/4), chiLo := (1/32), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component31Node26_sound : Sound component31Node26Box :=
  sound_of_literal_split component31Node26Box component31Node18Box component31Node25Box
    .chi (3/64) (by rfl) (by rfl)
    component31Node18_sound component31Node25_sound

private noncomputable def component31Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (13/4), chiLo := (0), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component31Node27_sound : Sound component31Node27Box :=
  sound_of_literal_split component31Node27Box component31Node8Box component31Node26Box
    .chi (1/32) (by rfl) (by rfl)
    component31Node8_sound component31Node26_sound

private noncomputable def component31Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (7/2), chiLo := (0), chiHi := (1/128) }

set_option maxRecDepth 1000000 in
private theorem component31Node28_sound : Sound component31Node28Box :=
  sound_of_literal_split component31Node28Box leaf1359Box leaf1360Box
    .k (27/8) (by rfl) (by rfl)
    leaf1359FlatSound leaf1360FlatSound

private noncomputable def component31Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (7/2), chiLo := (1/128), chiHi := (1/64) }

set_option maxRecDepth 1000000 in
private theorem component31Node29_sound : Sound component31Node29Box :=
  sound_of_literal_split component31Node29Box leaf1361Box leaf1362Box
    .k (27/8) (by rfl) (by rfl)
    leaf1361FlatSound leaf1362FlatSound

private noncomputable def component31Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (7/2), chiLo := (0), chiHi := (1/64) }

set_option maxRecDepth 1000000 in
private theorem component31Node30_sound : Sound component31Node30Box :=
  sound_of_literal_split component31Node30Box component31Node28Box component31Node29Box
    .chi (1/128) (by rfl) (by rfl)
    component31Node28_sound component31Node29_sound

private noncomputable def component31Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (1/64), chiHi := (3/128) }

set_option maxRecDepth 1000000 in
private theorem component31Node31_sound : Sound component31Node31Box :=
  sound_of_literal_split component31Node31Box leaf1364Box leaf1365Box
    .chi (5/256) (by rfl) (by rfl)
    leaf1364FlatSound leaf1365FlatSound

private noncomputable def component31Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (7/2), chiLo := (1/64), chiHi := (3/128) }

set_option maxRecDepth 1000000 in
private theorem component31Node32_sound : Sound component31Node32Box :=
  sound_of_literal_split component31Node32Box leaf1363Box component31Node31Box
    .k (27/8) (by rfl) (by rfl)
    leaf1363FlatSound component31Node31_sound

private noncomputable def component31Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (3/128), chiHi := (1/32) }

set_option maxRecDepth 1000000 in
private theorem component31Node33_sound : Sound component31Node33Box :=
  sound_of_literal_split component31Node33Box leaf1366Box leaf1367Box
    .chi (7/256) (by rfl) (by rfl)
    leaf1366FlatSound leaf1367FlatSound

private noncomputable def component31Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (7/256), chiHi := (1/32) }

set_option maxRecDepth 1000000 in
private theorem component31Node34_sound : Sound component31Node34Box :=
  sound_of_literal_split component31Node34Box leaf1369Box leaf1370Box
    .k (55/16) (by rfl) (by rfl)
    leaf1369FlatSound leaf1370FlatSound

private noncomputable def component31Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (3/128), chiHi := (1/32) }

set_option maxRecDepth 1000000 in
private theorem component31Node35_sound : Sound component31Node35Box :=
  sound_of_literal_split component31Node35Box leaf1368Box component31Node34Box
    .chi (7/256) (by rfl) (by rfl)
    leaf1368FlatSound component31Node34_sound

private noncomputable def component31Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (7/2), chiLo := (3/128), chiHi := (1/32) }

set_option maxRecDepth 1000000 in
private theorem component31Node36_sound : Sound component31Node36Box :=
  sound_of_literal_split component31Node36Box component31Node33Box component31Node35Box
    .k (27/8) (by rfl) (by rfl)
    component31Node33_sound component31Node35_sound

private noncomputable def component31Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (7/2), chiLo := (1/64), chiHi := (1/32) }

set_option maxRecDepth 1000000 in
private theorem component31Node37_sound : Sound component31Node37Box :=
  sound_of_literal_split component31Node37Box component31Node32Box component31Node36Box
    .chi (3/128) (by rfl) (by rfl)
    component31Node32_sound component31Node36_sound

private noncomputable def component31Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (7/2), chiLo := (0), chiHi := (1/32) }

set_option maxRecDepth 1000000 in
private theorem component31Node38_sound : Sound component31Node38Box :=
  sound_of_literal_split component31Node38Box component31Node30Box component31Node37Box
    .chi (1/64) (by rfl) (by rfl)
    component31Node30_sound component31Node37_sound

private noncomputable def component31Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (1/32), chiHi := (9/256) }

set_option maxRecDepth 1000000 in
private theorem component31Node39_sound : Sound component31Node39Box :=
  sound_of_literal_split component31Node39Box leaf1371Box leaf1372Box
    .k (53/16) (by rfl) (by rfl)
    leaf1371FlatSound leaf1372FlatSound

private noncomputable def component31Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (9/256), chiHi := (5/128) }

set_option maxRecDepth 1000000 in
private theorem component31Node40_sound : Sound component31Node40Box :=
  sound_of_literal_split component31Node40Box leaf1373Box leaf1374Box
    .k (53/16) (by rfl) (by rfl)
    leaf1373FlatSound leaf1374FlatSound

private noncomputable def component31Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (1/32), chiHi := (5/128) }

set_option maxRecDepth 1000000 in
private theorem component31Node41_sound : Sound component31Node41Box :=
  sound_of_literal_split component31Node41Box component31Node39Box component31Node40Box
    .chi (9/256) (by rfl) (by rfl)
    component31Node39_sound component31Node40_sound

private noncomputable def component31Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (5/128), chiHi := (3/64) }

set_option maxRecDepth 1000000 in
private theorem component31Node42_sound : Sound component31Node42Box :=
  sound_of_literal_split component31Node42Box leaf1375Box leaf1376Box
    .k (53/16) (by rfl) (by rfl)
    leaf1375FlatSound leaf1376FlatSound

private noncomputable def component31Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (1/32), chiHi := (3/64) }

set_option maxRecDepth 1000000 in
private theorem component31Node43_sound : Sound component31Node43Box :=
  sound_of_literal_split component31Node43Box component31Node41Box component31Node42Box
    .chi (5/128) (by rfl) (by rfl)
    component31Node41_sound component31Node42_sound

private noncomputable def component31Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (1/32), chiHi := (9/256) }

set_option maxRecDepth 1000000 in
private theorem component31Node44_sound : Sound component31Node44Box :=
  sound_of_literal_split component31Node44Box leaf1377Box leaf1378Box
    .k (55/16) (by rfl) (by rfl)
    leaf1377FlatSound leaf1378FlatSound

private noncomputable def component31Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (9/256), chiHi := (5/128) }

set_option maxRecDepth 1000000 in
private theorem component31Node45_sound : Sound component31Node45Box :=
  sound_of_literal_split component31Node45Box leaf1379Box leaf1380Box
    .k (55/16) (by rfl) (by rfl)
    leaf1379FlatSound leaf1380FlatSound

private noncomputable def component31Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (1/32), chiHi := (5/128) }

set_option maxRecDepth 1000000 in
private theorem component31Node46_sound : Sound component31Node46Box :=
  sound_of_literal_split component31Node46Box component31Node44Box component31Node45Box
    .chi (9/256) (by rfl) (by rfl)
    component31Node44_sound component31Node45_sound

private noncomputable def component31Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (5/128), chiHi := (11/256) }

set_option maxRecDepth 1000000 in
private theorem component31Node47_sound : Sound component31Node47Box :=
  sound_of_literal_split component31Node47Box leaf1381Box leaf1382Box
    .k (55/16) (by rfl) (by rfl)
    leaf1381FlatSound leaf1382FlatSound

private noncomputable def component31Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (11/256), chiHi := (3/64) }

set_option maxRecDepth 1000000 in
private theorem component31Node48_sound : Sound component31Node48Box :=
  sound_of_literal_split component31Node48Box leaf1383Box leaf1384Box
    .k (55/16) (by rfl) (by rfl)
    leaf1383FlatSound leaf1384FlatSound

private noncomputable def component31Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (5/128), chiHi := (3/64) }

set_option maxRecDepth 1000000 in
private theorem component31Node49_sound : Sound component31Node49Box :=
  sound_of_literal_split component31Node49Box component31Node47Box component31Node48Box
    .chi (11/256) (by rfl) (by rfl)
    component31Node47_sound component31Node48_sound

private noncomputable def component31Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (1/32), chiHi := (3/64) }

set_option maxRecDepth 1000000 in
private theorem component31Node50_sound : Sound component31Node50Box :=
  sound_of_literal_split component31Node50Box component31Node46Box component31Node49Box
    .chi (5/128) (by rfl) (by rfl)
    component31Node46_sound component31Node49_sound

private noncomputable def component31Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (7/2), chiLo := (1/32), chiHi := (3/64) }

set_option maxRecDepth 1000000 in
private theorem component31Node51_sound : Sound component31Node51Box :=
  sound_of_literal_split component31Node51Box component31Node43Box component31Node50Box
    .k (27/8) (by rfl) (by rfl)
    component31Node43_sound component31Node50_sound

private noncomputable def component31Node52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (3/64), chiHi := (7/128) }

set_option maxRecDepth 1000000 in
private theorem component31Node52_sound : Sound component31Node52Box :=
  sound_of_literal_split component31Node52Box leaf1385Box leaf1386Box
    .k (53/16) (by rfl) (by rfl)
    leaf1385FlatSound leaf1386FlatSound

private noncomputable def component31Node53Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (7/128), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component31Node53_sound : Sound component31Node53Box :=
  sound_of_literal_split component31Node53Box leaf1387Box leaf1388Box
    .k (53/16) (by rfl) (by rfl)
    leaf1387FlatSound leaf1388FlatSound

private noncomputable def component31Node54Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (3/64), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component31Node54_sound : Sound component31Node54Box :=
  sound_of_literal_split component31Node54Box component31Node52Box component31Node53Box
    .chi (7/128) (by rfl) (by rfl)
    component31Node52_sound component31Node53_sound

private noncomputable def component31Node55Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (3/64), chiHi := (7/128) }

set_option maxRecDepth 1000000 in
private theorem component31Node55_sound : Sound component31Node55Box :=
  sound_of_literal_split component31Node55Box leaf1389Box leaf1390Box
    .k (55/16) (by rfl) (by rfl)
    leaf1389FlatSound leaf1390FlatSound

private noncomputable def component31Node56Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (7/128), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component31Node56_sound : Sound component31Node56Box :=
  sound_of_literal_split component31Node56Box leaf1392Box leaf1393Box
    .chi (15/256) (by rfl) (by rfl)
    leaf1392FlatSound leaf1393FlatSound

private noncomputable def component31Node57Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (7/128), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component31Node57_sound : Sound component31Node57Box :=
  sound_of_literal_split component31Node57Box leaf1391Box component31Node56Box
    .k (55/16) (by rfl) (by rfl)
    leaf1391FlatSound component31Node56_sound

private noncomputable def component31Node58Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (3/64), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component31Node58_sound : Sound component31Node58Box :=
  sound_of_literal_split component31Node58Box component31Node55Box component31Node57Box
    .chi (7/128) (by rfl) (by rfl)
    component31Node55_sound component31Node57_sound

private noncomputable def component31Node59Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (7/2), chiLo := (3/64), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component31Node59_sound : Sound component31Node59Box :=
  sound_of_literal_split component31Node59Box component31Node54Box component31Node58Box
    .k (27/8) (by rfl) (by rfl)
    component31Node54_sound component31Node58_sound

private noncomputable def component31Node60Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (7/2), chiLo := (1/32), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component31Node60_sound : Sound component31Node60Box :=
  sound_of_literal_split component31Node60Box component31Node51Box component31Node59Box
    .chi (3/64) (by rfl) (by rfl)
    component31Node51_sound component31Node59_sound

private noncomputable def component31Node61Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (7/2), chiLo := (0), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component31Node61_sound : Sound component31Node61Box :=
  sound_of_literal_split component31Node61Box component31Node38Box component31Node60Box
    .chi (1/32) (by rfl) (by rfl)
    component31Node38_sound component31Node60_sound

noncomputable def component31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (7/2), chiLo := (0), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
theorem component31_sound : Sound component31Box :=
  sound_of_literal_split component31Box component31Node27Box component31Node61Box
    .k (13/4) (by rfl) (by rfl)
    component31Node27_sound component31Node61_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
