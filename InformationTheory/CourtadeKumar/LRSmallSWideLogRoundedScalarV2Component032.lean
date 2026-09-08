import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch6
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheSKBatch1

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

private noncomputable def leaf1394Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (1/16), chiHi := (9/128) }

private noncomputable def leaf1394Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217843/134217728) }, vSqrt := { lower := (65529/65536), upper := (33554496/33553991) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (159349135/134217728) }, upper := { exponent := 0, mantissa := (2489/2048) } }, logOuter := sk123LogOuterCertificate, logK := sk123LogKCertificate, logChi := chi125LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (67108487/67107982) } }, logDArg := sk123LogDArgCertificate }

private noncomputable def leaf1394InnerLog : WideLogData :=
  innerPair3Data

set_option maxRecDepth 1000000 in
private theorem leaf1394LocalValidity :
    LeafFacts leaf1394Box leaf1394Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1394Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (33554496/33553991) }) = true
      norm_num [leaf1394Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1394CertificateValid :
    WideCertificateValid leaf1394Box leaf1394Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk123ValidityFacts chi125ValidityFacts
    leaf1394LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1394CoverageChecked :
    coverageCheck (innerAD leaf1394Box) leaf1394InnerLog = true := by
  rfl'

private theorem leaf1394InnerLogValid :
    leaf1394InnerLog.Valid 8 (innerAD leaf1394Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint5PositiveFacts.valid leaf1394CoverageChecked

private noncomputable def leaf1394InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629207/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1394InputLogOnePlusV_eq :
    leaf1394InputLogOnePlusV = outerEnclosure 24
      (leaf1394Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1394RoundedFacts : LeafRoundedFacts 8
    leaf1394Certificate.logOnePlusV leaf1394InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1394InputLogOnePlusV_eq }

private noncomputable def leaf1394Inputs : Inputs :=
  inputsOfCaches globalInput sk123RoundedInputs
    chi125InputQChi innerPair3Input
    leaf1394InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1394LowerChecked :
    lowerCheck 24 leaf1394Box leaf1394Inputs = true := by
  rfl'

private theorem leaf1394CoversExact : CoversExact 8
    leaf1394Box leaf1394Certificate leaf1394InnerLog leaf1394Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk123RoundedFacts chi125RoundedFacts
    innerPair3RoundedFacts leaf1394RoundedFacts (by rfl)

private theorem leaf1394FlatSound : Sound leaf1394Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1394CertificateValid
    leaf1394InnerLogValid leaf1394CoversExact leaf1394LowerChecked

private noncomputable def leaf1395Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (1/16), chiHi := (9/128) }

private noncomputable def leaf1395Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217845/134217728) }, vSqrt := { lower := (65529/65536), upper := (16777248/16776991) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (159873389/134217728) }, upper := { exponent := 0, mantissa := (1249/1024) } }, logOuter := sk124LogOuterCertificate, logK := sk124LogKCertificate, logChi := chi125LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (33554239/33553982) } }, logDArg := sk124LogDArgCertificate }

private noncomputable def leaf1395InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf1395LocalValidity :
    LeafFacts leaf1395Box leaf1395Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1395Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (16777248/16776991) }) = true
      norm_num [leaf1395Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1395CertificateValid :
    WideCertificateValid leaf1395Box leaf1395Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk124ValidityFacts chi125ValidityFacts
    leaf1395LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1395CoverageChecked :
    coverageCheck (innerAD leaf1395Box) leaf1395InnerLog = true := by
  rfl'

private theorem leaf1395InnerLogValid :
    leaf1395InnerLog.Valid 8 (innerAD leaf1395Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf1395CoverageChecked

private noncomputable def leaf1395InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629209/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1395InputLogOnePlusV_eq :
    leaf1395InputLogOnePlusV = outerEnclosure 24
      (leaf1395Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1395RoundedFacts : LeafRoundedFacts 8
    leaf1395Certificate.logOnePlusV leaf1395InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1395InputLogOnePlusV_eq }

private noncomputable def leaf1395Inputs : Inputs :=
  inputsOfCaches globalInput sk124RoundedInputs
    chi125InputQChi innerPair12Input
    leaf1395InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1395LowerChecked :
    lowerCheck 24 leaf1395Box leaf1395Inputs = true := by
  rfl'

private theorem leaf1395CoversExact : CoversExact 8
    leaf1395Box leaf1395Certificate leaf1395InnerLog leaf1395Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk124RoundedFacts chi125RoundedFacts
    innerPair12RoundedFacts leaf1395RoundedFacts (by rfl)

private theorem leaf1395FlatSound : Sound leaf1395Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1395CertificateValid
    leaf1395InnerLogValid leaf1395CoversExact leaf1395LowerChecked

private noncomputable def leaf1396Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (9/128), chiHi := (5/64) }

private noncomputable def leaf1396Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217845/134217728) }, vSqrt := { lower := (65529/65536), upper := (16777248/16776971) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (162494669/134217728) }, upper := { exponent := 0, mantissa := (1269/1024) } }, logOuter := sk123LogOuterCertificate, logK := sk123LogKCertificate, logChi := chi126LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (33554219/33553942) } }, logDArg := sk123LogDArgCertificate }

private noncomputable def leaf1396InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf1396LocalValidity :
    LeafFacts leaf1396Box leaf1396Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1396Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (16777248/16776971) }) = true
      norm_num [leaf1396Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1396CertificateValid :
    WideCertificateValid leaf1396Box leaf1396Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk123ValidityFacts chi126ValidityFacts
    leaf1396LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1396CoverageChecked :
    coverageCheck (innerAD leaf1396Box) leaf1396InnerLog = true := by
  rfl'

private theorem leaf1396InnerLogValid :
    leaf1396InnerLog.Valid 8 (innerAD leaf1396Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf1396CoverageChecked

private noncomputable def leaf1396InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629219/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1396InputLogOnePlusV_eq :
    leaf1396InputLogOnePlusV = outerEnclosure 24
      (leaf1396Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1396RoundedFacts : LeafRoundedFacts 8
    leaf1396Certificate.logOnePlusV leaf1396InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1396InputLogOnePlusV_eq }

private noncomputable def leaf1396Inputs : Inputs :=
  inputsOfCaches globalInput sk123RoundedInputs
    chi126InputQChi innerPair12Input
    leaf1396InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1396LowerChecked :
    lowerCheck 24 leaf1396Box leaf1396Inputs = true := by
  rfl'

private theorem leaf1396CoversExact : CoversExact 8
    leaf1396Box leaf1396Certificate leaf1396InnerLog leaf1396Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk123RoundedFacts chi126RoundedFacts
    innerPair12RoundedFacts leaf1396RoundedFacts (by rfl)

private theorem leaf1396FlatSound : Sound leaf1396Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1396CertificateValid
    leaf1396InnerLogValid leaf1396CoversExact leaf1396LowerChecked

private noncomputable def leaf1397Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (9/128), chiHi := (5/64) }

private noncomputable def leaf1397Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217847/134217728) }, vSqrt := { lower := (65529/65536), upper := (2796208/2796161) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (163084455/134217728) }, upper := { exponent := 0, mantissa := (637/512) } }, logOuter := sk124LogOuterCertificate, logK := sk124LogKCertificate, logChi := chi126LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (5592369/5592322) } }, logDArg := sk124LogDArgCertificate }

private noncomputable def leaf1397InnerLog : WideLogData :=
  innerPair435Data

set_option maxRecDepth 1000000 in
private theorem leaf1397LocalValidity :
    LeafFacts leaf1397Box leaf1397Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1397Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (2796208/2796161) }) = true
      norm_num [leaf1397Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1397CertificateValid :
    WideCertificateValid leaf1397Box leaf1397Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk124ValidityFacts chi126ValidityFacts
    leaf1397LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1397CoverageChecked :
    coverageCheck (innerAD leaf1397Box) leaf1397InnerLog = true := by
  rfl'

private theorem leaf1397InnerLogValid :
    leaf1397InnerLog.Valid 8 (innerAD leaf1397Box) :=
  wideLogDataValid_of_cachedCheck endpoint142PositiveFacts
    endpoint33PositiveFacts.valid leaf1397CoverageChecked

private noncomputable def leaf1397InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814611/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1397InputLogOnePlusV_eq :
    leaf1397InputLogOnePlusV = outerEnclosure 24
      (leaf1397Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1397RoundedFacts : LeafRoundedFacts 8
    leaf1397Certificate.logOnePlusV leaf1397InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1397InputLogOnePlusV_eq }

private noncomputable def leaf1397Inputs : Inputs :=
  inputsOfCaches globalInput sk124RoundedInputs
    chi126InputQChi innerPair435Input
    leaf1397InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1397LowerChecked :
    lowerCheck 24 leaf1397Box leaf1397Inputs = true := by
  rfl'

private theorem leaf1397CoversExact : CoversExact 8
    leaf1397Box leaf1397Certificate leaf1397InnerLog leaf1397Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk124RoundedFacts chi126RoundedFacts
    innerPair435RoundedFacts leaf1397RoundedFacts (by rfl)

private theorem leaf1397FlatSound : Sound leaf1397Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1397CertificateValid
    leaf1397InnerLogValid leaf1397CoversExact leaf1397LowerChecked

private noncomputable def leaf1398Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (1/16), chiHi := (9/128) }

private noncomputable def leaf1398Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217847/134217728) }, vSqrt := { lower := (65529/65536), upper := (33554496/33553973) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (160397643/134217728) }, upper := { exponent := 0, mantissa := (2507/2048) } }, logOuter := sk125LogOuterCertificate, logK := sk125LogKCertificate, logChi := chi125LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (67108469/67107946) } }, logDArg := sk125LogDArgCertificate }

private noncomputable def leaf1398InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf1398LocalValidity :
    LeafFacts leaf1398Box leaf1398Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1398Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (33554496/33553973) }) = true
      norm_num [leaf1398Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1398CertificateValid :
    WideCertificateValid leaf1398Box leaf1398Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk125ValidityFacts chi125ValidityFacts
    leaf1398LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1398CoverageChecked :
    coverageCheck (innerAD leaf1398Box) leaf1398InnerLog = true := by
  rfl'

private theorem leaf1398InnerLogValid :
    leaf1398InnerLog.Valid 8 (innerAD leaf1398Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf1398CoverageChecked

private noncomputable def leaf1398InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629211/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1398InputLogOnePlusV_eq :
    leaf1398InputLogOnePlusV = outerEnclosure 24
      (leaf1398Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1398RoundedFacts : LeafRoundedFacts 8
    leaf1398Certificate.logOnePlusV leaf1398InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1398InputLogOnePlusV_eq }

private noncomputable def leaf1398Inputs : Inputs :=
  inputsOfCaches globalInput sk125RoundedInputs
    chi125InputQChi innerPair12Input
    leaf1398InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1398LowerChecked :
    lowerCheck 24 leaf1398Box leaf1398Inputs = true := by
  rfl'

private theorem leaf1398CoversExact : CoversExact 8
    leaf1398Box leaf1398Certificate leaf1398InnerLog leaf1398Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk125RoundedFacts chi125RoundedFacts
    innerPair12RoundedFacts leaf1398RoundedFacts (by rfl)

private theorem leaf1398FlatSound : Sound leaf1398Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1398CertificateValid
    leaf1398InnerLogValid leaf1398CoversExact leaf1398LowerChecked

private noncomputable def leaf1399Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (1/16), chiHi := (9/128) }

private noncomputable def leaf1399Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217849/134217728) }, vSqrt := { lower := (65529/65536), upper := (8388624/8388491) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (160921897/134217728) }, upper := { exponent := 0, mantissa := (629/512) } }, logOuter := sk126LogOuterCertificate, logK := sk126LogKCertificate, logChi := chi125LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (16777115/16776982) } }, logDArg := sk126LogDArgCertificate }

private noncomputable def leaf1399InnerLog : WideLogData :=
  innerPair15Data

set_option maxRecDepth 1000000 in
private theorem leaf1399LocalValidity :
    LeafFacts leaf1399Box leaf1399Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1399Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8388624/8388491) }) = true
      norm_num [leaf1399Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1399CertificateValid :
    WideCertificateValid leaf1399Box leaf1399Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk126ValidityFacts chi125ValidityFacts
    leaf1399LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1399CoverageChecked :
    coverageCheck (innerAD leaf1399Box) leaf1399InnerLog = true := by
  rfl'

private theorem leaf1399InnerLogValid :
    leaf1399InnerLog.Valid 8 (innerAD leaf1399Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint116PositiveFacts.valid leaf1399CoverageChecked

private noncomputable def leaf1399InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814607/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1399InputLogOnePlusV_eq :
    leaf1399InputLogOnePlusV = outerEnclosure 24
      (leaf1399Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1399RoundedFacts : LeafRoundedFacts 8
    leaf1399Certificate.logOnePlusV leaf1399InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1399InputLogOnePlusV_eq }

private noncomputable def leaf1399Inputs : Inputs :=
  inputsOfCaches globalInput sk126RoundedInputs
    chi125InputQChi innerPair15Input
    leaf1399InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1399LowerChecked :
    lowerCheck 24 leaf1399Box leaf1399Inputs = true := by
  rfl'

private theorem leaf1399CoversExact : CoversExact 8
    leaf1399Box leaf1399Certificate leaf1399InnerLog leaf1399Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk126RoundedFacts chi125RoundedFacts
    innerPair15RoundedFacts leaf1399RoundedFacts (by rfl)

private theorem leaf1399FlatSound : Sound leaf1399Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1399CertificateValid
    leaf1399InnerLogValid leaf1399CoversExact leaf1399LowerChecked

private noncomputable def leaf1400Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (9/128), chiHi := (19/256) }

private noncomputable def leaf1400Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435595/268435456) }, vSqrt := { lower := (65529/65536), upper := (67108992/67107895) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (327381351/268435456) }, upper := { exponent := 0, mantissa := (5065/4096) } }, logOuter := sk125LogOuterCertificate, logK := sk125LogKCertificate, logChi := chi147LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (134216887/134215790) } }, logDArg := sk125LogDArgCertificate }

private noncomputable def leaf1400InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf1400LocalValidity :
    LeafFacts leaf1400Box leaf1400Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1400Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (67108992/67107895) }) = true
      norm_num [leaf1400Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1400CertificateValid :
    WideCertificateValid leaf1400Box leaf1400Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk125ValidityFacts chi147ValidityFacts
    leaf1400LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1400CoverageChecked :
    coverageCheck (innerAD leaf1400Box) leaf1400InnerLog = true := by
  rfl'

private theorem leaf1400InnerLogValid :
    leaf1400InnerLog.Valid 8 (innerAD leaf1400Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf1400CoverageChecked

private noncomputable def leaf1400InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814609/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1400InputLogOnePlusV_eq :
    leaf1400InputLogOnePlusV = outerEnclosure 24
      (leaf1400Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1400RoundedFacts : LeafRoundedFacts 8
    leaf1400Certificate.logOnePlusV leaf1400InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1400InputLogOnePlusV_eq }

private noncomputable def leaf1400Inputs : Inputs :=
  inputsOfCaches globalInput sk125RoundedInputs
    chi147InputQChi innerPair12Input
    leaf1400InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1400LowerChecked :
    lowerCheck 24 leaf1400Box leaf1400Inputs = true := by
  rfl'

private theorem leaf1400CoversExact : CoversExact 8
    leaf1400Box leaf1400Certificate leaf1400InnerLog leaf1400Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk125RoundedFacts chi147RoundedFacts
    innerPair12RoundedFacts leaf1400RoundedFacts (by rfl)

private theorem leaf1400FlatSound : Sound leaf1400Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1400CertificateValid
    leaf1400InnerLogValid leaf1400CoversExact leaf1400LowerChecked

private noncomputable def leaf1401Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (19/256), chiHi := (5/64) }

private noncomputable def leaf1401Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435597/268435456) }, vSqrt := { lower := (65529/65536), upper := (16777248/16776961) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (330657949/268435456) }, upper := { exponent := 0, mantissa := (1279/1024) } }, logOuter := sk125LogOuterCertificate, logK := sk125LogKCertificate, logChi := chi148LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (33554209/33553922) } }, logDArg := sk125LogDArgCertificate }

private noncomputable def leaf1401InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf1401LocalValidity :
    LeafFacts leaf1401Box leaf1401Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1401Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (16777248/16776961) }) = true
      norm_num [leaf1401Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1401CertificateValid :
    WideCertificateValid leaf1401Box leaf1401Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk125ValidityFacts chi148ValidityFacts
    leaf1401LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1401CoverageChecked :
    coverageCheck (innerAD leaf1401Box) leaf1401InnerLog = true := by
  rfl'

private theorem leaf1401InnerLogValid :
    leaf1401InnerLog.Valid 8 (innerAD leaf1401Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf1401CoverageChecked

private noncomputable def leaf1401InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453653/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf1401InputLogOnePlusV_eq :
    leaf1401InputLogOnePlusV = outerEnclosure 24
      (leaf1401Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1401RoundedFacts : LeafRoundedFacts 8
    leaf1401Certificate.logOnePlusV leaf1401InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1401InputLogOnePlusV_eq }

private noncomputable def leaf1401Inputs : Inputs :=
  inputsOfCaches globalInput sk125RoundedInputs
    chi148InputQChi innerPair12Input
    leaf1401InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1401LowerChecked :
    lowerCheck 24 leaf1401Box leaf1401Inputs = true := by
  rfl'

private theorem leaf1401CoversExact : CoversExact 8
    leaf1401Box leaf1401Certificate leaf1401InnerLog leaf1401Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk125RoundedFacts chi148RoundedFacts
    innerPair12RoundedFacts leaf1401RoundedFacts (by rfl)

private theorem leaf1401FlatSound : Sound leaf1401Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1401CertificateValid
    leaf1401InnerLogValid leaf1401CoversExact leaf1401LowerChecked

private noncomputable def leaf1402Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (9/128), chiHi := (19/256) }

private noncomputable def leaf1402Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435597/268435456) }, vSqrt := { lower := (65529/65536), upper := (5592416/5592323) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (328560925/268435456) }, upper := { exponent := 0, mantissa := (1271/1024) } }, logOuter := sk126LogOuterCertificate, logK := sk126LogKCertificate, logChi := chi147LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (11184739/11184646) } }, logDArg := sk126LogDArgCertificate }

private noncomputable def leaf1402InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf1402LocalValidity :
    LeafFacts leaf1402Box leaf1402Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1402Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (5592416/5592323) }) = true
      norm_num [leaf1402Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1402CertificateValid :
    WideCertificateValid leaf1402Box leaf1402Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk126ValidityFacts chi147ValidityFacts
    leaf1402LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1402CoverageChecked :
    coverageCheck (innerAD leaf1402Box) leaf1402InnerLog = true := by
  rfl'

private theorem leaf1402InnerLogValid :
    leaf1402InnerLog.Valid 8 (innerAD leaf1402Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf1402CoverageChecked

private noncomputable def leaf1402InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907305/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1402InputLogOnePlusV_eq :
    leaf1402InputLogOnePlusV = outerEnclosure 24
      (leaf1402Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1402RoundedFacts : LeafRoundedFacts 8
    leaf1402Certificate.logOnePlusV leaf1402InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1402InputLogOnePlusV_eq }

private noncomputable def leaf1402Inputs : Inputs :=
  inputsOfCaches globalInput sk126RoundedInputs
    chi147InputQChi innerPair12Input
    leaf1402InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1402LowerChecked :
    lowerCheck 24 leaf1402Box leaf1402Inputs = true := by
  rfl'

private theorem leaf1402CoversExact : CoversExact 8
    leaf1402Box leaf1402Certificate leaf1402InnerLog leaf1402Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk126RoundedFacts chi147RoundedFacts
    innerPair12RoundedFacts leaf1402RoundedFacts (by rfl)

private theorem leaf1402FlatSound : Sound leaf1402Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1402CertificateValid
    leaf1402InnerLogValid leaf1402CoversExact leaf1402LowerChecked

private noncomputable def leaf1403Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (19/256), chiHi := (5/64) }

private noncomputable def leaf1403Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435599/268435456) }, vSqrt := { lower := (65529/65536), upper := (4194312/4194239) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (331903055/268435456) }, upper := { exponent := 0, mantissa := (321/256) } }, logOuter := sk126LogOuterCertificate, logK := sk126LogKCertificate, logChi := chi148LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (8388551/8388478) } }, logDArg := sk126LogDArgCertificate }

private noncomputable def leaf1403InnerLog : WideLogData :=
  innerPair13Data

set_option maxRecDepth 1000000 in
private theorem leaf1403LocalValidity :
    LeafFacts leaf1403Box leaf1403Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1403Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4194312/4194239) }) = true
      norm_num [leaf1403Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1403CertificateValid :
    WideCertificateValid leaf1403Box leaf1403Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk126ValidityFacts chi148ValidityFacts
    leaf1403LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1403CoverageChecked :
    coverageCheck (innerAD leaf1403Box) leaf1403InnerLog = true := by
  rfl'

private theorem leaf1403InnerLogValid :
    leaf1403InnerLog.Valid 8 (innerAD leaf1403Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint6PositiveFacts.valid leaf1403CoverageChecked

private noncomputable def leaf1403InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629227/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1403InputLogOnePlusV_eq :
    leaf1403InputLogOnePlusV = outerEnclosure 24
      (leaf1403Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1403RoundedFacts : LeafRoundedFacts 8
    leaf1403Certificate.logOnePlusV leaf1403InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1403InputLogOnePlusV_eq }

private noncomputable def leaf1403Inputs : Inputs :=
  inputsOfCaches globalInput sk126RoundedInputs
    chi148InputQChi innerPair13Input
    leaf1403InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1403LowerChecked :
    lowerCheck 24 leaf1403Box leaf1403Inputs = true := by
  rfl'

private theorem leaf1403CoversExact : CoversExact 8
    leaf1403Box leaf1403Certificate leaf1403InnerLog leaf1403Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk126RoundedFacts chi148RoundedFacts
    innerPair13RoundedFacts leaf1403RoundedFacts (by rfl)

private theorem leaf1403FlatSound : Sound leaf1403Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1403CertificateValid
    leaf1403InnerLogValid leaf1403CoversExact leaf1403LowerChecked

private noncomputable def leaf1404Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (5/64), chiHi := (21/256) }

private noncomputable def leaf1404Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435595/268435456) }, vSqrt := { lower := (65529/65536), upper := (67108992/67107835) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (331313271/268435456) }, upper := { exponent := 0, mantissa := (5125/4096) } }, logOuter := sk123LogOuterCertificate, logK := sk123LogKCertificate, logChi := chi127LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (134216827/134215670) } }, logDArg := sk123LogDArgCertificate }

private noncomputable def leaf1404InnerLog : WideLogData :=
  innerPair13Data

set_option maxRecDepth 1000000 in
private theorem leaf1404LocalValidity :
    LeafFacts leaf1404Box leaf1404Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1404Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (67108992/67107835) }) = true
      norm_num [leaf1404Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1404CertificateValid :
    WideCertificateValid leaf1404Box leaf1404Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk123ValidityFacts chi127ValidityFacts
    leaf1404LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1404CoverageChecked :
    coverageCheck (innerAD leaf1404Box) leaf1404InnerLog = true := by
  rfl'

private theorem leaf1404InnerLogValid :
    leaf1404InnerLog.Valid 8 (innerAD leaf1404Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint6PositiveFacts.valid leaf1404CoverageChecked

private noncomputable def leaf1404InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629225/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1404InputLogOnePlusV_eq :
    leaf1404InputLogOnePlusV = outerEnclosure 24
      (leaf1404Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1404RoundedFacts : LeafRoundedFacts 8
    leaf1404Certificate.logOnePlusV leaf1404InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1404InputLogOnePlusV_eq }

private noncomputable def leaf1404Inputs : Inputs :=
  inputsOfCaches globalInput sk123RoundedInputs
    chi127InputQChi innerPair13Input
    leaf1404InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1404LowerChecked :
    lowerCheck 24 leaf1404Box leaf1404Inputs = true := by
  rfl'

private theorem leaf1404CoversExact : CoversExact 8
    leaf1404Box leaf1404Certificate leaf1404InnerLog leaf1404Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk123RoundedFacts chi127RoundedFacts
    innerPair13RoundedFacts leaf1404RoundedFacts (by rfl)

private theorem leaf1404FlatSound : Sound leaf1404Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1404CertificateValid
    leaf1404InnerLogValid leaf1404CoversExact leaf1404LowerChecked

private noncomputable def leaf1405Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (21/256), chiHi := (11/128) }

private noncomputable def leaf1405Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435597/268435456) }, vSqrt := { lower := (65529/65536), upper := (11184832/11184631) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (334458805/268435456) }, upper := { exponent := 0, mantissa := (2587/2048) } }, logOuter := sk123LogOuterCertificate, logK := sk123LogKCertificate, logChi := chi128LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (22369463/22369262) } }, logDArg := sk123LogDArgCertificate }

private noncomputable def leaf1405InnerLog : WideLogData :=
  innerPair13Data

set_option maxRecDepth 1000000 in
private theorem leaf1405LocalValidity :
    LeafFacts leaf1405Box leaf1405Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1405Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (11184832/11184631) }) = true
      norm_num [leaf1405Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1405CertificateValid :
    WideCertificateValid leaf1405Box leaf1405Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk123ValidityFacts chi128ValidityFacts
    leaf1405LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1405CoverageChecked :
    coverageCheck (innerAD leaf1405Box) leaf1405InnerLog = true := by
  rfl'

private theorem leaf1405InnerLogValid :
    leaf1405InnerLog.Valid 8 (innerAD leaf1405Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint6PositiveFacts.valid leaf1405CoverageChecked

private noncomputable def leaf1405InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629231/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1405InputLogOnePlusV_eq :
    leaf1405InputLogOnePlusV = outerEnclosure 24
      (leaf1405Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1405RoundedFacts : LeafRoundedFacts 8
    leaf1405Certificate.logOnePlusV leaf1405InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1405InputLogOnePlusV_eq }

private noncomputable def leaf1405Inputs : Inputs :=
  inputsOfCaches globalInput sk123RoundedInputs
    chi128InputQChi innerPair13Input
    leaf1405InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1405LowerChecked :
    lowerCheck 24 leaf1405Box leaf1405Inputs = true := by
  rfl'

private theorem leaf1405CoversExact : CoversExact 8
    leaf1405Box leaf1405Certificate leaf1405InnerLog leaf1405Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk123RoundedFacts chi128RoundedFacts
    innerPair13RoundedFacts leaf1405RoundedFacts (by rfl)

private theorem leaf1405FlatSound : Sound leaf1405Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1405CertificateValid
    leaf1405InnerLogValid leaf1405CoversExact leaf1405LowerChecked

private noncomputable def leaf1406Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (5/64), chiHi := (21/256) }

private noncomputable def leaf1406Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435597/268435456) }, vSqrt := { lower := (65529/65536), upper := (33554496/33553907) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (332623909/268435456) }, upper := { exponent := 0, mantissa := (2573/2048) } }, logOuter := sk124LogOuterCertificate, logK := sk124LogKCertificate, logChi := chi127LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (67108403/67107814) } }, logDArg := sk124LogDArgCertificate }

private noncomputable def leaf1406InnerLog : WideLogData :=
  innerPair13Data

set_option maxRecDepth 1000000 in
private theorem leaf1406LocalValidity :
    LeafFacts leaf1406Box leaf1406Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1406Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (33554496/33553907) }) = true
      norm_num [leaf1406Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1406CertificateValid :
    WideCertificateValid leaf1406Box leaf1406Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk124ValidityFacts chi127ValidityFacts
    leaf1406LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1406CoverageChecked :
    coverageCheck (innerAD leaf1406Box) leaf1406InnerLog = true := by
  rfl'

private theorem leaf1406InnerLogValid :
    leaf1406InnerLog.Valid 8 (innerAD leaf1406Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint6PositiveFacts.valid leaf1406CoverageChecked

private noncomputable def leaf1406InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907307/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1406InputLogOnePlusV_eq :
    leaf1406InputLogOnePlusV = outerEnclosure 24
      (leaf1406Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1406RoundedFacts : LeafRoundedFacts 8
    leaf1406Certificate.logOnePlusV leaf1406InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1406InputLogOnePlusV_eq }

private noncomputable def leaf1406Inputs : Inputs :=
  inputsOfCaches globalInput sk124RoundedInputs
    chi127InputQChi innerPair13Input
    leaf1406InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1406LowerChecked :
    lowerCheck 24 leaf1406Box leaf1406Inputs = true := by
  rfl'

private theorem leaf1406CoversExact : CoversExact 8
    leaf1406Box leaf1406Certificate leaf1406InnerLog leaf1406Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk124RoundedFacts chi127RoundedFacts
    innerPair13RoundedFacts leaf1406RoundedFacts (by rfl)

private theorem leaf1406FlatSound : Sound leaf1406Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1406CertificateValid
    leaf1406InnerLogValid leaf1406CoversExact leaf1406LowerChecked

private noncomputable def leaf1407Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (21/256), chiHi := (11/128) }

private noncomputable def leaf1407Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435599/268435456) }, vSqrt := { lower := (65529/65536), upper := (16777248/16776941) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (335834975/268435456) }, upper := { exponent := 0, mantissa := (1299/1024) } }, logOuter := sk124LogOuterCertificate, logK := sk124LogKCertificate, logChi := chi128LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (33554189/33553882) } }, logDArg := sk124LogDArgCertificate }

private noncomputable def leaf1407InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1407LocalValidity :
    LeafFacts leaf1407Box leaf1407Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1407Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (16777248/16776941) }) = true
      norm_num [leaf1407Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1407CertificateValid :
    WideCertificateValid leaf1407Box leaf1407Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk124ValidityFacts chi128ValidityFacts
    leaf1407LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1407CoverageChecked :
    coverageCheck (innerAD leaf1407Box) leaf1407InnerLog = true := by
  rfl'

private theorem leaf1407InnerLogValid :
    leaf1407InnerLog.Valid 8 (innerAD leaf1407Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1407CoverageChecked

private noncomputable def leaf1407InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814617/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1407InputLogOnePlusV_eq :
    leaf1407InputLogOnePlusV = outerEnclosure 24
      (leaf1407Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1407RoundedFacts : LeafRoundedFacts 8
    leaf1407Certificate.logOnePlusV leaf1407InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1407InputLogOnePlusV_eq }

private noncomputable def leaf1407Inputs : Inputs :=
  inputsOfCaches globalInput sk124RoundedInputs
    chi128InputQChi innerPair16Input
    leaf1407InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1407LowerChecked :
    lowerCheck 24 leaf1407Box leaf1407Inputs = true := by
  rfl'

private theorem leaf1407CoversExact : CoversExact 8
    leaf1407Box leaf1407Certificate leaf1407InnerLog leaf1407Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk124RoundedFacts chi128RoundedFacts
    innerPair16RoundedFacts leaf1407RoundedFacts (by rfl)

private theorem leaf1407FlatSound : Sound leaf1407Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1407CertificateValid
    leaf1407InnerLogValid leaf1407CoversExact leaf1407LowerChecked

private noncomputable def leaf1408Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (11/128), chiHi := (23/256) }

private noncomputable def leaf1408Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435599/268435456) }, vSqrt := { lower := (65529/65536), upper := (67108992/67107737) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (337604339/268435456) }, upper := { exponent := 0, mantissa := (5223/4096) } }, logOuter := sk123LogOuterCertificate, logK := sk123LogKCertificate, logChi := chi129LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (134216729/134215474) } }, logDArg := sk123LogDArgCertificate }

private noncomputable def leaf1408InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1408LocalValidity :
    LeafFacts leaf1408Box leaf1408Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1408Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (67108992/67107737) }) = true
      norm_num [leaf1408Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1408CertificateValid :
    WideCertificateValid leaf1408Box leaf1408Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk123ValidityFacts chi129ValidityFacts
    leaf1408LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1408CoverageChecked :
    coverageCheck (innerAD leaf1408Box) leaf1408InnerLog = true := by
  rfl'

private theorem leaf1408InnerLogValid :
    leaf1408InnerLog.Valid 8 (innerAD leaf1408Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1408CoverageChecked

private noncomputable def leaf1408InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814619/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1408InputLogOnePlusV_eq :
    leaf1408InputLogOnePlusV = outerEnclosure 24
      (leaf1408Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1408RoundedFacts : LeafRoundedFacts 8
    leaf1408Certificate.logOnePlusV leaf1408InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1408InputLogOnePlusV_eq }

private noncomputable def leaf1408Inputs : Inputs :=
  inputsOfCaches globalInput sk123RoundedInputs
    chi129InputQChi innerPair16Input
    leaf1408InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1408LowerChecked :
    lowerCheck 24 leaf1408Box leaf1408Inputs = true := by
  rfl'

private theorem leaf1408CoversExact : CoversExact 8
    leaf1408Box leaf1408Certificate leaf1408InnerLog leaf1408Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk123RoundedFacts chi129RoundedFacts
    innerPair16RoundedFacts leaf1408RoundedFacts (by rfl)

private theorem leaf1408FlatSound : Sound leaf1408Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1408CertificateValid
    leaf1408InnerLogValid leaf1408CoversExact leaf1408LowerChecked

private noncomputable def leaf1409Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (23/256), chiHi := (3/32) }

private noncomputable def leaf1409Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435601/268435456) }, vSqrt := { lower := (65529/65536), upper := (8388624/8388461) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (340749873/268435456) }, upper := { exponent := 0, mantissa := (659/512) } }, logOuter := sk123LogOuterCertificate, logK := sk123LogKCertificate, logChi := chi130LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (16777085/16776922) } }, logDArg := sk123LogDArgCertificate }

private noncomputable def leaf1409InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1409LocalValidity :
    LeafFacts leaf1409Box leaf1409Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1409Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8388624/8388461) }) = true
      norm_num [leaf1409Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1409CertificateValid :
    WideCertificateValid leaf1409Box leaf1409Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk123ValidityFacts chi130ValidityFacts
    leaf1409LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1409CoverageChecked :
    coverageCheck (innerAD leaf1409Box) leaf1409InnerLog = true := by
  rfl'

private theorem leaf1409InnerLogValid :
    leaf1409InnerLog.Valid 8 (innerAD leaf1409Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1409CoverageChecked

private noncomputable def leaf1409InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907311/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1409InputLogOnePlusV_eq :
    leaf1409InputLogOnePlusV = outerEnclosure 24
      (leaf1409Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1409RoundedFacts : LeafRoundedFacts 8
    leaf1409Certificate.logOnePlusV leaf1409InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1409InputLogOnePlusV_eq }

private noncomputable def leaf1409Inputs : Inputs :=
  inputsOfCaches globalInput sk123RoundedInputs
    chi130InputQChi innerPair16Input
    leaf1409InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1409LowerChecked :
    lowerCheck 24 leaf1409Box leaf1409Inputs = true := by
  rfl'

private theorem leaf1409CoversExact : CoversExact 8
    leaf1409Box leaf1409Certificate leaf1409InnerLog leaf1409Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk123RoundedFacts chi130RoundedFacts
    innerPair16RoundedFacts leaf1409RoundedFacts (by rfl)

private theorem leaf1409FlatSound : Sound leaf1409Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1409CertificateValid
    leaf1409InnerLogValid leaf1409CoversExact leaf1409LowerChecked

private noncomputable def leaf1410Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (11/128), chiHi := (23/256) }

private noncomputable def leaf1410Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435601/268435456) }, vSqrt := { lower := (65529/65536), upper := (11184832/11184619) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (339046041/268435456) }, upper := { exponent := 0, mantissa := (2623/2048) } }, logOuter := sk124LogOuterCertificate, logK := sk124LogKCertificate, logChi := chi129LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (22369451/22369238) } }, logDArg := sk124LogDArgCertificate }

private noncomputable def leaf1410InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1410LocalValidity :
    LeafFacts leaf1410Box leaf1410Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1410Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (11184832/11184619) }) = true
      norm_num [leaf1410Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1410CertificateValid :
    WideCertificateValid leaf1410Box leaf1410Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk124ValidityFacts chi129ValidityFacts
    leaf1410LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1410CoverageChecked :
    coverageCheck (innerAD leaf1410Box) leaf1410InnerLog = true := by
  rfl'

private theorem leaf1410InnerLogValid :
    leaf1410InnerLog.Valid 8 (innerAD leaf1410Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1410CoverageChecked

private noncomputable def leaf1410InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453655/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf1410InputLogOnePlusV_eq :
    leaf1410InputLogOnePlusV = outerEnclosure 24
      (leaf1410Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1410RoundedFacts : LeafRoundedFacts 8
    leaf1410Certificate.logOnePlusV leaf1410InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1410InputLogOnePlusV_eq }

private noncomputable def leaf1410Inputs : Inputs :=
  inputsOfCaches globalInput sk124RoundedInputs
    chi129InputQChi innerPair16Input
    leaf1410InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1410LowerChecked :
    lowerCheck 24 leaf1410Box leaf1410Inputs = true := by
  rfl'

private theorem leaf1410CoversExact : CoversExact 8
    leaf1410Box leaf1410Certificate leaf1410InnerLog leaf1410Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk124RoundedFacts chi129RoundedFacts
    innerPair16RoundedFacts leaf1410RoundedFacts (by rfl)

private theorem leaf1410FlatSound : Sound leaf1410Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1410CertificateValid
    leaf1410InnerLogValid leaf1410CoversExact leaf1410LowerChecked

private noncomputable def leaf1411Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (23/256), chiHi := (3/32) }

private noncomputable def leaf1411Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435603/268435456) }, vSqrt := { lower := (65529/65536), upper := (4194312/4194229) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (342257107/268435456) }, upper := { exponent := 0, mantissa := (331/256) } }, logOuter := sk124LogOuterCertificate, logK := sk124LogKCertificate, logChi := chi130LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (8388541/8388458) } }, logDArg := sk124LogDArgCertificate }

private noncomputable def leaf1411InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1411LocalValidity :
    LeafFacts leaf1411Box leaf1411Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1411Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4194312/4194229) }) = true
      norm_num [leaf1411Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1411CertificateValid :
    WideCertificateValid leaf1411Box leaf1411Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk124ValidityFacts chi130ValidityFacts
    leaf1411LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1411CoverageChecked :
    coverageCheck (innerAD leaf1411Box) leaf1411InnerLog = true := by
  rfl'

private theorem leaf1411InnerLogValid :
    leaf1411InnerLog.Valid 8 (innerAD leaf1411Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1411CoverageChecked

private noncomputable def leaf1411InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629247/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1411InputLogOnePlusV_eq :
    leaf1411InputLogOnePlusV = outerEnclosure 24
      (leaf1411Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1411RoundedFacts : LeafRoundedFacts 8
    leaf1411Certificate.logOnePlusV leaf1411InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1411InputLogOnePlusV_eq }

private noncomputable def leaf1411Inputs : Inputs :=
  inputsOfCaches globalInput sk124RoundedInputs
    chi130InputQChi innerPair16Input
    leaf1411InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1411LowerChecked :
    lowerCheck 24 leaf1411Box leaf1411Inputs = true := by
  rfl'

private theorem leaf1411CoversExact : CoversExact 8
    leaf1411Box leaf1411Certificate leaf1411InnerLog leaf1411Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk124RoundedFacts chi130RoundedFacts
    innerPair16RoundedFacts leaf1411RoundedFacts (by rfl)

private theorem leaf1411FlatSound : Sound leaf1411Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1411CertificateValid
    leaf1411InnerLogValid leaf1411CoversExact leaf1411LowerChecked

private noncomputable def leaf1412Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (5/64), chiHi := (21/256) }

private noncomputable def leaf1412Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435599/268435456) }, vSqrt := { lower := (65529/65536), upper := (67108992/67107793) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (333934547/268435456) }, upper := { exponent := 0, mantissa := (5167/4096) } }, logOuter := sk125LogOuterCertificate, logK := sk125LogKCertificate, logChi := chi127LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (134216785/134215586) } }, logDArg := sk125LogDArgCertificate }

private noncomputable def leaf1412InnerLog : WideLogData :=
  innerPair13Data

set_option maxRecDepth 1000000 in
private theorem leaf1412LocalValidity :
    LeafFacts leaf1412Box leaf1412Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1412Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (67108992/67107793) }) = true
      norm_num [leaf1412Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1412CertificateValid :
    WideCertificateValid leaf1412Box leaf1412Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk125ValidityFacts chi127ValidityFacts
    leaf1412LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1412CoverageChecked :
    coverageCheck (innerAD leaf1412Box) leaf1412InnerLog = true := by
  rfl'

private theorem leaf1412InnerLogValid :
    leaf1412InnerLog.Valid 8 (innerAD leaf1412Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint6PositiveFacts.valid leaf1412CoverageChecked

private noncomputable def leaf1412InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629231/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1412InputLogOnePlusV_eq :
    leaf1412InputLogOnePlusV = outerEnclosure 24
      (leaf1412Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1412RoundedFacts : LeafRoundedFacts 8
    leaf1412Certificate.logOnePlusV leaf1412InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1412InputLogOnePlusV_eq }

private noncomputable def leaf1412Inputs : Inputs :=
  inputsOfCaches globalInput sk125RoundedInputs
    chi127InputQChi innerPair13Input
    leaf1412InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1412LowerChecked :
    lowerCheck 24 leaf1412Box leaf1412Inputs = true := by
  rfl'

private theorem leaf1412CoversExact : CoversExact 8
    leaf1412Box leaf1412Certificate leaf1412InnerLog leaf1412Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk125RoundedFacts chi127RoundedFacts
    innerPair13RoundedFacts leaf1412RoundedFacts (by rfl)

private theorem leaf1412FlatSound : Sound leaf1412Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1412CertificateValid
    leaf1412InnerLogValid leaf1412CoversExact leaf1412LowerChecked

private noncomputable def leaf1413Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (21/256), chiHi := (11/128) }

private noncomputable def leaf1413Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435601/268435456) }, vSqrt := { lower := (65529/65536), upper := (33554496/33553871) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (337211145/268435456) }, upper := { exponent := 0, mantissa := (2609/2048) } }, logOuter := sk125LogOuterCertificate, logK := sk125LogKCertificate, logChi := chi128LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (67108367/67107742) } }, logDArg := sk125LogDArgCertificate }

private noncomputable def leaf1413InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1413LocalValidity :
    LeafFacts leaf1413Box leaf1413Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1413Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (33554496/33553871) }) = true
      norm_num [leaf1413Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1413CertificateValid :
    WideCertificateValid leaf1413Box leaf1413Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk125ValidityFacts chi128ValidityFacts
    leaf1413LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1413CoverageChecked :
    coverageCheck (innerAD leaf1413Box) leaf1413InnerLog = true := by
  rfl'

private theorem leaf1413InnerLogValid :
    leaf1413InnerLog.Valid 8 (innerAD leaf1413Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1413CoverageChecked

private noncomputable def leaf1413InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629237/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1413InputLogOnePlusV_eq :
    leaf1413InputLogOnePlusV = outerEnclosure 24
      (leaf1413Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1413RoundedFacts : LeafRoundedFacts 8
    leaf1413Certificate.logOnePlusV leaf1413InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1413InputLogOnePlusV_eq }

private noncomputable def leaf1413Inputs : Inputs :=
  inputsOfCaches globalInput sk125RoundedInputs
    chi128InputQChi innerPair16Input
    leaf1413InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1413LowerChecked :
    lowerCheck 24 leaf1413Box leaf1413Inputs = true := by
  rfl'

private theorem leaf1413CoversExact : CoversExact 8
    leaf1413Box leaf1413Certificate leaf1413InnerLog leaf1413Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk125RoundedFacts chi128RoundedFacts
    innerPair16RoundedFacts leaf1413RoundedFacts (by rfl)

private theorem leaf1413FlatSound : Sound leaf1413Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1413CertificateValid
    leaf1413InnerLogValid leaf1413CoversExact leaf1413LowerChecked

private noncomputable def leaf1414Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (5/64), chiHi := (21/256) }

private noncomputable def leaf1414Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435601/268435456) }, vSqrt := { lower := (65529/65536), upper := (16777248/16776943) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (335245185/268435456) }, upper := { exponent := 0, mantissa := (1297/1024) } }, logOuter := sk126LogOuterCertificate, logK := sk126LogKCertificate, logChi := chi127LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (33554191/33553886) } }, logDArg := sk126LogDArgCertificate }

private noncomputable def leaf1414InnerLog : WideLogData :=
  innerPair13Data

set_option maxRecDepth 1000000 in
private theorem leaf1414LocalValidity :
    LeafFacts leaf1414Box leaf1414Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1414Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (16777248/16776943) }) = true
      norm_num [leaf1414Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1414CertificateValid :
    WideCertificateValid leaf1414Box leaf1414Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk126ValidityFacts chi127ValidityFacts
    leaf1414LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1414CoverageChecked :
    coverageCheck (innerAD leaf1414Box) leaf1414InnerLog = true := by
  rfl'

private theorem leaf1414InnerLogValid :
    leaf1414InnerLog.Valid 8 (innerAD leaf1414Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint6PositiveFacts.valid leaf1414CoverageChecked

private noncomputable def leaf1414InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629233/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1414InputLogOnePlusV_eq :
    leaf1414InputLogOnePlusV = outerEnclosure 24
      (leaf1414Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1414RoundedFacts : LeafRoundedFacts 8
    leaf1414Certificate.logOnePlusV leaf1414InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1414InputLogOnePlusV_eq }

private noncomputable def leaf1414Inputs : Inputs :=
  inputsOfCaches globalInput sk126RoundedInputs
    chi127InputQChi innerPair13Input
    leaf1414InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1414LowerChecked :
    lowerCheck 24 leaf1414Box leaf1414Inputs = true := by
  rfl'

private theorem leaf1414CoversExact : CoversExact 8
    leaf1414Box leaf1414Certificate leaf1414InnerLog leaf1414Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk126RoundedFacts chi127RoundedFacts
    innerPair13RoundedFacts leaf1414RoundedFacts (by rfl)

private theorem leaf1414FlatSound : Sound leaf1414Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1414CertificateValid
    leaf1414InnerLogValid leaf1414CoversExact leaf1414LowerChecked

private noncomputable def leaf1415Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (21/256), chiHi := (11/128) }

private noncomputable def leaf1415Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435603/268435456) }, vSqrt := { lower := (65529/65536), upper := (2796208/2796155) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (338587315/268435456) }, upper := { exponent := 0, mantissa := (655/512) } }, logOuter := sk126LogOuterCertificate, logK := sk126LogKCertificate, logChi := chi128LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (5592363/5592310) } }, logDArg := sk126LogDArgCertificate }

private noncomputable def leaf1415InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1415LocalValidity :
    LeafFacts leaf1415Box leaf1415Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1415Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (2796208/2796155) }) = true
      norm_num [leaf1415Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1415CertificateValid :
    WideCertificateValid leaf1415Box leaf1415Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk126ValidityFacts chi128ValidityFacts
    leaf1415LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1415CoverageChecked :
    coverageCheck (innerAD leaf1415Box) leaf1415InnerLog = true := by
  rfl'

private theorem leaf1415InnerLogValid :
    leaf1415InnerLog.Valid 8 (innerAD leaf1415Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1415CoverageChecked

private noncomputable def leaf1415InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453655/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf1415InputLogOnePlusV_eq :
    leaf1415InputLogOnePlusV = outerEnclosure 24
      (leaf1415Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1415RoundedFacts : LeafRoundedFacts 8
    leaf1415Certificate.logOnePlusV leaf1415InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1415InputLogOnePlusV_eq }

private noncomputable def leaf1415Inputs : Inputs :=
  inputsOfCaches globalInput sk126RoundedInputs
    chi128InputQChi innerPair16Input
    leaf1415InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1415LowerChecked :
    lowerCheck 24 leaf1415Box leaf1415Inputs = true := by
  rfl'

private theorem leaf1415CoversExact : CoversExact 8
    leaf1415Box leaf1415Certificate leaf1415InnerLog leaf1415Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk126RoundedFacts chi128RoundedFacts
    innerPair16RoundedFacts leaf1415RoundedFacts (by rfl)

private theorem leaf1415FlatSound : Sound leaf1415Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1415CertificateValid
    leaf1415InnerLogValid leaf1415CoversExact leaf1415LowerChecked

private noncomputable def leaf1416Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (11/128), chiHi := (23/256) }

private noncomputable def leaf1416Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435603/268435456) }, vSqrt := { lower := (65529/65536), upper := (67108992/67107691) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (340487743/268435456) }, upper := { exponent := 0, mantissa := (5269/4096) } }, logOuter := sk125LogOuterCertificate, logK := sk125LogKCertificate, logChi := chi129LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (134216683/134215382) } }, logDArg := sk125LogDArgCertificate }

private noncomputable def leaf1416InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1416LocalValidity :
    LeafFacts leaf1416Box leaf1416Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1416Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (67108992/67107691) }) = true
      norm_num [leaf1416Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1416CertificateValid :
    WideCertificateValid leaf1416Box leaf1416Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk125ValidityFacts chi129ValidityFacts
    leaf1416LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1416CoverageChecked :
    coverageCheck (innerAD leaf1416Box) leaf1416InnerLog = true := by
  rfl'

private theorem leaf1416InnerLogValid :
    leaf1416InnerLog.Valid 8 (innerAD leaf1416Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1416CoverageChecked

private noncomputable def leaf1416InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629243/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1416InputLogOnePlusV_eq :
    leaf1416InputLogOnePlusV = outerEnclosure 24
      (leaf1416Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1416RoundedFacts : LeafRoundedFacts 8
    leaf1416Certificate.logOnePlusV leaf1416InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1416InputLogOnePlusV_eq }

private noncomputable def leaf1416Inputs : Inputs :=
  inputsOfCaches globalInput sk125RoundedInputs
    chi129InputQChi innerPair16Input
    leaf1416InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1416LowerChecked :
    lowerCheck 24 leaf1416Box leaf1416Inputs = true := by
  rfl'

private theorem leaf1416CoversExact : CoversExact 8
    leaf1416Box leaf1416Certificate leaf1416InnerLog leaf1416Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk125RoundedFacts chi129RoundedFacts
    innerPair16RoundedFacts leaf1416RoundedFacts (by rfl)

private theorem leaf1416FlatSound : Sound leaf1416Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1416CertificateValid
    leaf1416InnerLogValid leaf1416CoversExact leaf1416LowerChecked

private noncomputable def leaf1417Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (23/256), chiHi := (3/32) }

private noncomputable def leaf1417Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435605/268435456) }, vSqrt := { lower := (65529/65536), upper := (8388624/8388455) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (343764341/268435456) }, upper := { exponent := 0, mantissa := (665/512) } }, logOuter := sk125LogOuterCertificate, logK := sk125LogKCertificate, logChi := chi130LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (16777079/16776910) } }, logDArg := sk125LogDArgCertificate }

private noncomputable def leaf1417InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1417LocalValidity :
    LeafFacts leaf1417Box leaf1417Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1417Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8388624/8388455) }) = true
      norm_num [leaf1417Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1417CertificateValid :
    WideCertificateValid leaf1417Box leaf1417Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk125ValidityFacts chi130ValidityFacts
    leaf1417LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1417CoverageChecked :
    coverageCheck (innerAD leaf1417Box) leaf1417InnerLog = true := by
  rfl'

private theorem leaf1417InnerLogValid :
    leaf1417InnerLog.Valid 8 (innerAD leaf1417Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1417CoverageChecked

private noncomputable def leaf1417InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814625/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1417InputLogOnePlusV_eq :
    leaf1417InputLogOnePlusV = outerEnclosure 24
      (leaf1417Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1417RoundedFacts : LeafRoundedFacts 8
    leaf1417Certificate.logOnePlusV leaf1417InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1417InputLogOnePlusV_eq }

private noncomputable def leaf1417Inputs : Inputs :=
  inputsOfCaches globalInput sk125RoundedInputs
    chi130InputQChi innerPair16Input
    leaf1417InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1417LowerChecked :
    lowerCheck 24 leaf1417Box leaf1417Inputs = true := by
  rfl'

private theorem leaf1417CoversExact : CoversExact 8
    leaf1417Box leaf1417Certificate leaf1417InnerLog leaf1417Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk125RoundedFacts chi130RoundedFacts
    innerPair16RoundedFacts leaf1417RoundedFacts (by rfl)

private theorem leaf1417FlatSound : Sound leaf1417Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1417CertificateValid
    leaf1417InnerLogValid leaf1417CoversExact leaf1417LowerChecked

private noncomputable def leaf1418Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (11/128), chiHi := (23/256) }

private noncomputable def leaf1418Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435605/268435456) }, vSqrt := { lower := (65529/65536), upper := (16777248/16776917) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (341929445/268435456) }, upper := { exponent := 0, mantissa := (1323/1024) } }, logOuter := sk126LogOuterCertificate, logK := sk126LogKCertificate, logChi := chi129LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (33554165/33553834) } }, logDArg := sk126LogDArgCertificate }

private noncomputable def leaf1418InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1418LocalValidity :
    LeafFacts leaf1418Box leaf1418Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1418Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (16777248/16776917) }) = true
      norm_num [leaf1418Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1418CertificateValid :
    WideCertificateValid leaf1418Box leaf1418Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk126ValidityFacts chi129ValidityFacts
    leaf1418LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1418CoverageChecked :
    coverageCheck (innerAD leaf1418Box) leaf1418InnerLog = true := by
  rfl'

private theorem leaf1418InnerLogValid :
    leaf1418InnerLog.Valid 8 (innerAD leaf1418Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1418CoverageChecked

private noncomputable def leaf1418InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814623/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1418InputLogOnePlusV_eq :
    leaf1418InputLogOnePlusV = outerEnclosure 24
      (leaf1418Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1418RoundedFacts : LeafRoundedFacts 8
    leaf1418Certificate.logOnePlusV leaf1418InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1418InputLogOnePlusV_eq }

private noncomputable def leaf1418Inputs : Inputs :=
  inputsOfCaches globalInput sk126RoundedInputs
    chi129InputQChi innerPair16Input
    leaf1418InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1418LowerChecked :
    lowerCheck 24 leaf1418Box leaf1418Inputs = true := by
  rfl'

private theorem leaf1418CoversExact : CoversExact 8
    leaf1418Box leaf1418Certificate leaf1418InnerLog leaf1418Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk126RoundedFacts chi129RoundedFacts
    innerPair16RoundedFacts leaf1418RoundedFacts (by rfl)

private theorem leaf1418FlatSound : Sound leaf1418Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1418CertificateValid
    leaf1418InnerLogValid leaf1418CoversExact leaf1418LowerChecked

private noncomputable def leaf1419Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (23/256), chiHi := (3/32) }

private noncomputable def leaf1419Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435607/268435456) }, vSqrt := { lower := (65529/65536), upper := (2097156/2097113) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (345271575/268435456) }, upper := { exponent := 0, mantissa := (167/128) } }, logOuter := sk126LogOuterCertificate, logK := sk126LogKCertificate, logChi := chi130LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (4194269/4194226) } }, logDArg := sk126LogDArgCertificate }

private noncomputable def leaf1419InnerLog : WideLogData :=
  innerPair436Data

set_option maxRecDepth 1000000 in
private theorem leaf1419LocalValidity :
    LeafFacts leaf1419Box leaf1419Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1419Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (2097156/2097113) }) = true
      norm_num [leaf1419Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1419CertificateValid :
    WideCertificateValid leaf1419Box leaf1419Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk126ValidityFacts chi130ValidityFacts
    leaf1419LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1419CoverageChecked :
    coverageCheck (innerAD leaf1419Box) leaf1419InnerLog = true := by
  rfl'

private theorem leaf1419InnerLogValid :
    leaf1419InnerLog.Valid 8 (innerAD leaf1419Box) :=
  wideLogDataValid_of_cachedCheck endpoint143PositiveFacts
    endpoint144PositiveFacts.valid leaf1419CoverageChecked

private noncomputable def leaf1419InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629253/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1419InputLogOnePlusV_eq :
    leaf1419InputLogOnePlusV = outerEnclosure 24
      (leaf1419Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1419RoundedFacts : LeafRoundedFacts 8
    leaf1419Certificate.logOnePlusV leaf1419InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1419InputLogOnePlusV_eq }

private noncomputable def leaf1419Inputs : Inputs :=
  inputsOfCaches globalInput sk126RoundedInputs
    chi130InputQChi innerPair436Input
    leaf1419InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1419LowerChecked :
    lowerCheck 24 leaf1419Box leaf1419Inputs = true := by
  rfl'

private theorem leaf1419CoversExact : CoversExact 8
    leaf1419Box leaf1419Certificate leaf1419InnerLog leaf1419Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk126RoundedFacts chi130RoundedFacts
    innerPair436RoundedFacts leaf1419RoundedFacts (by rfl)

private theorem leaf1419FlatSound : Sound leaf1419Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1419CertificateValid
    leaf1419InnerLogValid leaf1419CoversExact leaf1419LowerChecked

private noncomputable def component32Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (1/16), chiHi := (9/128) }

set_option maxRecDepth 1000000 in
private theorem component32Node0_sound : Sound component32Node0Box :=
  sound_of_literal_split component32Node0Box leaf1394Box leaf1395Box
    .k (49/16) (by rfl) (by rfl)
    leaf1394FlatSound leaf1395FlatSound

private noncomputable def component32Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (9/128), chiHi := (5/64) }

set_option maxRecDepth 1000000 in
private theorem component32Node1_sound : Sound component32Node1Box :=
  sound_of_literal_split component32Node1Box leaf1396Box leaf1397Box
    .k (49/16) (by rfl) (by rfl)
    leaf1396FlatSound leaf1397FlatSound

private noncomputable def component32Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (1/16), chiHi := (5/64) }

set_option maxRecDepth 1000000 in
private theorem component32Node2_sound : Sound component32Node2Box :=
  sound_of_literal_split component32Node2Box component32Node0Box component32Node1Box
    .chi (9/128) (by rfl) (by rfl)
    component32Node0_sound component32Node1_sound

private noncomputable def component32Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (1/16), chiHi := (9/128) }

set_option maxRecDepth 1000000 in
private theorem component32Node3_sound : Sound component32Node3Box :=
  sound_of_literal_split component32Node3Box leaf1398Box leaf1399Box
    .k (51/16) (by rfl) (by rfl)
    leaf1398FlatSound leaf1399FlatSound

private noncomputable def component32Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (9/128), chiHi := (5/64) }

set_option maxRecDepth 1000000 in
private theorem component32Node4_sound : Sound component32Node4Box :=
  sound_of_literal_split component32Node4Box leaf1400Box leaf1401Box
    .chi (19/256) (by rfl) (by rfl)
    leaf1400FlatSound leaf1401FlatSound

private noncomputable def component32Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (9/128), chiHi := (5/64) }

set_option maxRecDepth 1000000 in
private theorem component32Node5_sound : Sound component32Node5Box :=
  sound_of_literal_split component32Node5Box leaf1402Box leaf1403Box
    .chi (19/256) (by rfl) (by rfl)
    leaf1402FlatSound leaf1403FlatSound

private noncomputable def component32Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (9/128), chiHi := (5/64) }

set_option maxRecDepth 1000000 in
private theorem component32Node6_sound : Sound component32Node6Box :=
  sound_of_literal_split component32Node6Box component32Node4Box component32Node5Box
    .k (51/16) (by rfl) (by rfl)
    component32Node4_sound component32Node5_sound

private noncomputable def component32Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (1/16), chiHi := (5/64) }

set_option maxRecDepth 1000000 in
private theorem component32Node7_sound : Sound component32Node7Box :=
  sound_of_literal_split component32Node7Box component32Node3Box component32Node6Box
    .chi (9/128) (by rfl) (by rfl)
    component32Node3_sound component32Node6_sound

private noncomputable def component32Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (13/4), chiLo := (1/16), chiHi := (5/64) }

set_option maxRecDepth 1000000 in
private theorem component32Node8_sound : Sound component32Node8Box :=
  sound_of_literal_split component32Node8Box component32Node2Box component32Node7Box
    .k (25/8) (by rfl) (by rfl)
    component32Node2_sound component32Node7_sound

private noncomputable def component32Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (5/64), chiHi := (11/128) }

set_option maxRecDepth 1000000 in
private theorem component32Node9_sound : Sound component32Node9Box :=
  sound_of_literal_split component32Node9Box leaf1404Box leaf1405Box
    .chi (21/256) (by rfl) (by rfl)
    leaf1404FlatSound leaf1405FlatSound

private noncomputable def component32Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (5/64), chiHi := (11/128) }

set_option maxRecDepth 1000000 in
private theorem component32Node10_sound : Sound component32Node10Box :=
  sound_of_literal_split component32Node10Box leaf1406Box leaf1407Box
    .chi (21/256) (by rfl) (by rfl)
    leaf1406FlatSound leaf1407FlatSound

private noncomputable def component32Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (5/64), chiHi := (11/128) }

set_option maxRecDepth 1000000 in
private theorem component32Node11_sound : Sound component32Node11Box :=
  sound_of_literal_split component32Node11Box component32Node9Box component32Node10Box
    .k (49/16) (by rfl) (by rfl)
    component32Node9_sound component32Node10_sound

private noncomputable def component32Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (11/128), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component32Node12_sound : Sound component32Node12Box :=
  sound_of_literal_split component32Node12Box leaf1408Box leaf1409Box
    .chi (23/256) (by rfl) (by rfl)
    leaf1408FlatSound leaf1409FlatSound

private noncomputable def component32Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (11/128), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component32Node13_sound : Sound component32Node13Box :=
  sound_of_literal_split component32Node13Box leaf1410Box leaf1411Box
    .chi (23/256) (by rfl) (by rfl)
    leaf1410FlatSound leaf1411FlatSound

private noncomputable def component32Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (11/128), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component32Node14_sound : Sound component32Node14Box :=
  sound_of_literal_split component32Node14Box component32Node12Box component32Node13Box
    .k (49/16) (by rfl) (by rfl)
    component32Node12_sound component32Node13_sound

private noncomputable def component32Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (5/64), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component32Node15_sound : Sound component32Node15Box :=
  sound_of_literal_split component32Node15Box component32Node11Box component32Node14Box
    .chi (11/128) (by rfl) (by rfl)
    component32Node11_sound component32Node14_sound

private noncomputable def component32Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (5/64), chiHi := (11/128) }

set_option maxRecDepth 1000000 in
private theorem component32Node16_sound : Sound component32Node16Box :=
  sound_of_literal_split component32Node16Box leaf1412Box leaf1413Box
    .chi (21/256) (by rfl) (by rfl)
    leaf1412FlatSound leaf1413FlatSound

private noncomputable def component32Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (5/64), chiHi := (11/128) }

set_option maxRecDepth 1000000 in
private theorem component32Node17_sound : Sound component32Node17Box :=
  sound_of_literal_split component32Node17Box leaf1414Box leaf1415Box
    .chi (21/256) (by rfl) (by rfl)
    leaf1414FlatSound leaf1415FlatSound

private noncomputable def component32Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (5/64), chiHi := (11/128) }

set_option maxRecDepth 1000000 in
private theorem component32Node18_sound : Sound component32Node18Box :=
  sound_of_literal_split component32Node18Box component32Node16Box component32Node17Box
    .k (51/16) (by rfl) (by rfl)
    component32Node16_sound component32Node17_sound

private noncomputable def component32Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (11/128), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component32Node19_sound : Sound component32Node19Box :=
  sound_of_literal_split component32Node19Box leaf1416Box leaf1417Box
    .chi (23/256) (by rfl) (by rfl)
    leaf1416FlatSound leaf1417FlatSound

private noncomputable def component32Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (11/128), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component32Node20_sound : Sound component32Node20Box :=
  sound_of_literal_split component32Node20Box leaf1418Box leaf1419Box
    .chi (23/256) (by rfl) (by rfl)
    leaf1418FlatSound leaf1419FlatSound

private noncomputable def component32Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (11/128), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component32Node21_sound : Sound component32Node21Box :=
  sound_of_literal_split component32Node21Box component32Node19Box component32Node20Box
    .k (51/16) (by rfl) (by rfl)
    component32Node19_sound component32Node20_sound

private noncomputable def component32Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (5/64), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component32Node22_sound : Sound component32Node22Box :=
  sound_of_literal_split component32Node22Box component32Node18Box component32Node21Box
    .chi (11/128) (by rfl) (by rfl)
    component32Node18_sound component32Node21_sound

private noncomputable def component32Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (13/4), chiLo := (5/64), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component32Node23_sound : Sound component32Node23Box :=
  sound_of_literal_split component32Node23Box component32Node15Box component32Node22Box
    .k (25/8) (by rfl) (by rfl)
    component32Node15_sound component32Node22_sound

noncomputable def component32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (13/4), chiLo := (1/16), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
theorem component32_sound : Sound component32Box :=
  sound_of_literal_split component32Box component32Node8Box component32Node23Box
    .chi (5/64) (by rfl) (by rfl)
    component32Node8_sound component32Node23_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
