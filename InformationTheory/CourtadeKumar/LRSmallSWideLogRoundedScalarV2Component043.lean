import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch6
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch7
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

private noncomputable def leaf1926Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (1/8), chiHi := (17/128) }

private noncomputable def leaf1926Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435683/268435456) }, vSqrt := { lower := (65529/65536), upper := (67108928/67107215) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (369059615/268435456) }, upper := { exponent := 0, mantissa := (5745/4096) } }, logOuter := sk133LogOuterCertificate, logK := sk133LogKCertificate, logChi := chi107LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (134216143/134214430) } }, logDArg := sk133LogDArgCertificate }

private noncomputable def leaf1926InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf1926LocalValidity :
    LeafFacts leaf1926Box leaf1926Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1926Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (67108928/67107215) }) = true
      norm_num [leaf1926Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1926CertificateValid :
    WideCertificateValid leaf1926Box leaf1926Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk133ValidityFacts chi107ValidityFacts
    leaf1926LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1926CoverageChecked :
    coverageCheck (innerAD leaf1926Box) leaf1926InnerLog = true := by
  rfl'

private theorem leaf1926InnerLogValid :
    leaf1926InnerLog.Valid 8 (innerAD leaf1926Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf1926CoverageChecked

private noncomputable def leaf1926InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629295/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1926InputLogOnePlusV_eq :
    leaf1926InputLogOnePlusV = outerEnclosure 24
      (leaf1926Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1926RoundedFacts : LeafRoundedFacts 8
    leaf1926Certificate.logOnePlusV leaf1926InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1926InputLogOnePlusV_eq }

private noncomputable def leaf1926Inputs : Inputs :=
  inputsOfCaches globalInput sk133RoundedInputs
    chi107InputQChi innerPair22Input
    leaf1926InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1926LowerChecked :
    lowerCheck 24 leaf1926Box leaf1926Inputs = true := by
  rfl'

private theorem leaf1926CoversExact : CoversExact 8
    leaf1926Box leaf1926Certificate leaf1926InnerLog leaf1926Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk133RoundedFacts chi107RoundedFacts
    innerPair22RoundedFacts leaf1926RoundedFacts (by rfl)

private theorem leaf1926FlatSound : Sound leaf1926Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1926CertificateValid
    leaf1926InnerLogValid leaf1926CoversExact leaf1926LowerChecked

private noncomputable def leaf1927Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (1/8), chiHi := (17/128) }

private noncomputable def leaf1927Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435685/268435456) }, vSqrt := { lower := (65529/65536), upper := (33554464/33553599) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (370108125/268435456) }, upper := { exponent := 0, mantissa := (2881/2048) } }, logOuter := sk134LogOuterCertificate, logK := sk134LogKCertificate, logChi := chi107LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (67108063/67107198) } }, logDArg := sk134LogDArgCertificate }

private noncomputable def leaf1927InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1927LocalValidity :
    LeafFacts leaf1927Box leaf1927Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1927Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (33554464/33553599) }) = true
      norm_num [leaf1927Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1927CertificateValid :
    WideCertificateValid leaf1927Box leaf1927Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk134ValidityFacts chi107ValidityFacts
    leaf1927LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1927CoverageChecked :
    coverageCheck (innerAD leaf1927Box) leaf1927InnerLog = true := by
  rfl'

private theorem leaf1927InnerLogValid :
    leaf1927InnerLog.Valid 8 (innerAD leaf1927Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1927CoverageChecked

private noncomputable def leaf1927InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629297/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1927InputLogOnePlusV_eq :
    leaf1927InputLogOnePlusV = outerEnclosure 24
      (leaf1927Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1927RoundedFacts : LeafRoundedFacts 8
    leaf1927Certificate.logOnePlusV leaf1927InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1927InputLogOnePlusV_eq }

private noncomputable def leaf1927Inputs : Inputs :=
  inputsOfCaches globalInput sk134RoundedInputs
    chi107InputQChi innerPair26Input
    leaf1927InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1927LowerChecked :
    lowerCheck 24 leaf1927Box leaf1927Inputs = true := by
  rfl'

private theorem leaf1927CoversExact : CoversExact 8
    leaf1927Box leaf1927Certificate leaf1927InnerLog leaf1927Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk134RoundedFacts chi107RoundedFacts
    innerPair26RoundedFacts leaf1927RoundedFacts (by rfl)

private theorem leaf1927FlatSound : Sound leaf1927Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1927CertificateValid
    leaf1927InnerLogValid leaf1927CoversExact leaf1927LowerChecked

private noncomputable def leaf1928Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (17/128), chiHi := (9/64) }

private noncomputable def leaf1928Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435685/268435456) }, vSqrt := { lower := (65529/65536), upper := (33554464/33553559) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (375350685/268435456) }, upper := { exponent := 0, mantissa := (2921/2048) } }, logOuter := sk133LogOuterCertificate, logK := sk133LogKCertificate, logChi := chi108LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (67108023/67107118) } }, logDArg := sk133LogDArgCertificate }

private noncomputable def leaf1928InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1928LocalValidity :
    LeafFacts leaf1928Box leaf1928Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1928Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (33554464/33553559) }) = true
      norm_num [leaf1928Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1928CertificateValid :
    WideCertificateValid leaf1928Box leaf1928Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk133ValidityFacts chi108ValidityFacts
    leaf1928LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1928CoverageChecked :
    coverageCheck (innerAD leaf1928Box) leaf1928InnerLog = true := by
  rfl'

private theorem leaf1928InnerLogValid :
    leaf1928InnerLog.Valid 8 (innerAD leaf1928Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1928CoverageChecked

private noncomputable def leaf1928InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629307/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1928InputLogOnePlusV_eq :
    leaf1928InputLogOnePlusV = outerEnclosure 24
      (leaf1928Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1928RoundedFacts : LeafRoundedFacts 8
    leaf1928Certificate.logOnePlusV leaf1928InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1928InputLogOnePlusV_eq }

private noncomputable def leaf1928Inputs : Inputs :=
  inputsOfCaches globalInput sk133RoundedInputs
    chi108InputQChi innerPair26Input
    leaf1928InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1928LowerChecked :
    lowerCheck 24 leaf1928Box leaf1928Inputs = true := by
  rfl'

private theorem leaf1928CoversExact : CoversExact 8
    leaf1928Box leaf1928Certificate leaf1928InnerLog leaf1928Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk133RoundedFacts chi108RoundedFacts
    innerPair26RoundedFacts leaf1928RoundedFacts (by rfl)

private theorem leaf1928FlatSound : Sound leaf1928Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1928CertificateValid
    leaf1928InnerLogValid leaf1928CoversExact leaf1928LowerChecked

private noncomputable def leaf1929Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (17/128), chiHi := (9/64) }

private noncomputable def leaf1929Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435687/268435456) }, vSqrt := { lower := (65529/65536), upper := (16777232/16776775) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (376464727/268435456) }, upper := { exponent := 0, mantissa := (1465/1024) } }, logOuter := sk134LogOuterCertificate, logK := sk134LogKCertificate, logChi := chi108LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (33554007/33553550) } }, logDArg := sk134LogDArgCertificate }

private noncomputable def leaf1929InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1929LocalValidity :
    LeafFacts leaf1929Box leaf1929Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1929Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (16777232/16776775) }) = true
      norm_num [leaf1929Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1929CertificateValid :
    WideCertificateValid leaf1929Box leaf1929Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk134ValidityFacts chi108ValidityFacts
    leaf1929LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1929CoverageChecked :
    coverageCheck (innerAD leaf1929Box) leaf1929InnerLog = true := by
  rfl'

private theorem leaf1929InnerLogValid :
    leaf1929InnerLog.Valid 8 (innerAD leaf1929Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1929CoverageChecked

private noncomputable def leaf1929InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629309/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1929InputLogOnePlusV_eq :
    leaf1929InputLogOnePlusV = outerEnclosure 24
      (leaf1929Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1929RoundedFacts : LeafRoundedFacts 8
    leaf1929Certificate.logOnePlusV leaf1929InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1929InputLogOnePlusV_eq }

private noncomputable def leaf1929Inputs : Inputs :=
  inputsOfCaches globalInput sk134RoundedInputs
    chi108InputQChi innerPair26Input
    leaf1929InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1929LowerChecked :
    lowerCheck 24 leaf1929Box leaf1929Inputs = true := by
  rfl'

private theorem leaf1929CoversExact : CoversExact 8
    leaf1929Box leaf1929Certificate leaf1929InnerLog leaf1929Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk134RoundedFacts chi108RoundedFacts
    innerPair26RoundedFacts leaf1929RoundedFacts (by rfl)

private theorem leaf1929FlatSound : Sound leaf1929Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1929CertificateValid
    leaf1929InnerLogValid leaf1929CoversExact leaf1929LowerChecked

private noncomputable def leaf1930Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (1/8), chiHi := (17/128) }

private noncomputable def leaf1930Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435687/268435456) }, vSqrt := { lower := (65529/65536), upper := (67108928/67107181) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (371156635/268435456) }, upper := { exponent := 0, mantissa := (5779/4096) } }, logOuter := sk135LogOuterCertificate, logK := sk135LogKCertificate, logChi := chi107LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (134216109/134214362) } }, logDArg := sk135LogDArgCertificate }

private noncomputable def leaf1930InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1930LocalValidity :
    LeafFacts leaf1930Box leaf1930Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1930Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (67108928/67107181) }) = true
      norm_num [leaf1930Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1930CertificateValid :
    WideCertificateValid leaf1930Box leaf1930Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk135ValidityFacts chi107ValidityFacts
    leaf1930LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1930CoverageChecked :
    coverageCheck (innerAD leaf1930Box) leaf1930InnerLog = true := by
  rfl'

private theorem leaf1930InnerLogValid :
    leaf1930InnerLog.Valid 8 (innerAD leaf1930Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1930CoverageChecked

private noncomputable def leaf1930InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629299/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1930InputLogOnePlusV_eq :
    leaf1930InputLogOnePlusV = outerEnclosure 24
      (leaf1930Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1930RoundedFacts : LeafRoundedFacts 8
    leaf1930Certificate.logOnePlusV leaf1930InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1930InputLogOnePlusV_eq }

private noncomputable def leaf1930Inputs : Inputs :=
  inputsOfCaches globalInput sk135RoundedInputs
    chi107InputQChi innerPair26Input
    leaf1930InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1930LowerChecked :
    lowerCheck 24 leaf1930Box leaf1930Inputs = true := by
  rfl'

private theorem leaf1930CoversExact : CoversExact 8
    leaf1930Box leaf1930Certificate leaf1930InnerLog leaf1930Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk135RoundedFacts chi107RoundedFacts
    innerPair26RoundedFacts leaf1930RoundedFacts (by rfl)

private theorem leaf1930FlatSound : Sound leaf1930Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1930CertificateValid
    leaf1930InnerLogValid leaf1930CoversExact leaf1930LowerChecked

private noncomputable def leaf1931Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (1/8), chiHi := (17/128) }

private noncomputable def leaf1931Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435689/268435456) }, vSqrt := { lower := (65529/65536), upper := (16777232/16776791) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (372205145/268435456) }, upper := { exponent := 0, mantissa := (1449/1024) } }, logOuter := sk136LogOuterCertificate, logK := sk136LogKCertificate, logChi := chi107LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (33554023/33553582) } }, logDArg := sk136LogDArgCertificate }

private noncomputable def leaf1931InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1931LocalValidity :
    LeafFacts leaf1931Box leaf1931Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1931Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (16777232/16776791) }) = true
      norm_num [leaf1931Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1931CertificateValid :
    WideCertificateValid leaf1931Box leaf1931Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk136ValidityFacts chi107ValidityFacts
    leaf1931LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1931CoverageChecked :
    coverageCheck (innerAD leaf1931Box) leaf1931InnerLog = true := by
  rfl'

private theorem leaf1931InnerLogValid :
    leaf1931InnerLog.Valid 8 (innerAD leaf1931Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1931CoverageChecked

private noncomputable def leaf1931InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629301/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1931InputLogOnePlusV_eq :
    leaf1931InputLogOnePlusV = outerEnclosure 24
      (leaf1931Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1931RoundedFacts : LeafRoundedFacts 8
    leaf1931Certificate.logOnePlusV leaf1931InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1931InputLogOnePlusV_eq }

private noncomputable def leaf1931Inputs : Inputs :=
  inputsOfCaches globalInput sk136RoundedInputs
    chi107InputQChi innerPair26Input
    leaf1931InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1931LowerChecked :
    lowerCheck 24 leaf1931Box leaf1931Inputs = true := by
  rfl'

private theorem leaf1931CoversExact : CoversExact 8
    leaf1931Box leaf1931Certificate leaf1931InnerLog leaf1931Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk136RoundedFacts chi107RoundedFacts
    innerPair26RoundedFacts leaf1931RoundedFacts (by rfl)

private theorem leaf1931FlatSound : Sound leaf1931Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1931CertificateValid
    leaf1931InnerLogValid leaf1931CoversExact leaf1931LowerChecked

private noncomputable def leaf1932Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (17/128), chiHi := (9/64) }

private noncomputable def leaf1932Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435689/268435456) }, vSqrt := { lower := (65529/65536), upper := (33554464/33553541) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (377578769/268435456) }, upper := { exponent := 0, mantissa := (2939/2048) } }, logOuter := sk135LogOuterCertificate, logK := sk135LogKCertificate, logChi := chi108LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (67108005/67107082) } }, logDArg := sk135LogDArgCertificate }

private noncomputable def leaf1932InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1932LocalValidity :
    LeafFacts leaf1932Box leaf1932Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1932Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (33554464/33553541) }) = true
      norm_num [leaf1932Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1932CertificateValid :
    WideCertificateValid leaf1932Box leaf1932Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk135ValidityFacts chi108ValidityFacts
    leaf1932LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1932CoverageChecked :
    coverageCheck (innerAD leaf1932Box) leaf1932InnerLog = true := by
  rfl'

private theorem leaf1932InnerLogValid :
    leaf1932InnerLog.Valid 8 (innerAD leaf1932Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1932CoverageChecked

private noncomputable def leaf1932InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629311/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1932InputLogOnePlusV_eq :
    leaf1932InputLogOnePlusV = outerEnclosure 24
      (leaf1932Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1932RoundedFacts : LeafRoundedFacts 8
    leaf1932Certificate.logOnePlusV leaf1932InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1932InputLogOnePlusV_eq }

private noncomputable def leaf1932Inputs : Inputs :=
  inputsOfCaches globalInput sk135RoundedInputs
    chi108InputQChi innerPair26Input
    leaf1932InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1932LowerChecked :
    lowerCheck 24 leaf1932Box leaf1932Inputs = true := by
  rfl'

private theorem leaf1932CoversExact : CoversExact 8
    leaf1932Box leaf1932Certificate leaf1932InnerLog leaf1932Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk135RoundedFacts chi108RoundedFacts
    innerPair26RoundedFacts leaf1932RoundedFacts (by rfl)

private theorem leaf1932FlatSound : Sound leaf1932Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1932CertificateValid
    leaf1932InnerLogValid leaf1932CoversExact leaf1932LowerChecked

private noncomputable def leaf1933Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (17/128), chiHi := (9/64) }

private noncomputable def leaf1933Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435691/268435456) }, vSqrt := { lower := (65529/65536), upper := (8388616/8388383) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (378692811/268435456) }, upper := { exponent := 0, mantissa := (737/512) } }, logOuter := sk136LogOuterCertificate, logK := sk136LogKCertificate, logChi := chi108LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (16776999/16776766) } }, logDArg := sk136LogDArgCertificate }

private noncomputable def leaf1933InnerLog : WideLogData :=
  innerPair395Data

set_option maxRecDepth 1000000 in
private theorem leaf1933LocalValidity :
    LeafFacts leaf1933Box leaf1933Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1933Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8388616/8388383) }) = true
      norm_num [leaf1933Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1933CertificateValid :
    WideCertificateValid leaf1933Box leaf1933Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk136ValidityFacts chi108ValidityFacts
    leaf1933LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1933CoverageChecked :
    coverageCheck (innerAD leaf1933Box) leaf1933InnerLog = true := by
  rfl'

private theorem leaf1933InnerLogValid :
    leaf1933InnerLog.Valid 8 (innerAD leaf1933Box) :=
  wideLogDataValid_of_cachedCheck endpoint107PositiveFacts
    endpoint109PositiveFacts.valid leaf1933CoverageChecked

private noncomputable def leaf1933InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814657/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1933InputLogOnePlusV_eq :
    leaf1933InputLogOnePlusV = outerEnclosure 24
      (leaf1933Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1933RoundedFacts : LeafRoundedFacts 8
    leaf1933Certificate.logOnePlusV leaf1933InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1933InputLogOnePlusV_eq }

private noncomputable def leaf1933Inputs : Inputs :=
  inputsOfCaches globalInput sk136RoundedInputs
    chi108InputQChi innerPair395Input
    leaf1933InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1933LowerChecked :
    lowerCheck 24 leaf1933Box leaf1933Inputs = true := by
  rfl'

private theorem leaf1933CoversExact : CoversExact 8
    leaf1933Box leaf1933Certificate leaf1933InnerLog leaf1933Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk136RoundedFacts chi108RoundedFacts
    innerPair395RoundedFacts leaf1933RoundedFacts (by rfl)

private theorem leaf1933FlatSound : Sound leaf1933Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1933CertificateValid
    leaf1933InnerLogValid leaf1933CoversExact leaf1933LowerChecked

private noncomputable def leaf1934Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (9/64), chiHi := (19/128) }

private noncomputable def leaf1934Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435687/268435456) }, vSqrt := { lower := (65529/65536), upper := (67108928/67107021) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (381641755/268435456) }, upper := { exponent := 0, mantissa := (5939/4096) } }, logOuter := sk133LogOuterCertificate, logK := sk133LogKCertificate, logChi := chi109LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (134215949/134214042) } }, logDArg := sk133LogDArgCertificate }

private noncomputable def leaf1934InnerLog : WideLogData :=
  innerPair144Data

set_option maxRecDepth 1000000 in
private theorem leaf1934LocalValidity :
    LeafFacts leaf1934Box leaf1934Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1934Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (67108928/67107021) }) = true
      norm_num [leaf1934Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1934CertificateValid :
    WideCertificateValid leaf1934Box leaf1934Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk133ValidityFacts chi109ValidityFacts
    leaf1934LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1934CoverageChecked :
    coverageCheck (innerAD leaf1934Box) leaf1934InnerLog = true := by
  rfl'

private theorem leaf1934InnerLogValid :
    leaf1934InnerLog.Valid 8 (innerAD leaf1934Box) :=
  wideLogDataValid_of_cachedCheck endpoint38PositiveFacts
    endpoint41PositiveFacts.valid leaf1934CoverageChecked

private noncomputable def leaf1934InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629319/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1934InputLogOnePlusV_eq :
    leaf1934InputLogOnePlusV = outerEnclosure 24
      (leaf1934Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1934RoundedFacts : LeafRoundedFacts 8
    leaf1934Certificate.logOnePlusV leaf1934InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1934InputLogOnePlusV_eq }

private noncomputable def leaf1934Inputs : Inputs :=
  inputsOfCaches globalInput sk133RoundedInputs
    chi109InputQChi innerPair144Input
    leaf1934InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1934LowerChecked :
    lowerCheck 24 leaf1934Box leaf1934Inputs = true := by
  rfl'

private theorem leaf1934CoversExact : CoversExact 8
    leaf1934Box leaf1934Certificate leaf1934InnerLog leaf1934Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk133RoundedFacts chi109RoundedFacts
    innerPair144RoundedFacts leaf1934RoundedFacts (by rfl)

private theorem leaf1934FlatSound : Sound leaf1934Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1934CertificateValid
    leaf1934InnerLogValid leaf1934CoversExact leaf1934LowerChecked

private noncomputable def leaf1935Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (9/64), chiHi := (19/128) }

private noncomputable def leaf1935Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435689/268435456) }, vSqrt := { lower := (65529/65536), upper := (33554464/33553501) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (382821329/268435456) }, upper := { exponent := 0, mantissa := (2979/2048) } }, logOuter := sk134LogOuterCertificate, logK := sk134LogKCertificate, logChi := chi109LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (67107965/67107002) } }, logDArg := sk134LogDArgCertificate }

private noncomputable def leaf1935InnerLog : WideLogData :=
  innerPair406Data

set_option maxRecDepth 1000000 in
private theorem leaf1935LocalValidity :
    LeafFacts leaf1935Box leaf1935Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1935Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (33554464/33553501) }) = true
      norm_num [leaf1935Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1935CertificateValid :
    WideCertificateValid leaf1935Box leaf1935Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk134ValidityFacts chi109ValidityFacts
    leaf1935LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1935CoverageChecked :
    coverageCheck (innerAD leaf1935Box) leaf1935InnerLog = true := by
  rfl'

private theorem leaf1935InnerLogValid :
    leaf1935InnerLog.Valid 8 (innerAD leaf1935Box) :=
  wideLogDataValid_of_cachedCheck endpoint119PositiveFacts
    endpoint42PositiveFacts.valid leaf1935CoverageChecked

private noncomputable def leaf1935InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629321/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1935InputLogOnePlusV_eq :
    leaf1935InputLogOnePlusV = outerEnclosure 24
      (leaf1935Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1935RoundedFacts : LeafRoundedFacts 8
    leaf1935Certificate.logOnePlusV leaf1935InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1935InputLogOnePlusV_eq }

private noncomputable def leaf1935Inputs : Inputs :=
  inputsOfCaches globalInput sk134RoundedInputs
    chi109InputQChi innerPair406Input
    leaf1935InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1935LowerChecked :
    lowerCheck 24 leaf1935Box leaf1935Inputs = true := by
  rfl'

private theorem leaf1935CoversExact : CoversExact 8
    leaf1935Box leaf1935Certificate leaf1935InnerLog leaf1935Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk134RoundedFacts chi109RoundedFacts
    innerPair406RoundedFacts leaf1935RoundedFacts (by rfl)

private theorem leaf1935FlatSound : Sound leaf1935Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1935CertificateValid
    leaf1935InnerLogValid leaf1935CoversExact leaf1935LowerChecked

private noncomputable def leaf1936Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (19/128), chiHi := (5/32) }

private noncomputable def leaf1936Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435689/268435456) }, vSqrt := { lower := (65529/65536), upper := (16777232/16776731) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (387932825/268435456) }, upper := { exponent := 0, mantissa := (1509/1024) } }, logOuter := sk133LogOuterCertificate, logK := sk133LogKCertificate, logChi := chi110LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (33553963/33553462) } }, logDArg := sk133LogDArgCertificate }

private noncomputable def leaf1936InnerLog : WideLogData :=
  innerPair38Data

set_option maxRecDepth 1000000 in
private theorem leaf1936LocalValidity :
    LeafFacts leaf1936Box leaf1936Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1936Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (16777232/16776731) }) = true
      norm_num [leaf1936Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1936CertificateValid :
    WideCertificateValid leaf1936Box leaf1936Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk133ValidityFacts chi110ValidityFacts
    leaf1936LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1936CoverageChecked :
    coverageCheck (innerAD leaf1936Box) leaf1936InnerLog = true := by
  rfl'

private theorem leaf1936InnerLogValid :
    leaf1936InnerLog.Valid 8 (innerAD leaf1936Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint120PositiveFacts.valid leaf1936CoverageChecked

private noncomputable def leaf1936InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629331/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1936InputLogOnePlusV_eq :
    leaf1936InputLogOnePlusV = outerEnclosure 24
      (leaf1936Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1936RoundedFacts : LeafRoundedFacts 8
    leaf1936Certificate.logOnePlusV leaf1936InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1936InputLogOnePlusV_eq }

private noncomputable def leaf1936Inputs : Inputs :=
  inputsOfCaches globalInput sk133RoundedInputs
    chi110InputQChi innerPair38Input
    leaf1936InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1936LowerChecked :
    lowerCheck 24 leaf1936Box leaf1936Inputs = true := by
  rfl'

private theorem leaf1936CoversExact : CoversExact 8
    leaf1936Box leaf1936Certificate leaf1936InnerLog leaf1936Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk133RoundedFacts chi110RoundedFacts
    innerPair38RoundedFacts leaf1936RoundedFacts (by rfl)

private theorem leaf1936FlatSound : Sound leaf1936Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1936CertificateValid
    leaf1936InnerLogValid leaf1936CoversExact leaf1936LowerChecked

private noncomputable def leaf1937Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (19/128), chiHi := (5/32) }

private noncomputable def leaf1937Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435691/268435456) }, vSqrt := { lower := (65529/65536), upper := (8388616/8388363) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (389177931/268435456) }, upper := { exponent := 0, mantissa := (757/512) } }, logOuter := sk134LogOuterCertificate, logK := sk134LogKCertificate, logChi := chi110LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (16776979/16776726) } }, logDArg := sk134LogDArgCertificate }

private noncomputable def leaf1937InnerLog : WideLogData :=
  innerPair446Data

set_option maxRecDepth 1000000 in
private theorem leaf1937LocalValidity :
    LeafFacts leaf1937Box leaf1937Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1937Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8388616/8388363) }) = true
      norm_num [leaf1937Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1937CertificateValid :
    WideCertificateValid leaf1937Box leaf1937Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk134ValidityFacts chi110ValidityFacts
    leaf1937LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1937CoverageChecked :
    coverageCheck (innerAD leaf1937Box) leaf1937InnerLog = true := by
  rfl'

private theorem leaf1937InnerLogValid :
    leaf1937InnerLog.Valid 8 (innerAD leaf1937Box) :=
  wideLogDataValid_of_cachedCheck endpoint161PositiveFacts
    endpoint111PositiveFacts.valid leaf1937CoverageChecked

private noncomputable def leaf1937InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814667/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1937InputLogOnePlusV_eq :
    leaf1937InputLogOnePlusV = outerEnclosure 24
      (leaf1937Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1937RoundedFacts : LeafRoundedFacts 8
    leaf1937Certificate.logOnePlusV leaf1937InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1937InputLogOnePlusV_eq }

private noncomputable def leaf1937Inputs : Inputs :=
  inputsOfCaches globalInput sk134RoundedInputs
    chi110InputQChi innerPair446Input
    leaf1937InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1937LowerChecked :
    lowerCheck 24 leaf1937Box leaf1937Inputs = true := by
  rfl'

private theorem leaf1937CoversExact : CoversExact 8
    leaf1937Box leaf1937Certificate leaf1937InnerLog leaf1937Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk134RoundedFacts chi110RoundedFacts
    innerPair446RoundedFacts leaf1937RoundedFacts (by rfl)

private theorem leaf1937FlatSound : Sound leaf1937Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1937CertificateValid
    leaf1937InnerLogValid leaf1937CoversExact leaf1937LowerChecked

private noncomputable def leaf1938Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (9/64), chiHi := (19/128) }

private noncomputable def leaf1938Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435691/268435456) }, vSqrt := { lower := (65529/65536), upper := (67108928/67106983) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (384000903/268435456) }, upper := { exponent := 0, mantissa := (5977/4096) } }, logOuter := sk135LogOuterCertificate, logK := sk135LogKCertificate, logChi := chi109LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (134215911/134213966) } }, logDArg := sk135LogDArgCertificate }

private noncomputable def leaf1938InnerLog : WideLogData :=
  innerPair443Data

set_option maxRecDepth 1000000 in
private theorem leaf1938LocalValidity :
    LeafFacts leaf1938Box leaf1938Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1938Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (67108928/67106983) }) = true
      norm_num [leaf1938Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1938CertificateValid :
    WideCertificateValid leaf1938Box leaf1938Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk135ValidityFacts chi109ValidityFacts
    leaf1938LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1938CoverageChecked :
    coverageCheck (innerAD leaf1938Box) leaf1938InnerLog = true := by
  rfl'

private theorem leaf1938InnerLogValid :
    leaf1938InnerLog.Valid 8 (innerAD leaf1938Box) :=
  wideLogDataValid_of_cachedCheck endpoint156PositiveFacts
    endpoint160PositiveFacts.valid leaf1938CoverageChecked

private noncomputable def leaf1938InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907331/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1938InputLogOnePlusV_eq :
    leaf1938InputLogOnePlusV = outerEnclosure 24
      (leaf1938Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1938RoundedFacts : LeafRoundedFacts 8
    leaf1938Certificate.logOnePlusV leaf1938InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1938InputLogOnePlusV_eq }

private noncomputable def leaf1938Inputs : Inputs :=
  inputsOfCaches globalInput sk135RoundedInputs
    chi109InputQChi innerPair443Input
    leaf1938InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1938LowerChecked :
    lowerCheck 24 leaf1938Box leaf1938Inputs = true := by
  rfl'

private theorem leaf1938CoversExact : CoversExact 8
    leaf1938Box leaf1938Certificate leaf1938InnerLog leaf1938Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk135RoundedFacts chi109RoundedFacts
    innerPair443RoundedFacts leaf1938RoundedFacts (by rfl)

private theorem leaf1938FlatSound : Sound leaf1938Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1938CertificateValid
    leaf1938InnerLogValid leaf1938CoversExact leaf1938LowerChecked

private noncomputable def leaf1939Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (9/64), chiHi := (37/256) }

private noncomputable def leaf1939Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871185/536870912) }, vSqrt := { lower := (65529/65536), upper := (33554464/33553507) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (770393921/536870912) }, upper := { exponent := 0, mantissa := (2973/2048) } }, logOuter := sk136LogOuterCertificate, logK := sk136LogKCertificate, logChi := chi175LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (67107971/67107014) } }, logDArg := sk136LogDArgCertificate }

private noncomputable def leaf1939InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf1939LocalValidity :
    LeafFacts leaf1939Box leaf1939Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1939Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (33554464/33553507) }) = true
      norm_num [leaf1939Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1939CertificateValid :
    WideCertificateValid leaf1939Box leaf1939Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk136ValidityFacts chi175ValidityFacts
    leaf1939LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1939CoverageChecked :
    coverageCheck (innerAD leaf1939Box) leaf1939InnerLog = true := by
  rfl'

private theorem leaf1939InnerLogValid :
    leaf1939InnerLog.Valid 8 (innerAD leaf1939Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf1939CoverageChecked

private noncomputable def leaf1939InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453665/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf1939InputLogOnePlusV_eq :
    leaf1939InputLogOnePlusV = outerEnclosure 24
      (leaf1939Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1939RoundedFacts : LeafRoundedFacts 8
    leaf1939Certificate.logOnePlusV leaf1939InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1939InputLogOnePlusV_eq }

private noncomputable def leaf1939Inputs : Inputs :=
  inputsOfCaches globalInput sk136RoundedInputs
    chi175InputQChi innerPair27Input
    leaf1939InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1939LowerChecked :
    lowerCheck 24 leaf1939Box leaf1939Inputs = true := by
  rfl'

private theorem leaf1939CoversExact : CoversExact 8
    leaf1939Box leaf1939Certificate leaf1939InnerLog leaf1939Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk136RoundedFacts chi175RoundedFacts
    innerPair27RoundedFacts leaf1939RoundedFacts (by rfl)

private theorem leaf1939FlatSound : Sound leaf1939Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1939CertificateValid
    leaf1939InnerLogValid leaf1939CoversExact leaf1939LowerChecked

private noncomputable def leaf1940Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (37/256), chiHi := (19/128) }

private noncomputable def leaf1940Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871187/536870912) }, vSqrt := { lower := (65529/65536), upper := (16777232/16776741) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (776881587/536870912) }, upper := { exponent := 0, mantissa := (1499/1024) } }, logOuter := sk136LogOuterCertificate, logK := sk136LogKCertificate, logChi := chi176LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (33553973/33553482) } }, logDArg := sk136LogDArgCertificate }

private noncomputable def leaf1940InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1940LocalValidity :
    LeafFacts leaf1940Box leaf1940Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1940Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (16777232/16776741) }) = true
      norm_num [leaf1940Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1940CertificateValid :
    WideCertificateValid leaf1940Box leaf1940Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk136ValidityFacts chi176ValidityFacts
    leaf1940LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1940CoverageChecked :
    coverageCheck (innerAD leaf1940Box) leaf1940InnerLog = true := by
  rfl'

private theorem leaf1940InnerLogValid :
    leaf1940InnerLog.Valid 8 (innerAD leaf1940Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1940CoverageChecked

private noncomputable def leaf1940InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814663/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1940InputLogOnePlusV_eq :
    leaf1940InputLogOnePlusV = outerEnclosure 24
      (leaf1940Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1940RoundedFacts : LeafRoundedFacts 8
    leaf1940Certificate.logOnePlusV leaf1940InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1940InputLogOnePlusV_eq }

private noncomputable def leaf1940Inputs : Inputs :=
  inputsOfCaches globalInput sk136RoundedInputs
    chi176InputQChi innerPair34Input
    leaf1940InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1940LowerChecked :
    lowerCheck 24 leaf1940Box leaf1940Inputs = true := by
  rfl'

private theorem leaf1940CoversExact : CoversExact 8
    leaf1940Box leaf1940Certificate leaf1940InnerLog leaf1940Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk136RoundedFacts chi176RoundedFacts
    innerPair34RoundedFacts leaf1940RoundedFacts (by rfl)

private theorem leaf1940FlatSound : Sound leaf1940Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1940CertificateValid
    leaf1940InnerLogValid leaf1940CoversExact leaf1940LowerChecked

private noncomputable def leaf1941Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (19/128), chiHi := (39/256) }

private noncomputable def leaf1941Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871187/536870912) }, vSqrt := { lower := (65529/65536), upper := (134217856/134213867) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (780879039/536870912) }, upper := { exponent := 0, mantissa := (12053/8192) } }, logOuter := sk135LogOuterCertificate, logK := sk135LogKCertificate, logChi := chi177LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (268431723/268427734) } }, logDArg := sk135LogDArgCertificate }

private noncomputable def leaf1941InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1941LocalValidity :
    LeafFacts leaf1941Box leaf1941Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1941Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (134217856/134213867) }) = true
      norm_num [leaf1941Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1941CertificateValid :
    WideCertificateValid leaf1941Box leaf1941Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk135ValidityFacts chi177ValidityFacts
    leaf1941LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1941CoverageChecked :
    coverageCheck (innerAD leaf1941Box) leaf1941InnerLog = true := by
  rfl'

private theorem leaf1941InnerLogValid :
    leaf1941InnerLog.Valid 8 (innerAD leaf1941Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1941CoverageChecked

private noncomputable def leaf1941InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814665/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1941InputLogOnePlusV_eq :
    leaf1941InputLogOnePlusV = outerEnclosure 24
      (leaf1941Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1941RoundedFacts : LeafRoundedFacts 8
    leaf1941Certificate.logOnePlusV leaf1941InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1941InputLogOnePlusV_eq }

private noncomputable def leaf1941Inputs : Inputs :=
  inputsOfCaches globalInput sk135RoundedInputs
    chi177InputQChi innerPair34Input
    leaf1941InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1941LowerChecked :
    lowerCheck 24 leaf1941Box leaf1941Inputs = true := by
  rfl'

private theorem leaf1941CoversExact : CoversExact 8
    leaf1941Box leaf1941Certificate leaf1941InnerLog leaf1941Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk135RoundedFacts chi177RoundedFacts
    innerPair34RoundedFacts leaf1941RoundedFacts (by rfl)

private theorem leaf1941FlatSound : Sound leaf1941Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1941CertificateValid
    leaf1941InnerLogValid leaf1941CoversExact leaf1941LowerChecked

private noncomputable def leaf1942Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (39/256), chiHi := (5/32) }

private noncomputable def leaf1942Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871189/536870912) }, vSqrt := { lower := (65529/65536), upper := (16777232/16776721) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (787301173/536870912) }, upper := { exponent := 0, mantissa := (1519/1024) } }, logOuter := sk135LogOuterCertificate, logK := sk135LogKCertificate, logChi := chi178LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (33553953/33553442) } }, logDArg := sk135LogDArgCertificate }

private noncomputable def leaf1942InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1942LocalValidity :
    LeafFacts leaf1942Box leaf1942Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1942Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (16777232/16776721) }) = true
      norm_num [leaf1942Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1942CertificateValid :
    WideCertificateValid leaf1942Box leaf1942Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk135ValidityFacts chi178ValidityFacts
    leaf1942LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1942CoverageChecked :
    coverageCheck (innerAD leaf1942Box) leaf1942InnerLog = true := by
  rfl'

private theorem leaf1942InnerLogValid :
    leaf1942InnerLog.Valid 8 (innerAD leaf1942Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1942CoverageChecked

private noncomputable def leaf1942InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453667/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf1942InputLogOnePlusV_eq :
    leaf1942InputLogOnePlusV = outerEnclosure 24
      (leaf1942Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1942RoundedFacts : LeafRoundedFacts 8
    leaf1942Certificate.logOnePlusV leaf1942InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1942InputLogOnePlusV_eq }

private noncomputable def leaf1942Inputs : Inputs :=
  inputsOfCaches globalInput sk135RoundedInputs
    chi178InputQChi innerPair34Input
    leaf1942InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1942LowerChecked :
    lowerCheck 24 leaf1942Box leaf1942Inputs = true := by
  rfl'

private theorem leaf1942CoversExact : CoversExact 8
    leaf1942Box leaf1942Certificate leaf1942InnerLog leaf1942Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk135RoundedFacts chi178RoundedFacts
    innerPair34RoundedFacts leaf1942RoundedFacts (by rfl)

private theorem leaf1942FlatSound : Sound leaf1942Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1942CertificateValid
    leaf1942InnerLogValid leaf1942CoversExact leaf1942LowerChecked

private noncomputable def leaf1943Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (19/128), chiHi := (39/256) }

private noncomputable def leaf1943Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871189/536870912) }, vSqrt := { lower := (65529/65536), upper := (33554464/33553457) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (783369253/536870912) }, upper := { exponent := 0, mantissa := (3023/2048) } }, logOuter := sk136LogOuterCertificate, logK := sk136LogKCertificate, logChi := chi177LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (67107921/67106914) } }, logDArg := sk136LogDArgCertificate }

private noncomputable def leaf1943InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1943LocalValidity :
    LeafFacts leaf1943Box leaf1943Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1943Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (33554464/33553457) }) = true
      norm_num [leaf1943Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1943CertificateValid :
    WideCertificateValid leaf1943Box leaf1943Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk136ValidityFacts chi177ValidityFacts
    leaf1943LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1943CoverageChecked :
    coverageCheck (innerAD leaf1943Box) leaf1943InnerLog = true := by
  rfl'

private theorem leaf1943InnerLogValid :
    leaf1943InnerLog.Valid 8 (innerAD leaf1943Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1943CoverageChecked

private noncomputable def leaf1943InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907333/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1943InputLogOnePlusV_eq :
    leaf1943InputLogOnePlusV = outerEnclosure 24
      (leaf1943Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1943RoundedFacts : LeafRoundedFacts 8
    leaf1943Certificate.logOnePlusV leaf1943InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1943InputLogOnePlusV_eq }

private noncomputable def leaf1943Inputs : Inputs :=
  inputsOfCaches globalInput sk136RoundedInputs
    chi177InputQChi innerPair34Input
    leaf1943InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1943LowerChecked :
    lowerCheck 24 leaf1943Box leaf1943Inputs = true := by
  rfl'

private theorem leaf1943CoversExact : CoversExact 8
    leaf1943Box leaf1943Certificate leaf1943InnerLog leaf1943Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk136RoundedFacts chi177RoundedFacts
    innerPair34RoundedFacts leaf1943RoundedFacts (by rfl)

private theorem leaf1943FlatSound : Sound leaf1943Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1943CertificateValid
    leaf1943InnerLogValid leaf1943CoversExact leaf1943LowerChecked

private noncomputable def leaf1944Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (39/256), chiHi := (5/32) }

private noncomputable def leaf1944Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871191/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717428736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (789856919/536870912) }, upper := { exponent := 0, mantissa := (381/256) } }, logOuter := sk136LogOuterCertificate, logK := sk136LogKCertificate, logChi := chi178LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435922431/137434857472) } }, logDArg := sk136LogDArgCertificate }

private noncomputable def leaf1944InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1944LocalValidity :
    LeafFacts leaf1944Box leaf1944Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1944Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717428736) }) = true
      norm_num [leaf1944Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1944CertificateValid :
    WideCertificateValid leaf1944Box leaf1944Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk136ValidityFacts chi178ValidityFacts
    leaf1944LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1944CoverageChecked :
    coverageCheck (innerAD leaf1944Box) leaf1944InnerLog = true := by
  rfl'

private theorem leaf1944InnerLogValid :
    leaf1944InnerLog.Valid 8 (innerAD leaf1944Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1944CoverageChecked

private noncomputable def leaf1944InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629211/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1944InputLogOnePlusV_eq :
    leaf1944InputLogOnePlusV = outerEnclosure 24
      (leaf1944Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1944RoundedFacts : LeafRoundedFacts 8
    leaf1944Certificate.logOnePlusV leaf1944InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1944InputLogOnePlusV_eq }

private noncomputable def leaf1944Inputs : Inputs :=
  inputsOfCaches globalInput sk136RoundedInputs
    chi178InputQChi innerPair34Input
    leaf1944InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1944LowerChecked :
    lowerCheck 24 leaf1944Box leaf1944Inputs = true := by
  rfl'

private theorem leaf1944CoversExact : CoversExact 8
    leaf1944Box leaf1944Certificate leaf1944InnerLog leaf1944Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk136RoundedFacts chi178RoundedFacts
    innerPair34RoundedFacts leaf1944RoundedFacts (by rfl)

private theorem leaf1944FlatSound : Sound leaf1944Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1944CertificateValid
    leaf1944InnerLogValid leaf1944CoversExact leaf1944LowerChecked

private noncomputable def leaf1945Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (1/8), chiHi := (17/128) }

private noncomputable def leaf1945Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435691/268435456) }, vSqrt := { lower := (65529/65536), upper := (67108928/67107147) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (373253655/268435456) }, upper := { exponent := 0, mantissa := (5813/4096) } }, logOuter := sk137LogOuterCertificate, logK := sk137LogKCertificate, logChi := chi107LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (134216075/134214294) } }, logDArg := sk137LogDArgCertificate }

private noncomputable def leaf1945InnerLog : WideLogData :=
  innerPair30Data

set_option maxRecDepth 1000000 in
private theorem leaf1945LocalValidity :
    LeafFacts leaf1945Box leaf1945Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1945Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (67108928/67107147) }) = true
      norm_num [leaf1945Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1945CertificateValid :
    WideCertificateValid leaf1945Box leaf1945Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk137ValidityFacts chi107ValidityFacts
    leaf1945LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1945CoverageChecked :
    coverageCheck (innerAD leaf1945Box) leaf1945InnerLog = true := by
  rfl'

private theorem leaf1945InnerLogValid :
    leaf1945InnerLog.Valid 8 (innerAD leaf1945Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint119PositiveFacts.valid leaf1945CoverageChecked

private noncomputable def leaf1945InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629303/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1945InputLogOnePlusV_eq :
    leaf1945InputLogOnePlusV = outerEnclosure 24
      (leaf1945Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1945RoundedFacts : LeafRoundedFacts 8
    leaf1945Certificate.logOnePlusV leaf1945InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1945InputLogOnePlusV_eq }

private noncomputable def leaf1945Inputs : Inputs :=
  inputsOfCaches globalInput sk137RoundedInputs
    chi107InputQChi innerPair30Input
    leaf1945InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1945LowerChecked :
    lowerCheck 24 leaf1945Box leaf1945Inputs = true := by
  rfl'

private theorem leaf1945CoversExact : CoversExact 8
    leaf1945Box leaf1945Certificate leaf1945InnerLog leaf1945Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk137RoundedFacts chi107RoundedFacts
    innerPair30RoundedFacts leaf1945RoundedFacts (by rfl)

private theorem leaf1945FlatSound : Sound leaf1945Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1945CertificateValid
    leaf1945InnerLogValid leaf1945CoversExact leaf1945LowerChecked

private noncomputable def leaf1946Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (1/8), chiHi := (17/128) }

private noncomputable def leaf1946Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435693/268435456) }, vSqrt := { lower := (65529/65536), upper := (33554464/33553565) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (374302165/268435456) }, upper := { exponent := 0, mantissa := (2915/2048) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi107LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (67108029/67107130) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf1946InnerLog : WideLogData :=
  innerPair137Data

set_option maxRecDepth 1000000 in
private theorem leaf1946LocalValidity :
    LeafFacts leaf1946Box leaf1946Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1946Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (33554464/33553565) }) = true
      norm_num [leaf1946Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1946CertificateValid :
    WideCertificateValid leaf1946Box leaf1946Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi107ValidityFacts
    leaf1946LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1946CoverageChecked :
    coverageCheck (innerAD leaf1946Box) leaf1946InnerLog = true := by
  rfl'

private theorem leaf1946InnerLogValid :
    leaf1946InnerLog.Valid 8 (innerAD leaf1946Box) :=
  wideLogDataValid_of_cachedCheck endpoint34PositiveFacts
    endpoint40PositiveFacts.valid leaf1946CoverageChecked

private noncomputable def leaf1946InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629305/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1946InputLogOnePlusV_eq :
    leaf1946InputLogOnePlusV = outerEnclosure 24
      (leaf1946Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1946RoundedFacts : LeafRoundedFacts 8
    leaf1946Certificate.logOnePlusV leaf1946InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1946InputLogOnePlusV_eq }

private noncomputable def leaf1946Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi107InputQChi innerPair137Input
    leaf1946InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1946LowerChecked :
    lowerCheck 24 leaf1946Box leaf1946Inputs = true := by
  rfl'

private theorem leaf1946CoversExact : CoversExact 8
    leaf1946Box leaf1946Certificate leaf1946InnerLog leaf1946Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi107RoundedFacts
    innerPair137RoundedFacts leaf1946RoundedFacts (by rfl)

private theorem leaf1946FlatSound : Sound leaf1946Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1946CertificateValid
    leaf1946InnerLogValid leaf1946CoversExact leaf1946LowerChecked

private noncomputable def leaf1947Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (17/128), chiHi := (9/64) }

private noncomputable def leaf1947Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435693/268435456) }, vSqrt := { lower := (65529/65536), upper := (33554464/33553523) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (379806853/268435456) }, upper := { exponent := 0, mantissa := (2957/2048) } }, logOuter := sk137LogOuterCertificate, logK := sk137LogKCertificate, logChi := chi108LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (67107987/67107046) } }, logDArg := sk137LogDArgCertificate }

private noncomputable def leaf1947InnerLog : WideLogData :=
  innerPair448Data

set_option maxRecDepth 1000000 in
private theorem leaf1947LocalValidity :
    LeafFacts leaf1947Box leaf1947Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1947Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (33554464/33553523) }) = true
      norm_num [leaf1947Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1947CertificateValid :
    WideCertificateValid leaf1947Box leaf1947Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk137ValidityFacts chi108ValidityFacts
    leaf1947LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1947CoverageChecked :
    coverageCheck (innerAD leaf1947Box) leaf1947InnerLog = true := by
  rfl'

private theorem leaf1947InnerLogValid :
    leaf1947InnerLog.Valid 8 (innerAD leaf1947Box) :=
  wideLogDataValid_of_cachedCheck endpoint162PositiveFacts
    endpoint163PositiveFacts.valid leaf1947CoverageChecked

private noncomputable def leaf1947InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907329/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1947InputLogOnePlusV_eq :
    leaf1947InputLogOnePlusV = outerEnclosure 24
      (leaf1947Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1947RoundedFacts : LeafRoundedFacts 8
    leaf1947Certificate.logOnePlusV leaf1947InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1947InputLogOnePlusV_eq }

private noncomputable def leaf1947Inputs : Inputs :=
  inputsOfCaches globalInput sk137RoundedInputs
    chi108InputQChi innerPair448Input
    leaf1947InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1947LowerChecked :
    lowerCheck 24 leaf1947Box leaf1947Inputs = true := by
  rfl'

private theorem leaf1947CoversExact : CoversExact 8
    leaf1947Box leaf1947Certificate leaf1947InnerLog leaf1947Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk137RoundedFacts chi108RoundedFacts
    innerPair448RoundedFacts leaf1947RoundedFacts (by rfl)

private theorem leaf1947FlatSound : Sound leaf1947Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1947CertificateValid
    leaf1947InnerLogValid leaf1947CoversExact leaf1947LowerChecked

private noncomputable def leaf1948Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (17/128), chiHi := (35/256) }

private noncomputable def leaf1948Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871185/536870912) }, vSqrt := { lower := (65529/65536), upper := (67108928/67107079) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (761874761/536870912) }, upper := { exponent := 0, mantissa := (5881/4096) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi179LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (134216007/134214158) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf1948InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1948LocalValidity :
    LeafFacts leaf1948Box leaf1948Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1948Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (67108928/67107079) }) = true
      norm_num [leaf1948Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1948CertificateValid :
    WideCertificateValid leaf1948Box leaf1948Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi179ValidityFacts
    leaf1948LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1948CoverageChecked :
    coverageCheck (innerAD leaf1948Box) leaf1948InnerLog = true := by
  rfl'

private theorem leaf1948InnerLogValid :
    leaf1948InnerLog.Valid 8 (innerAD leaf1948Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1948CoverageChecked

private noncomputable def leaf1948InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (45427/65536) }

set_option maxRecDepth 1000000 in
private theorem leaf1948InputLogOnePlusV_eq :
    leaf1948InputLogOnePlusV = outerEnclosure 24
      (leaf1948Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1948RoundedFacts : LeafRoundedFacts 8
    leaf1948Certificate.logOnePlusV leaf1948InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1948InputLogOnePlusV_eq }

private noncomputable def leaf1948Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi179InputQChi innerPair26Input
    leaf1948InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1948LowerChecked :
    lowerCheck 24 leaf1948Box leaf1948Inputs = true := by
  rfl'

private theorem leaf1948CoversExact : CoversExact 8
    leaf1948Box leaf1948Certificate leaf1948InnerLog leaf1948Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi179RoundedFacts
    innerPair26RoundedFacts leaf1948RoundedFacts (by rfl)

private theorem leaf1948FlatSound : Sound leaf1948Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1948CertificateValid
    leaf1948InnerLogValid leaf1948CoversExact leaf1948LowerChecked

private noncomputable def leaf1949Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (35/256), chiHi := (9/64) }

private noncomputable def leaf1949Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871187/536870912) }, vSqrt := { lower := (65529/65536), upper := (16777232/16776757) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (768493491/536870912) }, upper := { exponent := 0, mantissa := (1483/1024) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi180LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (33553989/33553514) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf1949InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf1949LocalValidity :
    LeafFacts leaf1949Box leaf1949Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1949Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (16777232/16776757) }) = true
      norm_num [leaf1949Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1949CertificateValid :
    WideCertificateValid leaf1949Box leaf1949Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi180ValidityFacts
    leaf1949LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1949CoverageChecked :
    coverageCheck (innerAD leaf1949Box) leaf1949InnerLog = true := by
  rfl'

private theorem leaf1949InnerLogValid :
    leaf1949InnerLog.Valid 8 (innerAD leaf1949Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf1949CoverageChecked

private noncomputable def leaf1949InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814659/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1949InputLogOnePlusV_eq :
    leaf1949InputLogOnePlusV = outerEnclosure 24
      (leaf1949Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1949RoundedFacts : LeafRoundedFacts 8
    leaf1949Certificate.logOnePlusV leaf1949InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1949InputLogOnePlusV_eq }

private noncomputable def leaf1949Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi180InputQChi innerPair27Input
    leaf1949InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1949LowerChecked :
    lowerCheck 24 leaf1949Box leaf1949Inputs = true := by
  rfl'

private theorem leaf1949CoversExact : CoversExact 8
    leaf1949Box leaf1949Certificate leaf1949InnerLog leaf1949Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi180RoundedFacts
    innerPair27RoundedFacts leaf1949RoundedFacts (by rfl)

private theorem leaf1949FlatSound : Sound leaf1949Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1949CertificateValid
    leaf1949InnerLogValid leaf1949CoversExact leaf1949LowerChecked

private noncomputable def leaf1950Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (1/8), chiHi := (33/256) }

private noncomputable def leaf1950Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871183/536870912) }, vSqrt := { lower := (65529/65536), upper := (134217856/134214329) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (750734323/536870912) }, upper := { exponent := 0, mantissa := (11591/8192) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi181LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (268432185/268428658) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf1950InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1950LocalValidity :
    LeafFacts leaf1950Box leaf1950Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1950Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (134217856/134214329) }) = true
      norm_num [leaf1950Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1950CertificateValid :
    WideCertificateValid leaf1950Box leaf1950Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi181ValidityFacts
    leaf1950LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1950CoverageChecked :
    coverageCheck (innerAD leaf1950Box) leaf1950InnerLog = true := by
  rfl'

private theorem leaf1950InnerLogValid :
    leaf1950InnerLog.Valid 8 (innerAD leaf1950Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1950CoverageChecked

private noncomputable def leaf1950InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629301/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1950InputLogOnePlusV_eq :
    leaf1950InputLogOnePlusV = outerEnclosure 24
      (leaf1950Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1950RoundedFacts : LeafRoundedFacts 8
    leaf1950Certificate.logOnePlusV leaf1950InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1950InputLogOnePlusV_eq }

private noncomputable def leaf1950Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi181InputQChi innerPair26Input
    leaf1950InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1950LowerChecked :
    lowerCheck 24 leaf1950Box leaf1950Inputs = true := by
  rfl'

private theorem leaf1950CoversExact : CoversExact 8
    leaf1950Box leaf1950Certificate leaf1950InnerLog leaf1950Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi181RoundedFacts
    innerPair26RoundedFacts leaf1950RoundedFacts (by rfl)

private theorem leaf1950FlatSound : Sound leaf1950Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1950CertificateValid
    leaf1950InnerLogValid leaf1950CoversExact leaf1950LowerChecked

private noncomputable def leaf1951Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (33/256), chiHi := (17/128) }

private noncomputable def leaf1951Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871185/536870912) }, vSqrt := { lower := (65529/65536), upper := (67108928/67107113) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (757418585/536870912) }, upper := { exponent := 0, mantissa := (5847/4096) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi182LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (134216041/134214226) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf1951InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1951LocalValidity :
    LeafFacts leaf1951Box leaf1951Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1951Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (67108928/67107113) }) = true
      norm_num [leaf1951Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1951CertificateValid :
    WideCertificateValid leaf1951Box leaf1951Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi182ValidityFacts
    leaf1951LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1951CoverageChecked :
    coverageCheck (innerAD leaf1951Box) leaf1951InnerLog = true := by
  rfl'

private theorem leaf1951InnerLogValid :
    leaf1951InnerLog.Valid 8 (innerAD leaf1951Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1951CoverageChecked

private noncomputable def leaf1951InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907327/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1951InputLogOnePlusV_eq :
    leaf1951InputLogOnePlusV = outerEnclosure 24
      (leaf1951Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1951RoundedFacts : LeafRoundedFacts 8
    leaf1951Certificate.logOnePlusV leaf1951InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1951InputLogOnePlusV_eq }

private noncomputable def leaf1951Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi182InputQChi innerPair26Input
    leaf1951InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1951LowerChecked :
    lowerCheck 24 leaf1951Box leaf1951Inputs = true := by
  rfl'

private theorem leaf1951CoversExact : CoversExact 8
    leaf1951Box leaf1951Certificate leaf1951InnerLog leaf1951Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi182RoundedFacts
    innerPair26RoundedFacts leaf1951RoundedFacts (by rfl)

private theorem leaf1951FlatSound : Sound leaf1951Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1951CertificateValid
    leaf1951InnerLogValid leaf1951CoversExact leaf1951LowerChecked

private noncomputable def leaf1952Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (1/8), chiHi := (33/256) }

private noncomputable def leaf1952Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871185/536870912) }, vSqrt := { lower := (65529/65536), upper := (16777232/16776787) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (752831345/536870912) }, upper := { exponent := 0, mantissa := (1453/1024) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi181LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (33554019/33553574) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf1952InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1952LocalValidity :
    LeafFacts leaf1952Box leaf1952Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1952Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (16777232/16776787) }) = true
      norm_num [leaf1952Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1952CertificateValid :
    WideCertificateValid leaf1952Box leaf1952Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi181ValidityFacts
    leaf1952LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1952CoverageChecked :
    coverageCheck (innerAD leaf1952Box) leaf1952InnerLog = true := by
  rfl'

private theorem leaf1952InnerLogValid :
    leaf1952InnerLog.Valid 8 (innerAD leaf1952Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1952CoverageChecked

private noncomputable def leaf1952InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629303/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1952InputLogOnePlusV_eq :
    leaf1952InputLogOnePlusV = outerEnclosure 24
      (leaf1952Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1952RoundedFacts : LeafRoundedFacts 8
    leaf1952Certificate.logOnePlusV leaf1952InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1952InputLogOnePlusV_eq }

private noncomputable def leaf1952Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi181InputQChi innerPair26Input
    leaf1952InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1952LowerChecked :
    lowerCheck 24 leaf1952Box leaf1952Inputs = true := by
  rfl'

private theorem leaf1952CoversExact : CoversExact 8
    leaf1952Box leaf1952Certificate leaf1952InnerLog leaf1952Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi181RoundedFacts
    innerPair26RoundedFacts leaf1952RoundedFacts (by rfl)

private theorem leaf1952FlatSound : Sound leaf1952Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1952CertificateValid
    leaf1952InnerLogValid leaf1952CoversExact leaf1952LowerChecked

private noncomputable def leaf1953Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (33/256), chiHi := (17/128) }

private noncomputable def leaf1953Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871187/536870912) }, vSqrt := { lower := (65529/65536), upper := (8388616/8388387) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (759581139/536870912) }, upper := { exponent := 0, mantissa := (733/512) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi182LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (16777003/16776774) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf1953InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1953LocalValidity :
    LeafFacts leaf1953Box leaf1953Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1953Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8388616/8388387) }) = true
      norm_num [leaf1953Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1953CertificateValid :
    WideCertificateValid leaf1953Box leaf1953Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi182ValidityFacts
    leaf1953LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1953CoverageChecked :
    coverageCheck (innerAD leaf1953Box) leaf1953InnerLog = true := by
  rfl'

private theorem leaf1953InnerLogValid :
    leaf1953InnerLog.Valid 8 (innerAD leaf1953Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1953CoverageChecked

private noncomputable def leaf1953InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814655/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1953InputLogOnePlusV_eq :
    leaf1953InputLogOnePlusV = outerEnclosure 24
      (leaf1953Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1953RoundedFacts : LeafRoundedFacts 8
    leaf1953Certificate.logOnePlusV leaf1953InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1953InputLogOnePlusV_eq }

private noncomputable def leaf1953Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi182InputQChi innerPair26Input
    leaf1953InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1953LowerChecked :
    lowerCheck 24 leaf1953Box leaf1953Inputs = true := by
  rfl'

private theorem leaf1953CoversExact : CoversExact 8
    leaf1953Box leaf1953Certificate leaf1953InnerLog leaf1953Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi182RoundedFacts
    innerPair26RoundedFacts leaf1953RoundedFacts (by rfl)

private theorem leaf1953FlatSound : Sound leaf1953Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1953CertificateValid
    leaf1953InnerLogValid leaf1953CoversExact leaf1953LowerChecked

private noncomputable def leaf1954Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (17/128), chiHi := (35/256) }

private noncomputable def leaf1954Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871187/536870912) }, vSqrt := { lower := (65529/65536), upper := (134217856/134214123) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (764102847/536870912) }, upper := { exponent := 0, mantissa := (11797/8192) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi179LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (268431979/268428246) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf1954InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf1954LocalValidity :
    LeafFacts leaf1954Box leaf1954Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1954Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (134217856/134214123) }) = true
      norm_num [leaf1954Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1954CertificateValid :
    WideCertificateValid leaf1954Box leaf1954Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi179ValidityFacts
    leaf1954LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1954CoverageChecked :
    coverageCheck (innerAD leaf1954Box) leaf1954InnerLog = true := by
  rfl'

private theorem leaf1954InnerLogValid :
    leaf1954InnerLog.Valid 8 (innerAD leaf1954Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf1954CoverageChecked

private noncomputable def leaf1954InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814657/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1954InputLogOnePlusV_eq :
    leaf1954InputLogOnePlusV = outerEnclosure 24
      (leaf1954Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1954RoundedFacts : LeafRoundedFacts 8
    leaf1954Certificate.logOnePlusV leaf1954InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1954InputLogOnePlusV_eq }

private noncomputable def leaf1954Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi179InputQChi innerPair27Input
    leaf1954InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1954LowerChecked :
    lowerCheck 24 leaf1954Box leaf1954Inputs = true := by
  rfl'

private theorem leaf1954CoversExact : CoversExact 8
    leaf1954Box leaf1954Certificate leaf1954InnerLog leaf1954Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi179RoundedFacts
    innerPair27RoundedFacts leaf1954RoundedFacts (by rfl)

private theorem leaf1954FlatSound : Sound leaf1954Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1954CertificateValid
    leaf1954InnerLogValid leaf1954CoversExact leaf1954LowerChecked

private noncomputable def leaf1955Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (35/256), chiHi := (9/64) }

private noncomputable def leaf1955Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871189/536870912) }, vSqrt := { lower := (65529/65536), upper := (33554464/33553505) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (770787109/536870912) }, upper := { exponent := 0, mantissa := (2975/2048) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi180LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (67107969/67107010) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf1955InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf1955LocalValidity :
    LeafFacts leaf1955Box leaf1955Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1955Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (33554464/33553505) }) = true
      norm_num [leaf1955Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1955CertificateValid :
    WideCertificateValid leaf1955Box leaf1955Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi180ValidityFacts
    leaf1955LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1955CoverageChecked :
    coverageCheck (innerAD leaf1955Box) leaf1955InnerLog = true := by
  rfl'

private theorem leaf1955InnerLogValid :
    leaf1955InnerLog.Valid 8 (innerAD leaf1955Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf1955CoverageChecked

private noncomputable def leaf1955InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453665/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf1955InputLogOnePlusV_eq :
    leaf1955InputLogOnePlusV = outerEnclosure 24
      (leaf1955Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1955RoundedFacts : LeafRoundedFacts 8
    leaf1955Certificate.logOnePlusV leaf1955InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1955InputLogOnePlusV_eq }

private noncomputable def leaf1955Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi180InputQChi innerPair27Input
    leaf1955InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1955LowerChecked :
    lowerCheck 24 leaf1955Box leaf1955Inputs = true := by
  rfl'

private theorem leaf1955CoversExact : CoversExact 8
    leaf1955Box leaf1955Certificate leaf1955InnerLog leaf1955Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi180RoundedFacts
    innerPair27RoundedFacts leaf1955RoundedFacts (by rfl)

private theorem leaf1955FlatSound : Sound leaf1955Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1955CertificateValid
    leaf1955InnerLogValid leaf1955CoversExact leaf1955LowerChecked

private noncomputable def leaf1956Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (17/128), chiHi := (35/256) }

private noncomputable def leaf1956Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871189/536870912) }, vSqrt := { lower := (65529/65536), upper := (16777232/16776761) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (766330933/536870912) }, upper := { exponent := 0, mantissa := (1479/1024) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi179LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (33553993/33553522) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf1956InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf1956LocalValidity :
    LeafFacts leaf1956Box leaf1956Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1956Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (16777232/16776761) }) = true
      norm_num [leaf1956Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1956CertificateValid :
    WideCertificateValid leaf1956Box leaf1956Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi179ValidityFacts
    leaf1956LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1956CoverageChecked :
    coverageCheck (innerAD leaf1956Box) leaf1956InnerLog = true := by
  rfl'

private theorem leaf1956InnerLogValid :
    leaf1956InnerLog.Valid 8 (innerAD leaf1956Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf1956CoverageChecked

private noncomputable def leaf1956InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907329/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1956InputLogOnePlusV_eq :
    leaf1956InputLogOnePlusV = outerEnclosure 24
      (leaf1956Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1956RoundedFacts : LeafRoundedFacts 8
    leaf1956Certificate.logOnePlusV leaf1956InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1956InputLogOnePlusV_eq }

private noncomputable def leaf1956Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi179InputQChi innerPair27Input
    leaf1956InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1956LowerChecked :
    lowerCheck 24 leaf1956Box leaf1956Inputs = true := by
  rfl'

private theorem leaf1956CoversExact : CoversExact 8
    leaf1956Box leaf1956Certificate leaf1956InnerLog leaf1956Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi179RoundedFacts
    innerPair27RoundedFacts leaf1956RoundedFacts (by rfl)

private theorem leaf1956FlatSound : Sound leaf1956Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1956CertificateValid
    leaf1956InnerLogValid leaf1956CoversExact leaf1956LowerChecked

private noncomputable def leaf1957Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (35/256), chiHi := (9/64) }

private noncomputable def leaf1957Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871191/536870912) }, vSqrt := { lower := (65529/65536), upper := (4194308/4194187) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (773080727/536870912) }, upper := { exponent := 0, mantissa := (373/256) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi180LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (8388495/8388374) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf1957InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1957LocalValidity :
    LeafFacts leaf1957Box leaf1957Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1957Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4194308/4194187) }) = true
      norm_num [leaf1957Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1957CertificateValid :
    WideCertificateValid leaf1957Box leaf1957Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi180ValidityFacts
    leaf1957LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1957CoverageChecked :
    coverageCheck (innerAD leaf1957Box) leaf1957InnerLog = true := by
  rfl'

private theorem leaf1957InnerLogValid :
    leaf1957InnerLog.Valid 8 (innerAD leaf1957Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1957CoverageChecked

private noncomputable def leaf1957InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629323/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1957InputLogOnePlusV_eq :
    leaf1957InputLogOnePlusV = outerEnclosure 24
      (leaf1957Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1957RoundedFacts : LeafRoundedFacts 8
    leaf1957Certificate.logOnePlusV leaf1957InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1957InputLogOnePlusV_eq }

private noncomputable def leaf1957Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi180InputQChi innerPair34Input
    leaf1957InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1957LowerChecked :
    lowerCheck 24 leaf1957Box leaf1957Inputs = true := by
  rfl'

private theorem leaf1957CoversExact : CoversExact 8
    leaf1957Box leaf1957Certificate leaf1957InnerLog leaf1957Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi180RoundedFacts
    innerPair34RoundedFacts leaf1957RoundedFacts (by rfl)

private theorem leaf1957FlatSound : Sound leaf1957Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1957CertificateValid
    leaf1957InnerLogValid leaf1957CoversExact leaf1957LowerChecked

private noncomputable def leaf1958Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (9/64), chiHi := (37/256) }

private noncomputable def leaf1958Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871187/536870912) }, vSqrt := { lower := (65529/65536), upper := (134217856/134213991) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (772753071/536870912) }, upper := { exponent := 0, mantissa := (11929/8192) } }, logOuter := sk137LogOuterCertificate, logK := sk137LogKCertificate, logChi := chi175LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (268431847/268427982) } }, logDArg := sk137LogDArgCertificate }

private noncomputable def leaf1958InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1958LocalValidity :
    LeafFacts leaf1958Box leaf1958Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1958Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (134217856/134213991) }) = true
      norm_num [leaf1958Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1958CertificateValid :
    WideCertificateValid leaf1958Box leaf1958Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk137ValidityFacts chi175ValidityFacts
    leaf1958LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1958CoverageChecked :
    coverageCheck (innerAD leaf1958Box) leaf1958InnerLog = true := by
  rfl'

private theorem leaf1958InnerLogValid :
    leaf1958InnerLog.Valid 8 (innerAD leaf1958Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1958CoverageChecked

private noncomputable def leaf1958InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814661/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1958InputLogOnePlusV_eq :
    leaf1958InputLogOnePlusV = outerEnclosure 24
      (leaf1958Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1958RoundedFacts : LeafRoundedFacts 8
    leaf1958Certificate.logOnePlusV leaf1958InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1958InputLogOnePlusV_eq }

private noncomputable def leaf1958Inputs : Inputs :=
  inputsOfCaches globalInput sk137RoundedInputs
    chi175InputQChi innerPair34Input
    leaf1958InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1958LowerChecked :
    lowerCheck 24 leaf1958Box leaf1958Inputs = true := by
  rfl'

private theorem leaf1958CoversExact : CoversExact 8
    leaf1958Box leaf1958Certificate leaf1958InnerLog leaf1958Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk137RoundedFacts chi175RoundedFacts
    innerPair34RoundedFacts leaf1958RoundedFacts (by rfl)

private theorem leaf1958FlatSound : Sound leaf1958Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1958CertificateValid
    leaf1958InnerLogValid leaf1958CoversExact leaf1958LowerChecked

private noncomputable def leaf1959Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (37/256), chiHi := (19/128) }

private noncomputable def leaf1959Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871189/536870912) }, vSqrt := { lower := (65529/65536), upper := (67108928/67106945) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (779306269/536870912) }, upper := { exponent := 0, mantissa := (6015/4096) } }, logOuter := sk137LogOuterCertificate, logK := sk137LogKCertificate, logChi := chi176LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (134215873/134213890) } }, logDArg := sk137LogDArgCertificate }

private noncomputable def leaf1959InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1959LocalValidity :
    LeafFacts leaf1959Box leaf1959Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1959Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (67108928/67106945) }) = true
      norm_num [leaf1959Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1959CertificateValid :
    WideCertificateValid leaf1959Box leaf1959Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk137ValidityFacts chi176ValidityFacts
    leaf1959LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1959CoverageChecked :
    coverageCheck (innerAD leaf1959Box) leaf1959InnerLog = true := by
  rfl'

private theorem leaf1959InnerLogValid :
    leaf1959InnerLog.Valid 8 (innerAD leaf1959Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1959CoverageChecked

private noncomputable def leaf1959InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629329/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1959InputLogOnePlusV_eq :
    leaf1959InputLogOnePlusV = outerEnclosure 24
      (leaf1959Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1959RoundedFacts : LeafRoundedFacts 8
    leaf1959Certificate.logOnePlusV leaf1959InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1959InputLogOnePlusV_eq }

private noncomputable def leaf1959Inputs : Inputs :=
  inputsOfCaches globalInput sk137RoundedInputs
    chi176InputQChi innerPair34Input
    leaf1959InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1959LowerChecked :
    lowerCheck 24 leaf1959Box leaf1959Inputs = true := by
  rfl'

private theorem leaf1959CoversExact : CoversExact 8
    leaf1959Box leaf1959Certificate leaf1959InnerLog leaf1959Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk137RoundedFacts chi176RoundedFacts
    innerPair34RoundedFacts leaf1959RoundedFacts (by rfl)

private theorem leaf1959FlatSound : Sound leaf1959Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1959CertificateValid
    leaf1959InnerLogValid leaf1959CoversExact leaf1959LowerChecked

private noncomputable def leaf1960Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (9/64), chiHi := (37/256) }

private noncomputable def leaf1960Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871189/536870912) }, vSqrt := { lower := (65529/65536), upper := (67108928/67106977) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (775112221/536870912) }, upper := { exponent := 0, mantissa := (5983/4096) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi175LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (134215905/134213954) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf1960InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1960LocalValidity :
    LeafFacts leaf1960Box leaf1960Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1960Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (67108928/67106977) }) = true
      norm_num [leaf1960Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1960CertificateValid :
    WideCertificateValid leaf1960Box leaf1960Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi175ValidityFacts
    leaf1960LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1960CoverageChecked :
    coverageCheck (innerAD leaf1960Box) leaf1960InnerLog = true := by
  rfl'

private theorem leaf1960InnerLogValid :
    leaf1960InnerLog.Valid 8 (innerAD leaf1960Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1960CoverageChecked

private noncomputable def leaf1960InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629325/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1960InputLogOnePlusV_eq :
    leaf1960InputLogOnePlusV = outerEnclosure 24
      (leaf1960Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1960RoundedFacts : LeafRoundedFacts 8
    leaf1960Certificate.logOnePlusV leaf1960InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1960InputLogOnePlusV_eq }

private noncomputable def leaf1960Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi175InputQChi innerPair34Input
    leaf1960InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1960LowerChecked :
    lowerCheck 24 leaf1960Box leaf1960Inputs = true := by
  rfl'

private theorem leaf1960CoversExact : CoversExact 8
    leaf1960Box leaf1960Certificate leaf1960InnerLog leaf1960Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi175RoundedFacts
    innerPair34RoundedFacts leaf1960RoundedFacts (by rfl)

private theorem leaf1960FlatSound : Sound leaf1960Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1960CertificateValid
    leaf1960InnerLogValid leaf1960CoversExact leaf1960LowerChecked

private noncomputable def leaf1961Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (37/256), chiHi := (19/128) }

private noncomputable def leaf1961Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871191/536870912) }, vSqrt := { lower := (65529/65536), upper := (33554464/33553463) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (781730951/536870912) }, upper := { exponent := 0, mantissa := (3017/2048) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi176LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (67107927/67106926) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf1961InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1961LocalValidity :
    LeafFacts leaf1961Box leaf1961Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1961Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (33554464/33553463) }) = true
      norm_num [leaf1961Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1961CertificateValid :
    WideCertificateValid leaf1961Box leaf1961Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi176ValidityFacts
    leaf1961LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1961CoverageChecked :
    coverageCheck (innerAD leaf1961Box) leaf1961InnerLog = true := by
  rfl'

private theorem leaf1961InnerLogValid :
    leaf1961InnerLog.Valid 8 (innerAD leaf1961Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1961CoverageChecked

private noncomputable def leaf1961InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629331/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1961InputLogOnePlusV_eq :
    leaf1961InputLogOnePlusV = outerEnclosure 24
      (leaf1961Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1961RoundedFacts : LeafRoundedFacts 8
    leaf1961Certificate.logOnePlusV leaf1961InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1961InputLogOnePlusV_eq }

private noncomputable def leaf1961Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi176InputQChi innerPair34Input
    leaf1961InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1961LowerChecked :
    lowerCheck 24 leaf1961Box leaf1961Inputs = true := by
  rfl'

private theorem leaf1961CoversExact : CoversExact 8
    leaf1961Box leaf1961Certificate leaf1961InnerLog leaf1961Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi176RoundedFacts
    innerPair34RoundedFacts leaf1961RoundedFacts (by rfl)

private theorem leaf1961FlatSound : Sound leaf1961Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1961CertificateValid
    leaf1961InnerLogValid leaf1961CoversExact leaf1961LowerChecked

private noncomputable def leaf1962Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (19/128), chiHi := (39/256) }

private noncomputable def leaf1962Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871191/536870912) }, vSqrt := { lower := (65529/65536), upper := (134217856/134213789) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (785859467/536870912) }, upper := { exponent := 0, mantissa := (12131/8192) } }, logOuter := sk137LogOuterCertificate, logK := sk137LogKCertificate, logChi := chi177LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (268431645/268427578) } }, logDArg := sk137LogDArgCertificate }

private noncomputable def leaf1962InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1962LocalValidity :
    LeafFacts leaf1962Box leaf1962Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1962Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (134217856/134213789) }) = true
      norm_num [leaf1962Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1962CertificateValid :
    WideCertificateValid leaf1962Box leaf1962Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk137ValidityFacts chi177ValidityFacts
    leaf1962LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1962CoverageChecked :
    coverageCheck (innerAD leaf1962Box) leaf1962InnerLog = true := by
  rfl'

private theorem leaf1962InnerLogValid :
    leaf1962InnerLog.Valid 8 (innerAD leaf1962Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1962CoverageChecked

private noncomputable def leaf1962InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629335/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1962InputLogOnePlusV_eq :
    leaf1962InputLogOnePlusV = outerEnclosure 24
      (leaf1962Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1962RoundedFacts : LeafRoundedFacts 8
    leaf1962Certificate.logOnePlusV leaf1962InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1962InputLogOnePlusV_eq }

private noncomputable def leaf1962Inputs : Inputs :=
  inputsOfCaches globalInput sk137RoundedInputs
    chi177InputQChi innerPair34Input
    leaf1962InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1962LowerChecked :
    lowerCheck 24 leaf1962Box leaf1962Inputs = true := by
  rfl'

private theorem leaf1962CoversExact : CoversExact 8
    leaf1962Box leaf1962Certificate leaf1962InnerLog leaf1962Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk137RoundedFacts chi177RoundedFacts
    innerPair34RoundedFacts leaf1962RoundedFacts (by rfl)

private theorem leaf1962FlatSound : Sound leaf1962Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1962CertificateValid
    leaf1962InnerLogValid leaf1962CoversExact leaf1962LowerChecked

private noncomputable def leaf1963Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (39/256), chiHi := (5/32) }

private noncomputable def leaf1963Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871193/536870912) }, vSqrt := { lower := (65529/65536), upper := (22906164565/22905802752) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (792412665/536870912) }, upper := { exponent := 0, mantissa := (1529/1024) } }, logOuter := sk137LogOuterCertificate, logK := sk137LogKCertificate, logChi := chi178LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (45811967317/45811605504) } }, logDArg := sk137LogDArgCertificate }

private noncomputable def leaf1963InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1963LocalValidity :
    LeafFacts leaf1963Box leaf1963Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1963Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22906164565/22905802752) }) = true
      norm_num [leaf1963Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1963CertificateValid :
    WideCertificateValid leaf1963Box leaf1963Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk137ValidityFacts chi178ValidityFacts
    leaf1963LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1963CoverageChecked :
    coverageCheck (innerAD leaf1963Box) leaf1963InnerLog = true := by
  rfl'

private theorem leaf1963InnerLogValid :
    leaf1963InnerLog.Valid 8 (innerAD leaf1963Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1963CoverageChecked

private noncomputable def leaf1963InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629213/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1963InputLogOnePlusV_eq :
    leaf1963InputLogOnePlusV = outerEnclosure 24
      (leaf1963Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1963RoundedFacts : LeafRoundedFacts 8
    leaf1963Certificate.logOnePlusV leaf1963InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1963InputLogOnePlusV_eq }

private noncomputable def leaf1963Inputs : Inputs :=
  inputsOfCaches globalInput sk137RoundedInputs
    chi178InputQChi innerPair34Input
    leaf1963InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1963LowerChecked :
    lowerCheck 24 leaf1963Box leaf1963Inputs = true := by
  rfl'

private theorem leaf1963CoversExact : CoversExact 8
    leaf1963Box leaf1963Certificate leaf1963InnerLog leaf1963Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk137RoundedFacts chi178RoundedFacts
    innerPair34RoundedFacts leaf1963RoundedFacts (by rfl)

private theorem leaf1963FlatSound : Sound leaf1963Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1963CertificateValid
    leaf1963InnerLogValid leaf1963CoversExact leaf1963LowerChecked

private noncomputable def leaf1964Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (19/128), chiHi := (39/256) }

private noncomputable def leaf1964Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871193/536870912) }, vSqrt := { lower := (65529/65536), upper := (13743698739/13743488000) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (788349681/536870912) }, upper := { exponent := 0, mantissa := (6085/4096) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi177LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (27487186739/27486976000) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf1964InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1964LocalValidity :
    LeafFacts leaf1964Box leaf1964Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1964Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (13743698739/13743488000) }) = true
      norm_num [leaf1964Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1964CertificateValid :
    WideCertificateValid leaf1964Box leaf1964Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi177ValidityFacts
    leaf1964LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1964CoverageChecked :
    coverageCheck (innerAD leaf1964Box) leaf1964InnerLog = true := by
  rfl'

private theorem leaf1964InnerLogValid :
    leaf1964InnerLog.Valid 8 (innerAD leaf1964Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1964CoverageChecked

private noncomputable def leaf1964InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629209/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1964InputLogOnePlusV_eq :
    leaf1964InputLogOnePlusV = outerEnclosure 24
      (leaf1964Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1964RoundedFacts : LeafRoundedFacts 8
    leaf1964Certificate.logOnePlusV leaf1964InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1964InputLogOnePlusV_eq }

private noncomputable def leaf1964Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi177InputQChi innerPair34Input
    leaf1964InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1964LowerChecked :
    lowerCheck 24 leaf1964Box leaf1964Inputs = true := by
  rfl'

private theorem leaf1964CoversExact : CoversExact 8
    leaf1964Box leaf1964Certificate leaf1964InnerLog leaf1964Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi177RoundedFacts
    innerPair34RoundedFacts leaf1964RoundedFacts (by rfl)

private theorem leaf1964FlatSound : Sound leaf1964Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1964CertificateValid
    leaf1964InnerLogValid leaf1964CoversExact leaf1964LowerChecked

private noncomputable def leaf1965Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (39/256), chiHi := (5/32) }

private noncomputable def leaf1965Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871195/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717387776) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (794968411/536870912) }, upper := { exponent := 0, mantissa := (767/512) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi178LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435881471/137434775552) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf1965InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1965LocalValidity :
    LeafFacts leaf1965Box leaf1965Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1965Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717387776) }) = true
      norm_num [leaf1965Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1965CertificateValid :
    WideCertificateValid leaf1965Box leaf1965Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi178ValidityFacts
    leaf1965LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1965CoverageChecked :
    coverageCheck (innerAD leaf1965Box) leaf1965InnerLog = true := by
  rfl'

private theorem leaf1965InnerLogValid :
    leaf1965InnerLog.Valid 8 (innerAD leaf1965Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1965CoverageChecked

private noncomputable def leaf1965InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (363413/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf1965InputLogOnePlusV_eq :
    leaf1965InputLogOnePlusV = outerEnclosure 24
      (leaf1965Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1965RoundedFacts : LeafRoundedFacts 8
    leaf1965Certificate.logOnePlusV leaf1965InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1965InputLogOnePlusV_eq }

private noncomputable def leaf1965Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi178InputQChi innerPair34Input
    leaf1965InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1965LowerChecked :
    lowerCheck 24 leaf1965Box leaf1965Inputs = true := by
  rfl'

private theorem leaf1965CoversExact : CoversExact 8
    leaf1965Box leaf1965Certificate leaf1965InnerLog leaf1965Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi178RoundedFacts
    innerPair34RoundedFacts leaf1965RoundedFacts (by rfl)

private theorem leaf1965FlatSound : Sound leaf1965Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1965CertificateValid
    leaf1965InnerLogValid leaf1965CoversExact leaf1965LowerChecked

private noncomputable def leaf1966Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (9/64), chiHi := (37/256) }

private noncomputable def leaf1966Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871191/536870912) }, vSqrt := { lower := (65529/65536), upper := (134217856/134213917) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (777471371/536870912) }, upper := { exponent := 0, mantissa := (12003/8192) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi175LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (268431773/268427834) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf1966InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1966LocalValidity :
    LeafFacts leaf1966Box leaf1966Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1966Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (134217856/134213917) }) = true
      norm_num [leaf1966Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1966CertificateValid :
    WideCertificateValid leaf1966Box leaf1966Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi175ValidityFacts
    leaf1966LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1966CoverageChecked :
    coverageCheck (innerAD leaf1966Box) leaf1966InnerLog = true := by
  rfl'

private theorem leaf1966InnerLogValid :
    leaf1966InnerLog.Valid 8 (innerAD leaf1966Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1966CoverageChecked

private noncomputable def leaf1966InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629327/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1966InputLogOnePlusV_eq :
    leaf1966InputLogOnePlusV = outerEnclosure 24
      (leaf1966Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1966RoundedFacts : LeafRoundedFacts 8
    leaf1966Certificate.logOnePlusV leaf1966InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1966InputLogOnePlusV_eq }

private noncomputable def leaf1966Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi175InputQChi innerPair34Input
    leaf1966InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1966LowerChecked :
    lowerCheck 24 leaf1966Box leaf1966Inputs = true := by
  rfl'

private theorem leaf1966CoversExact : CoversExact 8
    leaf1966Box leaf1966Certificate leaf1966InnerLog leaf1966Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi175RoundedFacts
    innerPair34RoundedFacts leaf1966RoundedFacts (by rfl)

private theorem leaf1966FlatSound : Sound leaf1966Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1966CertificateValid
    leaf1966InnerLogValid leaf1966CoversExact leaf1966LowerChecked

private noncomputable def leaf1967Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (37/256), chiHi := (19/128) }

private noncomputable def leaf1967Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871193/536870912) }, vSqrt := { lower := (65529/65536), upper := (67108928/67106907) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (784155633/536870912) }, upper := { exponent := 0, mantissa := (6053/4096) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi176LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (134215835/134213814) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf1967InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1967LocalValidity :
    LeafFacts leaf1967Box leaf1967Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1967Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (67108928/67106907) }) = true
      norm_num [leaf1967Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1967CertificateValid :
    WideCertificateValid leaf1967Box leaf1967Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi176ValidityFacts
    leaf1967LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1967CoverageChecked :
    coverageCheck (innerAD leaf1967Box) leaf1967InnerLog = true := by
  rfl'

private theorem leaf1967InnerLogValid :
    leaf1967InnerLog.Valid 8 (innerAD leaf1967Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1967CoverageChecked

private noncomputable def leaf1967InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629333/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1967InputLogOnePlusV_eq :
    leaf1967InputLogOnePlusV = outerEnclosure 24
      (leaf1967Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1967RoundedFacts : LeafRoundedFacts 8
    leaf1967Certificate.logOnePlusV leaf1967InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1967InputLogOnePlusV_eq }

private noncomputable def leaf1967Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi176InputQChi innerPair34Input
    leaf1967InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1967LowerChecked :
    lowerCheck 24 leaf1967Box leaf1967Inputs = true := by
  rfl'

private theorem leaf1967CoversExact : CoversExact 8
    leaf1967Box leaf1967Certificate leaf1967InnerLog leaf1967Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi176RoundedFacts
    innerPair34RoundedFacts leaf1967RoundedFacts (by rfl)

private theorem leaf1967FlatSound : Sound leaf1967Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1967CertificateValid
    leaf1967InnerLogValid leaf1967CoversExact leaf1967LowerChecked

private noncomputable def leaf1968Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (9/64), chiHi := (37/256) }

private noncomputable def leaf1968Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871193/536870912) }, vSqrt := { lower := (65529/65536), upper := (16777232/16776735) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (779830521/536870912) }, upper := { exponent := 0, mantissa := (1505/1024) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi175LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (33553967/33553470) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf1968InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1968LocalValidity :
    LeafFacts leaf1968Box leaf1968Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1968Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (16777232/16776735) }) = true
      norm_num [leaf1968Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1968CertificateValid :
    WideCertificateValid leaf1968Box leaf1968Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi175ValidityFacts
    leaf1968LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1968CoverageChecked :
    coverageCheck (innerAD leaf1968Box) leaf1968InnerLog = true := by
  rfl'

private theorem leaf1968InnerLogValid :
    leaf1968InnerLog.Valid 8 (innerAD leaf1968Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1968CoverageChecked

private noncomputable def leaf1968InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629329/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1968InputLogOnePlusV_eq :
    leaf1968InputLogOnePlusV = outerEnclosure 24
      (leaf1968Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1968RoundedFacts : LeafRoundedFacts 8
    leaf1968Certificate.logOnePlusV leaf1968InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1968InputLogOnePlusV_eq }

private noncomputable def leaf1968Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi175InputQChi innerPair34Input
    leaf1968InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1968LowerChecked :
    lowerCheck 24 leaf1968Box leaf1968Inputs = true := by
  rfl'

private theorem leaf1968CoversExact : CoversExact 8
    leaf1968Box leaf1968Certificate leaf1968InnerLog leaf1968Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi175RoundedFacts
    innerPair34RoundedFacts leaf1968RoundedFacts (by rfl)

private theorem leaf1968FlatSound : Sound leaf1968Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1968CertificateValid
    leaf1968InnerLogValid leaf1968CoversExact leaf1968LowerChecked

private noncomputable def leaf1969Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (37/256), chiHi := (19/128) }

private noncomputable def leaf1969Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871195/536870912) }, vSqrt := { lower := (65529/65536), upper := (493448/493433) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (786580315/536870912) }, upper := { exponent := 0, mantissa := (759/512) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi176LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (986881/986866) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf1969InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1969LocalValidity :
    LeafFacts leaf1969Box leaf1969Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1969Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (493448/493433) }) = true
      norm_num [leaf1969Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1969CertificateValid :
    WideCertificateValid leaf1969Box leaf1969Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi176ValidityFacts
    leaf1969LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1969CoverageChecked :
    coverageCheck (innerAD leaf1969Box) leaf1969InnerLog = true := by
  rfl'

private theorem leaf1969InnerLogValid :
    leaf1969InnerLog.Valid 8 (innerAD leaf1969Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1969CoverageChecked

private noncomputable def leaf1969InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453667/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf1969InputLogOnePlusV_eq :
    leaf1969InputLogOnePlusV = outerEnclosure 24
      (leaf1969Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1969RoundedFacts : LeafRoundedFacts 8
    leaf1969Certificate.logOnePlusV leaf1969InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1969InputLogOnePlusV_eq }

private noncomputable def leaf1969Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi176InputQChi innerPair34Input
    leaf1969InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1969LowerChecked :
    lowerCheck 24 leaf1969Box leaf1969Inputs = true := by
  rfl'

private theorem leaf1969CoversExact : CoversExact 8
    leaf1969Box leaf1969Certificate leaf1969InnerLog leaf1969Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi176RoundedFacts
    innerPair34RoundedFacts leaf1969RoundedFacts (by rfl)

private theorem leaf1969FlatSound : Sound leaf1969Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1969CertificateValid
    leaf1969InnerLogValid leaf1969CoversExact leaf1969LowerChecked

private noncomputable def leaf1970Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (19/128), chiHi := (39/256) }

private noncomputable def leaf1970Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871195/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717420032) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (790839895/536870912) }, upper := { exponent := 0, mantissa := (12209/8192) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi177LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435913727/137434840064) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf1970InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1970LocalValidity :
    LeafFacts leaf1970Box leaf1970Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1970Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717420032) }) = true
      norm_num [leaf1970Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1970CertificateValid :
    WideCertificateValid leaf1970Box leaf1970Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi177ValidityFacts
    leaf1970LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1970CoverageChecked :
    coverageCheck (innerAD leaf1970Box) leaf1970InnerLog = true := by
  rfl'

private theorem leaf1970InnerLogValid :
    leaf1970InnerLog.Valid 8 (innerAD leaf1970Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1970CoverageChecked

private noncomputable def leaf1970InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907303/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1970InputLogOnePlusV_eq :
    leaf1970InputLogOnePlusV = outerEnclosure 24
      (leaf1970Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1970RoundedFacts : LeafRoundedFacts 8
    leaf1970Certificate.logOnePlusV leaf1970InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1970InputLogOnePlusV_eq }

private noncomputable def leaf1970Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi177InputQChi innerPair34Input
    leaf1970InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1970LowerChecked :
    lowerCheck 24 leaf1970Box leaf1970Inputs = true := by
  rfl'

private theorem leaf1970CoversExact : CoversExact 8
    leaf1970Box leaf1970Certificate leaf1970InnerLog leaf1970Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi177RoundedFacts
    innerPair34RoundedFacts leaf1970RoundedFacts (by rfl)

private theorem leaf1970FlatSound : Sound leaf1970Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1970CertificateValid
    leaf1970InnerLogValid leaf1970CoversExact leaf1970LowerChecked

private noncomputable def leaf1971Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (39/256), chiHi := (5/32) }

private noncomputable def leaf1971Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871197/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717367296) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (797524157/536870912) }, upper := { exponent := 0, mantissa := (1539/1024) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi178LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435860991/137434734592) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf1971InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf1971LocalValidity :
    LeafFacts leaf1971Box leaf1971Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1971Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717367296) }) = true
      norm_num [leaf1971Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1971CertificateValid :
    WideCertificateValid leaf1971Box leaf1971Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi178ValidityFacts
    leaf1971LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1971CoverageChecked :
    coverageCheck (innerAD leaf1971Box) leaf1971InnerLog = true := by
  rfl'

private theorem leaf1971InnerLogValid :
    leaf1971InnerLog.Valid 8 (innerAD leaf1971Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf1971CoverageChecked

private noncomputable def leaf1971InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814609/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1971InputLogOnePlusV_eq :
    leaf1971InputLogOnePlusV = outerEnclosure 24
      (leaf1971Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1971RoundedFacts : LeafRoundedFacts 8
    leaf1971Certificate.logOnePlusV leaf1971InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1971InputLogOnePlusV_eq }

private noncomputable def leaf1971Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi178InputQChi innerPair35Input
    leaf1971InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1971LowerChecked :
    lowerCheck 24 leaf1971Box leaf1971Inputs = true := by
  rfl'

private theorem leaf1971CoversExact : CoversExact 8
    leaf1971Box leaf1971Certificate leaf1971InnerLog leaf1971Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi178RoundedFacts
    innerPair35RoundedFacts leaf1971RoundedFacts (by rfl)

private theorem leaf1971FlatSound : Sound leaf1971Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1971CertificateValid
    leaf1971InnerLogValid leaf1971CoversExact leaf1971LowerChecked

private noncomputable def leaf1972Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (19/128), chiHi := (39/256) }

private noncomputable def leaf1972Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871197/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717400064) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (793330109/536870912) }, upper := { exponent := 0, mantissa := (1531/1024) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi177LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435893759/137434800128) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf1972InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1972LocalValidity :
    LeafFacts leaf1972Box leaf1972Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1972Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717400064) }) = true
      norm_num [leaf1972Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1972CertificateValid :
    WideCertificateValid leaf1972Box leaf1972Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi177ValidityFacts
    leaf1972LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1972CoverageChecked :
    coverageCheck (innerAD leaf1972Box) leaf1972InnerLog = true := by
  rfl'

private theorem leaf1972InnerLogValid :
    leaf1972InnerLog.Valid 8 (innerAD leaf1972Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1972CoverageChecked

private noncomputable def leaf1972InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814607/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1972InputLogOnePlusV_eq :
    leaf1972InputLogOnePlusV = outerEnclosure 24
      (leaf1972Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1972RoundedFacts : LeafRoundedFacts 8
    leaf1972Certificate.logOnePlusV leaf1972InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1972InputLogOnePlusV_eq }

private noncomputable def leaf1972Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi177InputQChi innerPair34Input
    leaf1972InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1972LowerChecked :
    lowerCheck 24 leaf1972Box leaf1972Inputs = true := by
  rfl'

private theorem leaf1972CoversExact : CoversExact 8
    leaf1972Box leaf1972Certificate leaf1972InnerLog leaf1972Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi177RoundedFacts
    innerPair34RoundedFacts leaf1972RoundedFacts (by rfl)

private theorem leaf1972FlatSound : Sound leaf1972Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1972CertificateValid
    leaf1972InnerLogValid leaf1972CoversExact leaf1972LowerChecked

private noncomputable def leaf1973Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (39/256), chiHi := (5/32) }

private noncomputable def leaf1973Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871199/536870912) }, vSqrt := { lower := (65529/65536), upper := (22906164565/22905782272) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (800079903/536870912) }, upper := { exponent := 0, mantissa := (193/128) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi178LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (45811946837/45811564544) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf1973InnerLog : WideLogData :=
  innerPair409Data

set_option maxRecDepth 1000000 in
private theorem leaf1973LocalValidity :
    LeafFacts leaf1973Box leaf1973Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1973Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22906164565/22905782272) }) = true
      norm_num [leaf1973Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1973CertificateValid :
    WideCertificateValid leaf1973Box leaf1973Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi178ValidityFacts
    leaf1973LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1973CoverageChecked :
    coverageCheck (innerAD leaf1973Box) leaf1973InnerLog = true := by
  rfl'

private theorem leaf1973InnerLogValid :
    leaf1973InnerLog.Valid 8 (innerAD leaf1973Box) :=
  wideLogDataValid_of_cachedCheck endpoint120PositiveFacts
    endpoint49PositiveFacts.valid leaf1973CoverageChecked

private noncomputable def leaf1973InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629221/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1973InputLogOnePlusV_eq :
    leaf1973InputLogOnePlusV = outerEnclosure 24
      (leaf1973Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1973RoundedFacts : LeafRoundedFacts 8
    leaf1973Certificate.logOnePlusV leaf1973InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1973InputLogOnePlusV_eq }

private noncomputable def leaf1973Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi178InputQChi innerPair409Input
    leaf1973InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1973LowerChecked :
    lowerCheck 24 leaf1973Box leaf1973Inputs = true := by
  rfl'

private theorem leaf1973CoversExact : CoversExact 8
    leaf1973Box leaf1973Certificate leaf1973InnerLog leaf1973Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi178RoundedFacts
    innerPair409RoundedFacts leaf1973RoundedFacts (by rfl)

private theorem leaf1973FlatSound : Sound leaf1973Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1973CertificateValid
    leaf1973InnerLogValid leaf1973CoversExact leaf1973LowerChecked

private noncomputable def component43Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (1/8), chiHi := (17/128) }

set_option maxRecDepth 1000000 in
private theorem component43Node0_sound : Sound component43Node0Box :=
  sound_of_literal_split component43Node0Box leaf1926Box leaf1927Box
    .k (97/32) (by rfl) (by rfl)
    leaf1926FlatSound leaf1927FlatSound

private noncomputable def component43Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (17/128), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component43Node1_sound : Sound component43Node1Box :=
  sound_of_literal_split component43Node1Box leaf1928Box leaf1929Box
    .k (97/32) (by rfl) (by rfl)
    leaf1928FlatSound leaf1929FlatSound

private noncomputable def component43Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (1/8), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component43Node2_sound : Sound component43Node2Box :=
  sound_of_literal_split component43Node2Box component43Node0Box component43Node1Box
    .chi (17/128) (by rfl) (by rfl)
    component43Node0_sound component43Node1_sound

private noncomputable def component43Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (1/8), chiHi := (17/128) }

set_option maxRecDepth 1000000 in
private theorem component43Node3_sound : Sound component43Node3Box :=
  sound_of_literal_split component43Node3Box leaf1930Box leaf1931Box
    .k (99/32) (by rfl) (by rfl)
    leaf1930FlatSound leaf1931FlatSound

private noncomputable def component43Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (17/128), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component43Node4_sound : Sound component43Node4Box :=
  sound_of_literal_split component43Node4Box leaf1932Box leaf1933Box
    .k (99/32) (by rfl) (by rfl)
    leaf1932FlatSound leaf1933FlatSound

private noncomputable def component43Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (1/8), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component43Node5_sound : Sound component43Node5Box :=
  sound_of_literal_split component43Node5Box component43Node3Box component43Node4Box
    .chi (17/128) (by rfl) (by rfl)
    component43Node3_sound component43Node4_sound

private noncomputable def component43Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (1/8), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component43Node6_sound : Sound component43Node6Box :=
  sound_of_literal_split component43Node6Box component43Node2Box component43Node5Box
    .k (49/16) (by rfl) (by rfl)
    component43Node2_sound component43Node5_sound

private noncomputable def component43Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (9/64), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component43Node7_sound : Sound component43Node7Box :=
  sound_of_literal_split component43Node7Box leaf1934Box leaf1935Box
    .k (97/32) (by rfl) (by rfl)
    leaf1934FlatSound leaf1935FlatSound

private noncomputable def component43Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (19/128), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component43Node8_sound : Sound component43Node8Box :=
  sound_of_literal_split component43Node8Box leaf1936Box leaf1937Box
    .k (97/32) (by rfl) (by rfl)
    leaf1936FlatSound leaf1937FlatSound

private noncomputable def component43Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (9/64), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component43Node9_sound : Sound component43Node9Box :=
  sound_of_literal_split component43Node9Box component43Node7Box component43Node8Box
    .chi (19/128) (by rfl) (by rfl)
    component43Node7_sound component43Node8_sound

private noncomputable def component43Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (9/64), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component43Node10_sound : Sound component43Node10Box :=
  sound_of_literal_split component43Node10Box leaf1939Box leaf1940Box
    .chi (37/256) (by rfl) (by rfl)
    leaf1939FlatSound leaf1940FlatSound

private noncomputable def component43Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (9/64), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component43Node11_sound : Sound component43Node11Box :=
  sound_of_literal_split component43Node11Box leaf1938Box component43Node10Box
    .k (99/32) (by rfl) (by rfl)
    leaf1938FlatSound component43Node10_sound

private noncomputable def component43Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (19/128), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component43Node12_sound : Sound component43Node12Box :=
  sound_of_literal_split component43Node12Box leaf1941Box leaf1942Box
    .chi (39/256) (by rfl) (by rfl)
    leaf1941FlatSound leaf1942FlatSound

private noncomputable def component43Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (19/128), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component43Node13_sound : Sound component43Node13Box :=
  sound_of_literal_split component43Node13Box leaf1943Box leaf1944Box
    .chi (39/256) (by rfl) (by rfl)
    leaf1943FlatSound leaf1944FlatSound

private noncomputable def component43Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (19/128), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component43Node14_sound : Sound component43Node14Box :=
  sound_of_literal_split component43Node14Box component43Node12Box component43Node13Box
    .k (99/32) (by rfl) (by rfl)
    component43Node12_sound component43Node13_sound

private noncomputable def component43Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (9/64), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component43Node15_sound : Sound component43Node15Box :=
  sound_of_literal_split component43Node15Box component43Node11Box component43Node14Box
    .chi (19/128) (by rfl) (by rfl)
    component43Node11_sound component43Node14_sound

private noncomputable def component43Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (9/64), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component43Node16_sound : Sound component43Node16Box :=
  sound_of_literal_split component43Node16Box component43Node9Box component43Node15Box
    .k (49/16) (by rfl) (by rfl)
    component43Node9_sound component43Node15_sound

private noncomputable def component43Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (1/8), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component43Node17_sound : Sound component43Node17Box :=
  sound_of_literal_split component43Node17Box component43Node6Box component43Node16Box
    .chi (9/64) (by rfl) (by rfl)
    component43Node6_sound component43Node16_sound

private noncomputable def component43Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (1/8), chiHi := (17/128) }

set_option maxRecDepth 1000000 in
private theorem component43Node18_sound : Sound component43Node18Box :=
  sound_of_literal_split component43Node18Box leaf1945Box leaf1946Box
    .k (101/32) (by rfl) (by rfl)
    leaf1945FlatSound leaf1946FlatSound

private noncomputable def component43Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (17/128), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component43Node19_sound : Sound component43Node19Box :=
  sound_of_literal_split component43Node19Box leaf1948Box leaf1949Box
    .chi (35/256) (by rfl) (by rfl)
    leaf1948FlatSound leaf1949FlatSound

private noncomputable def component43Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (17/128), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component43Node20_sound : Sound component43Node20Box :=
  sound_of_literal_split component43Node20Box leaf1947Box component43Node19Box
    .k (101/32) (by rfl) (by rfl)
    leaf1947FlatSound component43Node19_sound

private noncomputable def component43Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (1/8), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component43Node21_sound : Sound component43Node21Box :=
  sound_of_literal_split component43Node21Box component43Node18Box component43Node20Box
    .chi (17/128) (by rfl) (by rfl)
    component43Node18_sound component43Node20_sound

private noncomputable def component43Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (1/8), chiHi := (17/128) }

set_option maxRecDepth 1000000 in
private theorem component43Node22_sound : Sound component43Node22Box :=
  sound_of_literal_split component43Node22Box leaf1950Box leaf1951Box
    .chi (33/256) (by rfl) (by rfl)
    leaf1950FlatSound leaf1951FlatSound

private noncomputable def component43Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (1/8), chiHi := (17/128) }

set_option maxRecDepth 1000000 in
private theorem component43Node23_sound : Sound component43Node23Box :=
  sound_of_literal_split component43Node23Box leaf1952Box leaf1953Box
    .chi (33/256) (by rfl) (by rfl)
    leaf1952FlatSound leaf1953FlatSound

private noncomputable def component43Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (1/8), chiHi := (17/128) }

set_option maxRecDepth 1000000 in
private theorem component43Node24_sound : Sound component43Node24Box :=
  sound_of_literal_split component43Node24Box component43Node22Box component43Node23Box
    .k (103/32) (by rfl) (by rfl)
    component43Node22_sound component43Node23_sound

private noncomputable def component43Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (17/128), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component43Node25_sound : Sound component43Node25Box :=
  sound_of_literal_split component43Node25Box leaf1954Box leaf1955Box
    .chi (35/256) (by rfl) (by rfl)
    leaf1954FlatSound leaf1955FlatSound

private noncomputable def component43Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (17/128), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component43Node26_sound : Sound component43Node26Box :=
  sound_of_literal_split component43Node26Box leaf1956Box leaf1957Box
    .chi (35/256) (by rfl) (by rfl)
    leaf1956FlatSound leaf1957FlatSound

private noncomputable def component43Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (17/128), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component43Node27_sound : Sound component43Node27Box :=
  sound_of_literal_split component43Node27Box component43Node25Box component43Node26Box
    .k (103/32) (by rfl) (by rfl)
    component43Node25_sound component43Node26_sound

private noncomputable def component43Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (1/8), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component43Node28_sound : Sound component43Node28Box :=
  sound_of_literal_split component43Node28Box component43Node24Box component43Node27Box
    .chi (17/128) (by rfl) (by rfl)
    component43Node24_sound component43Node27_sound

private noncomputable def component43Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (1/8), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component43Node29_sound : Sound component43Node29Box :=
  sound_of_literal_split component43Node29Box component43Node21Box component43Node28Box
    .k (51/16) (by rfl) (by rfl)
    component43Node21_sound component43Node28_sound

private noncomputable def component43Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (9/64), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component43Node30_sound : Sound component43Node30Box :=
  sound_of_literal_split component43Node30Box leaf1958Box leaf1959Box
    .chi (37/256) (by rfl) (by rfl)
    leaf1958FlatSound leaf1959FlatSound

private noncomputable def component43Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (9/64), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component43Node31_sound : Sound component43Node31Box :=
  sound_of_literal_split component43Node31Box leaf1960Box leaf1961Box
    .chi (37/256) (by rfl) (by rfl)
    leaf1960FlatSound leaf1961FlatSound

private noncomputable def component43Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (9/64), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component43Node32_sound : Sound component43Node32Box :=
  sound_of_literal_split component43Node32Box component43Node30Box component43Node31Box
    .k (101/32) (by rfl) (by rfl)
    component43Node30_sound component43Node31_sound

private noncomputable def component43Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (19/128), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component43Node33_sound : Sound component43Node33Box :=
  sound_of_literal_split component43Node33Box leaf1962Box leaf1963Box
    .chi (39/256) (by rfl) (by rfl)
    leaf1962FlatSound leaf1963FlatSound

private noncomputable def component43Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (19/128), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component43Node34_sound : Sound component43Node34Box :=
  sound_of_literal_split component43Node34Box leaf1964Box leaf1965Box
    .chi (39/256) (by rfl) (by rfl)
    leaf1964FlatSound leaf1965FlatSound

private noncomputable def component43Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (19/128), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component43Node35_sound : Sound component43Node35Box :=
  sound_of_literal_split component43Node35Box component43Node33Box component43Node34Box
    .k (101/32) (by rfl) (by rfl)
    component43Node33_sound component43Node34_sound

private noncomputable def component43Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (9/64), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component43Node36_sound : Sound component43Node36Box :=
  sound_of_literal_split component43Node36Box component43Node32Box component43Node35Box
    .chi (19/128) (by rfl) (by rfl)
    component43Node32_sound component43Node35_sound

private noncomputable def component43Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (9/64), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component43Node37_sound : Sound component43Node37Box :=
  sound_of_literal_split component43Node37Box leaf1966Box leaf1967Box
    .chi (37/256) (by rfl) (by rfl)
    leaf1966FlatSound leaf1967FlatSound

private noncomputable def component43Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (9/64), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component43Node38_sound : Sound component43Node38Box :=
  sound_of_literal_split component43Node38Box leaf1968Box leaf1969Box
    .chi (37/256) (by rfl) (by rfl)
    leaf1968FlatSound leaf1969FlatSound

private noncomputable def component43Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (9/64), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component43Node39_sound : Sound component43Node39Box :=
  sound_of_literal_split component43Node39Box component43Node37Box component43Node38Box
    .k (103/32) (by rfl) (by rfl)
    component43Node37_sound component43Node38_sound

private noncomputable def component43Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (19/128), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component43Node40_sound : Sound component43Node40Box :=
  sound_of_literal_split component43Node40Box leaf1970Box leaf1971Box
    .chi (39/256) (by rfl) (by rfl)
    leaf1970FlatSound leaf1971FlatSound

private noncomputable def component43Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (19/128), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component43Node41_sound : Sound component43Node41Box :=
  sound_of_literal_split component43Node41Box leaf1972Box leaf1973Box
    .chi (39/256) (by rfl) (by rfl)
    leaf1972FlatSound leaf1973FlatSound

private noncomputable def component43Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (19/128), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component43Node42_sound : Sound component43Node42Box :=
  sound_of_literal_split component43Node42Box component43Node40Box component43Node41Box
    .k (103/32) (by rfl) (by rfl)
    component43Node40_sound component43Node41_sound

private noncomputable def component43Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (9/64), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component43Node43_sound : Sound component43Node43Box :=
  sound_of_literal_split component43Node43Box component43Node39Box component43Node42Box
    .chi (19/128) (by rfl) (by rfl)
    component43Node39_sound component43Node42_sound

private noncomputable def component43Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (9/64), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component43Node44_sound : Sound component43Node44Box :=
  sound_of_literal_split component43Node44Box component43Node36Box component43Node43Box
    .k (51/16) (by rfl) (by rfl)
    component43Node36_sound component43Node43_sound

private noncomputable def component43Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (1/8), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component43Node45_sound : Sound component43Node45Box :=
  sound_of_literal_split component43Node45Box component43Node29Box component43Node44Box
    .chi (9/64) (by rfl) (by rfl)
    component43Node29_sound component43Node44_sound

noncomputable def component43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (13/4), chiLo := (1/8), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
theorem component43_sound : Sound component43Box :=
  sound_of_literal_split component43Box component43Node17Box component43Node45Box
    .k (25/8) (by rfl) (by rfl)
    component43Node17_sound component43Node45_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
