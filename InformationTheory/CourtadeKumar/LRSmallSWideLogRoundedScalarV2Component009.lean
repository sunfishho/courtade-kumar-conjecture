import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch2
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

private noncomputable def leaf355Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (49/32), chiLo := (1/4), chiHi := (9/32) }

private noncomputable def leaf355Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108979/67108864) }, vSqrt := { lower := (16383/16384), upper := (16777232/16776775) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (92240271/67108864) }, upper := { exponent := 0, mantissa := (1465/1024) } }, logOuter := sk43LogOuterCertificate, logK := sk43LogKCertificate, logChi := chi46LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (33554007/33553550) } }, logDArg := sk43LogDArgCertificate }

private noncomputable def leaf355InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf355LocalValidity :
    LeafFacts leaf355Box leaf355Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf355Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (16777232/16776775) }) = true
      norm_num [leaf355Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf355CertificateValid :
    WideCertificateValid leaf355Box leaf355Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk43ValidityFacts chi46ValidityFacts
    leaf355LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf355CoverageChecked :
    coverageCheck (innerAD leaf355Box) leaf355InnerLog = true := by
  rfl'

private theorem leaf355InnerLogValid :
    leaf355InnerLog.Valid 8 (innerAD leaf355Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf355CoverageChecked

private noncomputable def leaf355InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629309/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf355InputLogOnePlusV_eq :
    leaf355InputLogOnePlusV = outerEnclosure 24
      (leaf355Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf355RoundedFacts : LeafRoundedFacts 8
    leaf355Certificate.logOnePlusV leaf355InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf355InputLogOnePlusV_eq }

private noncomputable def leaf355Inputs : Inputs :=
  inputsOfCaches globalInput sk43RoundedInputs
    chi46InputQChi innerPair22Input
    leaf355InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf355LowerChecked :
    lowerCheck 24 leaf355Box leaf355Inputs = true := by
  rfl'

private theorem leaf355CoversExact : CoversExact 8
    leaf355Box leaf355Certificate leaf355InnerLog leaf355Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk43RoundedFacts chi46RoundedFacts
    innerPair22RoundedFacts leaf355RoundedFacts (by rfl)

private theorem leaf355FlatSound : Sound leaf355Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf355CertificateValid
    leaf355InnerLogValid leaf355CoversExact leaf355LowerChecked

private noncomputable def leaf356Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/32), kHi := (25/16), chiLo := (1/4), chiHi := (9/32) }

private noncomputable def leaf356Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108981/67108864) }, vSqrt := { lower := (16383/16384), upper := (8388616/8388383) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (92764525/67108864) }, upper := { exponent := 0, mantissa := (737/512) } }, logOuter := sk44LogOuterCertificate, logK := sk44LogKCertificate, logChi := chi46LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (16776999/16776766) } }, logDArg := sk44LogDArgCertificate }

private noncomputable def leaf356InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf356LocalValidity :
    LeafFacts leaf356Box leaf356Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf356Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (8388616/8388383) }) = true
      norm_num [leaf356Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf356CertificateValid :
    WideCertificateValid leaf356Box leaf356Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk44ValidityFacts chi46ValidityFacts
    leaf356LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf356CoverageChecked :
    coverageCheck (innerAD leaf356Box) leaf356InnerLog = true := by
  rfl'

private theorem leaf356InnerLogValid :
    leaf356InnerLog.Valid 8 (innerAD leaf356Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf356CoverageChecked

private noncomputable def leaf356InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (5814657/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf356InputLogOnePlusV_eq :
    leaf356InputLogOnePlusV = outerEnclosure 24
      (leaf356Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf356RoundedFacts : LeafRoundedFacts 8
    leaf356Certificate.logOnePlusV leaf356InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf356InputLogOnePlusV_eq }

private noncomputable def leaf356Inputs : Inputs :=
  inputsOfCaches globalInput sk44RoundedInputs
    chi46InputQChi innerPair27Input
    leaf356InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf356LowerChecked :
    lowerCheck 24 leaf356Box leaf356Inputs = true := by
  rfl'

private theorem leaf356CoversExact : CoversExact 8
    leaf356Box leaf356Certificate leaf356InnerLog leaf356Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk44RoundedFacts chi46RoundedFacts
    innerPair27RoundedFacts leaf356RoundedFacts (by rfl)

private theorem leaf356FlatSound : Sound leaf356Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf356CertificateValid
    leaf356InnerLogValid leaf356CoversExact leaf356LowerChecked

private noncomputable def leaf357Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (49/32), chiLo := (9/32), chiHi := (5/16) }

private noncomputable def leaf357Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108981/67108864) }, vSqrt := { lower := (16383/16384), upper := (8388616/8388363) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (95385805/67108864) }, upper := { exponent := 0, mantissa := (757/512) } }, logOuter := sk43LogOuterCertificate, logK := sk43LogKCertificate, logChi := chi47LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (16776979/16776726) } }, logDArg := sk43LogDArgCertificate }

private noncomputable def leaf357InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf357LocalValidity :
    LeafFacts leaf357Box leaf357Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf357Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (8388616/8388363) }) = true
      norm_num [leaf357Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf357CertificateValid :
    WideCertificateValid leaf357Box leaf357Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk43ValidityFacts chi47ValidityFacts
    leaf357LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf357CoverageChecked :
    coverageCheck (innerAD leaf357Box) leaf357InnerLog = true := by
  rfl'

private theorem leaf357InnerLogValid :
    leaf357InnerLog.Valid 8 (innerAD leaf357Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf357CoverageChecked

private noncomputable def leaf357InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (5814667/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf357InputLogOnePlusV_eq :
    leaf357InputLogOnePlusV = outerEnclosure 24
      (leaf357Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf357RoundedFacts : LeafRoundedFacts 8
    leaf357Certificate.logOnePlusV leaf357InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf357InputLogOnePlusV_eq }

private noncomputable def leaf357Inputs : Inputs :=
  inputsOfCaches globalInput sk43RoundedInputs
    chi47InputQChi innerPair27Input
    leaf357InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf357LowerChecked :
    lowerCheck 24 leaf357Box leaf357Inputs = true := by
  rfl'

private theorem leaf357CoversExact : CoversExact 8
    leaf357Box leaf357Certificate leaf357InnerLog leaf357Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk43RoundedFacts chi47RoundedFacts
    innerPair27RoundedFacts leaf357RoundedFacts (by rfl)

private theorem leaf357FlatSound : Sound leaf357Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf357CertificateValid
    leaf357InnerLogValid leaf357CoversExact leaf357LowerChecked

private noncomputable def leaf358Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/32), kHi := (25/16), chiLo := (9/32), chiHi := (5/16) }

private noncomputable def leaf358Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108983/67108864) }, vSqrt := { lower := (16383/16384), upper := (68718493695/68717428736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (95975591/67108864) }, upper := { exponent := 0, mantissa := (381/256) } }, logOuter := sk44LogOuterCertificate, logK := sk44LogKCertificate, logChi := chi47LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (137435922431/137434857472) } }, logDArg := sk44LogDArgCertificate }

private noncomputable def leaf358InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf358LocalValidity :
    LeafFacts leaf358Box leaf358Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf358Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (68718493695/68717428736) }) = true
      norm_num [leaf358Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf358CertificateValid :
    WideCertificateValid leaf358Box leaf358Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk44ValidityFacts chi47ValidityFacts
    leaf358LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf358CoverageChecked :
    coverageCheck (innerAD leaf358Box) leaf358InnerLog = true := by
  rfl'

private theorem leaf358InnerLogValid :
    leaf358InnerLog.Valid 8 (innerAD leaf358Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf358CoverageChecked

private noncomputable def leaf358InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629211/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf358InputLogOnePlusV_eq :
    leaf358InputLogOnePlusV = outerEnclosure 24
      (leaf358Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf358RoundedFacts : LeafRoundedFacts 8
    leaf358Certificate.logOnePlusV leaf358InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf358InputLogOnePlusV_eq }

private noncomputable def leaf358Inputs : Inputs :=
  inputsOfCaches globalInput sk44RoundedInputs
    chi47InputQChi innerPair27Input
    leaf358InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf358LowerChecked :
    lowerCheck 24 leaf358Box leaf358Inputs = true := by
  rfl'

private theorem leaf358CoversExact : CoversExact 8
    leaf358Box leaf358Certificate leaf358InnerLog leaf358Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk44RoundedFacts chi47RoundedFacts
    innerPair27RoundedFacts leaf358RoundedFacts (by rfl)

private theorem leaf358FlatSound : Sound leaf358Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf358CertificateValid
    leaf358InnerLogValid leaf358CoversExact leaf358LowerChecked

private noncomputable def leaf359Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/16), kHi := (51/32), chiLo := (1/4), chiHi := (9/32) }

private noncomputable def leaf359Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108983/67108864) }, vSqrt := { lower := (16383/16384), upper := (16777232/16776757) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (93288779/67108864) }, upper := { exponent := 0, mantissa := (1483/1024) } }, logOuter := sk45LogOuterCertificate, logK := sk45LogKCertificate, logChi := chi46LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (33553989/33553514) } }, logDArg := sk45LogDArgCertificate }

private noncomputable def leaf359InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf359LocalValidity :
    LeafFacts leaf359Box leaf359Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf359Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (16777232/16776757) }) = true
      norm_num [leaf359Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf359CertificateValid :
    WideCertificateValid leaf359Box leaf359Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk45ValidityFacts chi46ValidityFacts
    leaf359LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf359CoverageChecked :
    coverageCheck (innerAD leaf359Box) leaf359InnerLog = true := by
  rfl'

private theorem leaf359InnerLogValid :
    leaf359InnerLog.Valid 8 (innerAD leaf359Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf359CoverageChecked

private noncomputable def leaf359InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (5814659/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf359InputLogOnePlusV_eq :
    leaf359InputLogOnePlusV = outerEnclosure 24
      (leaf359Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf359RoundedFacts : LeafRoundedFacts 8
    leaf359Certificate.logOnePlusV leaf359InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf359InputLogOnePlusV_eq }

private noncomputable def leaf359Inputs : Inputs :=
  inputsOfCaches globalInput sk45RoundedInputs
    chi46InputQChi innerPair27Input
    leaf359InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf359LowerChecked :
    lowerCheck 24 leaf359Box leaf359Inputs = true := by
  rfl'

private theorem leaf359CoversExact : CoversExact 8
    leaf359Box leaf359Certificate leaf359InnerLog leaf359Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk45RoundedFacts chi46RoundedFacts
    innerPair27RoundedFacts leaf359RoundedFacts (by rfl)

private theorem leaf359FlatSound : Sound leaf359Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf359CertificateValid
    leaf359InnerLogValid leaf359CoversExact leaf359LowerChecked

private noncomputable def leaf360Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/32), kHi := (13/8), chiLo := (1/4), chiHi := (9/32) }

private noncomputable def leaf360Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108985/67108864) }, vSqrt := { lower := (16383/16384), upper := (4194308/4194187) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (93813033/67108864) }, upper := { exponent := 0, mantissa := (373/256) } }, logOuter := sk46LogOuterCertificate, logK := sk46LogKCertificate, logChi := chi46LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (8388495/8388374) } }, logDArg := sk46LogDArgCertificate }

private noncomputable def leaf360InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf360LocalValidity :
    LeafFacts leaf360Box leaf360Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf360Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (4194308/4194187) }) = true
      norm_num [leaf360Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf360CertificateValid :
    WideCertificateValid leaf360Box leaf360Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk46ValidityFacts chi46ValidityFacts
    leaf360LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf360CoverageChecked :
    coverageCheck (innerAD leaf360Box) leaf360InnerLog = true := by
  rfl'

private theorem leaf360InnerLogValid :
    leaf360InnerLog.Valid 8 (innerAD leaf360Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf360CoverageChecked

private noncomputable def leaf360InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629323/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf360InputLogOnePlusV_eq :
    leaf360InputLogOnePlusV = outerEnclosure 24
      (leaf360Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf360RoundedFacts : LeafRoundedFacts 8
    leaf360Certificate.logOnePlusV leaf360InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf360InputLogOnePlusV_eq }

private noncomputable def leaf360Inputs : Inputs :=
  inputsOfCaches globalInput sk46RoundedInputs
    chi46InputQChi innerPair27Input
    leaf360InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf360LowerChecked :
    lowerCheck 24 leaf360Box leaf360Inputs = true := by
  rfl'

private theorem leaf360CoversExact : CoversExact 8
    leaf360Box leaf360Certificate leaf360InnerLog leaf360Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk46RoundedFacts chi46RoundedFacts
    innerPair27RoundedFacts leaf360RoundedFacts (by rfl)

private theorem leaf360FlatSound : Sound leaf360Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf360CertificateValid
    leaf360InnerLogValid leaf360CoversExact leaf360LowerChecked

private noncomputable def leaf361Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/16), kHi := (51/32), chiLo := (9/32), chiHi := (5/16) }

private noncomputable def leaf361Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108985/67108864) }, vSqrt := { lower := (16383/16384), upper := (68718493695/68717387776) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (96565377/67108864) }, upper := { exponent := 0, mantissa := (767/512) } }, logOuter := sk45LogOuterCertificate, logK := sk45LogKCertificate, logChi := chi47LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (137435881471/137434775552) } }, logDArg := sk45LogDArgCertificate }

private noncomputable def leaf361InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf361LocalValidity :
    LeafFacts leaf361Box leaf361Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf361Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (68718493695/68717387776) }) = true
      norm_num [leaf361Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf361CertificateValid :
    WideCertificateValid leaf361Box leaf361Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk45ValidityFacts chi47ValidityFacts
    leaf361LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf361CoverageChecked :
    coverageCheck (innerAD leaf361Box) leaf361InnerLog = true := by
  rfl'

private theorem leaf361InnerLogValid :
    leaf361InnerLog.Valid 8 (innerAD leaf361Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf361CoverageChecked

private noncomputable def leaf361InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (363413/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf361InputLogOnePlusV_eq :
    leaf361InputLogOnePlusV = outerEnclosure 24
      (leaf361Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf361RoundedFacts : LeafRoundedFacts 8
    leaf361Certificate.logOnePlusV leaf361InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf361InputLogOnePlusV_eq }

private noncomputable def leaf361Inputs : Inputs :=
  inputsOfCaches globalInput sk45RoundedInputs
    chi47InputQChi innerPair34Input
    leaf361InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf361LowerChecked :
    lowerCheck 24 leaf361Box leaf361Inputs = true := by
  rfl'

private theorem leaf361CoversExact : CoversExact 8
    leaf361Box leaf361Certificate leaf361InnerLog leaf361Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk45RoundedFacts chi47RoundedFacts
    innerPair34RoundedFacts leaf361RoundedFacts (by rfl)

private theorem leaf361FlatSound : Sound leaf361Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf361CertificateValid
    leaf361InnerLogValid leaf361CoversExact leaf361LowerChecked

private noncomputable def leaf362Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/32), kHi := (13/8), chiLo := (9/32), chiHi := (5/16) }

private noncomputable def leaf362Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108987/67108864) }, vSqrt := { lower := (16383/16384), upper := (22906164565/22905782272) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (97155163/67108864) }, upper := { exponent := 0, mantissa := (193/128) } }, logOuter := sk46LogOuterCertificate, logK := sk46LogKCertificate, logChi := chi47LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (45811946837/45811564544) } }, logDArg := sk46LogDArgCertificate }

private noncomputable def leaf362InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf362LocalValidity :
    LeafFacts leaf362Box leaf362Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf362Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (22906164565/22905782272) }) = true
      norm_num [leaf362Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf362CertificateValid :
    WideCertificateValid leaf362Box leaf362Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk46ValidityFacts chi47ValidityFacts
    leaf362LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf362CoverageChecked :
    coverageCheck (innerAD leaf362Box) leaf362InnerLog = true := by
  rfl'

private theorem leaf362InnerLogValid :
    leaf362InnerLog.Valid 8 (innerAD leaf362Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf362CoverageChecked

private noncomputable def leaf362InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629221/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf362InputLogOnePlusV_eq :
    leaf362InputLogOnePlusV = outerEnclosure 24
      (leaf362Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf362RoundedFacts : LeafRoundedFacts 8
    leaf362Certificate.logOnePlusV leaf362InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf362InputLogOnePlusV_eq }

private noncomputable def leaf362Inputs : Inputs :=
  inputsOfCaches globalInput sk46RoundedInputs
    chi47InputQChi innerPair35Input
    leaf362InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf362LowerChecked :
    lowerCheck 24 leaf362Box leaf362Inputs = true := by
  rfl'

private theorem leaf362CoversExact : CoversExact 8
    leaf362Box leaf362Certificate leaf362InnerLog leaf362Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk46RoundedFacts chi47RoundedFacts
    innerPair35RoundedFacts leaf362RoundedFacts (by rfl)

private theorem leaf362FlatSound : Sound leaf362Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf362CertificateValid
    leaf362InnerLogValid leaf362CoversExact leaf362LowerChecked

private noncomputable def leaf363Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (53/32), chiLo := (1/4), chiHi := (9/32) }

private noncomputable def leaf363Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108987/67108864) }, vSqrt := { lower := (16383/16384), upper := (986896/986867) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (94337287/67108864) }, upper := { exponent := 0, mantissa := (1501/1024) } }, logOuter := sk55LogOuterCertificate, logK := sk55LogKCertificate, logChi := chi46LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (1973763/1973734) } }, logDArg := sk55LogDArgCertificate }

private noncomputable def leaf363InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf363LocalValidity :
    LeafFacts leaf363Box leaf363Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf363Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (986896/986867) }) = true
      norm_num [leaf363Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf363CertificateValid :
    WideCertificateValid leaf363Box leaf363Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk55ValidityFacts chi46ValidityFacts
    leaf363LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf363CoverageChecked :
    coverageCheck (innerAD leaf363Box) leaf363InnerLog = true := by
  rfl'

private theorem leaf363InnerLogValid :
    leaf363InnerLog.Valid 8 (innerAD leaf363Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf363CoverageChecked

private noncomputable def leaf363InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629327/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf363InputLogOnePlusV_eq :
    leaf363InputLogOnePlusV = outerEnclosure 24
      (leaf363Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf363RoundedFacts : LeafRoundedFacts 8
    leaf363Certificate.logOnePlusV leaf363InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf363InputLogOnePlusV_eq }

private noncomputable def leaf363Inputs : Inputs :=
  inputsOfCaches globalInput sk55RoundedInputs
    chi46InputQChi innerPair27Input
    leaf363InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf363LowerChecked :
    lowerCheck 24 leaf363Box leaf363Inputs = true := by
  rfl'

private theorem leaf363CoversExact : CoversExact 8
    leaf363Box leaf363Certificate leaf363InnerLog leaf363Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk55RoundedFacts chi46RoundedFacts
    innerPair27RoundedFacts leaf363RoundedFacts (by rfl)

private theorem leaf363FlatSound : Sound leaf363Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf363CertificateValid
    leaf363InnerLogValid leaf363CoversExact leaf363LowerChecked

private noncomputable def leaf364Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/32), kHi := (27/16), chiLo := (1/4), chiHi := (9/32) }

private noncomputable def leaf364Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108989/67108864) }, vSqrt := { lower := (16383/16384), upper := (8388616/8388365) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (94861541/67108864) }, upper := { exponent := 0, mantissa := (755/512) } }, logOuter := sk56LogOuterCertificate, logK := sk56LogKCertificate, logChi := chi46LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (16776981/16776730) } }, logDArg := sk56LogDArgCertificate }

private noncomputable def leaf364InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf364LocalValidity :
    LeafFacts leaf364Box leaf364Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf364Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (8388616/8388365) }) = true
      norm_num [leaf364Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf364CertificateValid :
    WideCertificateValid leaf364Box leaf364Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk56ValidityFacts chi46ValidityFacts
    leaf364LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf364CoverageChecked :
    coverageCheck (innerAD leaf364Box) leaf364InnerLog = true := by
  rfl'

private theorem leaf364InnerLogValid :
    leaf364InnerLog.Valid 8 (innerAD leaf364Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf364CoverageChecked

private noncomputable def leaf364InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (2907333/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf364InputLogOnePlusV_eq :
    leaf364InputLogOnePlusV = outerEnclosure 24
      (leaf364Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf364RoundedFacts : LeafRoundedFacts 8
    leaf364Certificate.logOnePlusV leaf364InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf364InputLogOnePlusV_eq }

private noncomputable def leaf364Inputs : Inputs :=
  inputsOfCaches globalInput sk56RoundedInputs
    chi46InputQChi innerPair27Input
    leaf364InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf364LowerChecked :
    lowerCheck 24 leaf364Box leaf364Inputs = true := by
  rfl'

private theorem leaf364CoversExact : CoversExact 8
    leaf364Box leaf364Certificate leaf364InnerLog leaf364Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk56RoundedFacts chi46RoundedFacts
    innerPair27RoundedFacts leaf364RoundedFacts (by rfl)

private theorem leaf364FlatSound : Sound leaf364Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf364CertificateValid
    leaf364InnerLogValid leaf364CoversExact leaf364LowerChecked

private noncomputable def leaf365Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/16), kHi := (7/4), chiLo := (1/4), chiHi := (17/64) }

private noncomputable def leaf365Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108953/67108864) }, vSqrt := { lower := (16383/16384), upper := (4194312/4194185) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (95385833/67108864) }, upper := { exponent := 0, mantissa := (375/256) } }, logOuter := sk34LogOuterCertificate, logK := sk34LogKCertificate, logChi := chi54LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (8388497/8388370) } }, logDArg := sk34LogDArgCertificate }

private noncomputable def leaf365InnerLog : WideLogData :=
  innerPair145Data

set_option maxRecDepth 1000000 in
private theorem leaf365LocalValidity :
    LeafFacts leaf365Box leaf365Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf365Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (4194312/4194185) }) = true
      norm_num [leaf365Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf365CertificateValid :
    WideCertificateValid leaf365Box leaf365Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk34ValidityFacts chi54ValidityFacts
    leaf365LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf365CoverageChecked :
    coverageCheck (innerAD leaf365Box) leaf365InnerLog = true := by
  rfl'

private theorem leaf365InnerLogValid :
    leaf365InnerLog.Valid 8 (innerAD leaf365Box) :=
  wideLogDataValid_of_cachedCheck endpoint38PositiveFacts
    endpoint42PositiveFacts.valid leaf365CoverageChecked

private noncomputable def leaf365InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629335/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf365InputLogOnePlusV_eq :
    leaf365InputLogOnePlusV = outerEnclosure 24
      (leaf365Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf365RoundedFacts : LeafRoundedFacts 8
    leaf365Certificate.logOnePlusV leaf365InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf365InputLogOnePlusV_eq }

private noncomputable def leaf365Inputs : Inputs :=
  inputsOfCaches globalInput sk34RoundedInputs
    chi54InputQChi innerPair145Input
    leaf365InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf365LowerChecked :
    lowerCheck 24 leaf365Box leaf365Inputs = true := by
  rfl'

private theorem leaf365CoversExact : CoversExact 8
    leaf365Box leaf365Certificate leaf365InnerLog leaf365Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk34RoundedFacts chi54RoundedFacts
    innerPair145RoundedFacts leaf365RoundedFacts (by rfl)

private theorem leaf365FlatSound : Sound leaf365Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf365CertificateValid
    leaf365InnerLogValid leaf365CoversExact leaf365LowerChecked

private noncomputable def leaf366Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/16), kHi := (7/4), chiLo := (17/64), chiHi := (9/32) }

private noncomputable def leaf366Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108955/67108864) }, vSqrt := { lower := (16383/16384), upper := (34359279615/34358706176) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (97155195/67108864) }, upper := { exponent := 0, mantissa := (191/128) } }, logOuter := sk34LogOuterCertificate, logK := sk34LogKCertificate, logChi := chi55LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68717985791/68717412352) } }, logDArg := sk34LogDArgCertificate }

private noncomputable def leaf366InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf366LocalValidity :
    LeafFacts leaf366Box leaf366Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf366Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34359279615/34358706176) }) = true
      norm_num [leaf366Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf366CertificateValid :
    WideCertificateValid leaf366Box leaf366Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk34ValidityFacts chi55ValidityFacts
    leaf366LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf366CoverageChecked :
    coverageCheck (innerAD leaf366Box) leaf366InnerLog = true := by
  rfl'

private theorem leaf366InnerLogValid :
    leaf366InnerLog.Valid 8 (innerAD leaf366Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf366CoverageChecked

private noncomputable def leaf366InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629221/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf366InputLogOnePlusV_eq :
    leaf366InputLogOnePlusV = outerEnclosure 24
      (leaf366Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf366RoundedFacts : LeafRoundedFacts 8
    leaf366Certificate.logOnePlusV leaf366InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf366InputLogOnePlusV_eq }

private noncomputable def leaf366Inputs : Inputs :=
  inputsOfCaches globalInput sk34RoundedInputs
    chi55InputQChi innerPair34Input
    leaf366InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf366LowerChecked :
    lowerCheck 24 leaf366Box leaf366Inputs = true := by
  rfl'

private theorem leaf366CoversExact : CoversExact 8
    leaf366Box leaf366Certificate leaf366InnerLog leaf366Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk34RoundedFacts chi55RoundedFacts
    innerPair34RoundedFacts leaf366RoundedFacts (by rfl)

private theorem leaf366FlatSound : Sound leaf366Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf366CertificateValid
    leaf366InnerLogValid leaf366CoversExact leaf366LowerChecked

private noncomputable def leaf367Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (27/16), chiLo := (9/32), chiHi := (19/64) }

private noncomputable def leaf367Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108955/67108864) }, vSqrt := { lower := (16383/16384), upper := (133693695/133691392) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (97744983/67108864) }, upper := { exponent := 0, mantissa := (1537/1024) } }, logOuter := sk33LogOuterCertificate, logK := sk33LogKCertificate, logChi := chi56LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (267385087/267382784) } }, logDArg := sk33LogDArgCertificate }

private noncomputable def leaf367InnerLog : WideLogData :=
  innerPair148Data

set_option maxRecDepth 1000000 in
private theorem leaf367LocalValidity :
    LeafFacts leaf367Box leaf367Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf367Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (133693695/133691392) }) = true
      norm_num [leaf367Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf367CertificateValid :
    WideCertificateValid leaf367Box leaf367Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk33ValidityFacts chi56ValidityFacts
    leaf367LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf367CoverageChecked :
    coverageCheck (innerAD leaf367Box) leaf367InnerLog = true := by
  rfl'

private theorem leaf367InnerLogValid :
    leaf367InnerLog.Valid 8 (innerAD leaf367Box) :=
  wideLogDataValid_of_cachedCheck endpoint41PositiveFacts
    endpoint49PositiveFacts.valid leaf367CoverageChecked

private noncomputable def leaf367InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629225/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf367InputLogOnePlusV_eq :
    leaf367InputLogOnePlusV = outerEnclosure 24
      (leaf367Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf367RoundedFacts : LeafRoundedFacts 8
    leaf367Certificate.logOnePlusV leaf367InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf367InputLogOnePlusV_eq }

private noncomputable def leaf367Inputs : Inputs :=
  inputsOfCaches globalInput sk33RoundedInputs
    chi56InputQChi innerPair148Input
    leaf367InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf367LowerChecked :
    lowerCheck 24 leaf367Box leaf367Inputs = true := by
  rfl'

private theorem leaf367CoversExact : CoversExact 8
    leaf367Box leaf367Certificate leaf367InnerLog leaf367Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk33RoundedFacts chi56RoundedFacts
    innerPair148RoundedFacts leaf367RoundedFacts (by rfl)

private theorem leaf367FlatSound : Sound leaf367Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf367CertificateValid
    leaf367InnerLogValid leaf367CoversExact leaf367LowerChecked

private noncomputable def leaf368Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (27/16), chiLo := (19/64), chiHi := (5/16) }

private noncomputable def leaf368Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108957/67108864) }, vSqrt := { lower := (16383/16384), upper := (34359279615/34358632448) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (99448813/67108864) }, upper := { exponent := 0, mantissa := (391/256) } }, logOuter := sk33LogOuterCertificate, logK := sk33LogKCertificate, logChi := chi57LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68717912063/68717264896) } }, logDArg := sk33LogDArgCertificate }

private noncomputable def leaf368InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf368LocalValidity :
    LeafFacts leaf368Box leaf368Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf368Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34359279615/34358632448) }) = true
      norm_num [leaf368Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf368CertificateValid :
    WideCertificateValid leaf368Box leaf368Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk33ValidityFacts chi57ValidityFacts
    leaf368LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf368CoverageChecked :
    coverageCheck (innerAD leaf368Box) leaf368InnerLog = true := by
  rfl'

private theorem leaf368InnerLogValid :
    leaf368InnerLog.Valid 8 (innerAD leaf368Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf368CoverageChecked

private noncomputable def leaf368InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629239/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf368InputLogOnePlusV_eq :
    leaf368InputLogOnePlusV = outerEnclosure 24
      (leaf368Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf368RoundedFacts : LeafRoundedFacts 8
    leaf368Certificate.logOnePlusV leaf368InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf368InputLogOnePlusV_eq }

private noncomputable def leaf368Inputs : Inputs :=
  inputsOfCaches globalInput sk33RoundedInputs
    chi57InputQChi innerPair35Input
    leaf368InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf368LowerChecked :
    lowerCheck 24 leaf368Box leaf368Inputs = true := by
  rfl'

private theorem leaf368CoversExact : CoversExact 8
    leaf368Box leaf368Certificate leaf368InnerLog leaf368Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk33RoundedFacts chi57RoundedFacts
    innerPair35RoundedFacts leaf368RoundedFacts (by rfl)

private theorem leaf368FlatSound : Sound leaf368Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf368CertificateValid
    leaf368InnerLogValid leaf368CoversExact leaf368LowerChecked

private noncomputable def leaf369Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/16), kHi := (7/4), chiLo := (9/32), chiHi := (19/64) }

private noncomputable def leaf369Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108957/67108864) }, vSqrt := { lower := (16383/16384), upper := (3817697735/3817627648) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (98924557/67108864) }, upper := { exponent := 0, mantissa := (389/256) } }, logOuter := sk34LogOuterCertificate, logK := sk34LogKCertificate, logChi := chi56LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (7635325383/7635255296) } }, logDArg := sk34LogDArgCertificate }

private noncomputable def leaf369InnerLog : WideLogData :=
  innerPair151Data

set_option maxRecDepth 1000000 in
private theorem leaf369LocalValidity :
    LeafFacts leaf369Box leaf369Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf369Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (3817697735/3817627648) }) = true
      norm_num [leaf369Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf369CertificateValid :
    WideCertificateValid leaf369Box leaf369Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk34ValidityFacts chi56ValidityFacts
    leaf369LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf369CoverageChecked :
    coverageCheck (innerAD leaf369Box) leaf369InnerLog = true := by
  rfl'

private theorem leaf369InnerLogValid :
    leaf369InnerLog.Valid 8 (innerAD leaf369Box) :=
  wideLogDataValid_of_cachedCheck endpoint42PositiveFacts
    endpoint19PositiveFacts.valid leaf369CoverageChecked

private noncomputable def leaf369InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629235/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf369InputLogOnePlusV_eq :
    leaf369InputLogOnePlusV = outerEnclosure 24
      (leaf369Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf369RoundedFacts : LeafRoundedFacts 8
    leaf369Certificate.logOnePlusV leaf369InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf369InputLogOnePlusV_eq }

private noncomputable def leaf369Inputs : Inputs :=
  inputsOfCaches globalInput sk34RoundedInputs
    chi56InputQChi innerPair151Input
    leaf369InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf369LowerChecked :
    lowerCheck 24 leaf369Box leaf369Inputs = true := by
  rfl'

private theorem leaf369CoversExact : CoversExact 8
    leaf369Box leaf369Certificate leaf369InnerLog leaf369Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk34RoundedFacts chi56RoundedFacts
    innerPair151RoundedFacts leaf369RoundedFacts (by rfl)

private theorem leaf369FlatSound : Sound leaf369Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf369CertificateValid
    leaf369InnerLogValid leaf369CoversExact leaf369LowerChecked

private noncomputable def leaf370Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/16), kHi := (7/4), chiLo := (19/64), chiHi := (5/16) }

private noncomputable def leaf370Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108959/67108864) }, vSqrt := { lower := (16383/16384), upper := (34359279615/34358591488) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (100693919/67108864) }, upper := { exponent := 0, mantissa := (99/64) } }, logOuter := sk34LogOuterCertificate, logK := sk34LogKCertificate, logChi := chi57LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68717871103/68717182976) } }, logDArg := sk34LogDArgCertificate }

private noncomputable def leaf370InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf370LocalValidity :
    LeafFacts leaf370Box leaf370Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf370Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34359279615/34358591488) }) = true
      norm_num [leaf370Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf370CertificateValid :
    WideCertificateValid leaf370Box leaf370Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk34ValidityFacts chi57ValidityFacts
    leaf370LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf370CoverageChecked :
    coverageCheck (innerAD leaf370Box) leaf370InnerLog = true := by
  rfl'

private theorem leaf370InnerLogValid :
    leaf370InnerLog.Valid 8 (innerAD leaf370Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf370CoverageChecked

private noncomputable def leaf370InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629249/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf370InputLogOnePlusV_eq :
    leaf370InputLogOnePlusV = outerEnclosure 24
      (leaf370Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf370RoundedFacts : LeafRoundedFacts 8
    leaf370Certificate.logOnePlusV leaf370InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf370InputLogOnePlusV_eq }

private noncomputable def leaf370Inputs : Inputs :=
  inputsOfCaches globalInput sk34RoundedInputs
    chi57InputQChi innerPair40Input
    leaf370InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf370LowerChecked :
    lowerCheck 24 leaf370Box leaf370Inputs = true := by
  rfl'

private theorem leaf370CoversExact : CoversExact 8
    leaf370Box leaf370Certificate leaf370InnerLog leaf370Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk34RoundedFacts chi57RoundedFacts
    innerPair40RoundedFacts leaf370RoundedFacts (by rfl)

private theorem leaf370FlatSound : Sound leaf370Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf370CertificateValid
    leaf370InnerLogValid leaf370CoversExact leaf370LowerChecked

private noncomputable def leaf371Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (49/32), chiLo := (5/16), chiHi := (11/32) }

private noncomputable def leaf371Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108983/67108864) }, vSqrt := { lower := (16383/16384), upper := (68718493695/68717268992) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (98531339/67108864) }, upper := { exponent := 0, mantissa := (1563/1024) } }, logOuter := sk43LogOuterCertificate, logK := sk43LogKCertificate, logChi := chi48LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (137435762687/137434537984) } }, logDArg := sk43LogDArgCertificate }

private noncomputable def leaf371InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf371LocalValidity :
    LeafFacts leaf371Box leaf371Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf371Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (68718493695/68717268992) }) = true
      norm_num [leaf371Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf371CertificateValid :
    WideCertificateValid leaf371Box leaf371Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk43ValidityFacts chi48ValidityFacts
    leaf371LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf371CoverageChecked :
    coverageCheck (innerAD leaf371Box) leaf371InnerLog = true := by
  rfl'

private theorem leaf371InnerLogValid :
    leaf371InnerLog.Valid 8 (innerAD leaf371Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf371CoverageChecked

private noncomputable def leaf371InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (5814615/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf371InputLogOnePlusV_eq :
    leaf371InputLogOnePlusV = outerEnclosure 24
      (leaf371Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf371RoundedFacts : LeafRoundedFacts 8
    leaf371Certificate.logOnePlusV leaf371InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf371InputLogOnePlusV_eq }

private noncomputable def leaf371Inputs : Inputs :=
  inputsOfCaches globalInput sk43RoundedInputs
    chi48InputQChi innerPair35Input
    leaf371InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf371LowerChecked :
    lowerCheck 24 leaf371Box leaf371Inputs = true := by
  rfl'

private theorem leaf371CoversExact : CoversExact 8
    leaf371Box leaf371Certificate leaf371InnerLog leaf371Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk43RoundedFacts chi48RoundedFacts
    innerPair35RoundedFacts leaf371RoundedFacts (by rfl)

private theorem leaf371FlatSound : Sound leaf371Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf371CertificateValid
    leaf371InnerLogValid leaf371CoversExact leaf371LowerChecked

private noncomputable def leaf372Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/32), kHi := (25/16), chiLo := (5/16), chiHi := (11/32) }

private noncomputable def leaf372Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108985/67108864) }, vSqrt := { lower := (16383/16384), upper := (22906164565/22905741312) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (99186657/67108864) }, upper := { exponent := 0, mantissa := (787/512) } }, logOuter := sk44LogOuterCertificate, logK := sk44LogKCertificate, logChi := chi48LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (45811905877/45811482624) } }, logDArg := sk44LogDArgCertificate }

private noncomputable def leaf372InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf372LocalValidity :
    LeafFacts leaf372Box leaf372Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf372Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (22906164565/22905741312) }) = true
      norm_num [leaf372Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf372CertificateValid :
    WideCertificateValid leaf372Box leaf372Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk44ValidityFacts chi48ValidityFacts
    leaf372LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf372CoverageChecked :
    coverageCheck (innerAD leaf372Box) leaf372InnerLog = true := by
  rfl'

private theorem leaf372InnerLogValid :
    leaf372InnerLog.Valid 8 (innerAD leaf372Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf372CoverageChecked

private noncomputable def leaf372InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (2907309/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf372InputLogOnePlusV_eq :
    leaf372InputLogOnePlusV = outerEnclosure 24
      (leaf372Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf372RoundedFacts : LeafRoundedFacts 8
    leaf372Certificate.logOnePlusV leaf372InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf372InputLogOnePlusV_eq }

private noncomputable def leaf372Inputs : Inputs :=
  inputsOfCaches globalInput sk44RoundedInputs
    chi48InputQChi innerPair35Input
    leaf372InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf372LowerChecked :
    lowerCheck 24 leaf372Box leaf372Inputs = true := by
  rfl'

private theorem leaf372CoversExact : CoversExact 8
    leaf372Box leaf372Certificate leaf372InnerLog leaf372Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk44RoundedFacts chi48RoundedFacts
    innerPair35RoundedFacts leaf372RoundedFacts (by rfl)

private theorem leaf372FlatSound : Sound leaf372Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf372CertificateValid
    leaf372InnerLogValid leaf372CoversExact leaf372LowerChecked

private noncomputable def leaf373Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (49/32), chiLo := (11/32), chiHi := (3/8) }

private noncomputable def leaf373Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108985/67108864) }, vSqrt := { lower := (16383/16384), upper := (68718493695/68717068288) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (101676873/67108864) }, upper := { exponent := 0, mantissa := (403/256) } }, logOuter := sk43LogOuterCertificate, logK := sk43LogKCertificate, logChi := chi49LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (137435561983/137434136576) } }, logDArg := sk43LogDArgCertificate }

private noncomputable def leaf373InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf373LocalValidity :
    LeafFacts leaf373Box leaf373Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf373Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (68718493695/68717068288) }) = true
      norm_num [leaf373Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf373CertificateValid :
    WideCertificateValid leaf373Box leaf373Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk43ValidityFacts chi49ValidityFacts
    leaf373LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf373CoverageChecked :
    coverageCheck (innerAD leaf373Box) leaf373InnerLog = true := by
  rfl'

private theorem leaf373InnerLogValid :
    leaf373InnerLog.Valid 8 (innerAD leaf373Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf373CoverageChecked

private noncomputable def leaf373InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629255/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf373InputLogOnePlusV_eq :
    leaf373InputLogOnePlusV = outerEnclosure 24
      (leaf373Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf373RoundedFacts : LeafRoundedFacts 8
    leaf373Certificate.logOnePlusV leaf373InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf373InputLogOnePlusV_eq }

private noncomputable def leaf373Inputs : Inputs :=
  inputsOfCaches globalInput sk43RoundedInputs
    chi49InputQChi innerPair41Input
    leaf373InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf373LowerChecked :
    lowerCheck 24 leaf373Box leaf373Inputs = true := by
  rfl'

private theorem leaf373CoversExact : CoversExact 8
    leaf373Box leaf373Certificate leaf373InnerLog leaf373Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk43RoundedFacts chi49RoundedFacts
    innerPair41RoundedFacts leaf373RoundedFacts (by rfl)

private theorem leaf373FlatSound : Sound leaf373Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf373CertificateValid
    leaf373InnerLogValid leaf373CoversExact leaf373LowerChecked

private noncomputable def leaf374Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/32), kHi := (25/16), chiLo := (11/32), chiHi := (3/8) }

private noncomputable def leaf374Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108987/67108864) }, vSqrt := { lower := (16383/16384), upper := (68718493695/68717019136) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (102397723/67108864) }, upper := { exponent := 0, mantissa := (203/128) } }, logOuter := sk44LogOuterCertificate, logK := sk44LogKCertificate, logChi := chi49LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (137435512831/137434038272) } }, logDArg := sk44LogDArgCertificate }

private noncomputable def leaf374InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf374LocalValidity :
    LeafFacts leaf374Box leaf374Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf374Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (68718493695/68717019136) }) = true
      norm_num [leaf374Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf374CertificateValid :
    WideCertificateValid leaf374Box leaf374Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk44ValidityFacts chi49ValidityFacts
    leaf374LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf374CoverageChecked :
    coverageCheck (innerAD leaf374Box) leaf374InnerLog = true := by
  rfl'

private theorem leaf374InnerLogValid :
    leaf374InnerLog.Valid 8 (innerAD leaf374Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf374CoverageChecked

private noncomputable def leaf374InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629261/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf374InputLogOnePlusV_eq :
    leaf374InputLogOnePlusV = outerEnclosure 24
      (leaf374Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf374RoundedFacts : LeafRoundedFacts 8
    leaf374Certificate.logOnePlusV leaf374InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf374InputLogOnePlusV_eq }

private noncomputable def leaf374Inputs : Inputs :=
  inputsOfCaches globalInput sk44RoundedInputs
    chi49InputQChi innerPair41Input
    leaf374InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf374LowerChecked :
    lowerCheck 24 leaf374Box leaf374Inputs = true := by
  rfl'

private theorem leaf374CoversExact : CoversExact 8
    leaf374Box leaf374Certificate leaf374InnerLog leaf374Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk44RoundedFacts chi49RoundedFacts
    innerPair41RoundedFacts leaf374RoundedFacts (by rfl)

private theorem leaf374FlatSound : Sound leaf374Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf374CertificateValid
    leaf374InnerLogValid leaf374CoversExact leaf374LowerChecked

private noncomputable def leaf375Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/16), kHi := (13/8), chiLo := (5/16), chiHi := (21/64) }

private noncomputable def leaf375Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108957/67108864) }, vSqrt := { lower := (16383/16384), upper := (6871855923/6871724032) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (99842005/67108864) }, upper := { exponent := 0, mantissa := (785/512) } }, logOuter := sk36LogOuterCertificate, logK := sk36LogKCertificate, logChi := chi58LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (13743579955/13743448064) } }, logDArg := sk36LogDArgCertificate }

private noncomputable def leaf375InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf375LocalValidity :
    LeafFacts leaf375Box leaf375Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf375Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (6871855923/6871724032) }) = true
      norm_num [leaf375Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf375CertificateValid :
    WideCertificateValid leaf375Box leaf375Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk36ValidityFacts chi58ValidityFacts
    leaf375LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf375CoverageChecked :
    coverageCheck (innerAD leaf375Box) leaf375InnerLog = true := by
  rfl'

private theorem leaf375InnerLogValid :
    leaf375InnerLog.Valid 8 (innerAD leaf375Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf375CoverageChecked

private noncomputable def leaf375InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (5814621/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf375InputLogOnePlusV_eq :
    leaf375InputLogOnePlusV = outerEnclosure 24
      (leaf375Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf375RoundedFacts : LeafRoundedFacts 8
    leaf375Certificate.logOnePlusV leaf375InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf375InputLogOnePlusV_eq }

private noncomputable def leaf375Inputs : Inputs :=
  inputsOfCaches globalInput sk36RoundedInputs
    chi58InputQChi innerPair35Input
    leaf375InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf375LowerChecked :
    lowerCheck 24 leaf375Box leaf375Inputs = true := by
  rfl'

private theorem leaf375CoversExact : CoversExact 8
    leaf375Box leaf375Certificate leaf375InnerLog leaf375Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk36RoundedFacts chi58RoundedFacts
    innerPair35RoundedFacts leaf375RoundedFacts (by rfl)

private theorem leaf375FlatSound : Sound leaf375Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf375CertificateValid
    leaf375InnerLogValid leaf375CoversExact leaf375LowerChecked

private noncomputable def leaf376Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/16), kHi := (13/8), chiLo := (21/64), chiHi := (11/32) }

private noncomputable def leaf376Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108959/67108864) }, vSqrt := { lower := (16383/16384), upper := (34359279615/34358566912) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (101480303/67108864) }, upper := { exponent := 0, mantissa := (399/256) } }, logOuter := sk36LogOuterCertificate, logK := sk36LogKCertificate, logChi := chi59LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68717846527/68717133824) } }, logDArg := sk36LogDArgCertificate }

private noncomputable def leaf376InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf376LocalValidity :
    LeafFacts leaf376Box leaf376Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf376Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34359279615/34358566912) }) = true
      norm_num [leaf376Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf376CertificateValid :
    WideCertificateValid leaf376Box leaf376Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk36ValidityFacts chi59ValidityFacts
    leaf376LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf376CoverageChecked :
    coverageCheck (innerAD leaf376Box) leaf376InnerLog = true := by
  rfl'

private theorem leaf376InnerLogValid :
    leaf376InnerLog.Valid 8 (innerAD leaf376Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf376CoverageChecked

private noncomputable def leaf376InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629255/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf376InputLogOnePlusV_eq :
    leaf376InputLogOnePlusV = outerEnclosure 24
      (leaf376Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf376RoundedFacts : LeafRoundedFacts 8
    leaf376Certificate.logOnePlusV leaf376InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf376InputLogOnePlusV_eq }

private noncomputable def leaf376Inputs : Inputs :=
  inputsOfCaches globalInput sk36RoundedInputs
    chi59InputQChi innerPair40Input
    leaf376InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf376LowerChecked :
    lowerCheck 24 leaf376Box leaf376Inputs = true := by
  rfl'

private theorem leaf376CoversExact : CoversExact 8
    leaf376Box leaf376Certificate leaf376InnerLog leaf376Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk36RoundedFacts chi59RoundedFacts
    innerPair40RoundedFacts leaf376RoundedFacts (by rfl)

private theorem leaf376FlatSound : Sound leaf376Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf376CertificateValid
    leaf376InnerLogValid leaf376CoversExact leaf376LowerChecked

private noncomputable def leaf377Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/16), kHi := (13/8), chiLo := (11/32), chiHi := (23/64) }

private noncomputable def leaf377Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108961/67108864) }, vSqrt := { lower := (16383/16384), upper := (11453093205/11452837888) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (103118601/67108864) }, upper := { exponent := 0, mantissa := (811/512) } }, logOuter := sk36LogOuterCertificate, logK := sk36LogKCertificate, logChi := chi60LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (22905931093/22905675776) } }, logDArg := sk36LogDArgCertificate }

private noncomputable def leaf377InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf377LocalValidity :
    LeafFacts leaf377Box leaf377Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf377Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (11453093205/11452837888) }) = true
      norm_num [leaf377Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf377CertificateValid :
    WideCertificateValid leaf377Box leaf377Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk36ValidityFacts chi60ValidityFacts
    leaf377LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf377CoverageChecked :
    coverageCheck (innerAD leaf377Box) leaf377InnerLog = true := by
  rfl'

private theorem leaf377InnerLogValid :
    leaf377InnerLog.Valid 8 (innerAD leaf377Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf377CoverageChecked

private noncomputable def leaf377InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (2907317/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf377InputLogOnePlusV_eq :
    leaf377InputLogOnePlusV = outerEnclosure 24
      (leaf377Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf377RoundedFacts : LeafRoundedFacts 8
    leaf377Certificate.logOnePlusV leaf377InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf377InputLogOnePlusV_eq }

private noncomputable def leaf377Inputs : Inputs :=
  inputsOfCaches globalInput sk36RoundedInputs
    chi60InputQChi innerPair41Input
    leaf377InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf377LowerChecked :
    lowerCheck 24 leaf377Box leaf377Inputs = true := by
  rfl'

private theorem leaf377CoversExact : CoversExact 8
    leaf377Box leaf377Certificate leaf377InnerLog leaf377Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk36RoundedFacts chi60RoundedFacts
    innerPair41RoundedFacts leaf377RoundedFacts (by rfl)

private theorem leaf377FlatSound : Sound leaf377Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf377CertificateValid
    leaf377InnerLogValid leaf377CoversExact leaf377LowerChecked

private noncomputable def leaf378Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/16), kHi := (13/8), chiLo := (23/64), chiHi := (3/8) }

private noncomputable def leaf378Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108963/67108864) }, vSqrt := { lower := (16383/16384), upper := (34359279615/34358460416) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (104756899/67108864) }, upper := { exponent := 0, mantissa := (103/64) } }, logOuter := sk36LogOuterCertificate, logK := sk36LogKCertificate, logChi := chi61LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68717740031/68716920832) } }, logDArg := sk36LogDArgCertificate }

private noncomputable def leaf378InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf378LocalValidity :
    LeafFacts leaf378Box leaf378Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf378Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34359279615/34358460416) }) = true
      norm_num [leaf378Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf378CertificateValid :
    WideCertificateValid leaf378Box leaf378Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk36ValidityFacts chi61ValidityFacts
    leaf378LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf378CoverageChecked :
    coverageCheck (innerAD leaf378Box) leaf378InnerLog = true := by
  rfl'

private theorem leaf378InnerLogValid :
    leaf378InnerLog.Valid 8 (innerAD leaf378Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf378CoverageChecked

private noncomputable def leaf378InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629281/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf378InputLogOnePlusV_eq :
    leaf378InputLogOnePlusV = outerEnclosure 24
      (leaf378Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf378RoundedFacts : LeafRoundedFacts 8
    leaf378Certificate.logOnePlusV leaf378InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf378InputLogOnePlusV_eq }

private noncomputable def leaf378Inputs : Inputs :=
  inputsOfCaches globalInput sk36RoundedInputs
    chi61InputQChi innerPair41Input
    leaf378InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf378LowerChecked :
    lowerCheck 24 leaf378Box leaf378Inputs = true := by
  rfl'

private theorem leaf378CoversExact : CoversExact 8
    leaf378Box leaf378Certificate leaf378InnerLog leaf378Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk36RoundedFacts chi61RoundedFacts
    innerPair41RoundedFacts leaf378RoundedFacts (by rfl)

private theorem leaf378FlatSound : Sound leaf378Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf378CertificateValid
    leaf378InnerLogValid leaf378CoversExact leaf378LowerChecked

private noncomputable def leaf379Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (27/16), chiLo := (5/16), chiHi := (21/64) }

private noncomputable def leaf379Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108959/67108864) }, vSqrt := { lower := (16383/16384), upper := (34359279615/34358577152) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (101152643/67108864) }, upper := { exponent := 0, mantissa := (1591/1024) } }, logOuter := sk33LogOuterCertificate, logK := sk33LogKCertificate, logChi := chi58LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68717856767/68717154304) } }, logDArg := sk33LogDArgCertificate }

private noncomputable def leaf379InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf379LocalValidity :
    LeafFacts leaf379Box leaf379Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf379Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34359279615/34358577152) }) = true
      norm_num [leaf379Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf379CertificateValid :
    WideCertificateValid leaf379Box leaf379Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk33ValidityFacts chi58ValidityFacts
    leaf379LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf379CoverageChecked :
    coverageCheck (innerAD leaf379Box) leaf379InnerLog = true := by
  rfl'

private theorem leaf379InnerLogValid :
    leaf379InnerLog.Valid 8 (innerAD leaf379Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf379CoverageChecked

private noncomputable def leaf379InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (2907313/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf379InputLogOnePlusV_eq :
    leaf379InputLogOnePlusV = outerEnclosure 24
      (leaf379Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf379RoundedFacts : LeafRoundedFacts 8
    leaf379Certificate.logOnePlusV leaf379InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf379InputLogOnePlusV_eq }

private noncomputable def leaf379Inputs : Inputs :=
  inputsOfCaches globalInput sk33RoundedInputs
    chi58InputQChi innerPair40Input
    leaf379InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf379LowerChecked :
    lowerCheck 24 leaf379Box leaf379Inputs = true := by
  rfl'

private theorem leaf379CoversExact : CoversExact 8
    leaf379Box leaf379Certificate leaf379InnerLog leaf379Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk33RoundedFacts chi58RoundedFacts
    innerPair40RoundedFacts leaf379RoundedFacts (by rfl)

private theorem leaf379FlatSound : Sound leaf379Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf379CertificateValid
    leaf379InnerLogValid leaf379CoversExact leaf379LowerChecked

private noncomputable def leaf380Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (27/16), chiLo := (21/64), chiHi := (11/32) }

private noncomputable def leaf380Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108961/67108864) }, vSqrt := { lower := (16383/16384), upper := (34359279615/34358521856) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (102856473/67108864) }, upper := { exponent := 0, mantissa := (809/512) } }, logOuter := sk33LogOuterCertificate, logK := sk33LogKCertificate, logChi := chi59LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68717801471/68717043712) } }, logDArg := sk33LogDArgCertificate }

private noncomputable def leaf380InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf380LocalValidity :
    LeafFacts leaf380Box leaf380Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf380Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34359279615/34358521856) }) = true
      norm_num [leaf380Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf380CertificateValid :
    WideCertificateValid leaf380Box leaf380Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk33ValidityFacts chi59ValidityFacts
    leaf380LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf380CoverageChecked :
    coverageCheck (innerAD leaf380Box) leaf380InnerLog = true := by
  rfl'

private theorem leaf380InnerLogValid :
    leaf380InnerLog.Valid 8 (innerAD leaf380Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf380CoverageChecked

private noncomputable def leaf380InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (5814633/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf380InputLogOnePlusV_eq :
    leaf380InputLogOnePlusV = outerEnclosure 24
      (leaf380Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf380RoundedFacts : LeafRoundedFacts 8
    leaf380Certificate.logOnePlusV leaf380InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf380InputLogOnePlusV_eq }

private noncomputable def leaf380Inputs : Inputs :=
  inputsOfCaches globalInput sk33RoundedInputs
    chi59InputQChi innerPair41Input
    leaf380InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf380LowerChecked :
    lowerCheck 24 leaf380Box leaf380Inputs = true := by
  rfl'

private theorem leaf380CoversExact : CoversExact 8
    leaf380Box leaf380Certificate leaf380InnerLog leaf380Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk33RoundedFacts chi59RoundedFacts
    innerPair41RoundedFacts leaf380RoundedFacts (by rfl)

private theorem leaf380FlatSound : Sound leaf380Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf380CertificateValid
    leaf380InnerLogValid leaf380CoversExact leaf380LowerChecked

private noncomputable def leaf381Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/16), kHi := (7/4), chiLo := (5/16), chiHi := (21/64) }

private noncomputable def leaf381Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108961/67108864) }, vSqrt := { lower := (16383/16384), upper := (34359279615/34358534144) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (102463281/67108864) }, upper := { exponent := 0, mantissa := (403/256) } }, logOuter := sk34LogOuterCertificate, logK := sk34LogKCertificate, logChi := chi58LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68717813759/68717068288) } }, logDArg := sk34LogDArgCertificate }

private noncomputable def leaf381InnerLog : WideLogData :=
  innerPair178Data

set_option maxRecDepth 1000000 in
private theorem leaf381LocalValidity :
    LeafFacts leaf381Box leaf381Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf381Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34359279615/34358534144) }) = true
      norm_num [leaf381Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf381CertificateValid :
    WideCertificateValid leaf381Box leaf381Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk34ValidityFacts chi58ValidityFacts
    leaf381LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf381CoverageChecked :
    coverageCheck (innerAD leaf381Box) leaf381InnerLog = true := by
  rfl'

private theorem leaf381InnerLogValid :
    leaf381InnerLog.Valid 8 (innerAD leaf381Box) :=
  wideLogDataValid_of_cachedCheck endpoint49PositiveFacts
    endpoint47PositiveFacts.valid leaf381CoverageChecked

private noncomputable def leaf381InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629263/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf381InputLogOnePlusV_eq :
    leaf381InputLogOnePlusV = outerEnclosure 24
      (leaf381Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf381RoundedFacts : LeafRoundedFacts 8
    leaf381Certificate.logOnePlusV leaf381InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf381InputLogOnePlusV_eq }

private noncomputable def leaf381Inputs : Inputs :=
  inputsOfCaches globalInput sk34RoundedInputs
    chi58InputQChi innerPair178Input
    leaf381InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf381LowerChecked :
    lowerCheck 24 leaf381Box leaf381Inputs = true := by
  rfl'

private theorem leaf381CoversExact : CoversExact 8
    leaf381Box leaf381Certificate leaf381InnerLog leaf381Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk34RoundedFacts chi58RoundedFacts
    innerPair178RoundedFacts leaf381RoundedFacts (by rfl)

private theorem leaf381FlatSound : Sound leaf381Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf381CertificateValid
    leaf381InnerLogValid leaf381CoversExact leaf381LowerChecked

private noncomputable def leaf382Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/16), kHi := (7/4), chiLo := (21/64), chiHi := (11/32) }

private noncomputable def leaf382Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108963/67108864) }, vSqrt := { lower := (16383/16384), upper := (2290618641/2290565120) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (104232643/67108864) }, upper := { exponent := 0, mantissa := (205/128) } }, logOuter := sk34LogOuterCertificate, logK := sk34LogKCertificate, logChi := chi59LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (4581183761/4581130240) } }, logDArg := sk34LogDArgCertificate }

private noncomputable def leaf382InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf382LocalValidity :
    LeafFacts leaf382Box leaf382Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf382Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (2290618641/2290565120) }) = true
      norm_num [leaf382Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf382CertificateValid :
    WideCertificateValid leaf382Box leaf382Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk34ValidityFacts chi59ValidityFacts
    leaf382LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf382CoverageChecked :
    coverageCheck (innerAD leaf382Box) leaf382InnerLog = true := by
  rfl'

private theorem leaf382InnerLogValid :
    leaf382InnerLog.Valid 8 (innerAD leaf382Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf382CoverageChecked

private noncomputable def leaf382InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629277/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf382InputLogOnePlusV_eq :
    leaf382InputLogOnePlusV = outerEnclosure 24
      (leaf382Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf382RoundedFacts : LeafRoundedFacts 8
    leaf382Certificate.logOnePlusV leaf382InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf382InputLogOnePlusV_eq }

private noncomputable def leaf382Inputs : Inputs :=
  inputsOfCaches globalInput sk34RoundedInputs
    chi59InputQChi innerPair41Input
    leaf382InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf382LowerChecked :
    lowerCheck 24 leaf382Box leaf382Inputs = true := by
  rfl'

private theorem leaf382CoversExact : CoversExact 8
    leaf382Box leaf382Certificate leaf382InnerLog leaf382Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk34RoundedFacts chi59RoundedFacts
    innerPair41RoundedFacts leaf382RoundedFacts (by rfl)

private theorem leaf382FlatSound : Sound leaf382Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf382CertificateValid
    leaf382InnerLogValid leaf382CoversExact leaf382LowerChecked

private noncomputable def leaf383Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (27/16), chiLo := (11/32), chiHi := (23/64) }

private noncomputable def leaf383Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108963/67108864) }, vSqrt := { lower := (16383/16384), upper := (6871855923/6871693312) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (104560303/67108864) }, upper := { exponent := 0, mantissa := (1645/1024) } }, logOuter := sk33LogOuterCertificate, logK := sk33LogKCertificate, logChi := chi60LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (13743549235/13743386624) } }, logDArg := sk33LogDArgCertificate }

private noncomputable def leaf383InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf383LocalValidity :
    LeafFacts leaf383Box leaf383Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf383Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (6871855923/6871693312) }) = true
      norm_num [leaf383Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf383CertificateValid :
    WideCertificateValid leaf383Box leaf383Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk33ValidityFacts chi60ValidityFacts
    leaf383LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf383CoverageChecked :
    coverageCheck (innerAD leaf383Box) leaf383InnerLog = true := by
  rfl'

private theorem leaf383InnerLogValid :
    leaf383InnerLog.Valid 8 (innerAD leaf383Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf383CoverageChecked

private noncomputable def leaf383InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629279/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf383InputLogOnePlusV_eq :
    leaf383InputLogOnePlusV = outerEnclosure 24
      (leaf383Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf383RoundedFacts : LeafRoundedFacts 8
    leaf383Certificate.logOnePlusV leaf383InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf383InputLogOnePlusV_eq }

private noncomputable def leaf383Inputs : Inputs :=
  inputsOfCaches globalInput sk33RoundedInputs
    chi60InputQChi innerPair41Input
    leaf383InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf383LowerChecked :
    lowerCheck 24 leaf383Box leaf383Inputs = true := by
  rfl'

private theorem leaf383CoversExact : CoversExact 8
    leaf383Box leaf383Certificate leaf383InnerLog leaf383Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk33RoundedFacts chi60RoundedFacts
    innerPair41RoundedFacts leaf383RoundedFacts (by rfl)

private theorem leaf383FlatSound : Sound leaf383Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf383CertificateValid
    leaf383InnerLogValid leaf383CoversExact leaf383LowerChecked

private noncomputable def leaf384Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (27/16), chiLo := (23/64), chiHi := (3/8) }

private noncomputable def leaf384Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108965/67108864) }, vSqrt := { lower := (16383/16384), upper := (34359279615/34358411264) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (106264133/67108864) }, upper := { exponent := 0, mantissa := (209/128) } }, logOuter := sk33LogOuterCertificate, logK := sk33LogKCertificate, logChi := chi61LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68717690879/68716822528) } }, logDArg := sk33LogDArgCertificate }

private noncomputable def leaf384InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf384LocalValidity :
    LeafFacts leaf384Box leaf384Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf384Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34359279615/34358411264) }) = true
      norm_num [leaf384Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf384CertificateValid :
    WideCertificateValid leaf384Box leaf384Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk33ValidityFacts chi61ValidityFacts
    leaf384LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf384CoverageChecked :
    coverageCheck (innerAD leaf384Box) leaf384InnerLog = true := by
  rfl'

private theorem leaf384InnerLogValid :
    leaf384InnerLog.Valid 8 (innerAD leaf384Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf384CoverageChecked

private noncomputable def leaf384InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629293/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf384InputLogOnePlusV_eq :
    leaf384InputLogOnePlusV = outerEnclosure 24
      (leaf384Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf384RoundedFacts : LeafRoundedFacts 8
    leaf384Certificate.logOnePlusV leaf384InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf384InputLogOnePlusV_eq }

private noncomputable def leaf384Inputs : Inputs :=
  inputsOfCaches globalInput sk33RoundedInputs
    chi61InputQChi innerPair51Input
    leaf384InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf384LowerChecked :
    lowerCheck 24 leaf384Box leaf384Inputs = true := by
  rfl'

private theorem leaf384CoversExact : CoversExact 8
    leaf384Box leaf384Certificate leaf384InnerLog leaf384Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk33RoundedFacts chi61RoundedFacts
    innerPair51RoundedFacts leaf384RoundedFacts (by rfl)

private theorem leaf384FlatSound : Sound leaf384Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf384CertificateValid
    leaf384InnerLogValid leaf384CoversExact leaf384LowerChecked

private noncomputable def leaf385Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/16), kHi := (7/4), chiLo := (11/32), chiHi := (23/64) }

private noncomputable def leaf385Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108965/67108864) }, vSqrt := { lower := (16383/16384), upper := (34359279615/34358419456) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (106002005/67108864) }, upper := { exponent := 0, mantissa := (417/256) } }, logOuter := sk34LogOuterCertificate, logK := sk34LogKCertificate, logChi := chi60LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68717699071/68716838912) } }, logDArg := sk34LogDArgCertificate }

private noncomputable def leaf385InnerLog : WideLogData :=
  innerPair170Data

set_option maxRecDepth 1000000 in
private theorem leaf385LocalValidity :
    LeafFacts leaf385Box leaf385Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf385Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34359279615/34358419456) }) = true
      norm_num [leaf385Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf385CertificateValid :
    WideCertificateValid leaf385Box leaf385Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk34ValidityFacts chi60ValidityFacts
    leaf385LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf385CoverageChecked :
    coverageCheck (innerAD leaf385Box) leaf385InnerLog = true := by
  rfl'

private theorem leaf385InnerLogValid :
    leaf385InnerLog.Valid 8 (innerAD leaf385Box) :=
  wideLogDataValid_of_cachedCheck endpoint47PositiveFacts
    endpoint45PositiveFacts.valid leaf385CoverageChecked

private noncomputable def leaf385InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629291/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf385InputLogOnePlusV_eq :
    leaf385InputLogOnePlusV = outerEnclosure 24
      (leaf385Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf385RoundedFacts : LeafRoundedFacts 8
    leaf385Certificate.logOnePlusV leaf385InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf385InputLogOnePlusV_eq }

private noncomputable def leaf385Inputs : Inputs :=
  inputsOfCaches globalInput sk34RoundedInputs
    chi60InputQChi innerPair170Input
    leaf385InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf385LowerChecked :
    lowerCheck 24 leaf385Box leaf385Inputs = true := by
  rfl'

private theorem leaf385CoversExact : CoversExact 8
    leaf385Box leaf385Certificate leaf385InnerLog leaf385Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk34RoundedFacts chi60RoundedFacts
    innerPair170RoundedFacts leaf385RoundedFacts (by rfl)

private theorem leaf385FlatSound : Sound leaf385Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf385CertificateValid
    leaf385InnerLogValid leaf385CoversExact leaf385LowerChecked

private noncomputable def leaf386Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/16), kHi := (7/4), chiLo := (23/64), chiHi := (3/8) }

private noncomputable def leaf386Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108967/67108864) }, vSqrt := { lower := (16383/16384), upper := (34359279615/34358362112) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (107771367/67108864) }, upper := { exponent := 0, mantissa := (53/32) } }, logOuter := sk34LogOuterCertificate, logK := sk34LogKCertificate, logChi := chi61LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68717641727/68716724224) } }, logDArg := sk34LogDArgCertificate }

private noncomputable def leaf386InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf386LocalValidity :
    LeafFacts leaf386Box leaf386Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf386Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34359279615/34358362112) }) = true
      norm_num [leaf386Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf386CertificateValid :
    WideCertificateValid leaf386Box leaf386Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk34ValidityFacts chi61ValidityFacts
    leaf386LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf386CoverageChecked :
    coverageCheck (innerAD leaf386Box) leaf386InnerLog = true := by
  rfl'

private theorem leaf386InnerLogValid :
    leaf386InnerLog.Valid 8 (innerAD leaf386Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf386CoverageChecked

private noncomputable def leaf386InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629305/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf386InputLogOnePlusV_eq :
    leaf386InputLogOnePlusV = outerEnclosure 24
      (leaf386Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf386RoundedFacts : LeafRoundedFacts 8
    leaf386Certificate.logOnePlusV leaf386InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf386InputLogOnePlusV_eq }

private noncomputable def leaf386Inputs : Inputs :=
  inputsOfCaches globalInput sk34RoundedInputs
    chi61InputQChi innerPair51Input
    leaf386InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf386LowerChecked :
    lowerCheck 24 leaf386Box leaf386Inputs = true := by
  rfl'

private theorem leaf386CoversExact : CoversExact 8
    leaf386Box leaf386Certificate leaf386InnerLog leaf386Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk34RoundedFacts chi61RoundedFacts
    innerPair51RoundedFacts leaf386RoundedFacts (by rfl)

private theorem leaf386FlatSound : Sound leaf386Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf386CertificateValid
    leaf386InnerLogValid leaf386CoversExact leaf386LowerChecked

private noncomputable def component9Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (25/16), chiLo := (1/4), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component9Node0_sound : Sound component9Node0Box :=
  sound_of_literal_split component9Node0Box leaf355Box leaf356Box
    .k (49/32) (by rfl) (by rfl)
    leaf355FlatSound leaf356FlatSound

private noncomputable def component9Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (25/16), chiLo := (9/32), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component9Node1_sound : Sound component9Node1Box :=
  sound_of_literal_split component9Node1Box leaf357Box leaf358Box
    .k (49/32) (by rfl) (by rfl)
    leaf357FlatSound leaf358FlatSound

private noncomputable def component9Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (25/16), chiLo := (1/4), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component9Node2_sound : Sound component9Node2Box :=
  sound_of_literal_split component9Node2Box component9Node0Box component9Node1Box
    .chi (9/32) (by rfl) (by rfl)
    component9Node0_sound component9Node1_sound

private noncomputable def component9Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/16), kHi := (13/8), chiLo := (1/4), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component9Node3_sound : Sound component9Node3Box :=
  sound_of_literal_split component9Node3Box leaf359Box leaf360Box
    .k (51/32) (by rfl) (by rfl)
    leaf359FlatSound leaf360FlatSound

private noncomputable def component9Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/16), kHi := (13/8), chiLo := (9/32), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component9Node4_sound : Sound component9Node4Box :=
  sound_of_literal_split component9Node4Box leaf361Box leaf362Box
    .k (51/32) (by rfl) (by rfl)
    leaf361FlatSound leaf362FlatSound

private noncomputable def component9Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/16), kHi := (13/8), chiLo := (1/4), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component9Node5_sound : Sound component9Node5Box :=
  sound_of_literal_split component9Node5Box component9Node3Box component9Node4Box
    .chi (9/32) (by rfl) (by rfl)
    component9Node3_sound component9Node4_sound

private noncomputable def component9Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (13/8), chiLo := (1/4), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component9Node6_sound : Sound component9Node6Box :=
  sound_of_literal_split component9Node6Box component9Node2Box component9Node5Box
    .k (25/16) (by rfl) (by rfl)
    component9Node2_sound component9Node5_sound

private noncomputable def component9Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (27/16), chiLo := (1/4), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component9Node7_sound : Sound component9Node7Box :=
  sound_of_literal_split component9Node7Box leaf363Box leaf364Box
    .k (53/32) (by rfl) (by rfl)
    leaf363FlatSound leaf364FlatSound

private noncomputable def component9Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/16), kHi := (7/4), chiLo := (1/4), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component9Node8_sound : Sound component9Node8Box :=
  sound_of_literal_split component9Node8Box leaf365Box leaf366Box
    .chi (17/64) (by rfl) (by rfl)
    leaf365FlatSound leaf366FlatSound

private noncomputable def component9Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (7/4), chiLo := (1/4), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component9Node9_sound : Sound component9Node9Box :=
  sound_of_literal_split component9Node9Box component9Node7Box component9Node8Box
    .k (27/16) (by rfl) (by rfl)
    component9Node7_sound component9Node8_sound

private noncomputable def component9Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (27/16), chiLo := (9/32), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component9Node10_sound : Sound component9Node10Box :=
  sound_of_literal_split component9Node10Box leaf367Box leaf368Box
    .chi (19/64) (by rfl) (by rfl)
    leaf367FlatSound leaf368FlatSound

private noncomputable def component9Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/16), kHi := (7/4), chiLo := (9/32), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component9Node11_sound : Sound component9Node11Box :=
  sound_of_literal_split component9Node11Box leaf369Box leaf370Box
    .chi (19/64) (by rfl) (by rfl)
    leaf369FlatSound leaf370FlatSound

private noncomputable def component9Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (7/4), chiLo := (9/32), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component9Node12_sound : Sound component9Node12Box :=
  sound_of_literal_split component9Node12Box component9Node10Box component9Node11Box
    .k (27/16) (by rfl) (by rfl)
    component9Node10_sound component9Node11_sound

private noncomputable def component9Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (7/4), chiLo := (1/4), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component9Node13_sound : Sound component9Node13Box :=
  sound_of_literal_split component9Node13Box component9Node9Box component9Node12Box
    .chi (9/32) (by rfl) (by rfl)
    component9Node9_sound component9Node12_sound

private noncomputable def component9Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (7/4), chiLo := (1/4), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component9Node14_sound : Sound component9Node14Box :=
  sound_of_literal_split component9Node14Box component9Node6Box component9Node13Box
    .k (13/8) (by rfl) (by rfl)
    component9Node6_sound component9Node13_sound

private noncomputable def component9Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (25/16), chiLo := (5/16), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component9Node15_sound : Sound component9Node15Box :=
  sound_of_literal_split component9Node15Box leaf371Box leaf372Box
    .k (49/32) (by rfl) (by rfl)
    leaf371FlatSound leaf372FlatSound

private noncomputable def component9Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (25/16), chiLo := (11/32), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component9Node16_sound : Sound component9Node16Box :=
  sound_of_literal_split component9Node16Box leaf373Box leaf374Box
    .k (49/32) (by rfl) (by rfl)
    leaf373FlatSound leaf374FlatSound

private noncomputable def component9Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (25/16), chiLo := (5/16), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component9Node17_sound : Sound component9Node17Box :=
  sound_of_literal_split component9Node17Box component9Node15Box component9Node16Box
    .chi (11/32) (by rfl) (by rfl)
    component9Node15_sound component9Node16_sound

private noncomputable def component9Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/16), kHi := (13/8), chiLo := (5/16), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component9Node18_sound : Sound component9Node18Box :=
  sound_of_literal_split component9Node18Box leaf375Box leaf376Box
    .chi (21/64) (by rfl) (by rfl)
    leaf375FlatSound leaf376FlatSound

private noncomputable def component9Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/16), kHi := (13/8), chiLo := (11/32), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component9Node19_sound : Sound component9Node19Box :=
  sound_of_literal_split component9Node19Box leaf377Box leaf378Box
    .chi (23/64) (by rfl) (by rfl)
    leaf377FlatSound leaf378FlatSound

private noncomputable def component9Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/16), kHi := (13/8), chiLo := (5/16), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component9Node20_sound : Sound component9Node20Box :=
  sound_of_literal_split component9Node20Box component9Node18Box component9Node19Box
    .chi (11/32) (by rfl) (by rfl)
    component9Node18_sound component9Node19_sound

private noncomputable def component9Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (13/8), chiLo := (5/16), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component9Node21_sound : Sound component9Node21Box :=
  sound_of_literal_split component9Node21Box component9Node17Box component9Node20Box
    .k (25/16) (by rfl) (by rfl)
    component9Node17_sound component9Node20_sound

private noncomputable def component9Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (27/16), chiLo := (5/16), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component9Node22_sound : Sound component9Node22Box :=
  sound_of_literal_split component9Node22Box leaf379Box leaf380Box
    .chi (21/64) (by rfl) (by rfl)
    leaf379FlatSound leaf380FlatSound

private noncomputable def component9Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/16), kHi := (7/4), chiLo := (5/16), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component9Node23_sound : Sound component9Node23Box :=
  sound_of_literal_split component9Node23Box leaf381Box leaf382Box
    .chi (21/64) (by rfl) (by rfl)
    leaf381FlatSound leaf382FlatSound

private noncomputable def component9Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (7/4), chiLo := (5/16), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component9Node24_sound : Sound component9Node24Box :=
  sound_of_literal_split component9Node24Box component9Node22Box component9Node23Box
    .k (27/16) (by rfl) (by rfl)
    component9Node22_sound component9Node23_sound

private noncomputable def component9Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (27/16), chiLo := (11/32), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component9Node25_sound : Sound component9Node25Box :=
  sound_of_literal_split component9Node25Box leaf383Box leaf384Box
    .chi (23/64) (by rfl) (by rfl)
    leaf383FlatSound leaf384FlatSound

private noncomputable def component9Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/16), kHi := (7/4), chiLo := (11/32), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component9Node26_sound : Sound component9Node26Box :=
  sound_of_literal_split component9Node26Box leaf385Box leaf386Box
    .chi (23/64) (by rfl) (by rfl)
    leaf385FlatSound leaf386FlatSound

private noncomputable def component9Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (7/4), chiLo := (11/32), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component9Node27_sound : Sound component9Node27Box :=
  sound_of_literal_split component9Node27Box component9Node25Box component9Node26Box
    .k (27/16) (by rfl) (by rfl)
    component9Node25_sound component9Node26_sound

private noncomputable def component9Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (7/4), chiLo := (5/16), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component9Node28_sound : Sound component9Node28Box :=
  sound_of_literal_split component9Node28Box component9Node24Box component9Node27Box
    .chi (11/32) (by rfl) (by rfl)
    component9Node24_sound component9Node27_sound

private noncomputable def component9Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (7/4), chiLo := (5/16), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component9Node29_sound : Sound component9Node29Box :=
  sound_of_literal_split component9Node29Box component9Node21Box component9Node28Box
    .k (13/8) (by rfl) (by rfl)
    component9Node21_sound component9Node28_sound

noncomputable def component9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (7/4), chiLo := (1/4), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
theorem component9_sound : Sound component9Box :=
  sound_of_literal_split component9Box component9Node14Box component9Node29Box
    .chi (5/16) (by rfl) (by rfl)
    component9Node14_sound component9Node29_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
