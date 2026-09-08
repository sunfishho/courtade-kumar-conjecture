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

private noncomputable def leaf240Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (29/16), chiLo := (1/8), chiHi := (9/64) }

private noncomputable def leaf240Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108939/67108864) }, vSqrt := { lower := (16383/16384), upper := (16777248/16776955) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (81755191/67108864) }, upper := { exponent := 0, mantissa := (1285/1024) } }, logOuter := sk39LogOuterCertificate, logK := sk39LogKCertificate, logChi := chi40LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (33554203/33553910) } }, logDArg := sk39LogDArgCertificate }

private noncomputable def leaf240InnerLog : WideLogData :=
  innerPair13Data

set_option maxRecDepth 1000000 in
private theorem leaf240LocalValidity :
    LeafFacts leaf240Box leaf240Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf240Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (16777248/16776955) }) = true
      norm_num [leaf240Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf240CertificateValid :
    WideCertificateValid leaf240Box leaf240Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk39ValidityFacts chi40ValidityFacts
    leaf240LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf240CoverageChecked :
    coverageCheck (innerAD leaf240Box) leaf240InnerLog = true := by
  rfl'

private theorem leaf240InnerLogValid :
    leaf240InnerLog.Valid 8 (innerAD leaf240Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint6PositiveFacts.valid leaf240CoverageChecked

private noncomputable def leaf240InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629227/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf240InputLogOnePlusV_eq :
    leaf240InputLogOnePlusV = outerEnclosure 24
      (leaf240Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf240RoundedFacts : LeafRoundedFacts 8
    leaf240Certificate.logOnePlusV leaf240InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf240InputLogOnePlusV_eq }

private noncomputable def leaf240Inputs : Inputs :=
  inputsOfCaches globalInput sk39RoundedInputs
    chi40InputQChi innerPair13Input
    leaf240InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf240LowerChecked :
    lowerCheck 24 leaf240Box leaf240Inputs = true := by
  rfl'

private theorem leaf240CoversExact : CoversExact 8
    leaf240Box leaf240Certificate leaf240InnerLog leaf240Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk39RoundedFacts chi40RoundedFacts
    innerPair13RoundedFacts leaf240RoundedFacts (by rfl)

private theorem leaf240FlatSound : Sound leaf240Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf240CertificateValid
    leaf240InnerLogValid leaf240CoversExact leaf240LowerChecked

private noncomputable def leaf241Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (29/16), chiLo := (9/64), chiHi := (5/32) }

private noncomputable def leaf241Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108941/67108864) }, vSqrt := { lower := (16383/16384), upper := (8388624/8388463) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (83590085/67108864) }, upper := { exponent := 0, mantissa := (657/512) } }, logOuter := sk39LogOuterCertificate, logK := sk39LogKCertificate, logChi := chi41LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (16777087/16776926) } }, logDArg := sk39LogDArgCertificate }

private noncomputable def leaf241InnerLog : WideLogData :=
  innerPair13Data

set_option maxRecDepth 1000000 in
private theorem leaf241LocalValidity :
    LeafFacts leaf241Box leaf241Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf241Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (8388624/8388463) }) = true
      norm_num [leaf241Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf241CertificateValid :
    WideCertificateValid leaf241Box leaf241Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk39ValidityFacts chi41ValidityFacts
    leaf241LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf241CoverageChecked :
    coverageCheck (innerAD leaf241Box) leaf241InnerLog = true := by
  rfl'

private theorem leaf241InnerLogValid :
    leaf241InnerLog.Valid 8 (innerAD leaf241Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint6PositiveFacts.valid leaf241CoverageChecked

private noncomputable def leaf241InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (5814621/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf241InputLogOnePlusV_eq :
    leaf241InputLogOnePlusV = outerEnclosure 24
      (leaf241Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf241RoundedFacts : LeafRoundedFacts 8
    leaf241Certificate.logOnePlusV leaf241InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf241InputLogOnePlusV_eq }

private noncomputable def leaf241Inputs : Inputs :=
  inputsOfCaches globalInput sk39RoundedInputs
    chi41InputQChi innerPair13Input
    leaf241InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf241LowerChecked :
    lowerCheck 24 leaf241Box leaf241Inputs = true := by
  rfl'

private theorem leaf241CoversExact : CoversExact 8
    leaf241Box leaf241Certificate leaf241InnerLog leaf241Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk39RoundedFacts chi41RoundedFacts
    innerPair13RoundedFacts leaf241RoundedFacts (by rfl)

private theorem leaf241FlatSound : Sound leaf241Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf241CertificateValid
    leaf241InnerLogValid leaf241CoversExact leaf241LowerChecked

private noncomputable def leaf242Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (15/8), chiLo := (1/8), chiHi := (9/64) }

private noncomputable def leaf242Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108941/67108864) }, vSqrt := { lower := (16383/16384), upper := (8388624/8388473) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (82279445/67108864) }, upper := { exponent := 0, mantissa := (647/512) } }, logOuter := sk40LogOuterCertificate, logK := sk40LogKCertificate, logChi := chi40LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (16777097/16776946) } }, logDArg := sk40LogDArgCertificate }

private noncomputable def leaf242InnerLog : WideLogData :=
  innerPair13Data

set_option maxRecDepth 1000000 in
private theorem leaf242LocalValidity :
    LeafFacts leaf242Box leaf242Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf242Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (8388624/8388473) }) = true
      norm_num [leaf242Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf242CertificateValid :
    WideCertificateValid leaf242Box leaf242Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk40ValidityFacts chi40ValidityFacts
    leaf242LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf242CoverageChecked :
    coverageCheck (innerAD leaf242Box) leaf242InnerLog = true := by
  rfl'

private theorem leaf242InnerLogValid :
    leaf242InnerLog.Valid 8 (innerAD leaf242Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint6PositiveFacts.valid leaf242CoverageChecked

private noncomputable def leaf242InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (726827/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf242InputLogOnePlusV_eq :
    leaf242InputLogOnePlusV = outerEnclosure 24
      (leaf242Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf242RoundedFacts : LeafRoundedFacts 8
    leaf242Certificate.logOnePlusV leaf242InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf242InputLogOnePlusV_eq }

private noncomputable def leaf242Inputs : Inputs :=
  inputsOfCaches globalInput sk40RoundedInputs
    chi40InputQChi innerPair13Input
    leaf242InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf242LowerChecked :
    lowerCheck 24 leaf242Box leaf242Inputs = true := by
  rfl'

private theorem leaf242CoversExact : CoversExact 8
    leaf242Box leaf242Certificate leaf242InnerLog leaf242Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk40RoundedFacts chi40RoundedFacts
    innerPair13RoundedFacts leaf242RoundedFacts (by rfl)

private theorem leaf242FlatSound : Sound leaf242Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf242CertificateValid
    leaf242InnerLogValid leaf242CoversExact leaf242LowerChecked

private noncomputable def leaf243Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (15/8), chiLo := (9/64), chiHi := (5/32) }

private noncomputable def leaf243Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108943/67108864) }, vSqrt := { lower := (16383/16384), upper := (4194312/4194229) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (84179871/67108864) }, upper := { exponent := 0, mantissa := (331/256) } }, logOuter := sk40LogOuterCertificate, logK := sk40LogKCertificate, logChi := chi41LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (8388541/8388458) } }, logDArg := sk40LogDArgCertificate }

private noncomputable def leaf243InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf243LocalValidity :
    LeafFacts leaf243Box leaf243Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf243Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (4194312/4194229) }) = true
      norm_num [leaf243Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf243CertificateValid :
    WideCertificateValid leaf243Box leaf243Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk40ValidityFacts chi41ValidityFacts
    leaf243LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf243CoverageChecked :
    coverageCheck (innerAD leaf243Box) leaf243InnerLog = true := by
  rfl'

private theorem leaf243InnerLogValid :
    leaf243InnerLog.Valid 8 (innerAD leaf243Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf243CoverageChecked

private noncomputable def leaf243InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629247/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf243InputLogOnePlusV_eq :
    leaf243InputLogOnePlusV = outerEnclosure 24
      (leaf243Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf243RoundedFacts : LeafRoundedFacts 8
    leaf243Certificate.logOnePlusV leaf243InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf243InputLogOnePlusV_eq }

private noncomputable def leaf243Inputs : Inputs :=
  inputsOfCaches globalInput sk40RoundedInputs
    chi41InputQChi innerPair16Input
    leaf243InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf243LowerChecked :
    lowerCheck 24 leaf243Box leaf243Inputs = true := by
  rfl'

private theorem leaf243CoversExact : CoversExact 8
    leaf243Box leaf243Certificate leaf243InnerLog leaf243Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk40RoundedFacts chi41RoundedFacts
    innerPair16RoundedFacts leaf243RoundedFacts (by rfl)

private theorem leaf243FlatSound : Sound leaf243Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf243CertificateValid
    leaf243InnerLogValid leaf243CoversExact leaf243LowerChecked

private noncomputable def leaf244Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (29/16), chiLo := (5/32), chiHi := (11/64) }

private noncomputable def leaf244Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108943/67108864) }, vSqrt := { lower := (16383/16384), upper := (5592416/5592299) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (85424979/67108864) }, upper := { exponent := 0, mantissa := (1343/1024) } }, logOuter := sk39LogOuterCertificate, logK := sk39LogKCertificate, logChi := chi42LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (11184715/11184598) } }, logDArg := sk39LogDArgCertificate }

private noncomputable def leaf244InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf244LocalValidity :
    LeafFacts leaf244Box leaf244Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf244Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (5592416/5592299) }) = true
      norm_num [leaf244Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf244CertificateValid :
    WideCertificateValid leaf244Box leaf244Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk39ValidityFacts chi42ValidityFacts
    leaf244LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf244CoverageChecked :
    coverageCheck (innerAD leaf244Box) leaf244InnerLog = true := by
  rfl'

private theorem leaf244InnerLogValid :
    leaf244InnerLog.Valid 8 (innerAD leaf244Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf244CoverageChecked

private noncomputable def leaf244InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (1453657/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf244InputLogOnePlusV_eq :
    leaf244InputLogOnePlusV = outerEnclosure 24
      (leaf244Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf244RoundedFacts : LeafRoundedFacts 8
    leaf244Certificate.logOnePlusV leaf244InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf244InputLogOnePlusV_eq }

private noncomputable def leaf244Inputs : Inputs :=
  inputsOfCaches globalInput sk39RoundedInputs
    chi42InputQChi innerPair16Input
    leaf244InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf244LowerChecked :
    lowerCheck 24 leaf244Box leaf244Inputs = true := by
  rfl'

private theorem leaf244CoversExact : CoversExact 8
    leaf244Box leaf244Certificate leaf244InnerLog leaf244Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk39RoundedFacts chi42RoundedFacts
    innerPair16RoundedFacts leaf244RoundedFacts (by rfl)

private theorem leaf244FlatSound : Sound leaf244Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf244CertificateValid
    leaf244InnerLogValid leaf244CoversExact leaf244LowerChecked

private noncomputable def leaf245Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (29/16), chiLo := (11/64), chiHi := (3/16) }

private noncomputable def leaf245Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108945/67108864) }, vSqrt := { lower := (16383/16384), upper := (4194312/4194217) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (87259873/67108864) }, upper := { exponent := 0, mantissa := (343/256) } }, logOuter := sk39LogOuterCertificate, logK := sk39LogKCertificate, logChi := chi43LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (8388529/8388434) } }, logDArg := sk39LogDArgCertificate }

private noncomputable def leaf245InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf245LocalValidity :
    LeafFacts leaf245Box leaf245Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf245Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (4194312/4194217) }) = true
      norm_num [leaf245Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf245CertificateValid :
    WideCertificateValid leaf245Box leaf245Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk39ValidityFacts chi43ValidityFacts
    leaf245LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf245CoverageChecked :
    coverageCheck (innerAD leaf245Box) leaf245InnerLog = true := by
  rfl'

private theorem leaf245InnerLogValid :
    leaf245InnerLog.Valid 8 (innerAD leaf245Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf245CoverageChecked

private noncomputable def leaf245InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629271/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf245InputLogOnePlusV_eq :
    leaf245InputLogOnePlusV = outerEnclosure 24
      (leaf245Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf245RoundedFacts : LeafRoundedFacts 8
    leaf245Certificate.logOnePlusV leaf245InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf245InputLogOnePlusV_eq }

private noncomputable def leaf245Inputs : Inputs :=
  inputsOfCaches globalInput sk39RoundedInputs
    chi43InputQChi innerPair17Input
    leaf245InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf245LowerChecked :
    lowerCheck 24 leaf245Box leaf245Inputs = true := by
  rfl'

private theorem leaf245CoversExact : CoversExact 8
    leaf245Box leaf245Certificate leaf245InnerLog leaf245Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk39RoundedFacts chi43RoundedFacts
    innerPair17RoundedFacts leaf245RoundedFacts (by rfl)

private theorem leaf245FlatSound : Sound leaf245Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf245CertificateValid
    leaf245InnerLogValid leaf245CoversExact leaf245LowerChecked

private noncomputable def leaf246Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (15/8), chiLo := (5/32), chiHi := (11/64) }

private noncomputable def leaf246Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108945/67108864) }, vSqrt := { lower := (16383/16384), upper := (8388624/8388443) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (86080297/67108864) }, upper := { exponent := 0, mantissa := (677/512) } }, logOuter := sk40LogOuterCertificate, logK := sk40LogKCertificate, logChi := chi42LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (16777067/16776886) } }, logDArg := sk40LogDArgCertificate }

private noncomputable def leaf246InnerLog : WideLogData :=
  innerPair129Data

set_option maxRecDepth 1000000 in
private theorem leaf246LocalValidity :
    LeafFacts leaf246Box leaf246Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf246Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (8388624/8388443) }) = true
      norm_num [leaf246Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf246CertificateValid :
    WideCertificateValid leaf246Box leaf246Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk40ValidityFacts chi42ValidityFacts
    leaf246LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf246CoverageChecked :
    coverageCheck (innerAD leaf246Box) leaf246InnerLog = true := by
  rfl'

private theorem leaf246InnerLogValid :
    leaf246InnerLog.Valid 8 (innerAD leaf246Box) :=
  wideLogDataValid_of_cachedCheck endpoint28PositiveFacts
    endpoint9PositiveFacts.valid leaf246CoverageChecked

private noncomputable def leaf246InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (5814631/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf246InputLogOnePlusV_eq :
    leaf246InputLogOnePlusV = outerEnclosure 24
      (leaf246Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf246RoundedFacts : LeafRoundedFacts 8
    leaf246Certificate.logOnePlusV leaf246InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf246InputLogOnePlusV_eq }

private noncomputable def leaf246Inputs : Inputs :=
  inputsOfCaches globalInput sk40RoundedInputs
    chi42InputQChi innerPair129Input
    leaf246InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf246LowerChecked :
    lowerCheck 24 leaf246Box leaf246Inputs = true := by
  rfl'

private theorem leaf246CoversExact : CoversExact 8
    leaf246Box leaf246Certificate leaf246InnerLog leaf246Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk40RoundedFacts chi42RoundedFacts
    innerPair129RoundedFacts leaf246RoundedFacts (by rfl)

private theorem leaf246FlatSound : Sound leaf246Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf246CertificateValid
    leaf246InnerLogValid leaf246CoversExact leaf246LowerChecked

private noncomputable def leaf247Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (15/8), chiLo := (11/64), chiHi := (3/16) }

private noncomputable def leaf247Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108947/67108864) }, vSqrt := { lower := (16383/16384), upper := (2097156/2097107) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (87980723/67108864) }, upper := { exponent := 0, mantissa := (173/128) } }, logOuter := sk40LogOuterCertificate, logK := sk40LogKCertificate, logChi := chi43LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (4194263/4194214) } }, logDArg := sk40LogDArgCertificate }

private noncomputable def leaf247InnerLog : WideLogData :=
  innerPair130Data

set_option maxRecDepth 1000000 in
private theorem leaf247LocalValidity :
    LeafFacts leaf247Box leaf247Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf247Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (2097156/2097107) }) = true
      norm_num [leaf247Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf247CertificateValid :
    WideCertificateValid leaf247Box leaf247Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk40ValidityFacts chi43ValidityFacts
    leaf247LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf247CoverageChecked :
    coverageCheck (innerAD leaf247Box) leaf247InnerLog = true := by
  rfl'

private theorem leaf247InnerLogValid :
    leaf247InnerLog.Valid 8 (innerAD leaf247Box) :=
  wideLogDataValid_of_cachedCheck endpoint29PositiveFacts
    endpoint30PositiveFacts.valid leaf247CoverageChecked

private noncomputable def leaf247InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629277/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf247InputLogOnePlusV_eq :
    leaf247InputLogOnePlusV = outerEnclosure 24
      (leaf247Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf247RoundedFacts : LeafRoundedFacts 8
    leaf247Certificate.logOnePlusV leaf247InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf247InputLogOnePlusV_eq }

private noncomputable def leaf247Inputs : Inputs :=
  inputsOfCaches globalInput sk40RoundedInputs
    chi43InputQChi innerPair130Input
    leaf247InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf247LowerChecked :
    lowerCheck 24 leaf247Box leaf247Inputs = true := by
  rfl'

private theorem leaf247CoversExact : CoversExact 8
    leaf247Box leaf247Certificate leaf247InnerLog leaf247Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk40RoundedFacts chi43RoundedFacts
    innerPair130RoundedFacts leaf247RoundedFacts (by rfl)

private theorem leaf247FlatSound : Sound leaf247Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf247CertificateValid
    leaf247InnerLogValid leaf247CoversExact leaf247LowerChecked

private noncomputable def leaf248Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (31/16), chiLo := (1/8), chiHi := (9/64) }

private noncomputable def leaf248Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108943/67108864) }, vSqrt := { lower := (16383/16384), upper := (16777248/16776937) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (82803699/67108864) }, upper := { exponent := 0, mantissa := (1303/1024) } }, logOuter := sk41LogOuterCertificate, logK := sk41LogKCertificate, logChi := chi40LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (33554185/33553874) } }, logDArg := sk41LogDArgCertificate }

private noncomputable def leaf248InnerLog : WideLogData :=
  innerPair13Data

set_option maxRecDepth 1000000 in
private theorem leaf248LocalValidity :
    LeafFacts leaf248Box leaf248Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf248Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (16777248/16776937) }) = true
      norm_num [leaf248Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf248CertificateValid :
    WideCertificateValid leaf248Box leaf248Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk41ValidityFacts chi40ValidityFacts
    leaf248LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf248CoverageChecked :
    coverageCheck (innerAD leaf248Box) leaf248InnerLog = true := by
  rfl'

private theorem leaf248InnerLogValid :
    leaf248InnerLog.Valid 8 (innerAD leaf248Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint6PositiveFacts.valid leaf248CoverageChecked

private noncomputable def leaf248InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (2907309/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf248InputLogOnePlusV_eq :
    leaf248InputLogOnePlusV = outerEnclosure 24
      (leaf248Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf248RoundedFacts : LeafRoundedFacts 8
    leaf248Certificate.logOnePlusV leaf248InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf248InputLogOnePlusV_eq }

private noncomputable def leaf248Inputs : Inputs :=
  inputsOfCaches globalInput sk41RoundedInputs
    chi40InputQChi innerPair13Input
    leaf248InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf248LowerChecked :
    lowerCheck 24 leaf248Box leaf248Inputs = true := by
  rfl'

private theorem leaf248CoversExact : CoversExact 8
    leaf248Box leaf248Certificate leaf248InnerLog leaf248Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk41RoundedFacts chi40RoundedFacts
    innerPair13RoundedFacts leaf248RoundedFacts (by rfl)

private theorem leaf248FlatSound : Sound leaf248Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf248CertificateValid
    leaf248InnerLogValid leaf248CoversExact leaf248LowerChecked

private noncomputable def leaf249Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (31/16), chiLo := (9/64), chiHi := (5/32) }

private noncomputable def leaf249Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108945/67108864) }, vSqrt := { lower := (16383/16384), upper := (2796208/2796151) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (84769657/67108864) }, upper := { exponent := 0, mantissa := (667/512) } }, logOuter := sk41LogOuterCertificate, logK := sk41LogKCertificate, logChi := chi41LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (5592359/5592302) } }, logDArg := sk41LogDArgCertificate }

private noncomputable def leaf249InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf249LocalValidity :
    LeafFacts leaf249Box leaf249Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf249Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (2796208/2796151) }) = true
      norm_num [leaf249Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf249CertificateValid :
    WideCertificateValid leaf249Box leaf249Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk41ValidityFacts chi41ValidityFacts
    leaf249LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf249CoverageChecked :
    coverageCheck (innerAD leaf249Box) leaf249InnerLog = true := by
  rfl'

private theorem leaf249InnerLogValid :
    leaf249InnerLog.Valid 8 (innerAD leaf249Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf249CoverageChecked

private noncomputable def leaf249InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (2907313/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf249InputLogOnePlusV_eq :
    leaf249InputLogOnePlusV = outerEnclosure 24
      (leaf249Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf249RoundedFacts : LeafRoundedFacts 8
    leaf249Certificate.logOnePlusV leaf249InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf249InputLogOnePlusV_eq }

private noncomputable def leaf249Inputs : Inputs :=
  inputsOfCaches globalInput sk41RoundedInputs
    chi41InputQChi innerPair16Input
    leaf249InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf249LowerChecked :
    lowerCheck 24 leaf249Box leaf249Inputs = true := by
  rfl'

private theorem leaf249CoversExact : CoversExact 8
    leaf249Box leaf249Certificate leaf249InnerLog leaf249Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk41RoundedFacts chi41RoundedFacts
    innerPair16RoundedFacts leaf249RoundedFacts (by rfl)

private theorem leaf249FlatSound : Sound leaf249Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf249CertificateValid
    leaf249InnerLogValid leaf249CoversExact leaf249LowerChecked

private noncomputable def leaf250Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2), chiLo := (1/8), chiHi := (9/64) }

private noncomputable def leaf250Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108945/67108864) }, vSqrt := { lower := (65531/65536), upper := (524289/524279) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (83327953/67108864) }, upper := { exponent := 0, mantissa := (41/32) } }, logOuter := sk42LogOuterCertificate, logK := sk42LogKCertificate, logChi := chi40LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (524284/524279) } }, logDArg := sk42LogDArgCertificate }

private noncomputable def leaf250InnerLog : WideLogData :=
  innerPair13Data

set_option maxRecDepth 1000000 in
private theorem leaf250LocalValidity :
    LeafFacts leaf250Box leaf250Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf250Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (524289/524279) }) = true
      norm_num [leaf250Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf250CertificateValid :
    WideCertificateValid leaf250Box leaf250Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk42ValidityFacts chi40ValidityFacts
    leaf250LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf250CoverageChecked :
    coverageCheck (innerAD leaf250Box) leaf250InnerLog = true := by
  rfl'

private theorem leaf250InnerLogValid :
    leaf250InnerLog.Valid 8 (innerAD leaf250Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint6PositiveFacts.valid leaf250CoverageChecked

private noncomputable def leaf250InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629241/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf250InputLogOnePlusV_eq :
    leaf250InputLogOnePlusV = outerEnclosure 24
      (leaf250Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf250RoundedFacts : LeafRoundedFacts 8
    leaf250Certificate.logOnePlusV leaf250InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf250InputLogOnePlusV_eq }

private noncomputable def leaf250Inputs : Inputs :=
  inputsOfCaches globalInput sk42RoundedInputs
    chi40InputQChi innerPair13Input
    leaf250InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf250LowerChecked :
    lowerCheck 24 leaf250Box leaf250Inputs = true := by
  rfl'

private theorem leaf250CoversExact : CoversExact 8
    leaf250Box leaf250Certificate leaf250InnerLog leaf250Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk42RoundedFacts chi40RoundedFacts
    innerPair13RoundedFacts leaf250RoundedFacts (by rfl)

private theorem leaf250FlatSound : Sound leaf250Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf250CertificateValid
    leaf250InnerLogValid leaf250CoversExact leaf250LowerChecked

private noncomputable def leaf251Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (63/32), chiLo := (9/64), chiHi := (5/32) }

private noncomputable def leaf251Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217873/134217728) }, vSqrt := { lower := (16383/16384), upper := (16777232/16776901) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (170751673/134217728) }, upper := { exponent := 0, mantissa := (1339/1024) } }, logOuter := sk47LogOuterCertificate, logK := sk47LogKCertificate, logChi := chi41LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (33554133/33553802) } }, logDArg := sk47LogDArgCertificate }

private noncomputable def leaf251InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf251LocalValidity :
    LeafFacts leaf251Box leaf251Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf251Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (16777232/16776901) }) = true
      norm_num [leaf251Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf251CertificateValid :
    WideCertificateValid leaf251Box leaf251Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk47ValidityFacts chi41ValidityFacts
    leaf251LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf251CoverageChecked :
    coverageCheck (innerAD leaf251Box) leaf251InnerLog = true := by
  rfl'

private theorem leaf251InnerLogValid :
    leaf251InnerLog.Valid 8 (innerAD leaf251Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf251CoverageChecked

private noncomputable def leaf251InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (5814623/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf251InputLogOnePlusV_eq :
    leaf251InputLogOnePlusV = outerEnclosure 24
      (leaf251Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf251RoundedFacts : LeafRoundedFacts 8
    leaf251Certificate.logOnePlusV leaf251InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf251InputLogOnePlusV_eq }

private noncomputable def leaf251Inputs : Inputs :=
  inputsOfCaches globalInput sk47RoundedInputs
    chi41InputQChi innerPair16Input
    leaf251InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf251LowerChecked :
    lowerCheck 24 leaf251Box leaf251Inputs = true := by
  rfl'

private theorem leaf251CoversExact : CoversExact 8
    leaf251Box leaf251Certificate leaf251InnerLog leaf251Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk47RoundedFacts chi41RoundedFacts
    innerPair16RoundedFacts leaf251RoundedFacts (by rfl)

private theorem leaf251FlatSound : Sound leaf251Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf251CertificateValid
    leaf251InnerLogValid leaf251CoversExact leaf251LowerChecked

private noncomputable def leaf252Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/32), kHi := (2), chiLo := (9/64), chiHi := (5/32) }

private noncomputable def leaf252Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217875/134217728) }, vSqrt := { lower := (65531/65536), upper := (1048577/1048556) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (171341459/134217728) }, upper := { exponent := 0, mantissa := (21/16) } }, logOuter := sk48LogOuterCertificate, logK := sk48LogKCertificate, logChi := chi41LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (2097133/2097112) } }, logDArg := sk48LogDArgCertificate }

private noncomputable def leaf252InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf252LocalValidity :
    LeafFacts leaf252Box leaf252Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf252Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (1048577/1048556) }) = true
      norm_num [leaf252Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf252CertificateValid :
    WideCertificateValid leaf252Box leaf252Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk48ValidityFacts chi41ValidityFacts
    leaf252LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf252CoverageChecked :
    coverageCheck (innerAD leaf252Box) leaf252InnerLog = true := by
  rfl'

private theorem leaf252InnerLogValid :
    leaf252InnerLog.Valid 8 (innerAD leaf252Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf252CoverageChecked

private noncomputable def leaf252InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629249/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf252InputLogOnePlusV_eq :
    leaf252InputLogOnePlusV = outerEnclosure 24
      (leaf252Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf252RoundedFacts : LeafRoundedFacts 8
    leaf252Certificate.logOnePlusV leaf252InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf252InputLogOnePlusV_eq }

private noncomputable def leaf252Inputs : Inputs :=
  inputsOfCaches globalInput sk48RoundedInputs
    chi41InputQChi innerPair16Input
    leaf252InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf252LowerChecked :
    lowerCheck 24 leaf252Box leaf252Inputs = true := by
  rfl'

private theorem leaf252CoversExact : CoversExact 8
    leaf252Box leaf252Certificate leaf252InnerLog leaf252Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk48RoundedFacts chi41RoundedFacts
    innerPair16RoundedFacts leaf252RoundedFacts (by rfl)

private theorem leaf252FlatSound : Sound leaf252Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf252CertificateValid
    leaf252InnerLogValid leaf252CoversExact leaf252LowerChecked

private noncomputable def leaf253Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (31/16), chiLo := (5/32), chiHi := (11/64) }

private noncomputable def leaf253Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108947/67108864) }, vSqrt := { lower := (16383/16384), upper := (16777248/16776875) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (86735615/67108864) }, upper := { exponent := 0, mantissa := (1365/1024) } }, logOuter := sk41LogOuterCertificate, logK := sk41LogKCertificate, logChi := chi42LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (33554123/33553750) } }, logDArg := sk41LogDArgCertificate }

private noncomputable def leaf253InnerLog : WideLogData :=
  innerPair140Data

set_option maxRecDepth 1000000 in
private theorem leaf253LocalValidity :
    LeafFacts leaf253Box leaf253Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf253Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (16777248/16776875) }) = true
      norm_num [leaf253Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf253CertificateValid :
    WideCertificateValid leaf253Box leaf253Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk41ValidityFacts chi42ValidityFacts
    leaf253LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf253CoverageChecked :
    coverageCheck (innerAD leaf253Box) leaf253InnerLog = true := by
  rfl'

private theorem leaf253InnerLogValid :
    leaf253InnerLog.Valid 8 (innerAD leaf253Box) :=
  wideLogDataValid_of_cachedCheck endpoint35PositiveFacts
    endpoint36PositiveFacts.valid leaf253CoverageChecked

private noncomputable def leaf253InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629267/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf253InputLogOnePlusV_eq :
    leaf253InputLogOnePlusV = outerEnclosure 24
      (leaf253Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf253RoundedFacts : LeafRoundedFacts 8
    leaf253Certificate.logOnePlusV leaf253InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf253InputLogOnePlusV_eq }

private noncomputable def leaf253Inputs : Inputs :=
  inputsOfCaches globalInput sk41RoundedInputs
    chi42InputQChi innerPair140Input
    leaf253InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf253LowerChecked :
    lowerCheck 24 leaf253Box leaf253Inputs = true := by
  rfl'

private theorem leaf253CoversExact : CoversExact 8
    leaf253Box leaf253Certificate leaf253InnerLog leaf253Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk41RoundedFacts chi42RoundedFacts
    innerPair140RoundedFacts leaf253RoundedFacts (by rfl)

private theorem leaf253FlatSound : Sound leaf253Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf253CertificateValid
    leaf253InnerLogValid leaf253CoversExact leaf253LowerChecked

private noncomputable def leaf254Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (61/32), chiLo := (11/64), chiHi := (3/16) }

private noncomputable def leaf254Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217873/134217728) }, vSqrt := { lower := (16383/16384), upper := (8388616/8388425) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (177435937/134217728) }, upper := { exponent := 0, mantissa := (695/512) } }, logOuter := sk49LogOuterCertificate, logK := sk49LogKCertificate, logChi := chi43LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (16777041/16776850) } }, logDArg := sk49LogDArgCertificate }

private noncomputable def leaf254InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf254LocalValidity :
    LeafFacts leaf254Box leaf254Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf254Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (8388616/8388425) }) = true
      norm_num [leaf254Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf254CertificateValid :
    WideCertificateValid leaf254Box leaf254Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk49ValidityFacts chi43ValidityFacts
    leaf254LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf254CoverageChecked :
    coverageCheck (innerAD leaf254Box) leaf254InnerLog = true := by
  rfl'

private theorem leaf254InnerLogValid :
    leaf254InnerLog.Valid 8 (innerAD leaf254Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf254CoverageChecked

private noncomputable def leaf254InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (1453659/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf254InputLogOnePlusV_eq :
    leaf254InputLogOnePlusV = outerEnclosure 24
      (leaf254Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf254RoundedFacts : LeafRoundedFacts 8
    leaf254Certificate.logOnePlusV leaf254InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf254InputLogOnePlusV_eq }

private noncomputable def leaf254Inputs : Inputs :=
  inputsOfCaches globalInput sk49RoundedInputs
    chi43InputQChi innerPair21Input
    leaf254InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf254LowerChecked :
    lowerCheck 24 leaf254Box leaf254Inputs = true := by
  rfl'

private theorem leaf254CoversExact : CoversExact 8
    leaf254Box leaf254Certificate leaf254InnerLog leaf254Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk49RoundedFacts chi43RoundedFacts
    innerPair21RoundedFacts leaf254RoundedFacts (by rfl)

private theorem leaf254FlatSound : Sound leaf254Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf254CertificateValid
    leaf254InnerLogValid leaf254CoversExact leaf254LowerChecked

private noncomputable def leaf255Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/32), kHi := (31/16), chiLo := (11/64), chiHi := (3/16) }

private noncomputable def leaf255Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217875/134217728) }, vSqrt := { lower := (16383/16384), upper := (4194308/4194211) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (178156787/134217728) }, upper := { exponent := 0, mantissa := (349/256) } }, logOuter := sk50LogOuterCertificate, logK := sk50LogKCertificate, logChi := chi43LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (8388519/8388422) } }, logDArg := sk50LogDArgCertificate }

private noncomputable def leaf255InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf255LocalValidity :
    LeafFacts leaf255Box leaf255Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf255Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (4194308/4194211) }) = true
      norm_num [leaf255Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf255CertificateValid :
    WideCertificateValid leaf255Box leaf255Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk50ValidityFacts chi43ValidityFacts
    leaf255LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf255CoverageChecked :
    coverageCheck (innerAD leaf255Box) leaf255InnerLog = true := by
  rfl'

private theorem leaf255InnerLogValid :
    leaf255InnerLog.Valid 8 (innerAD leaf255Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf255CoverageChecked

private noncomputable def leaf255InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629275/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf255InputLogOnePlusV_eq :
    leaf255InputLogOnePlusV = outerEnclosure 24
      (leaf255Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf255RoundedFacts : LeafRoundedFacts 8
    leaf255Certificate.logOnePlusV leaf255InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf255InputLogOnePlusV_eq }

private noncomputable def leaf255Inputs : Inputs :=
  inputsOfCaches globalInput sk50RoundedInputs
    chi43InputQChi innerPair21Input
    leaf255InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf255LowerChecked :
    lowerCheck 24 leaf255Box leaf255Inputs = true := by
  rfl'

private theorem leaf255CoversExact : CoversExact 8
    leaf255Box leaf255Certificate leaf255InnerLog leaf255Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk50RoundedFacts chi43RoundedFacts
    innerPair21RoundedFacts leaf255RoundedFacts (by rfl)

private theorem leaf255FlatSound : Sound leaf255Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf255CertificateValid
    leaf255InnerLogValid leaf255CoversExact leaf255LowerChecked

private noncomputable def leaf256Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (63/32), chiLo := (5/32), chiHi := (11/64) }

private noncomputable def leaf256Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217875/134217728) }, vSqrt := { lower := (16383/16384), upper := (33554464/33553739) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (174814655/134217728) }, upper := { exponent := 0, mantissa := (2741/2048) } }, logOuter := sk47LogOuterCertificate, logK := sk47LogKCertificate, logChi := chi42LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (67108203/67107478) } }, logDArg := sk47LogDArgCertificate }

private noncomputable def leaf256InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf256LocalValidity :
    LeafFacts leaf256Box leaf256Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf256Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (33554464/33553739) }) = true
      norm_num [leaf256Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf256CertificateValid :
    WideCertificateValid leaf256Box leaf256Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk47ValidityFacts chi42ValidityFacts
    leaf256LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf256CoverageChecked :
    coverageCheck (innerAD leaf256Box) leaf256InnerLog = true := by
  rfl'

private theorem leaf256InnerLogValid :
    leaf256InnerLog.Valid 8 (innerAD leaf256Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf256CoverageChecked

private noncomputable def leaf256InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (5814631/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf256InputLogOnePlusV_eq :
    leaf256InputLogOnePlusV = outerEnclosure 24
      (leaf256Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf256RoundedFacts : LeafRoundedFacts 8
    leaf256Certificate.logOnePlusV leaf256InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf256InputLogOnePlusV_eq }

private noncomputable def leaf256Inputs : Inputs :=
  inputsOfCaches globalInput sk47RoundedInputs
    chi42InputQChi innerPair17Input
    leaf256InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf256LowerChecked :
    lowerCheck 24 leaf256Box leaf256Inputs = true := by
  rfl'

private theorem leaf256CoversExact : CoversExact 8
    leaf256Box leaf256Certificate leaf256InnerLog leaf256Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk47RoundedFacts chi42RoundedFacts
    innerPair17RoundedFacts leaf256RoundedFacts (by rfl)

private theorem leaf256FlatSound : Sound leaf256Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf256CertificateValid
    leaf256InnerLogValid leaf256CoversExact leaf256LowerChecked

private noncomputable def leaf257Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/32), kHi := (2), chiLo := (5/32), chiHi := (11/64) }

private noncomputable def leaf257Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217877/134217728) }, vSqrt := { lower := (65531/65536), upper := (1048577/1048554) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (175469973/134217728) }, upper := { exponent := 0, mantissa := (43/32) } }, logOuter := sk48LogOuterCertificate, logK := sk48LogKCertificate, logChi := chi42LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (2097131/2097108) } }, logDArg := sk48LogDArgCertificate }

private noncomputable def leaf257InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf257LocalValidity :
    LeafFacts leaf257Box leaf257Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf257Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (1048577/1048554) }) = true
      norm_num [leaf257Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf257CertificateValid :
    WideCertificateValid leaf257Box leaf257Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk48ValidityFacts chi42ValidityFacts
    leaf257LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf257CoverageChecked :
    coverageCheck (innerAD leaf257Box) leaf257InnerLog = true := by
  rfl'

private theorem leaf257InnerLogValid :
    leaf257InnerLog.Valid 8 (innerAD leaf257Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf257CoverageChecked

private noncomputable def leaf257InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629265/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf257InputLogOnePlusV_eq :
    leaf257InputLogOnePlusV = outerEnclosure 24
      (leaf257Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf257RoundedFacts : LeafRoundedFacts 8
    leaf257Certificate.logOnePlusV leaf257InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf257InputLogOnePlusV_eq }

private noncomputable def leaf257Inputs : Inputs :=
  inputsOfCaches globalInput sk48RoundedInputs
    chi42InputQChi innerPair17Input
    leaf257InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf257LowerChecked :
    lowerCheck 24 leaf257Box leaf257Inputs = true := by
  rfl'

private theorem leaf257CoversExact : CoversExact 8
    leaf257Box leaf257Certificate leaf257InnerLog leaf257Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk48RoundedFacts chi42RoundedFacts
    innerPair17RoundedFacts leaf257RoundedFacts (by rfl)

private theorem leaf257FlatSound : Sound leaf257Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf257CertificateValid
    leaf257InnerLogValid leaf257CoversExact leaf257LowerChecked

private noncomputable def leaf258Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (63/32), chiLo := (11/64), chiHi := (3/16) }

private noncomputable def leaf258Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217877/134217728) }, vSqrt := { lower := (16383/16384), upper := (8388616/8388419) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (178877637/134217728) }, upper := { exponent := 0, mantissa := (701/512) } }, logOuter := sk47LogOuterCertificate, logK := sk47LogKCertificate, logChi := chi43LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (16777035/16776838) } }, logDArg := sk47LogDArgCertificate }

private noncomputable def leaf258InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf258LocalValidity :
    LeafFacts leaf258Box leaf258Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf258Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (8388616/8388419) }) = true
      norm_num [leaf258Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf258CertificateValid :
    WideCertificateValid leaf258Box leaf258Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk47ValidityFacts chi43ValidityFacts
    leaf258LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf258CoverageChecked :
    coverageCheck (innerAD leaf258Box) leaf258InnerLog = true := by
  rfl'

private theorem leaf258InnerLogValid :
    leaf258InnerLog.Valid 8 (innerAD leaf258Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf258CoverageChecked

private noncomputable def leaf258InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (5814639/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf258InputLogOnePlusV_eq :
    leaf258InputLogOnePlusV = outerEnclosure 24
      (leaf258Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf258RoundedFacts : LeafRoundedFacts 8
    leaf258Certificate.logOnePlusV leaf258InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf258InputLogOnePlusV_eq }

private noncomputable def leaf258Inputs : Inputs :=
  inputsOfCaches globalInput sk47RoundedInputs
    chi43InputQChi innerPair21Input
    leaf258InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf258LowerChecked :
    lowerCheck 24 leaf258Box leaf258Inputs = true := by
  rfl'

private theorem leaf258CoversExact : CoversExact 8
    leaf258Box leaf258Certificate leaf258InnerLog leaf258Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk47RoundedFacts chi43RoundedFacts
    innerPair21RoundedFacts leaf258RoundedFacts (by rfl)

private theorem leaf258FlatSound : Sound leaf258Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf258CertificateValid
    leaf258InnerLogValid leaf258CoversExact leaf258LowerChecked

private noncomputable def leaf259Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/32), kHi := (2), chiLo := (11/64), chiHi := (3/16) }

private noncomputable def leaf259Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217879/134217728) }, vSqrt := { lower := (65531/65536), upper := (1048577/1048552) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (179598487/134217728) }, upper := { exponent := 0, mantissa := (11/8) } }, logOuter := sk48LogOuterCertificate, logK := sk48LogKCertificate, logChi := chi43LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (2097129/2097104) } }, logDArg := sk48LogDArgCertificate }

private noncomputable def leaf259InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf259LocalValidity :
    LeafFacts leaf259Box leaf259Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf259Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (1048577/1048552) }) = true
      norm_num [leaf259Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf259CertificateValid :
    WideCertificateValid leaf259Box leaf259Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk48ValidityFacts chi43ValidityFacts
    leaf259LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf259CoverageChecked :
    coverageCheck (innerAD leaf259Box) leaf259InnerLog = true := by
  rfl'

private theorem leaf259InnerLogValid :
    leaf259InnerLog.Valid 8 (innerAD leaf259Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf259CoverageChecked

private noncomputable def leaf259InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629281/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf259InputLogOnePlusV_eq :
    leaf259InputLogOnePlusV = outerEnclosure 24
      (leaf259Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf259RoundedFacts : LeafRoundedFacts 8
    leaf259Certificate.logOnePlusV leaf259InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf259InputLogOnePlusV_eq }

private noncomputable def leaf259Inputs : Inputs :=
  inputsOfCaches globalInput sk48RoundedInputs
    chi43InputQChi innerPair21Input
    leaf259InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf259LowerChecked :
    lowerCheck 24 leaf259Box leaf259Inputs = true := by
  rfl'

private theorem leaf259CoversExact : CoversExact 8
    leaf259Box leaf259Certificate leaf259InnerLog leaf259Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk48RoundedFacts chi43RoundedFacts
    innerPair21RoundedFacts leaf259RoundedFacts (by rfl)

private theorem leaf259FlatSound : Sound leaf259Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf259CertificateValid
    leaf259InnerLogValid leaf259CoversExact leaf259LowerChecked

private noncomputable def leaf260Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (29/16), chiLo := (3/16), chiHi := (13/64) }

private noncomputable def leaf260Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108947/67108864) }, vSqrt := { lower := (16383/16384), upper := (16777248/16776839) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (89094767/67108864) }, upper := { exponent := 0, mantissa := (1401/1024) } }, logOuter := sk39LogOuterCertificate, logK := sk39LogKCertificate, logChi := chi34LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (33554087/33553678) } }, logDArg := sk39LogDArgCertificate }

private noncomputable def leaf260InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf260LocalValidity :
    LeafFacts leaf260Box leaf260Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf260Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (16777248/16776839) }) = true
      norm_num [leaf260Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf260CertificateValid :
    WideCertificateValid leaf260Box leaf260Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk39ValidityFacts chi34ValidityFacts
    leaf260LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf260CoverageChecked :
    coverageCheck (innerAD leaf260Box) leaf260InnerLog = true := by
  rfl'

private theorem leaf260InnerLogValid :
    leaf260InnerLog.Valid 8 (innerAD leaf260Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf260CoverageChecked

private noncomputable def leaf260InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629285/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf260InputLogOnePlusV_eq :
    leaf260InputLogOnePlusV = outerEnclosure 24
      (leaf260Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf260RoundedFacts : LeafRoundedFacts 8
    leaf260Certificate.logOnePlusV leaf260InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf260InputLogOnePlusV_eq }

private noncomputable def leaf260Inputs : Inputs :=
  inputsOfCaches globalInput sk39RoundedInputs
    chi34InputQChi innerPair21Input
    leaf260InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf260LowerChecked :
    lowerCheck 24 leaf260Box leaf260Inputs = true := by
  rfl'

private theorem leaf260CoversExact : CoversExact 8
    leaf260Box leaf260Certificate leaf260InnerLog leaf260Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk39RoundedFacts chi34RoundedFacts
    innerPair21RoundedFacts leaf260RoundedFacts (by rfl)

private theorem leaf260FlatSound : Sound leaf260Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf260CertificateValid
    leaf260InnerLogValid leaf260CoversExact leaf260LowerChecked

private noncomputable def leaf261Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (29/16), chiLo := (13/64), chiHi := (7/32) }

private noncomputable def leaf261Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108949/67108864) }, vSqrt := { lower := (16383/16384), upper := (2796208/2796135) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (90929661/67108864) }, upper := { exponent := 0, mantissa := (715/512) } }, logOuter := sk39LogOuterCertificate, logK := sk39LogKCertificate, logChi := chi35LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (5592343/5592270) } }, logDArg := sk39LogDArgCertificate }

private noncomputable def leaf261InnerLog : WideLogData :=
  innerPair143Data

set_option maxRecDepth 1000000 in
private theorem leaf261LocalValidity :
    LeafFacts leaf261Box leaf261Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf261Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (2796208/2796135) }) = true
      norm_num [leaf261Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf261CertificateValid :
    WideCertificateValid leaf261Box leaf261Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk39ValidityFacts chi35ValidityFacts
    leaf261LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf261CoverageChecked :
    coverageCheck (innerAD leaf261Box) leaf261InnerLog = true := by
  rfl'

private theorem leaf261InnerLogValid :
    leaf261InnerLog.Valid 8 (innerAD leaf261Box) :=
  wideLogDataValid_of_cachedCheck endpoint37PositiveFacts
    endpoint38PositiveFacts.valid leaf261CoverageChecked

private noncomputable def leaf261InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (2907325/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf261InputLogOnePlusV_eq :
    leaf261InputLogOnePlusV = outerEnclosure 24
      (leaf261Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf261RoundedFacts : LeafRoundedFacts 8
    leaf261Certificate.logOnePlusV leaf261InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf261InputLogOnePlusV_eq }

private noncomputable def leaf261Inputs : Inputs :=
  inputsOfCaches globalInput sk39RoundedInputs
    chi35InputQChi innerPair143Input
    leaf261InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf261LowerChecked :
    lowerCheck 24 leaf261Box leaf261Inputs = true := by
  rfl'

private theorem leaf261CoversExact : CoversExact 8
    leaf261Box leaf261Certificate leaf261InnerLog leaf261Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk39RoundedFacts chi35RoundedFacts
    innerPair143RoundedFacts leaf261RoundedFacts (by rfl)

private theorem leaf261FlatSound : Sound leaf261Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf261CertificateValid
    leaf261InnerLogValid leaf261CoversExact leaf261LowerChecked

private noncomputable def leaf262Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (59/32), chiLo := (3/16), chiHi := (13/64) }

private noncomputable def leaf262Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217871/134217728) }, vSqrt := { lower := (16383/16384), upper := (1973792/1973745) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (179795091/134217728) }, upper := { exponent := 0, mantissa := (2815/2048) } }, logOuter := sk51LogOuterCertificate, logK := sk51LogKCertificate, logChi := chi34LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (3947537/3947490) } }, logDArg := sk51LogDArgCertificate }

private noncomputable def leaf262InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf262LocalValidity :
    LeafFacts leaf262Box leaf262Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf262Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (1973792/1973745) }) = true
      norm_num [leaf262Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf262CertificateValid :
    WideCertificateValid leaf262Box leaf262Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk51ValidityFacts chi34ValidityFacts
    leaf262LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf262CoverageChecked :
    coverageCheck (innerAD leaf262Box) leaf262InnerLog = true := by
  rfl'

private theorem leaf262InnerLogValid :
    leaf262InnerLog.Valid 8 (innerAD leaf262Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf262CoverageChecked

private noncomputable def leaf262InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (363415/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf262InputLogOnePlusV_eq :
    leaf262InputLogOnePlusV = outerEnclosure 24
      (leaf262Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf262RoundedFacts : LeafRoundedFacts 8
    leaf262Certificate.logOnePlusV leaf262InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf262InputLogOnePlusV_eq }

private noncomputable def leaf262Inputs : Inputs :=
  inputsOfCaches globalInput sk51RoundedInputs
    chi34InputQChi innerPair21Input
    leaf262InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf262LowerChecked :
    lowerCheck 24 leaf262Box leaf262Inputs = true := by
  rfl'

private theorem leaf262CoversExact : CoversExact 8
    leaf262Box leaf262Certificate leaf262InnerLog leaf262Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk51RoundedFacts chi34RoundedFacts
    innerPair21RoundedFacts leaf262RoundedFacts (by rfl)

private theorem leaf262FlatSound : Sound leaf262Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf262CertificateValid
    leaf262InnerLogValid leaf262CoversExact leaf262LowerChecked

private noncomputable def leaf263Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/32), kHi := (15/8), chiLo := (3/16), chiHi := (13/64) }

private noncomputable def leaf263Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217873/134217728) }, vSqrt := { lower := (16383/16384), upper := (8388616/8388413) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (180581473/134217728) }, upper := { exponent := 0, mantissa := (707/512) } }, logOuter := sk52LogOuterCertificate, logK := sk52LogKCertificate, logChi := chi34LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (16777029/16776826) } }, logDArg := sk52LogDArgCertificate }

private noncomputable def leaf263InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf263LocalValidity :
    LeafFacts leaf263Box leaf263Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf263Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (8388616/8388413) }) = true
      norm_num [leaf263Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf263CertificateValid :
    WideCertificateValid leaf263Box leaf263Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk52ValidityFacts chi34ValidityFacts
    leaf263LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf263CoverageChecked :
    coverageCheck (innerAD leaf263Box) leaf263InnerLog = true := by
  rfl'

private theorem leaf263InnerLogValid :
    leaf263InnerLog.Valid 8 (innerAD leaf263Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf263CoverageChecked

private noncomputable def leaf263InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (2907321/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf263InputLogOnePlusV_eq :
    leaf263InputLogOnePlusV = outerEnclosure 24
      (leaf263Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf263RoundedFacts : LeafRoundedFacts 8
    leaf263Certificate.logOnePlusV leaf263InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf263InputLogOnePlusV_eq }

private noncomputable def leaf263Inputs : Inputs :=
  inputsOfCaches globalInput sk52RoundedInputs
    chi34InputQChi innerPair22Input
    leaf263InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf263LowerChecked :
    lowerCheck 24 leaf263Box leaf263Inputs = true := by
  rfl'

private theorem leaf263CoversExact : CoversExact 8
    leaf263Box leaf263Certificate leaf263InnerLog leaf263Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk52RoundedFacts chi34RoundedFacts
    innerPair22RoundedFacts leaf263RoundedFacts (by rfl)

private theorem leaf263FlatSound : Sound leaf263Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf263CertificateValid
    leaf263InnerLogValid leaf263CoversExact leaf263LowerChecked

private noncomputable def leaf264Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (59/32), chiLo := (13/64), chiHi := (7/32) }

private noncomputable def leaf264Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217873/134217728) }, vSqrt := { lower := (16383/16384), upper := (16777232/16776803) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (183595945/134217728) }, upper := { exponent := 0, mantissa := (1437/1024) } }, logOuter := sk51LogOuterCertificate, logK := sk51LogKCertificate, logChi := chi35LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (33554035/33553606) } }, logDArg := sk51LogDArgCertificate }

private noncomputable def leaf264InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf264LocalValidity :
    LeafFacts leaf264Box leaf264Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf264Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (16777232/16776803) }) = true
      norm_num [leaf264Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf264CertificateValid :
    WideCertificateValid leaf264Box leaf264Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk51ValidityFacts chi35ValidityFacts
    leaf264LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf264CoverageChecked :
    coverageCheck (innerAD leaf264Box) leaf264InnerLog = true := by
  rfl'

private theorem leaf264InnerLogValid :
    leaf264InnerLog.Valid 8 (innerAD leaf264Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf264CoverageChecked

private noncomputable def leaf264InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629295/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf264InputLogOnePlusV_eq :
    leaf264InputLogOnePlusV = outerEnclosure 24
      (leaf264Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf264RoundedFacts : LeafRoundedFacts 8
    leaf264Certificate.logOnePlusV leaf264InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf264InputLogOnePlusV_eq }

private noncomputable def leaf264Inputs : Inputs :=
  inputsOfCaches globalInput sk51RoundedInputs
    chi35InputQChi innerPair22Input
    leaf264InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf264LowerChecked :
    lowerCheck 24 leaf264Box leaf264Inputs = true := by
  rfl'

private theorem leaf264CoversExact : CoversExact 8
    leaf264Box leaf264Certificate leaf264InnerLog leaf264Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk51RoundedFacts chi35RoundedFacts
    innerPair22RoundedFacts leaf264RoundedFacts (by rfl)

private theorem leaf264FlatSound : Sound leaf264Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf264CertificateValid
    leaf264InnerLogValid leaf264CoversExact leaf264LowerChecked

private noncomputable def leaf265Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/32), kHi := (15/8), chiLo := (13/64), chiHi := (7/32) }

private noncomputable def leaf265Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217875/134217728) }, vSqrt := { lower := (16383/16384), upper := (4194308/4194199) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (184447859/134217728) }, upper := { exponent := 0, mantissa := (361/256) } }, logOuter := sk52LogOuterCertificate, logK := sk52LogKCertificate, logChi := chi35LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (8388507/8388398) } }, logDArg := sk52LogDArgCertificate }

private noncomputable def leaf265InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf265LocalValidity :
    LeafFacts leaf265Box leaf265Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf265Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (4194308/4194199) }) = true
      norm_num [leaf265Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf265CertificateValid :
    WideCertificateValid leaf265Box leaf265Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk52ValidityFacts chi35ValidityFacts
    leaf265LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf265CoverageChecked :
    coverageCheck (innerAD leaf265Box) leaf265InnerLog = true := by
  rfl'

private theorem leaf265InnerLogValid :
    leaf265InnerLog.Valid 8 (innerAD leaf265Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf265CoverageChecked

private noncomputable def leaf265InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629299/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf265InputLogOnePlusV_eq :
    leaf265InputLogOnePlusV = outerEnclosure 24
      (leaf265Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf265RoundedFacts : LeafRoundedFacts 8
    leaf265Certificate.logOnePlusV leaf265InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf265InputLogOnePlusV_eq }

private noncomputable def leaf265Inputs : Inputs :=
  inputsOfCaches globalInput sk52RoundedInputs
    chi35InputQChi innerPair22Input
    leaf265InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf265LowerChecked :
    lowerCheck 24 leaf265Box leaf265Inputs = true := by
  rfl'

private theorem leaf265CoversExact : CoversExact 8
    leaf265Box leaf265Certificate leaf265InnerLog leaf265Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk52RoundedFacts chi35RoundedFacts
    innerPair22RoundedFacts leaf265RoundedFacts (by rfl)

private theorem leaf265FlatSound : Sound leaf265Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf265CertificateValid
    leaf265InnerLogValid leaf265CoversExact leaf265LowerChecked

private noncomputable def leaf266Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (29/16), chiLo := (7/32), chiHi := (15/64) }

private noncomputable def leaf266Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108951/67108864) }, vSqrt := { lower := (16383/16384), upper := (16777248/16776781) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (92764555/67108864) }, upper := { exponent := 0, mantissa := (1459/1024) } }, logOuter := sk39LogOuterCertificate, logK := sk39LogKCertificate, logChi := chi44LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (33554029/33553562) } }, logDArg := sk39LogDArgCertificate }

private noncomputable def leaf266InnerLog : WideLogData :=
  innerPair147Data

set_option maxRecDepth 1000000 in
private theorem leaf266LocalValidity :
    LeafFacts leaf266Box leaf266Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf266Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (16777248/16776781) }) = true
      norm_num [leaf266Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf266CertificateValid :
    WideCertificateValid leaf266Box leaf266Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk39ValidityFacts chi44ValidityFacts
    leaf266LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf266CoverageChecked :
    coverageCheck (innerAD leaf266Box) leaf266InnerLog = true := by
  rfl'

private theorem leaf266InnerLogValid :
    leaf266InnerLog.Valid 8 (innerAD leaf266Box) :=
  wideLogDataValid_of_cachedCheck endpoint39PositiveFacts
    endpoint40PositiveFacts.valid leaf266CoverageChecked

private noncomputable def leaf266InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (5814657/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf266InputLogOnePlusV_eq :
    leaf266InputLogOnePlusV = outerEnclosure 24
      (leaf266Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf266RoundedFacts : LeafRoundedFacts 8
    leaf266Certificate.logOnePlusV leaf266InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf266InputLogOnePlusV_eq }

private noncomputable def leaf266Inputs : Inputs :=
  inputsOfCaches globalInput sk39RoundedInputs
    chi44InputQChi innerPair147Input
    leaf266InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf266LowerChecked :
    lowerCheck 24 leaf266Box leaf266Inputs = true := by
  rfl'

private theorem leaf266CoversExact : CoversExact 8
    leaf266Box leaf266Certificate leaf266InnerLog leaf266Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk39RoundedFacts chi44RoundedFacts
    innerPair147RoundedFacts leaf266RoundedFacts (by rfl)

private theorem leaf266FlatSound : Sound leaf266Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf266CertificateValid
    leaf266InnerLogValid leaf266CoversExact leaf266LowerChecked

private noncomputable def leaf267Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (29/16), chiLo := (15/64), chiHi := (1/4) }

private noncomputable def leaf267Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108953/67108864) }, vSqrt := { lower := (16383/16384), upper := (1048578/1048547) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (94599449/67108864) }, upper := { exponent := 0, mantissa := (93/64) } }, logOuter := sk39LogOuterCertificate, logK := sk39LogKCertificate, logChi := chi45LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (2097125/2097094) } }, logDArg := sk39LogDArgCertificate }

private noncomputable def leaf267InnerLog : WideLogData :=
  innerPair144Data

set_option maxRecDepth 1000000 in
private theorem leaf267LocalValidity :
    LeafFacts leaf267Box leaf267Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf267Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (1048578/1048547) }) = true
      norm_num [leaf267Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf267CertificateValid :
    WideCertificateValid leaf267Box leaf267Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk39ValidityFacts chi45ValidityFacts
    leaf267LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf267CoverageChecked :
    coverageCheck (innerAD leaf267Box) leaf267InnerLog = true := by
  rfl'

private theorem leaf267InnerLogValid :
    leaf267InnerLog.Valid 8 (innerAD leaf267Box) :=
  wideLogDataValid_of_cachedCheck endpoint38PositiveFacts
    endpoint41PositiveFacts.valid leaf267CoverageChecked

private noncomputable def leaf267InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629329/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf267InputLogOnePlusV_eq :
    leaf267InputLogOnePlusV = outerEnclosure 24
      (leaf267Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf267RoundedFacts : LeafRoundedFacts 8
    leaf267Certificate.logOnePlusV leaf267InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf267InputLogOnePlusV_eq }

private noncomputable def leaf267Inputs : Inputs :=
  inputsOfCaches globalInput sk39RoundedInputs
    chi45InputQChi innerPair144Input
    leaf267InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf267LowerChecked :
    lowerCheck 24 leaf267Box leaf267Inputs = true := by
  rfl'

private theorem leaf267CoversExact : CoversExact 8
    leaf267Box leaf267Certificate leaf267InnerLog leaf267Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk39RoundedFacts chi45RoundedFacts
    innerPair144RoundedFacts leaf267RoundedFacts (by rfl)

private theorem leaf267FlatSound : Sound leaf267Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf267CertificateValid
    leaf267InnerLogValid leaf267CoversExact leaf267LowerChecked

private noncomputable def leaf268Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (59/32), chiLo := (7/32), chiHi := (15/64) }

private noncomputable def leaf268Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217875/134217728) }, vSqrt := { lower := (16383/16384), upper := (33554464/33553547) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (187396799/134217728) }, upper := { exponent := 0, mantissa := (2933/2048) } }, logOuter := sk51LogOuterCertificate, logK := sk51LogKCertificate, logChi := chi44LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (67108011/67107094) } }, logDArg := sk51LogDArgCertificate }

private noncomputable def leaf268InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf268LocalValidity :
    LeafFacts leaf268Box leaf268Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf268Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (33554464/33553547) }) = true
      norm_num [leaf268Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf268CertificateValid :
    WideCertificateValid leaf268Box leaf268Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk51ValidityFacts chi44ValidityFacts
    leaf268LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf268CoverageChecked :
    coverageCheck (innerAD leaf268Box) leaf268InnerLog = true := by
  rfl'

private theorem leaf268InnerLogValid :
    leaf268InnerLog.Valid 8 (innerAD leaf268Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf268CoverageChecked

private noncomputable def leaf268InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (5814655/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf268InputLogOnePlusV_eq :
    leaf268InputLogOnePlusV = outerEnclosure 24
      (leaf268Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf268RoundedFacts : LeafRoundedFacts 8
    leaf268Certificate.logOnePlusV leaf268InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf268InputLogOnePlusV_eq }

private noncomputable def leaf268Inputs : Inputs :=
  inputsOfCaches globalInput sk51RoundedInputs
    chi44InputQChi innerPair26Input
    leaf268InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf268LowerChecked :
    lowerCheck 24 leaf268Box leaf268Inputs = true := by
  rfl'

private theorem leaf268CoversExact : CoversExact 8
    leaf268Box leaf268Certificate leaf268InnerLog leaf268Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk51RoundedFacts chi44RoundedFacts
    innerPair26RoundedFacts leaf268RoundedFacts (by rfl)

private theorem leaf268FlatSound : Sound leaf268Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf268CertificateValid
    leaf268InnerLogValid leaf268CoversExact leaf268LowerChecked

private noncomputable def leaf269Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/32), kHi := (15/8), chiLo := (7/32), chiHi := (15/64) }

private noncomputable def leaf269Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217877/134217728) }, vSqrt := { lower := (16383/16384), upper := (8388616/8388383) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (188314245/134217728) }, upper := { exponent := 0, mantissa := (737/512) } }, logOuter := sk52LogOuterCertificate, logK := sk52LogKCertificate, logChi := chi44LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (16776999/16776766) } }, logDArg := sk52LogDArgCertificate }

private noncomputable def leaf269InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf269LocalValidity :
    LeafFacts leaf269Box leaf269Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf269Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (8388616/8388383) }) = true
      norm_num [leaf269Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf269CertificateValid :
    WideCertificateValid leaf269Box leaf269Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk52ValidityFacts chi44ValidityFacts
    leaf269LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf269CoverageChecked :
    coverageCheck (innerAD leaf269Box) leaf269InnerLog = true := by
  rfl'

private theorem leaf269InnerLogValid :
    leaf269InnerLog.Valid 8 (innerAD leaf269Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf269CoverageChecked

private noncomputable def leaf269InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (5814657/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf269InputLogOnePlusV_eq :
    leaf269InputLogOnePlusV = outerEnclosure 24
      (leaf269Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf269RoundedFacts : LeafRoundedFacts 8
    leaf269Certificate.logOnePlusV leaf269InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf269InputLogOnePlusV_eq }

private noncomputable def leaf269Inputs : Inputs :=
  inputsOfCaches globalInput sk52RoundedInputs
    chi44InputQChi innerPair27Input
    leaf269InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf269LowerChecked :
    lowerCheck 24 leaf269Box leaf269Inputs = true := by
  rfl'

private theorem leaf269CoversExact : CoversExact 8
    leaf269Box leaf269Certificate leaf269InnerLog leaf269Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk52RoundedFacts chi44RoundedFacts
    innerPair27RoundedFacts leaf269RoundedFacts (by rfl)

private theorem leaf269FlatSound : Sound leaf269Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf269CertificateValid
    leaf269InnerLogValid leaf269CoversExact leaf269LowerChecked

private noncomputable def leaf270Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (59/32), chiLo := (15/64), chiHi := (1/4) }

private noncomputable def leaf270Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217877/134217728) }, vSqrt := { lower := (16383/16384), upper := (2097154/2097093) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (191197653/134217728) }, upper := { exponent := 0, mantissa := (187/128) } }, logOuter := sk51LogOuterCertificate, logK := sk51LogKCertificate, logChi := chi45LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (4194247/4194186) } }, logDArg := sk51LogDArgCertificate }

private noncomputable def leaf270InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf270LocalValidity :
    LeafFacts leaf270Box leaf270Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf270Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (2097154/2097093) }) = true
      norm_num [leaf270Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf270CertificateValid :
    WideCertificateValid leaf270Box leaf270Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk51ValidityFacts chi45ValidityFacts
    leaf270LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf270CoverageChecked :
    coverageCheck (innerAD leaf270Box) leaf270InnerLog = true := by
  rfl'

private theorem leaf270InnerLogValid :
    leaf270InnerLog.Valid 8 (innerAD leaf270Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf270CoverageChecked

private noncomputable def leaf270InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629325/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf270InputLogOnePlusV_eq :
    leaf270InputLogOnePlusV = outerEnclosure 24
      (leaf270Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf270RoundedFacts : LeafRoundedFacts 8
    leaf270Certificate.logOnePlusV leaf270InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf270InputLogOnePlusV_eq }

private noncomputable def leaf270Inputs : Inputs :=
  inputsOfCaches globalInput sk51RoundedInputs
    chi45InputQChi innerPair27Input
    leaf270InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf270LowerChecked :
    lowerCheck 24 leaf270Box leaf270Inputs = true := by
  rfl'

private theorem leaf270CoversExact : CoversExact 8
    leaf270Box leaf270Certificate leaf270InnerLog leaf270Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk51RoundedFacts chi45RoundedFacts
    innerPair27RoundedFacts leaf270RoundedFacts (by rfl)

private theorem leaf270FlatSound : Sound leaf270Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf270CertificateValid
    leaf270InnerLogValid leaf270CoversExact leaf270LowerChecked

private noncomputable def leaf271Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/32), kHi := (15/8), chiLo := (15/64), chiHi := (1/4) }

private noncomputable def leaf271Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217879/134217728) }, vSqrt := { lower := (16383/16384), upper := (1048577/1048546) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (192180631/134217728) }, upper := { exponent := 0, mantissa := (47/32) } }, logOuter := sk52LogOuterCertificate, logK := sk52LogKCertificate, logChi := chi45LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (2097123/2097092) } }, logDArg := sk52LogDArgCertificate }

private noncomputable def leaf271InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf271LocalValidity :
    LeafFacts leaf271Box leaf271Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf271Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (1048577/1048546) }) = true
      norm_num [leaf271Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf271CertificateValid :
    WideCertificateValid leaf271Box leaf271Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk52ValidityFacts chi45ValidityFacts
    leaf271LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf271CoverageChecked :
    coverageCheck (innerAD leaf271Box) leaf271InnerLog = true := by
  rfl'

private theorem leaf271InnerLogValid :
    leaf271InnerLog.Valid 8 (innerAD leaf271Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf271CoverageChecked

private noncomputable def leaf271InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629329/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf271InputLogOnePlusV_eq :
    leaf271InputLogOnePlusV = outerEnclosure 24
      (leaf271Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf271RoundedFacts : LeafRoundedFacts 8
    leaf271Certificate.logOnePlusV leaf271InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf271InputLogOnePlusV_eq }

private noncomputable def leaf271Inputs : Inputs :=
  inputsOfCaches globalInput sk52RoundedInputs
    chi45InputQChi innerPair27Input
    leaf271InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf271LowerChecked :
    lowerCheck 24 leaf271Box leaf271Inputs = true := by
  rfl'

private theorem leaf271CoversExact : CoversExact 8
    leaf271Box leaf271Certificate leaf271InnerLog leaf271Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk52RoundedFacts chi45RoundedFacts
    innerPair27RoundedFacts leaf271RoundedFacts (by rfl)

private theorem leaf271FlatSound : Sound leaf271Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf271CertificateValid
    leaf271InnerLogValid leaf271CoversExact leaf271LowerChecked

private noncomputable def leaf272Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (61/32), chiLo := (3/16), chiHi := (13/64) }

private noncomputable def leaf272Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217875/134217728) }, vSqrt := { lower := (16383/16384), upper := (33554464/33553639) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (181367855/134217728) }, upper := { exponent := 0, mantissa := (2841/2048) } }, logOuter := sk49LogOuterCertificate, logK := sk49LogKCertificate, logChi := chi34LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (67108103/67107278) } }, logDArg := sk49LogDArgCertificate }

private noncomputable def leaf272InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf272LocalValidity :
    LeafFacts leaf272Box leaf272Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf272Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (33554464/33553639) }) = true
      norm_num [leaf272Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf272CertificateValid :
    WideCertificateValid leaf272Box leaf272Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk49ValidityFacts chi34ValidityFacts
    leaf272LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf272CoverageChecked :
    coverageCheck (innerAD leaf272Box) leaf272InnerLog = true := by
  rfl'

private theorem leaf272InnerLogValid :
    leaf272InnerLog.Valid 8 (innerAD leaf272Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf272CoverageChecked

private noncomputable def leaf272InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629287/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf272InputLogOnePlusV_eq :
    leaf272InputLogOnePlusV = outerEnclosure 24
      (leaf272Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf272RoundedFacts : LeafRoundedFacts 8
    leaf272Certificate.logOnePlusV leaf272InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf272InputLogOnePlusV_eq }

private noncomputable def leaf272Inputs : Inputs :=
  inputsOfCaches globalInput sk49RoundedInputs
    chi34InputQChi innerPair22Input
    leaf272InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf272LowerChecked :
    lowerCheck 24 leaf272Box leaf272Inputs = true := by
  rfl'

private theorem leaf272CoversExact : CoversExact 8
    leaf272Box leaf272Certificate leaf272InnerLog leaf272Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk49RoundedFacts chi34RoundedFacts
    innerPair22RoundedFacts leaf272RoundedFacts (by rfl)

private theorem leaf272FlatSound : Sound leaf272Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf272CertificateValid
    leaf272InnerLogValid leaf272CoversExact leaf272LowerChecked

private noncomputable def leaf273Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/32), kHi := (31/16), chiLo := (3/16), chiHi := (13/64) }

private noncomputable def leaf273Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217877/134217728) }, vSqrt := { lower := (16383/16384), upper := (16777232/16776813) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (182154237/134217728) }, upper := { exponent := 0, mantissa := (1427/1024) } }, logOuter := sk50LogOuterCertificate, logK := sk50LogKCertificate, logChi := chi34LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (33554045/33553626) } }, logDArg := sk50LogDArgCertificate }

private noncomputable def leaf273InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf273LocalValidity :
    LeafFacts leaf273Box leaf273Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf273Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (16777232/16776813) }) = true
      norm_num [leaf273Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf273CertificateValid :
    WideCertificateValid leaf273Box leaf273Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk50ValidityFacts chi34ValidityFacts
    leaf273LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf273CoverageChecked :
    coverageCheck (innerAD leaf273Box) leaf273InnerLog = true := by
  rfl'

private theorem leaf273InnerLogValid :
    leaf273InnerLog.Valid 8 (innerAD leaf273Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf273CoverageChecked

private noncomputable def leaf273InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (5814645/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf273InputLogOnePlusV_eq :
    leaf273InputLogOnePlusV = outerEnclosure 24
      (leaf273Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf273RoundedFacts : LeafRoundedFacts 8
    leaf273Certificate.logOnePlusV leaf273InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf273InputLogOnePlusV_eq }

private noncomputable def leaf273Inputs : Inputs :=
  inputsOfCaches globalInput sk50RoundedInputs
    chi34InputQChi innerPair22Input
    leaf273InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf273LowerChecked :
    lowerCheck 24 leaf273Box leaf273Inputs = true := by
  rfl'

private theorem leaf273CoversExact : CoversExact 8
    leaf273Box leaf273Certificate leaf273InnerLog leaf273Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk50RoundedFacts chi34RoundedFacts
    innerPair22RoundedFacts leaf273RoundedFacts (by rfl)

private theorem leaf273FlatSound : Sound leaf273Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf273CertificateValid
    leaf273InnerLogValid leaf273CoversExact leaf273LowerChecked

private noncomputable def leaf274Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (61/32), chiLo := (13/64), chiHi := (7/32) }

private noncomputable def leaf274Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217877/134217728) }, vSqrt := { lower := (16383/16384), upper := (16777232/16776789) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (185299773/134217728) }, upper := { exponent := 0, mantissa := (1451/1024) } }, logOuter := sk49LogOuterCertificate, logK := sk49LogKCertificate, logChi := chi35LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (33554021/33553578) } }, logDArg := sk49LogDArgCertificate }

private noncomputable def leaf274InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf274LocalValidity :
    LeafFacts leaf274Box leaf274Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf274Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (16777232/16776789) }) = true
      norm_num [leaf274Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf274CertificateValid :
    WideCertificateValid leaf274Box leaf274Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk49ValidityFacts chi35ValidityFacts
    leaf274LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf274CoverageChecked :
    coverageCheck (innerAD leaf274Box) leaf274InnerLog = true := by
  rfl'

private theorem leaf274InnerLogValid :
    leaf274InnerLog.Valid 8 (innerAD leaf274Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf274CoverageChecked

private noncomputable def leaf274InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (5814651/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf274InputLogOnePlusV_eq :
    leaf274InputLogOnePlusV = outerEnclosure 24
      (leaf274Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf274RoundedFacts : LeafRoundedFacts 8
    leaf274Certificate.logOnePlusV leaf274InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf274InputLogOnePlusV_eq }

private noncomputable def leaf274Inputs : Inputs :=
  inputsOfCaches globalInput sk49RoundedInputs
    chi35InputQChi innerPair26Input
    leaf274InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf274LowerChecked :
    lowerCheck 24 leaf274Box leaf274Inputs = true := by
  rfl'

private theorem leaf274CoversExact : CoversExact 8
    leaf274Box leaf274Certificate leaf274InnerLog leaf274Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk49RoundedFacts chi35RoundedFacts
    innerPair26RoundedFacts leaf274RoundedFacts (by rfl)

private theorem leaf274FlatSound : Sound leaf274Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf274CertificateValid
    leaf274InnerLogValid leaf274CoversExact leaf274LowerChecked

private noncomputable def leaf275Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/32), kHi := (31/16), chiLo := (13/64), chiHi := (7/32) }

private noncomputable def leaf275Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217879/134217728) }, vSqrt := { lower := (16383/16384), upper := (8388616/8388391) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (186151687/134217728) }, upper := { exponent := 0, mantissa := (729/512) } }, logOuter := sk50LogOuterCertificate, logK := sk50LogKCertificate, logChi := chi35LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (16777007/16776782) } }, logDArg := sk50LogDArgCertificate }

private noncomputable def leaf275InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf275LocalValidity :
    LeafFacts leaf275Box leaf275Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf275Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (8388616/8388391) }) = true
      norm_num [leaf275Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf275CertificateValid :
    WideCertificateValid leaf275Box leaf275Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk50ValidityFacts chi35ValidityFacts
    leaf275LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf275CoverageChecked :
    coverageCheck (innerAD leaf275Box) leaf275InnerLog = true := by
  rfl'

private theorem leaf275InnerLogValid :
    leaf275InnerLog.Valid 8 (innerAD leaf275Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf275CoverageChecked

private noncomputable def leaf275InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (5814653/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf275InputLogOnePlusV_eq :
    leaf275InputLogOnePlusV = outerEnclosure 24
      (leaf275Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf275RoundedFacts : LeafRoundedFacts 8
    leaf275Certificate.logOnePlusV leaf275InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf275InputLogOnePlusV_eq }

private noncomputable def leaf275Inputs : Inputs :=
  inputsOfCaches globalInput sk50RoundedInputs
    chi35InputQChi innerPair26Input
    leaf275InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf275LowerChecked :
    lowerCheck 24 leaf275Box leaf275Inputs = true := by
  rfl'

private theorem leaf275CoversExact : CoversExact 8
    leaf275Box leaf275Certificate leaf275InnerLog leaf275Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk50RoundedFacts chi35RoundedFacts
    innerPair26RoundedFacts leaf275RoundedFacts (by rfl)

private theorem leaf275FlatSound : Sound leaf275Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf275CertificateValid
    leaf275InnerLogValid leaf275CoversExact leaf275LowerChecked

private noncomputable def leaf276Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (63/32), chiLo := (3/16), chiHi := (13/64) }

private noncomputable def leaf276Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217879/134217728) }, vSqrt := { lower := (16383/16384), upper := (33554464/33553613) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (182940619/134217728) }, upper := { exponent := 0, mantissa := (2867/2048) } }, logOuter := sk47LogOuterCertificate, logK := sk47LogKCertificate, logChi := chi34LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (67108077/67107226) } }, logDArg := sk47LogDArgCertificate }

private noncomputable def leaf276InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf276LocalValidity :
    LeafFacts leaf276Box leaf276Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf276Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (33554464/33553613) }) = true
      norm_num [leaf276Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf276CertificateValid :
    WideCertificateValid leaf276Box leaf276Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk47ValidityFacts chi34ValidityFacts
    leaf276LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf276CoverageChecked :
    coverageCheck (innerAD leaf276Box) leaf276InnerLog = true := by
  rfl'

private theorem leaf276InnerLogValid :
    leaf276InnerLog.Valid 8 (innerAD leaf276Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf276CoverageChecked

private noncomputable def leaf276InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629293/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf276InputLogOnePlusV_eq :
    leaf276InputLogOnePlusV = outerEnclosure 24
      (leaf276Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf276RoundedFacts : LeafRoundedFacts 8
    leaf276Certificate.logOnePlusV leaf276InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf276InputLogOnePlusV_eq }

private noncomputable def leaf276Inputs : Inputs :=
  inputsOfCaches globalInput sk47RoundedInputs
    chi34InputQChi innerPair22Input
    leaf276InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf276LowerChecked :
    lowerCheck 24 leaf276Box leaf276Inputs = true := by
  rfl'

private theorem leaf276CoversExact : CoversExact 8
    leaf276Box leaf276Certificate leaf276InnerLog leaf276Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk47RoundedFacts chi34RoundedFacts
    innerPair22RoundedFacts leaf276RoundedFacts (by rfl)

private theorem leaf276FlatSound : Sound leaf276Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf276CertificateValid
    leaf276InnerLogValid leaf276CoversExact leaf276LowerChecked

private noncomputable def leaf277Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/32), kHi := (2), chiLo := (3/16), chiHi := (13/64) }

private noncomputable def leaf277Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217881/134217728) }, vSqrt := { lower := (65531/65536), upper := (1048577/1048550) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (183727001/134217728) }, upper := { exponent := 0, mantissa := (45/32) } }, logOuter := sk48LogOuterCertificate, logK := sk48LogKCertificate, logChi := chi34LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (2097127/2097100) } }, logDArg := sk48LogDArgCertificate }

private noncomputable def leaf277InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf277LocalValidity :
    LeafFacts leaf277Box leaf277Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf277Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (1048577/1048550) }) = true
      norm_num [leaf277Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf277CertificateValid :
    WideCertificateValid leaf277Box leaf277Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk48ValidityFacts chi34ValidityFacts
    leaf277LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf277CoverageChecked :
    coverageCheck (innerAD leaf277Box) leaf277InnerLog = true := by
  rfl'

private theorem leaf277InnerLogValid :
    leaf277InnerLog.Valid 8 (innerAD leaf277Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf277CoverageChecked

private noncomputable def leaf277InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629297/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf277InputLogOnePlusV_eq :
    leaf277InputLogOnePlusV = outerEnclosure 24
      (leaf277Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf277RoundedFacts : LeafRoundedFacts 8
    leaf277Certificate.logOnePlusV leaf277InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf277InputLogOnePlusV_eq }

private noncomputable def leaf277Inputs : Inputs :=
  inputsOfCaches globalInput sk48RoundedInputs
    chi34InputQChi innerPair22Input
    leaf277InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf277LowerChecked :
    lowerCheck 24 leaf277Box leaf277Inputs = true := by
  rfl'

private theorem leaf277CoversExact : CoversExact 8
    leaf277Box leaf277Certificate leaf277InnerLog leaf277Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk48RoundedFacts chi34RoundedFacts
    innerPair22RoundedFacts leaf277RoundedFacts (by rfl)

private theorem leaf277FlatSound : Sound leaf277Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf277CertificateValid
    leaf277InnerLogValid leaf277CoversExact leaf277LowerChecked

private noncomputable def leaf278Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (63/32), chiLo := (13/64), chiHi := (7/32) }

private noncomputable def leaf278Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217881/134217728) }, vSqrt := { lower := (16383/16384), upper := (16777232/16776775) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (187003601/134217728) }, upper := { exponent := 0, mantissa := (1465/1024) } }, logOuter := sk47LogOuterCertificate, logK := sk47LogKCertificate, logChi := chi35LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (33554007/33553550) } }, logDArg := sk47LogDArgCertificate }

private noncomputable def leaf278InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf278LocalValidity :
    LeafFacts leaf278Box leaf278Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf278Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (16777232/16776775) }) = true
      norm_num [leaf278Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf278CertificateValid :
    WideCertificateValid leaf278Box leaf278Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk47ValidityFacts chi35ValidityFacts
    leaf278LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf278CoverageChecked :
    coverageCheck (innerAD leaf278Box) leaf278InnerLog = true := by
  rfl'

private theorem leaf278InnerLogValid :
    leaf278InnerLog.Valid 8 (innerAD leaf278Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf278CoverageChecked

private noncomputable def leaf278InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629309/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf278InputLogOnePlusV_eq :
    leaf278InputLogOnePlusV = outerEnclosure 24
      (leaf278Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf278RoundedFacts : LeafRoundedFacts 8
    leaf278Certificate.logOnePlusV leaf278InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf278InputLogOnePlusV_eq }

private noncomputable def leaf278Inputs : Inputs :=
  inputsOfCaches globalInput sk47RoundedInputs
    chi35InputQChi innerPair26Input
    leaf278InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf278LowerChecked :
    lowerCheck 24 leaf278Box leaf278Inputs = true := by
  rfl'

private theorem leaf278CoversExact : CoversExact 8
    leaf278Box leaf278Certificate leaf278InnerLog leaf278Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk47RoundedFacts chi35RoundedFacts
    innerPair26RoundedFacts leaf278RoundedFacts (by rfl)

private theorem leaf278FlatSound : Sound leaf278Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf278CertificateValid
    leaf278InnerLogValid leaf278CoversExact leaf278LowerChecked

private noncomputable def leaf279Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/32), kHi := (2), chiLo := (13/64), chiHi := (7/32) }

private noncomputable def leaf279Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217883/134217728) }, vSqrt := { lower := (65531/65536), upper := (1048577/1048548) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (187855515/134217728) }, upper := { exponent := 0, mantissa := (23/16) } }, logOuter := sk48LogOuterCertificate, logK := sk48LogKCertificate, logChi := chi35LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (2097125/2097096) } }, logDArg := sk48LogDArgCertificate }

private noncomputable def leaf279InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf279LocalValidity :
    LeafFacts leaf279Box leaf279Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf279Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (1048577/1048548) }) = true
      norm_num [leaf279Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf279CertificateValid :
    WideCertificateValid leaf279Box leaf279Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk48ValidityFacts chi35ValidityFacts
    leaf279LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf279CoverageChecked :
    coverageCheck (innerAD leaf279Box) leaf279InnerLog = true := by
  rfl'

private theorem leaf279InnerLogValid :
    leaf279InnerLog.Valid 8 (innerAD leaf279Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf279CoverageChecked

private noncomputable def leaf279InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629313/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf279InputLogOnePlusV_eq :
    leaf279InputLogOnePlusV = outerEnclosure 24
      (leaf279Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf279RoundedFacts : LeafRoundedFacts 8
    leaf279Certificate.logOnePlusV leaf279InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf279InputLogOnePlusV_eq }

private noncomputable def leaf279Inputs : Inputs :=
  inputsOfCaches globalInput sk48RoundedInputs
    chi35InputQChi innerPair26Input
    leaf279InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf279LowerChecked :
    lowerCheck 24 leaf279Box leaf279Inputs = true := by
  rfl'

private theorem leaf279CoversExact : CoversExact 8
    leaf279Box leaf279Certificate leaf279InnerLog leaf279Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk48RoundedFacts chi35RoundedFacts
    innerPair26RoundedFacts leaf279RoundedFacts (by rfl)

private theorem leaf279FlatSound : Sound leaf279Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf279CertificateValid
    leaf279InnerLogValid leaf279CoversExact leaf279LowerChecked

private noncomputable def leaf280Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (61/32), chiLo := (7/32), chiHi := (15/64) }

private noncomputable def leaf280Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217879/134217728) }, vSqrt := { lower := (16383/16384), upper := (33554464/33553517) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (189231691/134217728) }, upper := { exponent := 0, mantissa := (2963/2048) } }, logOuter := sk49LogOuterCertificate, logK := sk49LogKCertificate, logChi := chi44LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (67107981/67107034) } }, logDArg := sk49LogDArgCertificate }

private noncomputable def leaf280InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf280LocalValidity :
    LeafFacts leaf280Box leaf280Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf280Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (33554464/33553517) }) = true
      norm_num [leaf280Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf280CertificateValid :
    WideCertificateValid leaf280Box leaf280Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk49ValidityFacts chi44ValidityFacts
    leaf280LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf280CoverageChecked :
    coverageCheck (innerAD leaf280Box) leaf280InnerLog = true := by
  rfl'

private theorem leaf280InnerLogValid :
    leaf280InnerLog.Valid 8 (innerAD leaf280Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf280CoverageChecked

private noncomputable def leaf280InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629317/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf280InputLogOnePlusV_eq :
    leaf280InputLogOnePlusV = outerEnclosure 24
      (leaf280Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf280RoundedFacts : LeafRoundedFacts 8
    leaf280Certificate.logOnePlusV leaf280InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf280InputLogOnePlusV_eq }

private noncomputable def leaf280Inputs : Inputs :=
  inputsOfCaches globalInput sk49RoundedInputs
    chi44InputQChi innerPair27Input
    leaf280InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf280LowerChecked :
    lowerCheck 24 leaf280Box leaf280Inputs = true := by
  rfl'

private theorem leaf280CoversExact : CoversExact 8
    leaf280Box leaf280Certificate leaf280InnerLog leaf280Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk49RoundedFacts chi44RoundedFacts
    innerPair27RoundedFacts leaf280RoundedFacts (by rfl)

private theorem leaf280FlatSound : Sound leaf280Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf280CertificateValid
    leaf280InnerLogValid leaf280CoversExact leaf280LowerChecked

private noncomputable def leaf281Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/32), kHi := (31/16), chiLo := (7/32), chiHi := (15/64) }

private noncomputable def leaf281Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217881/134217728) }, vSqrt := { lower := (16383/16384), upper := (16777232/16776751) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (190149137/134217728) }, upper := { exponent := 0, mantissa := (1489/1024) } }, logOuter := sk50LogOuterCertificate, logK := sk50LogKCertificate, logChi := chi44LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (33553983/33553502) } }, logDArg := sk50LogDArgCertificate }

private noncomputable def leaf281InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf281LocalValidity :
    LeafFacts leaf281Box leaf281Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf281Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (16777232/16776751) }) = true
      norm_num [leaf281Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf281CertificateValid :
    WideCertificateValid leaf281Box leaf281Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk50ValidityFacts chi44ValidityFacts
    leaf281LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf281CoverageChecked :
    coverageCheck (innerAD leaf281Box) leaf281InnerLog = true := by
  rfl'

private theorem leaf281InnerLogValid :
    leaf281InnerLog.Valid 8 (innerAD leaf281Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf281CoverageChecked

private noncomputable def leaf281InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629321/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf281InputLogOnePlusV_eq :
    leaf281InputLogOnePlusV = outerEnclosure 24
      (leaf281Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf281RoundedFacts : LeafRoundedFacts 8
    leaf281Certificate.logOnePlusV leaf281InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf281InputLogOnePlusV_eq }

private noncomputable def leaf281Inputs : Inputs :=
  inputsOfCaches globalInput sk50RoundedInputs
    chi44InputQChi innerPair27Input
    leaf281InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf281LowerChecked :
    lowerCheck 24 leaf281Box leaf281Inputs = true := by
  rfl'

private theorem leaf281CoversExact : CoversExact 8
    leaf281Box leaf281Certificate leaf281InnerLog leaf281Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk50RoundedFacts chi44RoundedFacts
    innerPair27RoundedFacts leaf281RoundedFacts (by rfl)

private theorem leaf281FlatSound : Sound leaf281Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf281CertificateValid
    leaf281InnerLogValid leaf281CoversExact leaf281LowerChecked

private noncomputable def leaf282Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (61/32), chiLo := (15/64), chiHi := (1/4) }

private noncomputable def leaf282Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217881/134217728) }, vSqrt := { lower := (16383/16384), upper := (2097154/2097091) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (193163609/134217728) }, upper := { exponent := 0, mantissa := (189/128) } }, logOuter := sk49LogOuterCertificate, logK := sk49LogKCertificate, logChi := chi45LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (4194245/4194182) } }, logDArg := sk49LogDArgCertificate }

private noncomputable def leaf282InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf282LocalValidity :
    LeafFacts leaf282Box leaf282Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf282Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (2097154/2097091) }) = true
      norm_num [leaf282Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf282CertificateValid :
    WideCertificateValid leaf282Box leaf282Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk49ValidityFacts chi45ValidityFacts
    leaf282LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf282CoverageChecked :
    coverageCheck (innerAD leaf282Box) leaf282InnerLog = true := by
  rfl'

private theorem leaf282InnerLogValid :
    leaf282InnerLog.Valid 8 (innerAD leaf282Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf282CoverageChecked

private noncomputable def leaf282InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629333/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf282InputLogOnePlusV_eq :
    leaf282InputLogOnePlusV = outerEnclosure 24
      (leaf282Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf282RoundedFacts : LeafRoundedFacts 8
    leaf282Certificate.logOnePlusV leaf282InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf282InputLogOnePlusV_eq }

private noncomputable def leaf282Inputs : Inputs :=
  inputsOfCaches globalInput sk49RoundedInputs
    chi45InputQChi innerPair34Input
    leaf282InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf282LowerChecked :
    lowerCheck 24 leaf282Box leaf282Inputs = true := by
  rfl'

private theorem leaf282CoversExact : CoversExact 8
    leaf282Box leaf282Certificate leaf282InnerLog leaf282Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk49RoundedFacts chi45RoundedFacts
    innerPair34RoundedFacts leaf282RoundedFacts (by rfl)

private theorem leaf282FlatSound : Sound leaf282Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf282CertificateValid
    leaf282InnerLogValid leaf282CoversExact leaf282LowerChecked

private noncomputable def leaf283Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/32), kHi := (31/16), chiLo := (15/64), chiHi := (1/4) }

private noncomputable def leaf283Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217883/134217728) }, vSqrt := { lower := (16383/16384), upper := (4581232913/4581163008) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (194146587/134217728) }, upper := { exponent := 0, mantissa := (95/64) } }, logOuter := sk50LogOuterCertificate, logK := sk50LogKCertificate, logChi := chi45LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (9162395921/9162326016) } }, logDArg := sk50LogDArgCertificate }

private noncomputable def leaf283InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf283LocalValidity :
    LeafFacts leaf283Box leaf283Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf283Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (4581232913/4581163008) }) = true
      norm_num [leaf283Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf283CertificateValid :
    WideCertificateValid leaf283Box leaf283Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk50ValidityFacts chi45ValidityFacts
    leaf283LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf283CoverageChecked :
    coverageCheck (innerAD leaf283Box) leaf283InnerLog = true := by
  rfl'

private theorem leaf283InnerLogValid :
    leaf283InnerLog.Valid 8 (innerAD leaf283Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf283CoverageChecked

private noncomputable def leaf283InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629209/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf283InputLogOnePlusV_eq :
    leaf283InputLogOnePlusV = outerEnclosure 24
      (leaf283Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf283RoundedFacts : LeafRoundedFacts 8
    leaf283Certificate.logOnePlusV leaf283InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf283InputLogOnePlusV_eq }

private noncomputable def leaf283Inputs : Inputs :=
  inputsOfCaches globalInput sk50RoundedInputs
    chi45InputQChi innerPair34Input
    leaf283InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf283LowerChecked :
    lowerCheck 24 leaf283Box leaf283Inputs = true := by
  rfl'

private theorem leaf283CoversExact : CoversExact 8
    leaf283Box leaf283Certificate leaf283InnerLog leaf283Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk50RoundedFacts chi45RoundedFacts
    innerPair34RoundedFacts leaf283RoundedFacts (by rfl)

private theorem leaf283FlatSound : Sound leaf283Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf283CertificateValid
    leaf283InnerLogValid leaf283CoversExact leaf283LowerChecked

private noncomputable def leaf284Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (63/32), chiLo := (7/32), chiHi := (15/64) }

private noncomputable def leaf284Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217883/134217728) }, vSqrt := { lower := (16383/16384), upper := (33554464/33553487) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (191066583/134217728) }, upper := { exponent := 0, mantissa := (2993/2048) } }, logOuter := sk47LogOuterCertificate, logK := sk47LogKCertificate, logChi := chi44LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (67107951/67106974) } }, logDArg := sk47LogDArgCertificate }

private noncomputable def leaf284InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf284LocalValidity :
    LeafFacts leaf284Box leaf284Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf284Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (33554464/33553487) }) = true
      norm_num [leaf284Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf284CertificateValid :
    WideCertificateValid leaf284Box leaf284Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk47ValidityFacts chi44ValidityFacts
    leaf284LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf284CoverageChecked :
    coverageCheck (innerAD leaf284Box) leaf284InnerLog = true := by
  rfl'

private theorem leaf284InnerLogValid :
    leaf284InnerLog.Valid 8 (innerAD leaf284Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf284CoverageChecked

private noncomputable def leaf284InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629325/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf284InputLogOnePlusV_eq :
    leaf284InputLogOnePlusV = outerEnclosure 24
      (leaf284Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf284RoundedFacts : LeafRoundedFacts 8
    leaf284Certificate.logOnePlusV leaf284InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf284InputLogOnePlusV_eq }

private noncomputable def leaf284Inputs : Inputs :=
  inputsOfCaches globalInput sk47RoundedInputs
    chi44InputQChi innerPair27Input
    leaf284InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf284LowerChecked :
    lowerCheck 24 leaf284Box leaf284Inputs = true := by
  rfl'

private theorem leaf284CoversExact : CoversExact 8
    leaf284Box leaf284Certificate leaf284InnerLog leaf284Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk47RoundedFacts chi44RoundedFacts
    innerPair27RoundedFacts leaf284RoundedFacts (by rfl)

private theorem leaf284FlatSound : Sound leaf284Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf284CertificateValid
    leaf284InnerLogValid leaf284CoversExact leaf284LowerChecked

private noncomputable def leaf285Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/32), kHi := (2), chiLo := (7/32), chiHi := (15/64) }

private noncomputable def leaf285Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217885/134217728) }, vSqrt := { lower := (65531/65536), upper := (1048577/1048546) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (191984029/134217728) }, upper := { exponent := 0, mantissa := (47/32) } }, logOuter := sk48LogOuterCertificate, logK := sk48LogKCertificate, logChi := chi44LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (2097123/2097092) } }, logDArg := sk48LogDArgCertificate }

private noncomputable def leaf285InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf285LocalValidity :
    LeafFacts leaf285Box leaf285Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf285Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (1048577/1048546) }) = true
      norm_num [leaf285Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf285CertificateValid :
    WideCertificateValid leaf285Box leaf285Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk48ValidityFacts chi44ValidityFacts
    leaf285LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf285CoverageChecked :
    coverageCheck (innerAD leaf285Box) leaf285InnerLog = true := by
  rfl'

private theorem leaf285InnerLogValid :
    leaf285InnerLog.Valid 8 (innerAD leaf285Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf285CoverageChecked

private noncomputable def leaf285InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629329/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf285InputLogOnePlusV_eq :
    leaf285InputLogOnePlusV = outerEnclosure 24
      (leaf285Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf285RoundedFacts : LeafRoundedFacts 8
    leaf285Certificate.logOnePlusV leaf285InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf285InputLogOnePlusV_eq }

private noncomputable def leaf285Inputs : Inputs :=
  inputsOfCaches globalInput sk48RoundedInputs
    chi44InputQChi innerPair27Input
    leaf285InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf285LowerChecked :
    lowerCheck 24 leaf285Box leaf285Inputs = true := by
  rfl'

private theorem leaf285CoversExact : CoversExact 8
    leaf285Box leaf285Certificate leaf285InnerLog leaf285Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk48RoundedFacts chi44RoundedFacts
    innerPair27RoundedFacts leaf285RoundedFacts (by rfl)

private theorem leaf285FlatSound : Sound leaf285Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf285CertificateValid
    leaf285InnerLogValid leaf285CoversExact leaf285LowerChecked

private noncomputable def leaf286Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (63/32), chiLo := (15/64), chiHi := (1/4) }

private noncomputable def leaf286Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217885/134217728) }, vSqrt := { lower := (16383/16384), upper := (68718493695/68717412352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (195129565/134217728) }, upper := { exponent := 0, mantissa := (191/128) } }, logOuter := sk47LogOuterCertificate, logK := sk47LogKCertificate, logChi := chi45LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (137435906047/137434824704) } }, logDArg := sk47LogDArgCertificate }

private noncomputable def leaf286InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf286LocalValidity :
    LeafFacts leaf286Box leaf286Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf286Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (68718493695/68717412352) }) = true
      norm_num [leaf286Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf286CertificateValid :
    WideCertificateValid leaf286Box leaf286Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk47ValidityFacts chi45ValidityFacts
    leaf286LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf286CoverageChecked :
    coverageCheck (innerAD leaf286Box) leaf286InnerLog = true := by
  rfl'

private theorem leaf286InnerLogValid :
    leaf286InnerLog.Valid 8 (innerAD leaf286Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf286CoverageChecked

private noncomputable def leaf286InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629213/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf286InputLogOnePlusV_eq :
    leaf286InputLogOnePlusV = outerEnclosure 24
      (leaf286Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf286RoundedFacts : LeafRoundedFacts 8
    leaf286Certificate.logOnePlusV leaf286InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf286InputLogOnePlusV_eq }

private noncomputable def leaf286Inputs : Inputs :=
  inputsOfCaches globalInput sk47RoundedInputs
    chi45InputQChi innerPair34Input
    leaf286InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf286LowerChecked :
    lowerCheck 24 leaf286Box leaf286Inputs = true := by
  rfl'

private theorem leaf286CoversExact : CoversExact 8
    leaf286Box leaf286Certificate leaf286InnerLog leaf286Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk47RoundedFacts chi45RoundedFacts
    innerPair34RoundedFacts leaf286RoundedFacts (by rfl)

private theorem leaf286FlatSound : Sound leaf286Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf286CertificateValid
    leaf286InnerLogValid leaf286CoversExact leaf286LowerChecked

private noncomputable def leaf287Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/32), kHi := (2), chiLo := (15/64), chiHi := (1/4) }

private noncomputable def leaf287Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217887/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68717379584) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (196112543/134217728) }, upper := { exponent := 0, mantissa := (3/2) } }, logOuter := sk48LogOuterCertificate, logK := sk48LogKCertificate, logChi := chi45LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435873279/137434759168) } }, logDArg := sk48LogDArgCertificate }

private noncomputable def leaf287InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf287LocalValidity :
    LeafFacts leaf287Box leaf287Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf287Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68717379584) }) = true
      norm_num [leaf287Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf287CertificateValid :
    WideCertificateValid leaf287Box leaf287Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk48ValidityFacts chi45ValidityFacts
    leaf287LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf287CoverageChecked :
    coverageCheck (innerAD leaf287Box) leaf287InnerLog = true := by
  rfl'

private theorem leaf287InnerLogValid :
    leaf287InnerLog.Valid 8 (innerAD leaf287Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf287CoverageChecked

private noncomputable def leaf287InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629217/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf287InputLogOnePlusV_eq :
    leaf287InputLogOnePlusV = outerEnclosure 24
      (leaf287Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf287RoundedFacts : LeafRoundedFacts 8
    leaf287Certificate.logOnePlusV leaf287InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf287InputLogOnePlusV_eq }

private noncomputable def leaf287Inputs : Inputs :=
  inputsOfCaches globalInput sk48RoundedInputs
    chi45InputQChi innerPair34Input
    leaf287InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf287LowerChecked :
    lowerCheck 24 leaf287Box leaf287Inputs = true := by
  rfl'

private theorem leaf287CoversExact : CoversExact 8
    leaf287Box leaf287Certificate leaf287InnerLog leaf287Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk48RoundedFacts chi45RoundedFacts
    innerPair34RoundedFacts leaf287RoundedFacts (by rfl)

private theorem leaf287FlatSound : Sound leaf287Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf287CertificateValid
    leaf287InnerLogValid leaf287CoversExact leaf287LowerChecked

private noncomputable def component6Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (29/16), chiLo := (1/8), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component6Node0_sound : Sound component6Node0Box :=
  sound_of_literal_split component6Node0Box leaf240Box leaf241Box
    .chi (9/64) (by rfl) (by rfl)
    leaf240FlatSound leaf241FlatSound

private noncomputable def component6Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (15/8), chiLo := (1/8), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component6Node1_sound : Sound component6Node1Box :=
  sound_of_literal_split component6Node1Box leaf242Box leaf243Box
    .chi (9/64) (by rfl) (by rfl)
    leaf242FlatSound leaf243FlatSound

private noncomputable def component6Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (15/8), chiLo := (1/8), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component6Node2_sound : Sound component6Node2Box :=
  sound_of_literal_split component6Node2Box component6Node0Box component6Node1Box
    .k (29/16) (by rfl) (by rfl)
    component6Node0_sound component6Node1_sound

private noncomputable def component6Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (29/16), chiLo := (5/32), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component6Node3_sound : Sound component6Node3Box :=
  sound_of_literal_split component6Node3Box leaf244Box leaf245Box
    .chi (11/64) (by rfl) (by rfl)
    leaf244FlatSound leaf245FlatSound

private noncomputable def component6Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (15/8), chiLo := (5/32), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component6Node4_sound : Sound component6Node4Box :=
  sound_of_literal_split component6Node4Box leaf246Box leaf247Box
    .chi (11/64) (by rfl) (by rfl)
    leaf246FlatSound leaf247FlatSound

private noncomputable def component6Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (15/8), chiLo := (5/32), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component6Node5_sound : Sound component6Node5Box :=
  sound_of_literal_split component6Node5Box component6Node3Box component6Node4Box
    .k (29/16) (by rfl) (by rfl)
    component6Node3_sound component6Node4_sound

private noncomputable def component6Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (15/8), chiLo := (1/8), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component6Node6_sound : Sound component6Node6Box :=
  sound_of_literal_split component6Node6Box component6Node2Box component6Node5Box
    .chi (5/32) (by rfl) (by rfl)
    component6Node2_sound component6Node5_sound

private noncomputable def component6Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (31/16), chiLo := (1/8), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component6Node7_sound : Sound component6Node7Box :=
  sound_of_literal_split component6Node7Box leaf248Box leaf249Box
    .chi (9/64) (by rfl) (by rfl)
    leaf248FlatSound leaf249FlatSound

private noncomputable def component6Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2), chiLo := (9/64), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component6Node8_sound : Sound component6Node8Box :=
  sound_of_literal_split component6Node8Box leaf251Box leaf252Box
    .k (63/32) (by rfl) (by rfl)
    leaf251FlatSound leaf252FlatSound

private noncomputable def component6Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2), chiLo := (1/8), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component6Node9_sound : Sound component6Node9Box :=
  sound_of_literal_split component6Node9Box leaf250Box component6Node8Box
    .chi (9/64) (by rfl) (by rfl)
    leaf250FlatSound component6Node8_sound

private noncomputable def component6Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (2), chiLo := (1/8), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component6Node10_sound : Sound component6Node10Box :=
  sound_of_literal_split component6Node10Box component6Node7Box component6Node9Box
    .k (31/16) (by rfl) (by rfl)
    component6Node7_sound component6Node9_sound

private noncomputable def component6Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (31/16), chiLo := (11/64), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component6Node11_sound : Sound component6Node11Box :=
  sound_of_literal_split component6Node11Box leaf254Box leaf255Box
    .k (61/32) (by rfl) (by rfl)
    leaf254FlatSound leaf255FlatSound

private noncomputable def component6Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (31/16), chiLo := (5/32), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component6Node12_sound : Sound component6Node12Box :=
  sound_of_literal_split component6Node12Box leaf253Box component6Node11Box
    .chi (11/64) (by rfl) (by rfl)
    leaf253FlatSound component6Node11_sound

private noncomputable def component6Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2), chiLo := (5/32), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component6Node13_sound : Sound component6Node13Box :=
  sound_of_literal_split component6Node13Box leaf256Box leaf257Box
    .k (63/32) (by rfl) (by rfl)
    leaf256FlatSound leaf257FlatSound

private noncomputable def component6Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2), chiLo := (11/64), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component6Node14_sound : Sound component6Node14Box :=
  sound_of_literal_split component6Node14Box leaf258Box leaf259Box
    .k (63/32) (by rfl) (by rfl)
    leaf258FlatSound leaf259FlatSound

private noncomputable def component6Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2), chiLo := (5/32), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component6Node15_sound : Sound component6Node15Box :=
  sound_of_literal_split component6Node15Box component6Node13Box component6Node14Box
    .chi (11/64) (by rfl) (by rfl)
    component6Node13_sound component6Node14_sound

private noncomputable def component6Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (2), chiLo := (5/32), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component6Node16_sound : Sound component6Node16Box :=
  sound_of_literal_split component6Node16Box component6Node12Box component6Node15Box
    .k (31/16) (by rfl) (by rfl)
    component6Node12_sound component6Node15_sound

private noncomputable def component6Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (2), chiLo := (1/8), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component6Node17_sound : Sound component6Node17Box :=
  sound_of_literal_split component6Node17Box component6Node10Box component6Node16Box
    .chi (5/32) (by rfl) (by rfl)
    component6Node10_sound component6Node16_sound

private noncomputable def component6Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (2), chiLo := (1/8), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component6Node18_sound : Sound component6Node18Box :=
  sound_of_literal_split component6Node18Box component6Node6Box component6Node17Box
    .k (15/8) (by rfl) (by rfl)
    component6Node6_sound component6Node17_sound

private noncomputable def component6Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (29/16), chiLo := (3/16), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component6Node19_sound : Sound component6Node19Box :=
  sound_of_literal_split component6Node19Box leaf260Box leaf261Box
    .chi (13/64) (by rfl) (by rfl)
    leaf260FlatSound leaf261FlatSound

private noncomputable def component6Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (15/8), chiLo := (3/16), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component6Node20_sound : Sound component6Node20Box :=
  sound_of_literal_split component6Node20Box leaf262Box leaf263Box
    .k (59/32) (by rfl) (by rfl)
    leaf262FlatSound leaf263FlatSound

private noncomputable def component6Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (15/8), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component6Node21_sound : Sound component6Node21Box :=
  sound_of_literal_split component6Node21Box leaf264Box leaf265Box
    .k (59/32) (by rfl) (by rfl)
    leaf264FlatSound leaf265FlatSound

private noncomputable def component6Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (15/8), chiLo := (3/16), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component6Node22_sound : Sound component6Node22Box :=
  sound_of_literal_split component6Node22Box component6Node20Box component6Node21Box
    .chi (13/64) (by rfl) (by rfl)
    component6Node20_sound component6Node21_sound

private noncomputable def component6Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (15/8), chiLo := (3/16), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component6Node23_sound : Sound component6Node23Box :=
  sound_of_literal_split component6Node23Box component6Node19Box component6Node22Box
    .k (29/16) (by rfl) (by rfl)
    component6Node19_sound component6Node22_sound

private noncomputable def component6Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (29/16), chiLo := (7/32), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component6Node24_sound : Sound component6Node24Box :=
  sound_of_literal_split component6Node24Box leaf266Box leaf267Box
    .chi (15/64) (by rfl) (by rfl)
    leaf266FlatSound leaf267FlatSound

private noncomputable def component6Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (15/8), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component6Node25_sound : Sound component6Node25Box :=
  sound_of_literal_split component6Node25Box leaf268Box leaf269Box
    .k (59/32) (by rfl) (by rfl)
    leaf268FlatSound leaf269FlatSound

private noncomputable def component6Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (15/8), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component6Node26_sound : Sound component6Node26Box :=
  sound_of_literal_split component6Node26Box leaf270Box leaf271Box
    .k (59/32) (by rfl) (by rfl)
    leaf270FlatSound leaf271FlatSound

private noncomputable def component6Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (15/8), chiLo := (7/32), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component6Node27_sound : Sound component6Node27Box :=
  sound_of_literal_split component6Node27Box component6Node25Box component6Node26Box
    .chi (15/64) (by rfl) (by rfl)
    component6Node25_sound component6Node26_sound

private noncomputable def component6Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (15/8), chiLo := (7/32), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component6Node28_sound : Sound component6Node28Box :=
  sound_of_literal_split component6Node28Box component6Node24Box component6Node27Box
    .k (29/16) (by rfl) (by rfl)
    component6Node24_sound component6Node27_sound

private noncomputable def component6Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (15/8), chiLo := (3/16), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component6Node29_sound : Sound component6Node29Box :=
  sound_of_literal_split component6Node29Box component6Node23Box component6Node28Box
    .chi (7/32) (by rfl) (by rfl)
    component6Node23_sound component6Node28_sound

private noncomputable def component6Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (31/16), chiLo := (3/16), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component6Node30_sound : Sound component6Node30Box :=
  sound_of_literal_split component6Node30Box leaf272Box leaf273Box
    .k (61/32) (by rfl) (by rfl)
    leaf272FlatSound leaf273FlatSound

private noncomputable def component6Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (31/16), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component6Node31_sound : Sound component6Node31Box :=
  sound_of_literal_split component6Node31Box leaf274Box leaf275Box
    .k (61/32) (by rfl) (by rfl)
    leaf274FlatSound leaf275FlatSound

private noncomputable def component6Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (31/16), chiLo := (3/16), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component6Node32_sound : Sound component6Node32Box :=
  sound_of_literal_split component6Node32Box component6Node30Box component6Node31Box
    .chi (13/64) (by rfl) (by rfl)
    component6Node30_sound component6Node31_sound

private noncomputable def component6Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2), chiLo := (3/16), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component6Node33_sound : Sound component6Node33Box :=
  sound_of_literal_split component6Node33Box leaf276Box leaf277Box
    .k (63/32) (by rfl) (by rfl)
    leaf276FlatSound leaf277FlatSound

private noncomputable def component6Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component6Node34_sound : Sound component6Node34Box :=
  sound_of_literal_split component6Node34Box leaf278Box leaf279Box
    .k (63/32) (by rfl) (by rfl)
    leaf278FlatSound leaf279FlatSound

private noncomputable def component6Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2), chiLo := (3/16), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component6Node35_sound : Sound component6Node35Box :=
  sound_of_literal_split component6Node35Box component6Node33Box component6Node34Box
    .chi (13/64) (by rfl) (by rfl)
    component6Node33_sound component6Node34_sound

private noncomputable def component6Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (2), chiLo := (3/16), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component6Node36_sound : Sound component6Node36Box :=
  sound_of_literal_split component6Node36Box component6Node32Box component6Node35Box
    .k (31/16) (by rfl) (by rfl)
    component6Node32_sound component6Node35_sound

private noncomputable def component6Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (31/16), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component6Node37_sound : Sound component6Node37Box :=
  sound_of_literal_split component6Node37Box leaf280Box leaf281Box
    .k (61/32) (by rfl) (by rfl)
    leaf280FlatSound leaf281FlatSound

private noncomputable def component6Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (31/16), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component6Node38_sound : Sound component6Node38Box :=
  sound_of_literal_split component6Node38Box leaf282Box leaf283Box
    .k (61/32) (by rfl) (by rfl)
    leaf282FlatSound leaf283FlatSound

private noncomputable def component6Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (31/16), chiLo := (7/32), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component6Node39_sound : Sound component6Node39Box :=
  sound_of_literal_split component6Node39Box component6Node37Box component6Node38Box
    .chi (15/64) (by rfl) (by rfl)
    component6Node37_sound component6Node38_sound

private noncomputable def component6Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component6Node40_sound : Sound component6Node40Box :=
  sound_of_literal_split component6Node40Box leaf284Box leaf285Box
    .k (63/32) (by rfl) (by rfl)
    leaf284FlatSound leaf285FlatSound

private noncomputable def component6Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component6Node41_sound : Sound component6Node41Box :=
  sound_of_literal_split component6Node41Box leaf286Box leaf287Box
    .k (63/32) (by rfl) (by rfl)
    leaf286FlatSound leaf287FlatSound

private noncomputable def component6Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2), chiLo := (7/32), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component6Node42_sound : Sound component6Node42Box :=
  sound_of_literal_split component6Node42Box component6Node40Box component6Node41Box
    .chi (15/64) (by rfl) (by rfl)
    component6Node40_sound component6Node41_sound

private noncomputable def component6Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (2), chiLo := (7/32), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component6Node43_sound : Sound component6Node43Box :=
  sound_of_literal_split component6Node43Box component6Node39Box component6Node42Box
    .k (31/16) (by rfl) (by rfl)
    component6Node39_sound component6Node42_sound

private noncomputable def component6Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (2), chiLo := (3/16), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component6Node44_sound : Sound component6Node44Box :=
  sound_of_literal_split component6Node44Box component6Node36Box component6Node43Box
    .chi (7/32) (by rfl) (by rfl)
    component6Node36_sound component6Node43_sound

private noncomputable def component6Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (2), chiLo := (3/16), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component6Node45_sound : Sound component6Node45Box :=
  sound_of_literal_split component6Node45Box component6Node29Box component6Node44Box
    .k (15/8) (by rfl) (by rfl)
    component6Node29_sound component6Node44_sound

noncomputable def component6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (2), chiLo := (1/8), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
theorem component6_sound : Sound component6Box :=
  sound_of_literal_split component6Box component6Node18Box component6Node45Box
    .chi (3/16) (by rfl) (by rfl)
    component6Node18_sound component6Node45_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
