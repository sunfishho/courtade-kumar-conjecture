import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch5
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch8
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheSKBatch3

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

private noncomputable def leaf4927Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (233/64), chiLo := (9/32), chiHi := (73/256) }

private noncomputable def leaf4927Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742435/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715122432) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2168354975/2147483648) }, upper := { exponent := 1, mantissa := (33393/32768) } }, logOuter := sk217LogOuterCertificate, logK := sk217LogKCertificate, logChi := chi281LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432534783/137430244864) } }, logDArg := sk217LogDArgCertificate }

private noncomputable def leaf4927InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4927LocalValidity :
    LeafFacts leaf4927Box leaf4927Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4927Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715122432) }) = true
      norm_num [leaf4927Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4927CertificateValid :
    WideCertificateValid leaf4927Box leaf4927Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk217ValidityFacts chi281ValidityFacts
    leaf4927LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4927CoverageChecked :
    coverageCheck (innerAD leaf4927Box) leaf4927InnerLog = true := by
  rfl'

private theorem leaf4927InnerLogValid :
    leaf4927InnerLog.Valid 8 (innerAD leaf4927Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4927CoverageChecked

private noncomputable def leaf4927InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726835/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf4927InputLogOnePlusV_eq :
    leaf4927InputLogOnePlusV = outerEnclosure 24
      (leaf4927Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4927RoundedFacts : LeafRoundedFacts 8
    leaf4927Certificate.logOnePlusV leaf4927InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4927InputLogOnePlusV_eq }

private noncomputable def leaf4927Inputs : Inputs :=
  inputsOfCaches globalInput sk217RoundedInputs
    chi281InputQChi innerPair116Input
    leaf4927InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4927LowerChecked :
    lowerCheck 24 leaf4927Box leaf4927Inputs = true := by
  rfl'

private theorem leaf4927CoversExact : CoversExact 8
    leaf4927Box leaf4927Certificate leaf4927InnerLog leaf4927Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk217RoundedFacts chi281RoundedFacts
    innerPair116RoundedFacts leaf4927RoundedFacts (by rfl)

private theorem leaf4927FlatSound : Sound leaf4927Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4927CertificateValid
    leaf4927InnerLogValid leaf4927CoversExact leaf4927LowerChecked

private noncomputable def leaf4928Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (233/64), kHi := (117/32), chiLo := (9/32), chiHi := (73/256) }

private noncomputable def leaf4928Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742437/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9816773193/9816443392) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2173073277/2147483648) }, upper := { exponent := 1, mantissa := (16733/16384) } }, logOuter := sk218LogOuterCertificate, logK := sk218LogKCertificate, logChi := chi281LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (19633216585/19632886784) } }, logDArg := sk218LogDArgCertificate }

private noncomputable def leaf4928InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4928LocalValidity :
    LeafFacts leaf4928Box leaf4928Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4928Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9816773193/9816443392) }) = true
      norm_num [leaf4928Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4928CertificateValid :
    WideCertificateValid leaf4928Box leaf4928Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk218ValidityFacts chi281ValidityFacts
    leaf4928LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4928CoverageChecked :
    coverageCheck (innerAD leaf4928Box) leaf4928InnerLog = true := by
  rfl'

private theorem leaf4928InnerLogValid :
    leaf4928InnerLog.Valid 8 (innerAD leaf4928Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4928CoverageChecked

private noncomputable def leaf4928InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629363/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4928InputLogOnePlusV_eq :
    leaf4928InputLogOnePlusV = outerEnclosure 24
      (leaf4928Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4928RoundedFacts : LeafRoundedFacts 8
    leaf4928Certificate.logOnePlusV leaf4928InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4928InputLogOnePlusV_eq }

private noncomputable def leaf4928Inputs : Inputs :=
  inputsOfCaches globalInput sk218RoundedInputs
    chi281InputQChi innerPair116Input
    leaf4928InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4928LowerChecked :
    lowerCheck 24 leaf4928Box leaf4928Inputs = true := by
  rfl'

private theorem leaf4928CoversExact : CoversExact 8
    leaf4928Box leaf4928Certificate leaf4928InnerLog leaf4928Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk218RoundedFacts chi281RoundedFacts
    innerPair116RoundedFacts leaf4928RoundedFacts (by rfl)

private theorem leaf4928FlatSound : Sound leaf4928Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4928CertificateValid
    leaf4928InnerLogValid leaf4928CoversExact leaf4928LowerChecked

private noncomputable def leaf4929Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (233/64), chiLo := (73/256), chiHi := (37/128) }

private noncomputable def leaf4929Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742437/1073741824) }, vSqrt := { lower := (8191/8192), upper := (7635268039/7635006976) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2183558397/2147483648) }, upper := { exponent := 1, mantissa := (16813/16384) } }, logOuter := sk217LogOuterCertificate, logK := sk217LogKCertificate, logChi := chi282LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (15270275015/15270013952) } }, logDArg := sk217LogDArgCertificate }

private noncomputable def leaf4929InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4929LocalValidity :
    LeafFacts leaf4929Box leaf4929Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4929Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (7635268039/7635006976) }) = true
      norm_num [leaf4929Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4929CertificateValid :
    WideCertificateValid leaf4929Box leaf4929Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk217ValidityFacts chi282ValidityFacts
    leaf4929LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4929CoverageChecked :
    coverageCheck (innerAD leaf4929Box) leaf4929InnerLog = true := by
  rfl'

private theorem leaf4929InnerLogValid :
    leaf4929InnerLog.Valid 8 (innerAD leaf4929Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4929CoverageChecked

private noncomputable def leaf4929InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453671/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf4929InputLogOnePlusV_eq :
    leaf4929InputLogOnePlusV = outerEnclosure 24
      (leaf4929Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4929RoundedFacts : LeafRoundedFacts 8
    leaf4929Certificate.logOnePlusV leaf4929InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4929InputLogOnePlusV_eq }

private noncomputable def leaf4929Inputs : Inputs :=
  inputsOfCaches globalInput sk217RoundedInputs
    chi282InputQChi innerPair116Input
    leaf4929InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4929LowerChecked :
    lowerCheck 24 leaf4929Box leaf4929Inputs = true := by
  rfl'

private theorem leaf4929CoversExact : CoversExact 8
    leaf4929Box leaf4929Certificate leaf4929InnerLog leaf4929Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk217RoundedFacts chi282RoundedFacts
    innerPair116RoundedFacts leaf4929RoundedFacts (by rfl)

private theorem leaf4929FlatSound : Sound leaf4929Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4929CertificateValid
    leaf4929InnerLogValid leaf4929CoversExact leaf4929LowerChecked

private noncomputable def leaf4930Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (233/64), kHi := (117/32), chiLo := (73/256), chiHi := (37/128) }

private noncomputable def leaf4930Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742439/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715043840) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2188342231/2147483648) }, upper := { exponent := 1, mantissa := (8425/8192) } }, logOuter := sk218LogOuterCertificate, logK := sk218LogKCertificate, logChi := chi282LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432456191/137430087680) } }, logDArg := sk218LogDArgCertificate }

private noncomputable def leaf4930InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4930LocalValidity :
    LeafFacts leaf4930Box leaf4930Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4930Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715043840) }) = true
      norm_num [leaf4930Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4930CertificateValid :
    WideCertificateValid leaf4930Box leaf4930Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk218ValidityFacts chi282ValidityFacts
    leaf4930LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4930CoverageChecked :
    coverageCheck (innerAD leaf4930Box) leaf4930InnerLog = true := by
  rfl'

private theorem leaf4930InnerLogValid :
    leaf4930InnerLog.Valid 8 (innerAD leaf4930Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4930CoverageChecked

private noncomputable def leaf4930InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814685/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4930InputLogOnePlusV_eq :
    leaf4930InputLogOnePlusV = outerEnclosure 24
      (leaf4930Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4930RoundedFacts : LeafRoundedFacts 8
    leaf4930Certificate.logOnePlusV leaf4930InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4930InputLogOnePlusV_eq }

private noncomputable def leaf4930Inputs : Inputs :=
  inputsOfCaches globalInput sk218RoundedInputs
    chi282InputQChi innerPair116Input
    leaf4930InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4930LowerChecked :
    lowerCheck 24 leaf4930Box leaf4930Inputs = true := by
  rfl'

private theorem leaf4930CoversExact : CoversExact 8
    leaf4930Box leaf4930Certificate leaf4930InnerLog leaf4930Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk218RoundedFacts chi282RoundedFacts
    innerPair116RoundedFacts leaf4930RoundedFacts (by rfl)

private theorem leaf4930FlatSound : Sound leaf4930Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4930CertificateValid
    leaf4930InnerLogValid leaf4930CoversExact leaf4930LowerChecked

private noncomputable def leaf4931Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (235/64), chiLo := (9/32), chiHi := (73/256) }

private noncomputable def leaf4931Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742439/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22905804117/22905028352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2177791579/2147483648) }, upper := { exponent := 1, mantissa := (33539/32768) } }, logOuter := sk219LogOuterCertificate, logK := sk219LogKCertificate, logChi := chi281LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45810832469/45810056704) } }, logDArg := sk219LogDArgCertificate }

private noncomputable def leaf4931InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4931LocalValidity :
    LeafFacts leaf4931Box leaf4931Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4931Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22905804117/22905028352) }) = true
      norm_num [leaf4931Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4931CertificateValid :
    WideCertificateValid leaf4931Box leaf4931Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk219ValidityFacts chi281ValidityFacts
    leaf4931LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4931CoverageChecked :
    coverageCheck (innerAD leaf4931Box) leaf4931InnerLog = true := by
  rfl'

private theorem leaf4931InnerLogValid :
    leaf4931InnerLog.Valid 8 (innerAD leaf4931Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4931CoverageChecked

private noncomputable def leaf4931InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629365/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4931InputLogOnePlusV_eq :
    leaf4931InputLogOnePlusV = outerEnclosure 24
      (leaf4931Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4931RoundedFacts : LeafRoundedFacts 8
    leaf4931Certificate.logOnePlusV leaf4931InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4931InputLogOnePlusV_eq }

private noncomputable def leaf4931Inputs : Inputs :=
  inputsOfCaches globalInput sk219RoundedInputs
    chi281InputQChi innerPair116Input
    leaf4931InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4931LowerChecked :
    lowerCheck 24 leaf4931Box leaf4931Inputs = true := by
  rfl'

private theorem leaf4931CoversExact : CoversExact 8
    leaf4931Box leaf4931Certificate leaf4931InnerLog leaf4931Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk219RoundedFacts chi281RoundedFacts
    innerPair116RoundedFacts leaf4931RoundedFacts (by rfl)

private theorem leaf4931FlatSound : Sound leaf4931Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4931CertificateValid
    leaf4931InnerLogValid leaf4931CoversExact leaf4931LowerChecked

private noncomputable def leaf4932Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (235/64), kHi := (59/16), chiLo := (9/32), chiHi := (73/256) }

private noncomputable def leaf4932Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742441/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715066368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2182509881/2147483648) }, upper := { exponent := 1, mantissa := (8403/8192) } }, logOuter := sk220LogOuterCertificate, logK := sk220LogKCertificate, logChi := chi281LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432478719/137430132736) } }, logDArg := sk220LogDArgCertificate }

private noncomputable def leaf4932InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4932LocalValidity :
    LeafFacts leaf4932Box leaf4932Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4932Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715066368) }) = true
      norm_num [leaf4932Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4932CertificateValid :
    WideCertificateValid leaf4932Box leaf4932Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk220ValidityFacts chi281ValidityFacts
    leaf4932LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4932CoverageChecked :
    coverageCheck (innerAD leaf4932Box) leaf4932InnerLog = true := by
  rfl'

private theorem leaf4932InnerLogValid :
    leaf4932InnerLog.Valid 8 (innerAD leaf4932Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4932CoverageChecked

private noncomputable def leaf4932InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629367/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4932InputLogOnePlusV_eq :
    leaf4932InputLogOnePlusV = outerEnclosure 24
      (leaf4932Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4932RoundedFacts : LeafRoundedFacts 8
    leaf4932Certificate.logOnePlusV leaf4932InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4932InputLogOnePlusV_eq }

private noncomputable def leaf4932Inputs : Inputs :=
  inputsOfCaches globalInput sk220RoundedInputs
    chi281InputQChi innerPair116Input
    leaf4932InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4932LowerChecked :
    lowerCheck 24 leaf4932Box leaf4932Inputs = true := by
  rfl'

private theorem leaf4932CoversExact : CoversExact 8
    leaf4932Box leaf4932Certificate leaf4932InnerLog leaf4932Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk220RoundedFacts chi281RoundedFacts
    innerPair116RoundedFacts leaf4932RoundedFacts (by rfl)

private theorem leaf4932FlatSound : Sound leaf4932Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4932CertificateValid
    leaf4932InnerLogValid leaf4932CoversExact leaf4932LowerChecked

private noncomputable def leaf4933Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (235/64), chiLo := (73/256), chiHi := (37/128) }

private noncomputable def leaf4933Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742441/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9816773193/9816432128) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2193126065/2147483648) }, upper := { exponent := 1, mantissa := (16887/16384) } }, logOuter := sk219LogOuterCertificate, logK := sk219LogKCertificate, logChi := chi282LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (19633205321/19632864256) } }, logDArg := sk219LogDArgCertificate }

private noncomputable def leaf4933InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4933LocalValidity :
    LeafFacts leaf4933Box leaf4933Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4933Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9816773193/9816432128) }) = true
      norm_num [leaf4933Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4933CertificateValid :
    WideCertificateValid leaf4933Box leaf4933Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk219ValidityFacts chi282ValidityFacts
    leaf4933LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4933CoverageChecked :
    coverageCheck (innerAD leaf4933Box) leaf4933InnerLog = true := by
  rfl'

private theorem leaf4933InnerLogValid :
    leaf4933InnerLog.Valid 8 (innerAD leaf4933Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4933CoverageChecked

private noncomputable def leaf4933InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907343/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4933InputLogOnePlusV_eq :
    leaf4933InputLogOnePlusV = outerEnclosure 24
      (leaf4933Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4933RoundedFacts : LeafRoundedFacts 8
    leaf4933Certificate.logOnePlusV leaf4933InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4933InputLogOnePlusV_eq }

private noncomputable def leaf4933Inputs : Inputs :=
  inputsOfCaches globalInput sk219RoundedInputs
    chi282InputQChi innerPair116Input
    leaf4933InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4933LowerChecked :
    lowerCheck 24 leaf4933Box leaf4933Inputs = true := by
  rfl'

private theorem leaf4933CoversExact : CoversExact 8
    leaf4933Box leaf4933Certificate leaf4933InnerLog leaf4933Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk219RoundedFacts chi282RoundedFacts
    innerPair116RoundedFacts leaf4933RoundedFacts (by rfl)

private theorem leaf4933FlatSound : Sound leaf4933Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4933CertificateValid
    leaf4933InnerLogValid leaf4933CoversExact leaf4933LowerChecked

private noncomputable def leaf4934Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (235/64), kHi := (59/16), chiLo := (73/256), chiHi := (37/128) }

private noncomputable def leaf4934Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742443/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22905804117/22905001984) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2197909899/2147483648) }, upper := { exponent := 1, mantissa := (4231/4096) } }, logOuter := sk220LogOuterCertificate, logK := sk220LogKCertificate, logChi := chi282LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45810806101/45810003968) } }, logDArg := sk220LogDArgCertificate }

private noncomputable def leaf4934InnerLog : WideLogData :=
  innerPair327Data

set_option maxRecDepth 1000000 in
private theorem leaf4934LocalValidity :
    LeafFacts leaf4934Box leaf4934Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4934Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22905804117/22905001984) }) = true
      norm_num [leaf4934Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4934CertificateValid :
    WideCertificateValid leaf4934Box leaf4934Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk220ValidityFacts chi282ValidityFacts
    leaf4934LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4934CoverageChecked :
    coverageCheck (innerAD leaf4934Box) leaf4934InnerLog = true := by
  rfl'

private theorem leaf4934InnerLogValid :
    leaf4934InnerLog.Valid 8 (innerAD leaf4934Box) :=
  wideLogDataValid_of_cachedCheck endpoint87PositiveFacts
    endpoint86PositiveFacts.valid leaf4934CoverageChecked

private noncomputable def leaf4934InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629375/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4934InputLogOnePlusV_eq :
    leaf4934InputLogOnePlusV = outerEnclosure 24
      (leaf4934Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4934RoundedFacts : LeafRoundedFacts 8
    leaf4934Certificate.logOnePlusV leaf4934InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4934InputLogOnePlusV_eq }

private noncomputable def leaf4934Inputs : Inputs :=
  inputsOfCaches globalInput sk220RoundedInputs
    chi282InputQChi innerPair327Input
    leaf4934InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4934LowerChecked :
    lowerCheck 24 leaf4934Box leaf4934Inputs = true := by
  rfl'

private theorem leaf4934CoversExact : CoversExact 8
    leaf4934Box leaf4934Certificate leaf4934InnerLog leaf4934Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk220RoundedFacts chi282RoundedFacts
    innerPair327RoundedFacts leaf4934RoundedFacts (by rfl)

private theorem leaf4934FlatSound : Sound leaf4934Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4934CertificateValid
    leaf4934InnerLogValid leaf4934CoversExact leaf4934LowerChecked

private noncomputable def leaf4935Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (233/64), chiLo := (37/128), chiHi := (75/256) }

private noncomputable def leaf4935Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742439/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715003136) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2198761819/2147483648) }, upper := { exponent := 1, mantissa := (33859/32768) } }, logOuter := sk217LogOuterCertificate, logK := sk217LogKCertificate, logChi := chi283LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432415487/137430006272) } }, logDArg := sk217LogDArgCertificate }

private noncomputable def leaf4935InnerLog : WideLogData :=
  innerPair117Data

set_option maxRecDepth 1000000 in
private theorem leaf4935LocalValidity :
    LeafFacts leaf4935Box leaf4935Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4935Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715003136) }) = true
      norm_num [leaf4935Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4935CertificateValid :
    WideCertificateValid leaf4935Box leaf4935Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk217ValidityFacts chi283ValidityFacts
    leaf4935LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4935CoverageChecked :
    coverageCheck (innerAD leaf4935Box) leaf4935InnerLog = true := by
  rfl'

private theorem leaf4935InnerLogValid :
    leaf4935InnerLog.Valid 8 (innerAD leaf4935Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint73PositiveFacts.valid leaf4935CoverageChecked

private noncomputable def leaf4935InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629375/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4935InputLogOnePlusV_eq :
    leaf4935InputLogOnePlusV = outerEnclosure 24
      (leaf4935Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4935RoundedFacts : LeafRoundedFacts 8
    leaf4935Certificate.logOnePlusV leaf4935InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4935InputLogOnePlusV_eq }

private noncomputable def leaf4935Inputs : Inputs :=
  inputsOfCaches globalInput sk217RoundedInputs
    chi283InputQChi innerPair117Input
    leaf4935InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4935LowerChecked :
    lowerCheck 24 leaf4935Box leaf4935Inputs = true := by
  rfl'

private theorem leaf4935CoversExact : CoversExact 8
    leaf4935Box leaf4935Certificate leaf4935InnerLog leaf4935Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk217RoundedFacts chi283RoundedFacts
    innerPair117RoundedFacts leaf4935RoundedFacts (by rfl)

private theorem leaf4935FlatSound : Sound leaf4935Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4935CertificateValid
    leaf4935InnerLogValid leaf4935CoversExact leaf4935LowerChecked

private noncomputable def leaf4936Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (233/64), kHi := (117/32), chiLo := (37/128), chiHi := (75/256) }

private noncomputable def leaf4936Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742441/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714983936) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2203611185/2147483648) }, upper := { exponent := 1, mantissa := (16967/16384) } }, logOuter := sk218LogOuterCertificate, logK := sk218LogKCertificate, logChi := chi283LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432396287/137429967872) } }, logDArg := sk218LogDArgCertificate }

private noncomputable def leaf4936InnerLog : WideLogData :=
  innerPair117Data

set_option maxRecDepth 1000000 in
private theorem leaf4936LocalValidity :
    LeafFacts leaf4936Box leaf4936Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4936Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714983936) }) = true
      norm_num [leaf4936Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4936CertificateValid :
    WideCertificateValid leaf4936Box leaf4936Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk218ValidityFacts chi283ValidityFacts
    leaf4936LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4936CoverageChecked :
    coverageCheck (innerAD leaf4936Box) leaf4936InnerLog = true := by
  rfl'

private theorem leaf4936InnerLogValid :
    leaf4936InnerLog.Valid 8 (innerAD leaf4936Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint73PositiveFacts.valid leaf4936CoverageChecked

private noncomputable def leaf4936InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629377/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4936InputLogOnePlusV_eq :
    leaf4936InputLogOnePlusV = outerEnclosure 24
      (leaf4936Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4936RoundedFacts : LeafRoundedFacts 8
    leaf4936Certificate.logOnePlusV leaf4936InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4936InputLogOnePlusV_eq }

private noncomputable def leaf4936Inputs : Inputs :=
  inputsOfCaches globalInput sk218RoundedInputs
    chi283InputQChi innerPair117Input
    leaf4936InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4936LowerChecked :
    lowerCheck 24 leaf4936Box leaf4936Inputs = true := by
  rfl'

private theorem leaf4936CoversExact : CoversExact 8
    leaf4936Box leaf4936Certificate leaf4936InnerLog leaf4936Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk218RoundedFacts chi283RoundedFacts
    innerPair117RoundedFacts leaf4936RoundedFacts (by rfl)

private theorem leaf4936FlatSound : Sound leaf4936Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4936CertificateValid
    leaf4936InnerLogValid leaf4936CoversExact leaf4936LowerChecked

private noncomputable def leaf4937Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (233/64), chiLo := (75/256), chiHi := (19/64) }

private noncomputable def leaf4937Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742441/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714943488) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2213965241/2147483648) }, upper := { exponent := 1, mantissa := (8523/8192) } }, logOuter := sk217LogOuterCertificate, logK := sk217LogKCertificate, logChi := chi284LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432355839/137429886976) } }, logDArg := sk217LogDArgCertificate }

private noncomputable def leaf4937InnerLog : WideLogData :=
  innerPair117Data

set_option maxRecDepth 1000000 in
private theorem leaf4937LocalValidity :
    LeafFacts leaf4937Box leaf4937Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4937Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714943488) }) = true
      norm_num [leaf4937Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4937CertificateValid :
    WideCertificateValid leaf4937Box leaf4937Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk217ValidityFacts chi284ValidityFacts
    leaf4937LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4937CoverageChecked :
    coverageCheck (innerAD leaf4937Box) leaf4937InnerLog = true := by
  rfl'

private theorem leaf4937InnerLogValid :
    leaf4937InnerLog.Valid 8 (innerAD leaf4937Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint73PositiveFacts.valid leaf4937CoverageChecked

private noncomputable def leaf4937InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814691/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4937InputLogOnePlusV_eq :
    leaf4937InputLogOnePlusV = outerEnclosure 24
      (leaf4937Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4937RoundedFacts : LeafRoundedFacts 8
    leaf4937Certificate.logOnePlusV leaf4937InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4937InputLogOnePlusV_eq }

private noncomputable def leaf4937Inputs : Inputs :=
  inputsOfCaches globalInput sk217RoundedInputs
    chi284InputQChi innerPair117Input
    leaf4937InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4937LowerChecked :
    lowerCheck 24 leaf4937Box leaf4937Inputs = true := by
  rfl'

private theorem leaf4937CoversExact : CoversExact 8
    leaf4937Box leaf4937Certificate leaf4937InnerLog leaf4937Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk217RoundedFacts chi284RoundedFacts
    innerPair117RoundedFacts leaf4937RoundedFacts (by rfl)

private theorem leaf4937FlatSound : Sound leaf4937Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4937CertificateValid
    leaf4937InnerLogValid leaf4937CoversExact leaf4937LowerChecked

private noncomputable def leaf4938Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (233/64), kHi := (117/32), chiLo := (75/256), chiHi := (19/64) }

private noncomputable def leaf4938Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742443/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714924032) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2218880139/2147483648) }, upper := { exponent := 1, mantissa := (4271/4096) } }, logOuter := sk218LogOuterCertificate, logK := sk218LogKCertificate, logChi := chi284LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432336383/137429848064) } }, logDArg := sk218LogDArgCertificate }

private noncomputable def leaf4938InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4938LocalValidity :
    LeafFacts leaf4938Box leaf4938Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4938Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714924032) }) = true
      norm_num [leaf4938Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4938CertificateValid :
    WideCertificateValid leaf4938Box leaf4938Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk218ValidityFacts chi284ValidityFacts
    leaf4938LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4938CoverageChecked :
    coverageCheck (innerAD leaf4938Box) leaf4938InnerLog = true := by
  rfl'

private theorem leaf4938InnerLogValid :
    leaf4938InnerLog.Valid 8 (innerAD leaf4938Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4938CoverageChecked

private noncomputable def leaf4938InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629385/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4938InputLogOnePlusV_eq :
    leaf4938InputLogOnePlusV = outerEnclosure 24
      (leaf4938Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4938RoundedFacts : LeafRoundedFacts 8
    leaf4938Certificate.logOnePlusV leaf4938InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4938InputLogOnePlusV_eq }

private noncomputable def leaf4938Inputs : Inputs :=
  inputsOfCaches globalInput sk218RoundedInputs
    chi284InputQChi innerPair242Input
    leaf4938InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4938LowerChecked :
    lowerCheck 24 leaf4938Box leaf4938Inputs = true := by
  rfl'

private theorem leaf4938CoversExact : CoversExact 8
    leaf4938Box leaf4938Certificate leaf4938InnerLog leaf4938Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk218RoundedFacts chi284RoundedFacts
    innerPair242RoundedFacts leaf4938RoundedFacts (by rfl)

private theorem leaf4938FlatSound : Sound leaf4938Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4938CertificateValid
    leaf4938InnerLogValid leaf4938CoversExact leaf4938LowerChecked

private noncomputable def leaf4939Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (235/64), chiLo := (37/128), chiHi := (75/256) }

private noncomputable def leaf4939Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742443/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714964736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2208460551/2147483648) }, upper := { exponent := 1, mantissa := (34009/32768) } }, logOuter := sk219LogOuterCertificate, logK := sk219LogKCertificate, logChi := chi283LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432377087/137429929472) } }, logDArg := sk219LogDArgCertificate }

private noncomputable def leaf4939InnerLog : WideLogData :=
  innerPair117Data

set_option maxRecDepth 1000000 in
private theorem leaf4939LocalValidity :
    LeafFacts leaf4939Box leaf4939Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4939Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714964736) }) = true
      norm_num [leaf4939Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4939CertificateValid :
    WideCertificateValid leaf4939Box leaf4939Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk219ValidityFacts chi283ValidityFacts
    leaf4939LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4939CoverageChecked :
    coverageCheck (innerAD leaf4939Box) leaf4939InnerLog = true := by
  rfl'

private theorem leaf4939InnerLogValid :
    leaf4939InnerLog.Valid 8 (innerAD leaf4939Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint73PositiveFacts.valid leaf4939CoverageChecked

private noncomputable def leaf4939InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907345/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4939InputLogOnePlusV_eq :
    leaf4939InputLogOnePlusV = outerEnclosure 24
      (leaf4939Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4939RoundedFacts : LeafRoundedFacts 8
    leaf4939Certificate.logOnePlusV leaf4939InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4939InputLogOnePlusV_eq }

private noncomputable def leaf4939Inputs : Inputs :=
  inputsOfCaches globalInput sk219RoundedInputs
    chi283InputQChi innerPair117Input
    leaf4939InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4939LowerChecked :
    lowerCheck 24 leaf4939Box leaf4939Inputs = true := by
  rfl'

private theorem leaf4939CoversExact : CoversExact 8
    leaf4939Box leaf4939Certificate leaf4939InnerLog leaf4939Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk219RoundedFacts chi283RoundedFacts
    innerPair117RoundedFacts leaf4939RoundedFacts (by rfl)

private theorem leaf4939FlatSound : Sound leaf4939Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4939CertificateValid
    leaf4939InnerLogValid leaf4939CoversExact leaf4939LowerChecked

private noncomputable def leaf4940Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (235/64), kHi := (59/16), chiLo := (37/128), chiHi := (75/256) }

private noncomputable def leaf4940Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742445/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714945536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2213309917/2147483648) }, upper := { exponent := 1, mantissa := (8521/8192) } }, logOuter := sk220LogOuterCertificate, logK := sk220LogKCertificate, logChi := chi283LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432357887/137429891072) } }, logDArg := sk220LogDArgCertificate }

private noncomputable def leaf4940InnerLog : WideLogData :=
  innerPair117Data

set_option maxRecDepth 1000000 in
private theorem leaf4940LocalValidity :
    LeafFacts leaf4940Box leaf4940Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4940Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714945536) }) = true
      norm_num [leaf4940Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4940CertificateValid :
    WideCertificateValid leaf4940Box leaf4940Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk220ValidityFacts chi283ValidityFacts
    leaf4940LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4940CoverageChecked :
    coverageCheck (innerAD leaf4940Box) leaf4940InnerLog = true := by
  rfl'

private theorem leaf4940InnerLogValid :
    leaf4940InnerLog.Valid 8 (innerAD leaf4940Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint73PositiveFacts.valid leaf4940CoverageChecked

private noncomputable def leaf4940InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814691/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4940InputLogOnePlusV_eq :
    leaf4940InputLogOnePlusV = outerEnclosure 24
      (leaf4940Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4940RoundedFacts : LeafRoundedFacts 8
    leaf4940Certificate.logOnePlusV leaf4940InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4940InputLogOnePlusV_eq }

private noncomputable def leaf4940Inputs : Inputs :=
  inputsOfCaches globalInput sk220RoundedInputs
    chi283InputQChi innerPair117Input
    leaf4940InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4940LowerChecked :
    lowerCheck 24 leaf4940Box leaf4940Inputs = true := by
  rfl'

private theorem leaf4940CoversExact : CoversExact 8
    leaf4940Box leaf4940Certificate leaf4940InnerLog leaf4940Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk220RoundedFacts chi283RoundedFacts
    innerPair117RoundedFacts leaf4940RoundedFacts (by rfl)

private theorem leaf4940FlatSound : Sound leaf4940Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4940CertificateValid
    leaf4940InnerLogValid leaf4940CoversExact leaf4940LowerChecked

private noncomputable def leaf4941Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (235/64), chiLo := (75/256), chiHi := (19/64) }

private noncomputable def leaf4941Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742445/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22905804117/22904968192) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2223795037/2147483648) }, upper := { exponent := 1, mantissa := (8561/8192) } }, logOuter := sk219LogOuterCertificate, logK := sk219LogKCertificate, logChi := chi284LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45810772309/45809936384) } }, logDArg := sk219LogDArgCertificate }

private noncomputable def leaf4941InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4941LocalValidity :
    LeafFacts leaf4941Box leaf4941Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4941Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22905804117/22904968192) }) = true
      norm_num [leaf4941Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4941CertificateValid :
    WideCertificateValid leaf4941Box leaf4941Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk219ValidityFacts chi284ValidityFacts
    leaf4941LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4941CoverageChecked :
    coverageCheck (innerAD leaf4941Box) leaf4941InnerLog = true := by
  rfl'

private theorem leaf4941InnerLogValid :
    leaf4941InnerLog.Valid 8 (innerAD leaf4941Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4941CoverageChecked

private noncomputable def leaf4941InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629387/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4941InputLogOnePlusV_eq :
    leaf4941InputLogOnePlusV = outerEnclosure 24
      (leaf4941Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4941RoundedFacts : LeafRoundedFacts 8
    leaf4941Certificate.logOnePlusV leaf4941InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4941InputLogOnePlusV_eq }

private noncomputable def leaf4941Inputs : Inputs :=
  inputsOfCaches globalInput sk219RoundedInputs
    chi284InputQChi innerPair242Input
    leaf4941InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4941LowerChecked :
    lowerCheck 24 leaf4941Box leaf4941Inputs = true := by
  rfl'

private theorem leaf4941CoversExact : CoversExact 8
    leaf4941Box leaf4941Certificate leaf4941InnerLog leaf4941Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk219RoundedFacts chi284RoundedFacts
    innerPair242RoundedFacts leaf4941RoundedFacts (by rfl)

private theorem leaf4941FlatSound : Sound leaf4941Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4941CertificateValid
    leaf4941InnerLogValid leaf4941CoversExact leaf4941LowerChecked

private noncomputable def leaf4942Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (235/64), kHi := (59/16), chiLo := (75/256), chiHi := (19/64) }

private noncomputable def leaf4942Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742447/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9816773193/9816412160) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2228709935/2147483648) }, upper := { exponent := 1, mantissa := (2145/2048) } }, logOuter := sk220LogOuterCertificate, logK := sk220LogKCertificate, logChi := chi284LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (19633185353/19632824320) } }, logDArg := sk220LogDArgCertificate }

private noncomputable def leaf4942InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4942LocalValidity :
    LeafFacts leaf4942Box leaf4942Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4942Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9816773193/9816412160) }) = true
      norm_num [leaf4942Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4942CertificateValid :
    WideCertificateValid leaf4942Box leaf4942Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk220ValidityFacts chi284ValidityFacts
    leaf4942LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4942CoverageChecked :
    coverageCheck (innerAD leaf4942Box) leaf4942InnerLog = true := by
  rfl'

private theorem leaf4942InnerLogValid :
    leaf4942InnerLog.Valid 8 (innerAD leaf4942Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4942CoverageChecked

private noncomputable def leaf4942InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629389/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4942InputLogOnePlusV_eq :
    leaf4942InputLogOnePlusV = outerEnclosure 24
      (leaf4942Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4942RoundedFacts : LeafRoundedFacts 8
    leaf4942Certificate.logOnePlusV leaf4942InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4942InputLogOnePlusV_eq }

private noncomputable def leaf4942Inputs : Inputs :=
  inputsOfCaches globalInput sk220RoundedInputs
    chi284InputQChi innerPair242Input
    leaf4942InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4942LowerChecked :
    lowerCheck 24 leaf4942Box leaf4942Inputs = true := by
  rfl'

private theorem leaf4942CoversExact : CoversExact 8
    leaf4942Box leaf4942Certificate leaf4942InnerLog leaf4942Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk220RoundedFacts chi284RoundedFacts
    innerPair242RoundedFacts leaf4942RoundedFacts (by rfl)

private theorem leaf4942FlatSound : Sound leaf4942Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4942CertificateValid
    leaf4942InnerLogValid leaf4942CoversExact leaf4942LowerChecked

private noncomputable def leaf4943Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (237/64), chiLo := (9/32), chiHi := (73/256) }

private noncomputable def leaf4943Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742443/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715047680) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2187228183/2147483648) }, upper := { exponent := 1, mantissa := (33685/32768) } }, logOuter := sk221LogOuterCertificate, logK := sk221LogKCertificate, logChi := chi281LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432460031/137430095360) } }, logDArg := sk221LogDArgCertificate }

private noncomputable def leaf4943InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4943LocalValidity :
    LeafFacts leaf4943Box leaf4943Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4943Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715047680) }) = true
      norm_num [leaf4943Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4943CertificateValid :
    WideCertificateValid leaf4943Box leaf4943Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk221ValidityFacts chi281ValidityFacts
    leaf4943LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4943CoverageChecked :
    coverageCheck (innerAD leaf4943Box) leaf4943InnerLog = true := by
  rfl'

private theorem leaf4943InnerLogValid :
    leaf4943InnerLog.Valid 8 (innerAD leaf4943Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4943CoverageChecked

private noncomputable def leaf4943InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629369/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4943InputLogOnePlusV_eq :
    leaf4943InputLogOnePlusV = outerEnclosure 24
      (leaf4943Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4943RoundedFacts : LeafRoundedFacts 8
    leaf4943Certificate.logOnePlusV leaf4943InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4943InputLogOnePlusV_eq }

private noncomputable def leaf4943Inputs : Inputs :=
  inputsOfCaches globalInput sk221RoundedInputs
    chi281InputQChi innerPair116Input
    leaf4943InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4943LowerChecked :
    lowerCheck 24 leaf4943Box leaf4943Inputs = true := by
  rfl'

private theorem leaf4943CoversExact : CoversExact 8
    leaf4943Box leaf4943Certificate leaf4943InnerLog leaf4943Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk221RoundedFacts chi281RoundedFacts
    innerPair116RoundedFacts leaf4943RoundedFacts (by rfl)

private theorem leaf4943FlatSound : Sound leaf4943Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4943CertificateValid
    leaf4943InnerLogValid leaf4943CoversExact leaf4943LowerChecked

private noncomputable def leaf4944Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (237/64), kHi := (119/32), chiLo := (9/32), chiHi := (73/256) }

private noncomputable def leaf4944Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742445/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22905804117/22905009664) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2191946485/2147483648) }, upper := { exponent := 1, mantissa := (16879/16384) } }, logOuter := sk222LogOuterCertificate, logK := sk222LogKCertificate, logChi := chi281LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45810813781/45810019328) } }, logDArg := sk222LogDArgCertificate }

private noncomputable def leaf4944InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4944LocalValidity :
    LeafFacts leaf4944Box leaf4944Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4944Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22905804117/22905009664) }) = true
      norm_num [leaf4944Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4944CertificateValid :
    WideCertificateValid leaf4944Box leaf4944Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk222ValidityFacts chi281ValidityFacts
    leaf4944LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4944CoverageChecked :
    coverageCheck (innerAD leaf4944Box) leaf4944InnerLog = true := by
  rfl'

private theorem leaf4944InnerLogValid :
    leaf4944InnerLog.Valid 8 (innerAD leaf4944Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4944CoverageChecked

private noncomputable def leaf4944InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907343/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4944InputLogOnePlusV_eq :
    leaf4944InputLogOnePlusV = outerEnclosure 24
      (leaf4944Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4944RoundedFacts : LeafRoundedFacts 8
    leaf4944Certificate.logOnePlusV leaf4944InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4944InputLogOnePlusV_eq }

private noncomputable def leaf4944Inputs : Inputs :=
  inputsOfCaches globalInput sk222RoundedInputs
    chi281InputQChi innerPair116Input
    leaf4944InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4944LowerChecked :
    lowerCheck 24 leaf4944Box leaf4944Inputs = true := by
  rfl'

private theorem leaf4944CoversExact : CoversExact 8
    leaf4944Box leaf4944Certificate leaf4944InnerLog leaf4944Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk222RoundedFacts chi281RoundedFacts
    innerPair116RoundedFacts leaf4944RoundedFacts (by rfl)

private theorem leaf4944FlatSound : Sound leaf4944Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4944CertificateValid
    leaf4944InnerLogValid leaf4944CoversExact leaf4944LowerChecked

private noncomputable def leaf4945Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (237/64), chiLo := (73/256), chiHi := (37/128) }

private noncomputable def leaf4945Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742445/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714987008) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2202693733/2147483648) }, upper := { exponent := 1, mantissa := (16961/16384) } }, logOuter := sk221LogOuterCertificate, logK := sk221LogKCertificate, logChi := chi282LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432399359/137429974016) } }, logDArg := sk221LogDArgCertificate }

private noncomputable def leaf4945InnerLog : WideLogData :=
  innerPair117Data

set_option maxRecDepth 1000000 in
private theorem leaf4945LocalValidity :
    LeafFacts leaf4945Box leaf4945Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4945Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714987008) }) = true
      norm_num [leaf4945Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4945CertificateValid :
    WideCertificateValid leaf4945Box leaf4945Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk221ValidityFacts chi282ValidityFacts
    leaf4945LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4945CoverageChecked :
    coverageCheck (innerAD leaf4945Box) leaf4945InnerLog = true := by
  rfl'

private theorem leaf4945InnerLogValid :
    leaf4945InnerLog.Valid 8 (innerAD leaf4945Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint73PositiveFacts.valid leaf4945CoverageChecked

private noncomputable def leaf4945InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629377/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4945InputLogOnePlusV_eq :
    leaf4945InputLogOnePlusV = outerEnclosure 24
      (leaf4945Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4945RoundedFacts : LeafRoundedFacts 8
    leaf4945Certificate.logOnePlusV leaf4945InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4945InputLogOnePlusV_eq }

private noncomputable def leaf4945Inputs : Inputs :=
  inputsOfCaches globalInput sk221RoundedInputs
    chi282InputQChi innerPair117Input
    leaf4945InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4945LowerChecked :
    lowerCheck 24 leaf4945Box leaf4945Inputs = true := by
  rfl'

private theorem leaf4945CoversExact : CoversExact 8
    leaf4945Box leaf4945Certificate leaf4945InnerLog leaf4945Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk221RoundedFacts chi282RoundedFacts
    innerPair117RoundedFacts leaf4945RoundedFacts (by rfl)

private theorem leaf4945FlatSound : Sound leaf4945Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4945CertificateValid
    leaf4945InnerLogValid leaf4945CoversExact leaf4945LowerChecked

private noncomputable def leaf4946Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (237/64), kHi := (119/32), chiLo := (73/256), chiHi := (37/128) }

private noncomputable def leaf4946Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742447/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714968064) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2207477567/2147483648) }, upper := { exponent := 1, mantissa := (8499/8192) } }, logOuter := sk222LogOuterCertificate, logK := sk222LogKCertificate, logChi := chi282LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432380415/137429936128) } }, logDArg := sk222LogDArgCertificate }

private noncomputable def leaf4946InnerLog : WideLogData :=
  innerPair117Data

set_option maxRecDepth 1000000 in
private theorem leaf4946LocalValidity :
    LeafFacts leaf4946Box leaf4946Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4946Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714968064) }) = true
      norm_num [leaf4946Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4946CertificateValid :
    WideCertificateValid leaf4946Box leaf4946Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk222ValidityFacts chi282ValidityFacts
    leaf4946LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4946CoverageChecked :
    coverageCheck (innerAD leaf4946Box) leaf4946InnerLog = true := by
  rfl'

private theorem leaf4946InnerLogValid :
    leaf4946InnerLog.Valid 8 (innerAD leaf4946Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint73PositiveFacts.valid leaf4946CoverageChecked

private noncomputable def leaf4946InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629379/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4946InputLogOnePlusV_eq :
    leaf4946InputLogOnePlusV = outerEnclosure 24
      (leaf4946Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4946RoundedFacts : LeafRoundedFacts 8
    leaf4946Certificate.logOnePlusV leaf4946InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4946InputLogOnePlusV_eq }

private noncomputable def leaf4946Inputs : Inputs :=
  inputsOfCaches globalInput sk222RoundedInputs
    chi282InputQChi innerPair117Input
    leaf4946InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4946LowerChecked :
    lowerCheck 24 leaf4946Box leaf4946Inputs = true := by
  rfl'

private theorem leaf4946CoversExact : CoversExact 8
    leaf4946Box leaf4946Certificate leaf4946InnerLog leaf4946Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk222RoundedFacts chi282RoundedFacts
    innerPair117RoundedFacts leaf4946RoundedFacts (by rfl)

private theorem leaf4946FlatSound : Sound leaf4946Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4946CertificateValid
    leaf4946InnerLogValid leaf4946CoversExact leaf4946LowerChecked

private noncomputable def leaf4947Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (239/64), chiLo := (9/32), chiHi := (73/256) }

private noncomputable def leaf4947Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742447/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715010304) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2196664787/2147483648) }, upper := { exponent := 1, mantissa := (33831/32768) } }, logOuter := sk223LogOuterCertificate, logK := sk223LogKCertificate, logChi := chi281LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432422655/137430020608) } }, logDArg := sk223LogDArgCertificate }

private noncomputable def leaf4947InnerLog : WideLogData :=
  innerPair311Data

set_option maxRecDepth 1000000 in
private theorem leaf4947LocalValidity :
    LeafFacts leaf4947Box leaf4947Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4947Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715010304) }) = true
      norm_num [leaf4947Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4947CertificateValid :
    WideCertificateValid leaf4947Box leaf4947Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk223ValidityFacts chi281ValidityFacts
    leaf4947LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4947CoverageChecked :
    coverageCheck (innerAD leaf4947Box) leaf4947InnerLog = true := by
  rfl'

private theorem leaf4947InnerLogValid :
    leaf4947InnerLog.Valid 8 (innerAD leaf4947Box) :=
  wideLogDataValid_of_cachedCheck endpoint82PositiveFacts
    endpoint86PositiveFacts.valid leaf4947CoverageChecked

private noncomputable def leaf4947InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814687/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4947InputLogOnePlusV_eq :
    leaf4947InputLogOnePlusV = outerEnclosure 24
      (leaf4947Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4947RoundedFacts : LeafRoundedFacts 8
    leaf4947Certificate.logOnePlusV leaf4947InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4947InputLogOnePlusV_eq }

private noncomputable def leaf4947Inputs : Inputs :=
  inputsOfCaches globalInput sk223RoundedInputs
    chi281InputQChi innerPair311Input
    leaf4947InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4947LowerChecked :
    lowerCheck 24 leaf4947Box leaf4947Inputs = true := by
  rfl'

private theorem leaf4947CoversExact : CoversExact 8
    leaf4947Box leaf4947Certificate leaf4947InnerLog leaf4947Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk223RoundedFacts chi281RoundedFacts
    innerPair311RoundedFacts leaf4947RoundedFacts (by rfl)

private theorem leaf4947FlatSound : Sound leaf4947Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4947CertificateValid
    leaf4947InnerLogValid leaf4947CoversExact leaf4947LowerChecked

private noncomputable def leaf4948Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (239/64), kHi := (15/4), chiLo := (9/32), chiHi := (73/256) }

private noncomputable def leaf4948Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742449/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714991616) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2201383089/2147483648) }, upper := { exponent := 1, mantissa := (2119/2048) } }, logOuter := sk224LogOuterCertificate, logK := sk224LogKCertificate, logChi := chi281LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432403967/137429983232) } }, logDArg := sk224LogDArgCertificate }

private noncomputable def leaf4948InnerLog : WideLogData :=
  innerPair327Data

set_option maxRecDepth 1000000 in
private theorem leaf4948LocalValidity :
    LeafFacts leaf4948Box leaf4948Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4948Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714991616) }) = true
      norm_num [leaf4948Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4948CertificateValid :
    WideCertificateValid leaf4948Box leaf4948Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk224ValidityFacts chi281ValidityFacts
    leaf4948LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4948CoverageChecked :
    coverageCheck (innerAD leaf4948Box) leaf4948InnerLog = true := by
  rfl'

private theorem leaf4948InnerLogValid :
    leaf4948InnerLog.Valid 8 (innerAD leaf4948Box) :=
  wideLogDataValid_of_cachedCheck endpoint87PositiveFacts
    endpoint86PositiveFacts.valid leaf4948CoverageChecked

private noncomputable def leaf4948InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (181709/262144) }

set_option maxRecDepth 1000000 in
private theorem leaf4948InputLogOnePlusV_eq :
    leaf4948InputLogOnePlusV = outerEnclosure 24
      (leaf4948Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4948RoundedFacts : LeafRoundedFacts 8
    leaf4948Certificate.logOnePlusV leaf4948InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4948InputLogOnePlusV_eq }

private noncomputable def leaf4948Inputs : Inputs :=
  inputsOfCaches globalInput sk224RoundedInputs
    chi281InputQChi innerPair327Input
    leaf4948InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4948LowerChecked :
    lowerCheck 24 leaf4948Box leaf4948Inputs = true := by
  rfl'

private theorem leaf4948CoversExact : CoversExact 8
    leaf4948Box leaf4948Certificate leaf4948InnerLog leaf4948Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk224RoundedFacts chi281RoundedFacts
    innerPair327RoundedFacts leaf4948RoundedFacts (by rfl)

private theorem leaf4948FlatSound : Sound leaf4948Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4948CertificateValid
    leaf4948InnerLogValid leaf4948CoversExact leaf4948LowerChecked

private noncomputable def leaf4949Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (239/64), chiLo := (73/256), chiHi := (37/128) }

private noncomputable def leaf4949Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742449/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22905804117/22904983040) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2212261401/2147483648) }, upper := { exponent := 1, mantissa := (17035/16384) } }, logOuter := sk223LogOuterCertificate, logK := sk223LogKCertificate, logChi := chi282LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45810787157/45809966080) } }, logDArg := sk223LogDArgCertificate }

private noncomputable def leaf4949InnerLog : WideLogData :=
  innerPair117Data

set_option maxRecDepth 1000000 in
private theorem leaf4949LocalValidity :
    LeafFacts leaf4949Box leaf4949Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4949Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22905804117/22904983040) }) = true
      norm_num [leaf4949Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4949CertificateValid :
    WideCertificateValid leaf4949Box leaf4949Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk223ValidityFacts chi282ValidityFacts
    leaf4949LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4949CoverageChecked :
    coverageCheck (innerAD leaf4949Box) leaf4949InnerLog = true := by
  rfl'

private theorem leaf4949InnerLogValid :
    leaf4949InnerLog.Valid 8 (innerAD leaf4949Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint73PositiveFacts.valid leaf4949CoverageChecked

private noncomputable def leaf4949InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629381/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4949InputLogOnePlusV_eq :
    leaf4949InputLogOnePlusV = outerEnclosure 24
      (leaf4949Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4949RoundedFacts : LeafRoundedFacts 8
    leaf4949Certificate.logOnePlusV leaf4949InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4949InputLogOnePlusV_eq }

private noncomputable def leaf4949Inputs : Inputs :=
  inputsOfCaches globalInput sk223RoundedInputs
    chi282InputQChi innerPair117Input
    leaf4949InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4949LowerChecked :
    lowerCheck 24 leaf4949Box leaf4949Inputs = true := by
  rfl'

private theorem leaf4949CoversExact : CoversExact 8
    leaf4949Box leaf4949Certificate leaf4949InnerLog leaf4949Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk223RoundedFacts chi282RoundedFacts
    innerPair117RoundedFacts leaf4949RoundedFacts (by rfl)

private theorem leaf4949FlatSound : Sound leaf4949Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4949CertificateValid
    leaf4949InnerLogValid leaf4949CoversExact leaf4949LowerChecked

private noncomputable def leaf4950Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (239/64), kHi := (15/4), chiLo := (73/256), chiHi := (37/128) }

private noncomputable def leaf4950Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742451/1073741824) }, vSqrt := { lower := (8191/8192), upper := (1598079357/1598021632) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2217045235/2147483648) }, upper := { exponent := 1, mantissa := (1067/1024) } }, logOuter := sk224LogOuterCertificate, logK := sk224LogKCertificate, logChi := chi282LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (3196100989/3196043264) } }, logDArg := sk224LogDArgCertificate }

private noncomputable def leaf4950InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4950LocalValidity :
    LeafFacts leaf4950Box leaf4950Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4950Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (1598079357/1598021632) }) = true
      norm_num [leaf4950Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4950CertificateValid :
    WideCertificateValid leaf4950Box leaf4950Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk224ValidityFacts chi282ValidityFacts
    leaf4950LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4950CoverageChecked :
    coverageCheck (innerAD leaf4950Box) leaf4950InnerLog = true := by
  rfl'

private theorem leaf4950InnerLogValid :
    leaf4950InnerLog.Valid 8 (innerAD leaf4950Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4950CoverageChecked

private noncomputable def leaf4950InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453673/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf4950InputLogOnePlusV_eq :
    leaf4950InputLogOnePlusV = outerEnclosure 24
      (leaf4950Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4950RoundedFacts : LeafRoundedFacts 8
    leaf4950Certificate.logOnePlusV leaf4950InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4950InputLogOnePlusV_eq }

private noncomputable def leaf4950Inputs : Inputs :=
  inputsOfCaches globalInput sk224RoundedInputs
    chi282InputQChi innerPair242Input
    leaf4950InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4950LowerChecked :
    lowerCheck 24 leaf4950Box leaf4950Inputs = true := by
  rfl'

private theorem leaf4950CoversExact : CoversExact 8
    leaf4950Box leaf4950Certificate leaf4950InnerLog leaf4950Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk224RoundedFacts chi282RoundedFacts
    innerPair242RoundedFacts leaf4950RoundedFacts (by rfl)

private theorem leaf4950FlatSound : Sound leaf4950Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4950CertificateValid
    leaf4950InnerLogValid leaf4950CoversExact leaf4950LowerChecked

private noncomputable def leaf4951Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (237/64), chiLo := (37/128), chiHi := (75/256) }

private noncomputable def leaf4951Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742447/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9816773193/9816418048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2218159283/2147483648) }, upper := { exponent := 1, mantissa := (34159/32768) } }, logOuter := sk221LogOuterCertificate, logK := sk221LogKCertificate, logChi := chi283LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (19633191241/19632836096) } }, logDArg := sk221LogDArgCertificate }

private noncomputable def leaf4951InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4951LocalValidity :
    LeafFacts leaf4951Box leaf4951Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4951Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9816773193/9816418048) }) = true
      norm_num [leaf4951Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4951CertificateValid :
    WideCertificateValid leaf4951Box leaf4951Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk221ValidityFacts chi283ValidityFacts
    leaf4951LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4951CoverageChecked :
    coverageCheck (innerAD leaf4951Box) leaf4951InnerLog = true := by
  rfl'

private theorem leaf4951InnerLogValid :
    leaf4951InnerLog.Valid 8 (innerAD leaf4951Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4951CoverageChecked

private noncomputable def leaf4951InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453673/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf4951InputLogOnePlusV_eq :
    leaf4951InputLogOnePlusV = outerEnclosure 24
      (leaf4951Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4951RoundedFacts : LeafRoundedFacts 8
    leaf4951Certificate.logOnePlusV leaf4951InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4951InputLogOnePlusV_eq }

private noncomputable def leaf4951Inputs : Inputs :=
  inputsOfCaches globalInput sk221RoundedInputs
    chi283InputQChi innerPair242Input
    leaf4951InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4951LowerChecked :
    lowerCheck 24 leaf4951Box leaf4951Inputs = true := by
  rfl'

private theorem leaf4951CoversExact : CoversExact 8
    leaf4951Box leaf4951Certificate leaf4951InnerLog leaf4951Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk221RoundedFacts chi283RoundedFacts
    innerPair242RoundedFacts leaf4951RoundedFacts (by rfl)

private theorem leaf4951FlatSound : Sound leaf4951Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4951CertificateValid
    leaf4951InnerLogValid leaf4951CoversExact leaf4951LowerChecked

private noncomputable def leaf4952Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (237/64), kHi := (119/32), chiLo := (37/128), chiHi := (75/256) }

private noncomputable def leaf4952Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742449/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714907136) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2223008649/2147483648) }, upper := { exponent := 1, mantissa := (17117/16384) } }, logOuter := sk222LogOuterCertificate, logK := sk222LogKCertificate, logChi := chi283LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432319487/137429814272) } }, logDArg := sk222LogDArgCertificate }

private noncomputable def leaf4952InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4952LocalValidity :
    LeafFacts leaf4952Box leaf4952Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4952Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714907136) }) = true
      norm_num [leaf4952Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4952CertificateValid :
    WideCertificateValid leaf4952Box leaf4952Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk222ValidityFacts chi283ValidityFacts
    leaf4952LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4952CoverageChecked :
    coverageCheck (innerAD leaf4952Box) leaf4952InnerLog = true := by
  rfl'

private theorem leaf4952InnerLogValid :
    leaf4952InnerLog.Valid 8 (innerAD leaf4952Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4952CoverageChecked

private noncomputable def leaf4952InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629387/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4952InputLogOnePlusV_eq :
    leaf4952InputLogOnePlusV = outerEnclosure 24
      (leaf4952Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4952RoundedFacts : LeafRoundedFacts 8
    leaf4952Certificate.logOnePlusV leaf4952InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4952InputLogOnePlusV_eq }

private noncomputable def leaf4952Inputs : Inputs :=
  inputsOfCaches globalInput sk222RoundedInputs
    chi283InputQChi innerPair242Input
    leaf4952InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4952LowerChecked :
    lowerCheck 24 leaf4952Box leaf4952Inputs = true := by
  rfl'

private theorem leaf4952CoversExact : CoversExact 8
    leaf4952Box leaf4952Certificate leaf4952InnerLog leaf4952Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk222RoundedFacts chi283RoundedFacts
    innerPair242RoundedFacts leaf4952RoundedFacts (by rfl)

private theorem leaf4952FlatSound : Sound leaf4952Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4952CertificateValid
    leaf4952InnerLogValid leaf4952CoversExact leaf4952LowerChecked

private noncomputable def leaf4953Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (237/64), chiLo := (75/256), chiHi := (19/64) }

private noncomputable def leaf4953Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742449/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714865664) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2233624833/2147483648) }, upper := { exponent := 1, mantissa := (8599/8192) } }, logOuter := sk221LogOuterCertificate, logK := sk221LogKCertificate, logChi := chi284LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432278015/137429731328) } }, logDArg := sk221LogDArgCertificate }

private noncomputable def leaf4953InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4953LocalValidity :
    LeafFacts leaf4953Box leaf4953Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4953Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714865664) }) = true
      norm_num [leaf4953Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4953CertificateValid :
    WideCertificateValid leaf4953Box leaf4953Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk221ValidityFacts chi284ValidityFacts
    leaf4953LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4953CoverageChecked :
    coverageCheck (innerAD leaf4953Box) leaf4953InnerLog = true := by
  rfl'

private theorem leaf4953InnerLogValid :
    leaf4953InnerLog.Valid 8 (innerAD leaf4953Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4953CoverageChecked

private noncomputable def leaf4953InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726837/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf4953InputLogOnePlusV_eq :
    leaf4953InputLogOnePlusV = outerEnclosure 24
      (leaf4953Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4953RoundedFacts : LeafRoundedFacts 8
    leaf4953Certificate.logOnePlusV leaf4953InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4953InputLogOnePlusV_eq }

private noncomputable def leaf4953Inputs : Inputs :=
  inputsOfCaches globalInput sk221RoundedInputs
    chi284InputQChi innerPair242Input
    leaf4953InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4953LowerChecked :
    lowerCheck 24 leaf4953Box leaf4953Inputs = true := by
  rfl'

private theorem leaf4953CoversExact : CoversExact 8
    leaf4953Box leaf4953Certificate leaf4953InnerLog leaf4953Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk221RoundedFacts chi284RoundedFacts
    innerPair242RoundedFacts leaf4953RoundedFacts (by rfl)

private theorem leaf4953FlatSound : Sound leaf4953Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4953CertificateValid
    leaf4953InnerLogValid leaf4953CoversExact leaf4953LowerChecked

private noncomputable def leaf4954Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (237/64), kHi := (119/32), chiLo := (75/256), chiHi := (19/64) }

private noncomputable def leaf4954Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742451/1073741824) }, vSqrt := { lower := (8191/8192), upper := (7635268039/7634982912) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2238539731/2147483648) }, upper := { exponent := 1, mantissa := (4309/4096) } }, logOuter := sk222LogOuterCertificate, logK := sk222LogKCertificate, logChi := chi284LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (15270250951/15269965824) } }, logDArg := sk222LogDArgCertificate }

private noncomputable def leaf4954InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4954LocalValidity :
    LeafFacts leaf4954Box leaf4954Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4954Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (7635268039/7634982912) }) = true
      norm_num [leaf4954Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4954CertificateValid :
    WideCertificateValid leaf4954Box leaf4954Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk222ValidityFacts chi284ValidityFacts
    leaf4954LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4954CoverageChecked :
    coverageCheck (innerAD leaf4954Box) leaf4954InnerLog = true := by
  rfl'

private theorem leaf4954InnerLogValid :
    leaf4954InnerLog.Valid 8 (innerAD leaf4954Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4954CoverageChecked

private noncomputable def leaf4954InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814697/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4954InputLogOnePlusV_eq :
    leaf4954InputLogOnePlusV = outerEnclosure 24
      (leaf4954Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4954RoundedFacts : LeafRoundedFacts 8
    leaf4954Certificate.logOnePlusV leaf4954InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4954InputLogOnePlusV_eq }

private noncomputable def leaf4954Inputs : Inputs :=
  inputsOfCaches globalInput sk222RoundedInputs
    chi284InputQChi innerPair242Input
    leaf4954InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4954LowerChecked :
    lowerCheck 24 leaf4954Box leaf4954Inputs = true := by
  rfl'

private theorem leaf4954CoversExact : CoversExact 8
    leaf4954Box leaf4954Certificate leaf4954InnerLog leaf4954Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk222RoundedFacts chi284RoundedFacts
    innerPair242RoundedFacts leaf4954RoundedFacts (by rfl)

private theorem leaf4954FlatSound : Sound leaf4954Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4954CertificateValid
    leaf4954InnerLogValid leaf4954CoversExact leaf4954LowerChecked

private noncomputable def leaf4955Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (239/64), chiLo := (37/128), chiHi := (75/256) }

private noncomputable def leaf4955Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742451/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714887936) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2227858015/2147483648) }, upper := { exponent := 1, mantissa := (34309/32768) } }, logOuter := sk223LogOuterCertificate, logK := sk223LogKCertificate, logChi := chi283LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432300287/137429775872) } }, logDArg := sk223LogDArgCertificate }

private noncomputable def leaf4955InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4955LocalValidity :
    LeafFacts leaf4955Box leaf4955Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4955Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714887936) }) = true
      norm_num [leaf4955Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4955CertificateValid :
    WideCertificateValid leaf4955Box leaf4955Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk223ValidityFacts chi283ValidityFacts
    leaf4955LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4955CoverageChecked :
    coverageCheck (innerAD leaf4955Box) leaf4955InnerLog = true := by
  rfl'

private theorem leaf4955InnerLogValid :
    leaf4955InnerLog.Valid 8 (innerAD leaf4955Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4955CoverageChecked

private noncomputable def leaf4955InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629389/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4955InputLogOnePlusV_eq :
    leaf4955InputLogOnePlusV = outerEnclosure 24
      (leaf4955Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4955RoundedFacts : LeafRoundedFacts 8
    leaf4955Certificate.logOnePlusV leaf4955InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4955InputLogOnePlusV_eq }

private noncomputable def leaf4955Inputs : Inputs :=
  inputsOfCaches globalInput sk223RoundedInputs
    chi283InputQChi innerPair242Input
    leaf4955InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4955LowerChecked :
    lowerCheck 24 leaf4955Box leaf4955Inputs = true := by
  rfl'

private theorem leaf4955CoversExact : CoversExact 8
    leaf4955Box leaf4955Certificate leaf4955InnerLog leaf4955Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk223RoundedFacts chi283RoundedFacts
    innerPair242RoundedFacts leaf4955RoundedFacts (by rfl)

private theorem leaf4955FlatSound : Sound leaf4955Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4955CertificateValid
    leaf4955InnerLogValid leaf4955CoversExact leaf4955LowerChecked

private noncomputable def leaf4956Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (239/64), kHi := (15/4), chiLo := (37/128), chiHi := (75/256) }

private noncomputable def leaf4956Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742453/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714868736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2232707381/2147483648) }, upper := { exponent := 1, mantissa := (2149/2048) } }, logOuter := sk224LogOuterCertificate, logK := sk224LogKCertificate, logChi := chi283LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432281087/137429737472) } }, logDArg := sk224LogDArgCertificate }

private noncomputable def leaf4956InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4956LocalValidity :
    LeafFacts leaf4956Box leaf4956Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4956Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714868736) }) = true
      norm_num [leaf4956Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4956CertificateValid :
    WideCertificateValid leaf4956Box leaf4956Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk224ValidityFacts chi283ValidityFacts
    leaf4956LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4956CoverageChecked :
    coverageCheck (innerAD leaf4956Box) leaf4956InnerLog = true := by
  rfl'

private theorem leaf4956InnerLogValid :
    leaf4956InnerLog.Valid 8 (innerAD leaf4956Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4956CoverageChecked

private noncomputable def leaf4956InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629391/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4956InputLogOnePlusV_eq :
    leaf4956InputLogOnePlusV = outerEnclosure 24
      (leaf4956Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4956RoundedFacts : LeafRoundedFacts 8
    leaf4956Certificate.logOnePlusV leaf4956InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4956InputLogOnePlusV_eq }

private noncomputable def leaf4956Inputs : Inputs :=
  inputsOfCaches globalInput sk224RoundedInputs
    chi283InputQChi innerPair242Input
    leaf4956InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4956LowerChecked :
    lowerCheck 24 leaf4956Box leaf4956Inputs = true := by
  rfl'

private theorem leaf4956CoversExact : CoversExact 8
    leaf4956Box leaf4956Certificate leaf4956InnerLog leaf4956Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk224RoundedFacts chi283RoundedFacts
    innerPair242RoundedFacts leaf4956RoundedFacts (by rfl)

private theorem leaf4956FlatSound : Sound leaf4956Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4956CertificateValid
    leaf4956InnerLogValid leaf4956CoversExact leaf4956LowerChecked

private noncomputable def leaf4957Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (239/64), chiLo := (75/256), chiHi := (19/64) }

private noncomputable def leaf4957Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742453/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714826752) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2243454629/2147483648) }, upper := { exponent := 1, mantissa := (8637/8192) } }, logOuter := sk223LogOuterCertificate, logK := sk223LogKCertificate, logChi := chi284LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432239103/137429653504) } }, logDArg := sk223LogDArgCertificate }

private noncomputable def leaf4957InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4957LocalValidity :
    LeafFacts leaf4957Box leaf4957Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4957Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714826752) }) = true
      norm_num [leaf4957Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4957CertificateValid :
    WideCertificateValid leaf4957Box leaf4957Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk223ValidityFacts chi284ValidityFacts
    leaf4957LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4957CoverageChecked :
    coverageCheck (innerAD leaf4957Box) leaf4957InnerLog = true := by
  rfl'

private theorem leaf4957InnerLogValid :
    leaf4957InnerLog.Valid 8 (innerAD leaf4957Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4957CoverageChecked

private noncomputable def leaf4957InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907349/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4957InputLogOnePlusV_eq :
    leaf4957InputLogOnePlusV = outerEnclosure 24
      (leaf4957Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4957RoundedFacts : LeafRoundedFacts 8
    leaf4957Certificate.logOnePlusV leaf4957InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4957InputLogOnePlusV_eq }

private noncomputable def leaf4957Inputs : Inputs :=
  inputsOfCaches globalInput sk223RoundedInputs
    chi284InputQChi innerPair242Input
    leaf4957InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4957LowerChecked :
    lowerCheck 24 leaf4957Box leaf4957Inputs = true := by
  rfl'

private theorem leaf4957CoversExact : CoversExact 8
    leaf4957Box leaf4957Certificate leaf4957InnerLog leaf4957Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk223RoundedFacts chi284RoundedFacts
    innerPair242RoundedFacts leaf4957RoundedFacts (by rfl)

private theorem leaf4957FlatSound : Sound leaf4957Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4957CertificateValid
    leaf4957InnerLogValid leaf4957CoversExact leaf4957LowerChecked

private noncomputable def leaf4958Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (239/64), kHi := (15/4), chiLo := (75/256), chiHi := (19/64) }

private noncomputable def leaf4958Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742455/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714807296) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2248369527/2147483648) }, upper := { exponent := 1, mantissa := (541/512) } }, logOuter := sk224LogOuterCertificate, logK := sk224LogKCertificate, logChi := chi284LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432219647/137429614592) } }, logDArg := sk224LogDArgCertificate }

private noncomputable def leaf4958InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4958LocalValidity :
    LeafFacts leaf4958Box leaf4958Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4958Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714807296) }) = true
      norm_num [leaf4958Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4958CertificateValid :
    WideCertificateValid leaf4958Box leaf4958Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk224ValidityFacts chi284ValidityFacts
    leaf4958LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4958CoverageChecked :
    coverageCheck (innerAD leaf4958Box) leaf4958InnerLog = true := by
  rfl'

private theorem leaf4958InnerLogValid :
    leaf4958InnerLog.Valid 8 (innerAD leaf4958Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4958CoverageChecked

private noncomputable def leaf4958InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629399/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4958InputLogOnePlusV_eq :
    leaf4958InputLogOnePlusV = outerEnclosure 24
      (leaf4958Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4958RoundedFacts : LeafRoundedFacts 8
    leaf4958Certificate.logOnePlusV leaf4958InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4958InputLogOnePlusV_eq }

private noncomputable def leaf4958Inputs : Inputs :=
  inputsOfCaches globalInput sk224RoundedInputs
    chi284InputQChi innerPair242Input
    leaf4958InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4958LowerChecked :
    lowerCheck 24 leaf4958Box leaf4958Inputs = true := by
  rfl'

private theorem leaf4958CoversExact : CoversExact 8
    leaf4958Box leaf4958Certificate leaf4958InnerLog leaf4958Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk224RoundedFacts chi284RoundedFacts
    innerPair242RoundedFacts leaf4958RoundedFacts (by rfl)

private theorem leaf4958FlatSound : Sound leaf4958Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4958CertificateValid
    leaf4958InnerLogValid leaf4958CoversExact leaf4958LowerChecked

private noncomputable def leaf4959Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (233/64), chiLo := (19/64), chiHi := (77/256) }

private noncomputable def leaf4959Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742443/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22905804117/22904961280) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2229168663/2147483648) }, upper := { exponent := 1, mantissa := (34325/32768) } }, logOuter := sk217LogOuterCertificate, logK := sk217LogKCertificate, logChi := chi285LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45810765397/45809922560) } }, logDArg := sk217LogDArgCertificate }

private noncomputable def leaf4959InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4959LocalValidity :
    LeafFacts leaf4959Box leaf4959Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4959Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22905804117/22904961280) }) = true
      norm_num [leaf4959Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4959CertificateValid :
    WideCertificateValid leaf4959Box leaf4959Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk217ValidityFacts chi285ValidityFacts
    leaf4959LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4959CoverageChecked :
    coverageCheck (innerAD leaf4959Box) leaf4959InnerLog = true := by
  rfl'

private theorem leaf4959InnerLogValid :
    leaf4959InnerLog.Valid 8 (innerAD leaf4959Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4959CoverageChecked

private noncomputable def leaf4959InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629389/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4959InputLogOnePlusV_eq :
    leaf4959InputLogOnePlusV = outerEnclosure 24
      (leaf4959Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4959RoundedFacts : LeafRoundedFacts 8
    leaf4959Certificate.logOnePlusV leaf4959InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4959InputLogOnePlusV_eq }

private noncomputable def leaf4959Inputs : Inputs :=
  inputsOfCaches globalInput sk217RoundedInputs
    chi285InputQChi innerPair242Input
    leaf4959InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4959LowerChecked :
    lowerCheck 24 leaf4959Box leaf4959Inputs = true := by
  rfl'

private theorem leaf4959CoversExact : CoversExact 8
    leaf4959Box leaf4959Certificate leaf4959InnerLog leaf4959Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk217RoundedFacts chi285RoundedFacts
    innerPair242RoundedFacts leaf4959RoundedFacts (by rfl)

private theorem leaf4959FlatSound : Sound leaf4959Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4959CertificateValid
    leaf4959InnerLogValid leaf4959CoversExact leaf4959LowerChecked

private noncomputable def leaf4960Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (233/64), kHi := (117/32), chiLo := (19/64), chiHi := (77/256) }

private noncomputable def leaf4960Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742445/1073741824) }, vSqrt := { lower := (8191/8192), upper := (1598079357/1598020096) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2234149093/2147483648) }, upper := { exponent := 1, mantissa := (17201/16384) } }, logOuter := sk218LogOuterCertificate, logK := sk218LogKCertificate, logChi := chi285LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (3196099453/3196040192) } }, logDArg := sk218LogDArgCertificate }

private noncomputable def leaf4960InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4960LocalValidity :
    LeafFacts leaf4960Box leaf4960Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4960Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (1598079357/1598020096) }) = true
      norm_num [leaf4960Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4960CertificateValid :
    WideCertificateValid leaf4960Box leaf4960Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk218ValidityFacts chi285ValidityFacts
    leaf4960LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4960CoverageChecked :
    coverageCheck (innerAD leaf4960Box) leaf4960InnerLog = true := by
  rfl'

private theorem leaf4960InnerLogValid :
    leaf4960InnerLog.Valid 8 (innerAD leaf4960Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4960CoverageChecked

private noncomputable def leaf4960InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726837/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf4960InputLogOnePlusV_eq :
    leaf4960InputLogOnePlusV = outerEnclosure 24
      (leaf4960Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4960RoundedFacts : LeafRoundedFacts 8
    leaf4960Certificate.logOnePlusV leaf4960InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4960InputLogOnePlusV_eq }

private noncomputable def leaf4960Inputs : Inputs :=
  inputsOfCaches globalInput sk218RoundedInputs
    chi285InputQChi innerPair242Input
    leaf4960InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4960LowerChecked :
    lowerCheck 24 leaf4960Box leaf4960Inputs = true := by
  rfl'

private theorem leaf4960CoversExact : CoversExact 8
    leaf4960Box leaf4960Certificate leaf4960InnerLog leaf4960Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk218RoundedFacts chi285RoundedFacts
    innerPair242RoundedFacts leaf4960RoundedFacts (by rfl)

private theorem leaf4960FlatSound : Sound leaf4960Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4960CertificateValid
    leaf4960InnerLogValid leaf4960CoversExact leaf4960LowerChecked

private noncomputable def leaf4961Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (233/64), chiLo := (77/256), chiHi := (39/128) }

private noncomputable def leaf4961Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742445/1073741824) }, vSqrt := { lower := (8191/8192), upper := (316670103/316658176) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2244372085/2147483648) }, upper := { exponent := 1, mantissa := (17279/16384) } }, logOuter := sk217LogOuterCertificate, logK := sk217LogKCertificate, logChi := chi286LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (633328279/633316352) } }, logDArg := sk217LogDArgCertificate }

private noncomputable def leaf4961InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4961LocalValidity :
    LeafFacts leaf4961Box leaf4961Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4961Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (316670103/316658176) }) = true
      norm_num [leaf4961Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4961CertificateValid :
    WideCertificateValid leaf4961Box leaf4961Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk217ValidityFacts chi286ValidityFacts
    leaf4961LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4961CoverageChecked :
    coverageCheck (innerAD leaf4961Box) leaf4961InnerLog = true := by
  rfl'

private theorem leaf4961InnerLogValid :
    leaf4961InnerLog.Valid 8 (innerAD leaf4961Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4961CoverageChecked

private noncomputable def leaf4961InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629397/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4961InputLogOnePlusV_eq :
    leaf4961InputLogOnePlusV = outerEnclosure 24
      (leaf4961Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4961RoundedFacts : LeafRoundedFacts 8
    leaf4961Certificate.logOnePlusV leaf4961InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4961InputLogOnePlusV_eq }

private noncomputable def leaf4961Inputs : Inputs :=
  inputsOfCaches globalInput sk217RoundedInputs
    chi286InputQChi innerPair242Input
    leaf4961InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4961LowerChecked :
    lowerCheck 24 leaf4961Box leaf4961Inputs = true := by
  rfl'

private theorem leaf4961CoversExact : CoversExact 8
    leaf4961Box leaf4961Certificate leaf4961InnerLog leaf4961Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk217RoundedFacts chi286RoundedFacts
    innerPair242RoundedFacts leaf4961RoundedFacts (by rfl)

private theorem leaf4961FlatSound : Sound leaf4961Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4961CertificateValid
    leaf4961InnerLogValid leaf4961CoversExact leaf4961LowerChecked

private noncomputable def leaf4962Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (233/64), kHi := (117/32), chiLo := (77/256), chiHi := (39/128) }

private noncomputable def leaf4962Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742447/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714804224) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2249418047/2147483648) }, upper := { exponent := 1, mantissa := (8659/8192) } }, logOuter := sk218LogOuterCertificate, logK := sk218LogKCertificate, logChi := chi286LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432216575/137429608448) } }, logDArg := sk218LogDArgCertificate }

private noncomputable def leaf4962InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4962LocalValidity :
    LeafFacts leaf4962Box leaf4962Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4962Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714804224) }) = true
      norm_num [leaf4962Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4962CertificateValid :
    WideCertificateValid leaf4962Box leaf4962Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk218ValidityFacts chi286ValidityFacts
    leaf4962LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4962CoverageChecked :
    coverageCheck (innerAD leaf4962Box) leaf4962InnerLog = true := by
  rfl'

private theorem leaf4962InnerLogValid :
    leaf4962InnerLog.Valid 8 (innerAD leaf4962Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4962CoverageChecked

private noncomputable def leaf4962InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629399/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4962InputLogOnePlusV_eq :
    leaf4962InputLogOnePlusV = outerEnclosure 24
      (leaf4962Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4962RoundedFacts : LeafRoundedFacts 8
    leaf4962Certificate.logOnePlusV leaf4962InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4962InputLogOnePlusV_eq }

private noncomputable def leaf4962Inputs : Inputs :=
  inputsOfCaches globalInput sk218RoundedInputs
    chi286InputQChi innerPair242Input
    leaf4962InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4962LowerChecked :
    lowerCheck 24 leaf4962Box leaf4962Inputs = true := by
  rfl'

private theorem leaf4962CoversExact : CoversExact 8
    leaf4962Box leaf4962Certificate leaf4962InnerLog leaf4962Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk218RoundedFacts chi286RoundedFacts
    innerPair242RoundedFacts leaf4962RoundedFacts (by rfl)

private theorem leaf4962FlatSound : Sound leaf4962Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4962CertificateValid
    leaf4962InnerLogValid leaf4962CoversExact leaf4962LowerChecked

private noncomputable def leaf4963Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (235/64), chiLo := (19/64), chiHi := (77/256) }

private noncomputable def leaf4963Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742447/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714844416) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2239129523/2147483648) }, upper := { exponent := 1, mantissa := (34479/32768) } }, logOuter := sk219LogOuterCertificate, logK := sk219LogKCertificate, logChi := chi285LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432256767/137429688832) } }, logDArg := sk219LogDArgCertificate }

private noncomputable def leaf4963InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4963LocalValidity :
    LeafFacts leaf4963Box leaf4963Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4963Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714844416) }) = true
      norm_num [leaf4963Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4963CertificateValid :
    WideCertificateValid leaf4963Box leaf4963Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk219ValidityFacts chi285ValidityFacts
    leaf4963LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4963CoverageChecked :
    coverageCheck (innerAD leaf4963Box) leaf4963InnerLog = true := by
  rfl'

private theorem leaf4963InnerLogValid :
    leaf4963InnerLog.Valid 8 (innerAD leaf4963Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4963CoverageChecked

private noncomputable def leaf4963InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814697/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4963InputLogOnePlusV_eq :
    leaf4963InputLogOnePlusV = outerEnclosure 24
      (leaf4963Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4963RoundedFacts : LeafRoundedFacts 8
    leaf4963Certificate.logOnePlusV leaf4963InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4963InputLogOnePlusV_eq }

private noncomputable def leaf4963Inputs : Inputs :=
  inputsOfCaches globalInput sk219RoundedInputs
    chi285InputQChi innerPair242Input
    leaf4963InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4963LowerChecked :
    lowerCheck 24 leaf4963Box leaf4963Inputs = true := by
  rfl'

private theorem leaf4963CoversExact : CoversExact 8
    leaf4963Box leaf4963Certificate leaf4963InnerLog leaf4963Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk219RoundedFacts chi285RoundedFacts
    innerPair242RoundedFacts leaf4963RoundedFacts (by rfl)

private theorem leaf4963FlatSound : Sound leaf4963Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4963CertificateValid
    leaf4963InnerLogValid leaf4963CoversExact leaf4963LowerChecked

private noncomputable def leaf4964Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (235/64), kHi := (59/16), chiLo := (19/64), chiHi := (77/256) }

private noncomputable def leaf4964Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742449/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22905804117/22904941568) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2244109953/2147483648) }, upper := { exponent := 1, mantissa := (8639/8192) } }, logOuter := sk220LogOuterCertificate, logK := sk220LogKCertificate, logChi := chi285LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45810745685/45809883136) } }, logDArg := sk220LogDArgCertificate }

private noncomputable def leaf4964InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4964LocalValidity :
    LeafFacts leaf4964Box leaf4964Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4964Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22905804117/22904941568) }) = true
      norm_num [leaf4964Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4964CertificateValid :
    WideCertificateValid leaf4964Box leaf4964Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk220ValidityFacts chi285ValidityFacts
    leaf4964LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4964CoverageChecked :
    coverageCheck (innerAD leaf4964Box) leaf4964InnerLog = true := by
  rfl'

private theorem leaf4964InnerLogValid :
    leaf4964InnerLog.Valid 8 (innerAD leaf4964Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4964CoverageChecked

private noncomputable def leaf4964InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629397/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4964InputLogOnePlusV_eq :
    leaf4964InputLogOnePlusV = outerEnclosure 24
      (leaf4964Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4964RoundedFacts : LeafRoundedFacts 8
    leaf4964Certificate.logOnePlusV leaf4964InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4964InputLogOnePlusV_eq }

private noncomputable def leaf4964Inputs : Inputs :=
  inputsOfCaches globalInput sk220RoundedInputs
    chi285InputQChi innerPair242Input
    leaf4964InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4964LowerChecked :
    lowerCheck 24 leaf4964Box leaf4964Inputs = true := by
  rfl'

private theorem leaf4964CoversExact : CoversExact 8
    leaf4964Box leaf4964Certificate leaf4964InnerLog leaf4964Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk220RoundedFacts chi285RoundedFacts
    innerPair242RoundedFacts leaf4964RoundedFacts (by rfl)

private theorem leaf4964FlatSound : Sound leaf4964Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4964CertificateValid
    leaf4964InnerLogValid leaf4964CoversExact leaf4964LowerChecked

private noncomputable def leaf4965Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (235/64), chiLo := (77/256), chiHi := (39/128) }

private noncomputable def leaf4965Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742449/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714784256) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2254464009/2147483648) }, upper := { exponent := 1, mantissa := (17357/16384) } }, logOuter := sk219LogOuterCertificate, logK := sk219LogKCertificate, logChi := chi286LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432196607/137429568512) } }, logDArg := sk219LogDArgCertificate }

private noncomputable def leaf4965InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4965LocalValidity :
    LeafFacts leaf4965Box leaf4965Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4965Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714784256) }) = true
      norm_num [leaf4965Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4965CertificateValid :
    WideCertificateValid leaf4965Box leaf4965Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk219ValidityFacts chi286ValidityFacts
    leaf4965LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4965CoverageChecked :
    coverageCheck (innerAD leaf4965Box) leaf4965InnerLog = true := by
  rfl'

private theorem leaf4965InnerLogValid :
    leaf4965InnerLog.Valid 8 (innerAD leaf4965Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4965CoverageChecked

private noncomputable def leaf4965InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814701/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4965InputLogOnePlusV_eq :
    leaf4965InputLogOnePlusV = outerEnclosure 24
      (leaf4965Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4965RoundedFacts : LeafRoundedFacts 8
    leaf4965Certificate.logOnePlusV leaf4965InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4965InputLogOnePlusV_eq }

private noncomputable def leaf4965Inputs : Inputs :=
  inputsOfCaches globalInput sk219RoundedInputs
    chi286InputQChi innerPair242Input
    leaf4965InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4965LowerChecked :
    lowerCheck 24 leaf4965Box leaf4965Inputs = true := by
  rfl'

private theorem leaf4965CoversExact : CoversExact 8
    leaf4965Box leaf4965Certificate leaf4965InnerLog leaf4965Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk219RoundedFacts chi286RoundedFacts
    innerPair242RoundedFacts leaf4965RoundedFacts (by rfl)

private theorem leaf4965FlatSound : Sound leaf4965Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4965CertificateValid
    leaf4965InnerLogValid leaf4965CoversExact leaf4965LowerChecked

private noncomputable def leaf4966Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (235/64), kHi := (59/16), chiLo := (77/256), chiHi := (39/128) }

private noncomputable def leaf4966Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742451/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714764288) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2259509971/2147483648) }, upper := { exponent := 1, mantissa := (4349/4096) } }, logOuter := sk220LogOuterCertificate, logK := sk220LogKCertificate, logChi := chi286LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432176639/137429528576) } }, logDArg := sk220LogDArgCertificate }

private noncomputable def leaf4966InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4966LocalValidity :
    LeafFacts leaf4966Box leaf4966Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4966Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714764288) }) = true
      norm_num [leaf4966Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4966CertificateValid :
    WideCertificateValid leaf4966Box leaf4966Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk220ValidityFacts chi286ValidityFacts
    leaf4966LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4966CoverageChecked :
    coverageCheck (innerAD leaf4966Box) leaf4966InnerLog = true := by
  rfl'

private theorem leaf4966InnerLogValid :
    leaf4966InnerLog.Valid 8 (innerAD leaf4966Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4966CoverageChecked

private noncomputable def leaf4966InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907351/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4966InputLogOnePlusV_eq :
    leaf4966InputLogOnePlusV = outerEnclosure 24
      (leaf4966Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4966RoundedFacts : LeafRoundedFacts 8
    leaf4966Certificate.logOnePlusV leaf4966InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4966InputLogOnePlusV_eq }

private noncomputable def leaf4966Inputs : Inputs :=
  inputsOfCaches globalInput sk220RoundedInputs
    chi286InputQChi innerPair242Input
    leaf4966InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4966LowerChecked :
    lowerCheck 24 leaf4966Box leaf4966Inputs = true := by
  rfl'

private theorem leaf4966CoversExact : CoversExact 8
    leaf4966Box leaf4966Certificate leaf4966InnerLog leaf4966Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk220RoundedFacts chi286RoundedFacts
    innerPair242RoundedFacts leaf4966RoundedFacts (by rfl)

private theorem leaf4966FlatSound : Sound leaf4966Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4966CertificateValid
    leaf4966InnerLogValid leaf4966CoversExact leaf4966LowerChecked

private noncomputable def leaf4967Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (233/64), chiLo := (39/128), chiHi := (79/256) }

private noncomputable def leaf4967Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742447/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714764544) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2259575507/2147483648) }, upper := { exponent := 1, mantissa := (34791/32768) } }, logOuter := sk217LogOuterCertificate, logK := sk217LogKCertificate, logChi := chi287LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432176895/137429529088) } }, logDArg := sk217LogDArgCertificate }

private noncomputable def leaf4967InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4967LocalValidity :
    LeafFacts leaf4967Box leaf4967Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4967Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714764544) }) = true
      norm_num [leaf4967Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4967CertificateValid :
    WideCertificateValid leaf4967Box leaf4967Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk217ValidityFacts chi287ValidityFacts
    leaf4967LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4967CoverageChecked :
    coverageCheck (innerAD leaf4967Box) leaf4967InnerLog = true := by
  rfl'

private theorem leaf4967InnerLogValid :
    leaf4967InnerLog.Valid 8 (innerAD leaf4967Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4967CoverageChecked

private noncomputable def leaf4967InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907351/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4967InputLogOnePlusV_eq :
    leaf4967InputLogOnePlusV = outerEnclosure 24
      (leaf4967Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4967RoundedFacts : LeafRoundedFacts 8
    leaf4967Certificate.logOnePlusV leaf4967InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4967InputLogOnePlusV_eq }

private noncomputable def leaf4967Inputs : Inputs :=
  inputsOfCaches globalInput sk217RoundedInputs
    chi287InputQChi innerPair242Input
    leaf4967InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4967LowerChecked :
    lowerCheck 24 leaf4967Box leaf4967Inputs = true := by
  rfl'

private theorem leaf4967CoversExact : CoversExact 8
    leaf4967Box leaf4967Certificate leaf4967InnerLog leaf4967Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk217RoundedFacts chi287RoundedFacts
    innerPair242RoundedFacts leaf4967RoundedFacts (by rfl)

private theorem leaf4967FlatSound : Sound leaf4967Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4967CertificateValid
    leaf4967InnerLogValid leaf4967CoversExact leaf4967LowerChecked

private noncomputable def leaf4968Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (233/64), kHi := (117/32), chiLo := (39/128), chiHi := (79/256) }

private noncomputable def leaf4968Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742449/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714744320) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2264687001/2147483648) }, upper := { exponent := 1, mantissa := (17435/16384) } }, logOuter := sk218LogOuterCertificate, logK := sk218LogKCertificate, logChi := chi287LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432156671/137429488640) } }, logDArg := sk218LogDArgCertificate }

private noncomputable def leaf4968InnerLog : WideLogData :=
  innerPair243Data

set_option maxRecDepth 1000000 in
private theorem leaf4968LocalValidity :
    LeafFacts leaf4968Box leaf4968Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4968Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714744320) }) = true
      norm_num [leaf4968Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4968CertificateValid :
    WideCertificateValid leaf4968Box leaf4968Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk218ValidityFacts chi287ValidityFacts
    leaf4968LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4968CoverageChecked :
    coverageCheck (innerAD leaf4968Box) leaf4968InnerLog = true := by
  rfl'

private theorem leaf4968InnerLogValid :
    leaf4968InnerLog.Valid 8 (innerAD leaf4968Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint74PositiveFacts.valid leaf4968CoverageChecked

private noncomputable def leaf4968InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814703/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4968InputLogOnePlusV_eq :
    leaf4968InputLogOnePlusV = outerEnclosure 24
      (leaf4968Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4968RoundedFacts : LeafRoundedFacts 8
    leaf4968Certificate.logOnePlusV leaf4968InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4968InputLogOnePlusV_eq }

private noncomputable def leaf4968Inputs : Inputs :=
  inputsOfCaches globalInput sk218RoundedInputs
    chi287InputQChi innerPair243Input
    leaf4968InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4968LowerChecked :
    lowerCheck 24 leaf4968Box leaf4968Inputs = true := by
  rfl'

private theorem leaf4968CoversExact : CoversExact 8
    leaf4968Box leaf4968Certificate leaf4968InnerLog leaf4968Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk218RoundedFacts chi287RoundedFacts
    innerPair243RoundedFacts leaf4968RoundedFacts (by rfl)

private theorem leaf4968FlatSound : Sound leaf4968Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4968CertificateValid
    leaf4968InnerLogValid leaf4968CoversExact leaf4968LowerChecked

private noncomputable def leaf4969Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (233/64), chiLo := (79/256), chiHi := (5/16) }

private noncomputable def leaf4969Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742449/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22905804117/22904901632) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2274778929/2147483648) }, upper := { exponent := 1, mantissa := (2189/2048) } }, logOuter := sk217LogOuterCertificate, logK := sk217LogKCertificate, logChi := chi288LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45810705749/45809803264) } }, logDArg := sk217LogDArgCertificate }

private noncomputable def leaf4969InnerLog : WideLogData :=
  innerPair243Data

set_option maxRecDepth 1000000 in
private theorem leaf4969LocalValidity :
    LeafFacts leaf4969Box leaf4969Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4969Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22905804117/22904901632) }) = true
      norm_num [leaf4969Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4969CertificateValid :
    WideCertificateValid leaf4969Box leaf4969Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk217ValidityFacts chi288ValidityFacts
    leaf4969LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4969CoverageChecked :
    coverageCheck (innerAD leaf4969Box) leaf4969InnerLog = true := by
  rfl'

private theorem leaf4969InnerLogValid :
    leaf4969InnerLog.Valid 8 (innerAD leaf4969Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint74PositiveFacts.valid leaf4969CoverageChecked

private noncomputable def leaf4969InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629411/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4969InputLogOnePlusV_eq :
    leaf4969InputLogOnePlusV = outerEnclosure 24
      (leaf4969Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4969RoundedFacts : LeafRoundedFacts 8
    leaf4969Certificate.logOnePlusV leaf4969InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4969InputLogOnePlusV_eq }

private noncomputable def leaf4969Inputs : Inputs :=
  inputsOfCaches globalInput sk217RoundedInputs
    chi288InputQChi innerPair243Input
    leaf4969InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4969LowerChecked :
    lowerCheck 24 leaf4969Box leaf4969Inputs = true := by
  rfl'

private theorem leaf4969CoversExact : CoversExact 8
    leaf4969Box leaf4969Certificate leaf4969InnerLog leaf4969Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk217RoundedFacts chi288RoundedFacts
    innerPair243RoundedFacts leaf4969RoundedFacts (by rfl)

private theorem leaf4969FlatSound : Sound leaf4969Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4969CertificateValid
    leaf4969InnerLogValid leaf4969CoversExact leaf4969LowerChecked

private noncomputable def leaf4970Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (233/64), kHi := (117/32), chiLo := (79/256), chiHi := (5/16) }

private noncomputable def leaf4970Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742451/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9816773193/9816383488) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2279955955/2147483648) }, upper := { exponent := 1, mantissa := (1097/1024) } }, logOuter := sk218LogOuterCertificate, logK := sk218LogKCertificate, logChi := chi288LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (19633156681/19632766976) } }, logDArg := sk218LogDArgCertificate }

private noncomputable def leaf4970InnerLog : WideLogData :=
  innerPair243Data

set_option maxRecDepth 1000000 in
private theorem leaf4970LocalValidity :
    LeafFacts leaf4970Box leaf4970Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4970Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9816773193/9816383488) }) = true
      norm_num [leaf4970Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4970CertificateValid :
    WideCertificateValid leaf4970Box leaf4970Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk218ValidityFacts chi288ValidityFacts
    leaf4970LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4970CoverageChecked :
    coverageCheck (innerAD leaf4970Box) leaf4970InnerLog = true := by
  rfl'

private theorem leaf4970InnerLogValid :
    leaf4970InnerLog.Valid 8 (innerAD leaf4970Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint74PositiveFacts.valid leaf4970CoverageChecked

private noncomputable def leaf4970InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814707/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4970InputLogOnePlusV_eq :
    leaf4970InputLogOnePlusV = outerEnclosure 24
      (leaf4970Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4970RoundedFacts : LeafRoundedFacts 8
    leaf4970Certificate.logOnePlusV leaf4970InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4970InputLogOnePlusV_eq }

private noncomputable def leaf4970Inputs : Inputs :=
  inputsOfCaches globalInput sk218RoundedInputs
    chi288InputQChi innerPair243Input
    leaf4970InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4970LowerChecked :
    lowerCheck 24 leaf4970Box leaf4970Inputs = true := by
  rfl'

private theorem leaf4970CoversExact : CoversExact 8
    leaf4970Box leaf4970Certificate leaf4970InnerLog leaf4970Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk218RoundedFacts chi288RoundedFacts
    innerPair243RoundedFacts leaf4970RoundedFacts (by rfl)

private theorem leaf4970FlatSound : Sound leaf4970Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4970CertificateValid
    leaf4970InnerLogValid leaf4970CoversExact leaf4970LowerChecked

private noncomputable def leaf4971Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (235/64), chiLo := (39/128), chiHi := (79/256) }

private noncomputable def leaf4971Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742451/1073741824) }, vSqrt := { lower := (8191/8192), upper := (7635268039/7634969344) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2269798495/2147483648) }, upper := { exponent := 1, mantissa := (34949/32768) } }, logOuter := sk219LogOuterCertificate, logK := sk219LogKCertificate, logChi := chi287LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (15270237383/15269938688) } }, logDArg := sk219LogDArgCertificate }

private noncomputable def leaf4971InnerLog : WideLogData :=
  innerPair243Data

set_option maxRecDepth 1000000 in
private theorem leaf4971LocalValidity :
    LeafFacts leaf4971Box leaf4971Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4971Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (7635268039/7634969344) }) = true
      norm_num [leaf4971Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4971CertificateValid :
    WideCertificateValid leaf4971Box leaf4971Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk219ValidityFacts chi287ValidityFacts
    leaf4971LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4971CoverageChecked :
    coverageCheck (innerAD leaf4971Box) leaf4971InnerLog = true := by
  rfl'

private theorem leaf4971InnerLogValid :
    leaf4971InnerLog.Valid 8 (innerAD leaf4971Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint74PositiveFacts.valid leaf4971CoverageChecked

private noncomputable def leaf4971InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629409/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4971InputLogOnePlusV_eq :
    leaf4971InputLogOnePlusV = outerEnclosure 24
      (leaf4971Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4971RoundedFacts : LeafRoundedFacts 8
    leaf4971Certificate.logOnePlusV leaf4971InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4971InputLogOnePlusV_eq }

private noncomputable def leaf4971Inputs : Inputs :=
  inputsOfCaches globalInput sk219RoundedInputs
    chi287InputQChi innerPair243Input
    leaf4971InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4971LowerChecked :
    lowerCheck 24 leaf4971Box leaf4971Inputs = true := by
  rfl'

private theorem leaf4971CoversExact : CoversExact 8
    leaf4971Box leaf4971Certificate leaf4971InnerLog leaf4971Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk219RoundedFacts chi287RoundedFacts
    innerPair243RoundedFacts leaf4971RoundedFacts (by rfl)

private theorem leaf4971FlatSound : Sound leaf4971Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4971CertificateValid
    leaf4971InnerLogValid leaf4971CoversExact leaf4971LowerChecked

private noncomputable def leaf4972Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (235/64), kHi := (59/16), chiLo := (39/128), chiHi := (79/256) }

private noncomputable def leaf4972Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742453/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714703872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2274909989/2147483648) }, upper := { exponent := 1, mantissa := (8757/8192) } }, logOuter := sk220LogOuterCertificate, logK := sk220LogKCertificate, logChi := chi287LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432116223/137429407744) } }, logDArg := sk220LogDArgCertificate }

private noncomputable def leaf4972InnerLog : WideLogData :=
  innerPair243Data

set_option maxRecDepth 1000000 in
private theorem leaf4972LocalValidity :
    LeafFacts leaf4972Box leaf4972Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4972Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714703872) }) = true
      norm_num [leaf4972Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4972CertificateValid :
    WideCertificateValid leaf4972Box leaf4972Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk220ValidityFacts chi287ValidityFacts
    leaf4972LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4972CoverageChecked :
    coverageCheck (innerAD leaf4972Box) leaf4972InnerLog = true := by
  rfl'

private theorem leaf4972InnerLogValid :
    leaf4972InnerLog.Valid 8 (innerAD leaf4972Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint74PositiveFacts.valid leaf4972CoverageChecked

private noncomputable def leaf4972InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629411/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4972InputLogOnePlusV_eq :
    leaf4972InputLogOnePlusV = outerEnclosure 24
      (leaf4972Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4972RoundedFacts : LeafRoundedFacts 8
    leaf4972Certificate.logOnePlusV leaf4972InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4972InputLogOnePlusV_eq }

private noncomputable def leaf4972Inputs : Inputs :=
  inputsOfCaches globalInput sk220RoundedInputs
    chi287InputQChi innerPair243Input
    leaf4972InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4972LowerChecked :
    lowerCheck 24 leaf4972Box leaf4972Inputs = true := by
  rfl'

private theorem leaf4972CoversExact : CoversExact 8
    leaf4972Box leaf4972Certificate leaf4972InnerLog leaf4972Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk220RoundedFacts chi287RoundedFacts
    innerPair243RoundedFacts leaf4972RoundedFacts (by rfl)

private theorem leaf4972FlatSound : Sound leaf4972Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4972CertificateValid
    leaf4972InnerLogValid leaf4972CoversExact leaf4972LowerChecked

private noncomputable def leaf4973Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (235/64), chiLo := (79/256), chiHi := (5/16) }

private noncomputable def leaf4973Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742453/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714663936) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2285132981/2147483648) }, upper := { exponent := 1, mantissa := (2199/2048) } }, logOuter := sk219LogOuterCertificate, logK := sk219LogKCertificate, logChi := chi288LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432076287/137429327872) } }, logDArg := sk219LogDArgCertificate }

private noncomputable def leaf4973InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf4973LocalValidity :
    LeafFacts leaf4973Box leaf4973Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4973Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714663936) }) = true
      norm_num [leaf4973Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4973CertificateValid :
    WideCertificateValid leaf4973Box leaf4973Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk219ValidityFacts chi288ValidityFacts
    leaf4973LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4973CoverageChecked :
    coverageCheck (innerAD leaf4973Box) leaf4973InnerLog = true := by
  rfl'

private theorem leaf4973InnerLogValid :
    leaf4973InnerLog.Valid 8 (innerAD leaf4973Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf4973CoverageChecked

private noncomputable def leaf4973InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453677/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf4973InputLogOnePlusV_eq :
    leaf4973InputLogOnePlusV = outerEnclosure 24
      (leaf4973Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4973RoundedFacts : LeafRoundedFacts 8
    leaf4973Certificate.logOnePlusV leaf4973InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4973InputLogOnePlusV_eq }

private noncomputable def leaf4973Inputs : Inputs :=
  inputsOfCaches globalInput sk219RoundedInputs
    chi288InputQChi innerPair249Input
    leaf4973InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4973LowerChecked :
    lowerCheck 24 leaf4973Box leaf4973Inputs = true := by
  rfl'

private theorem leaf4973CoversExact : CoversExact 8
    leaf4973Box leaf4973Certificate leaf4973InnerLog leaf4973Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk219RoundedFacts chi288RoundedFacts
    innerPair249RoundedFacts leaf4973RoundedFacts (by rfl)

private theorem leaf4973FlatSound : Sound leaf4973Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4973CertificateValid
    leaf4973InnerLogValid leaf4973CoversExact leaf4973LowerChecked

private noncomputable def leaf4974Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (235/64), kHi := (59/16), chiLo := (79/256), chiHi := (5/16) }

private noncomputable def leaf4974Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742455/1073741824) }, vSqrt := { lower := (8191/8192), upper := (7635268039/7634960384) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2290310007/2147483648) }, upper := { exponent := 1, mantissa := (551/512) } }, logOuter := sk220LogOuterCertificate, logK := sk220LogKCertificate, logChi := chi288LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (15270228423/15269920768) } }, logDArg := sk220LogDArgCertificate }

private noncomputable def leaf4974InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf4974LocalValidity :
    LeafFacts leaf4974Box leaf4974Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4974Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (7635268039/7634960384) }) = true
      norm_num [leaf4974Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4974CertificateValid :
    WideCertificateValid leaf4974Box leaf4974Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk220ValidityFacts chi288ValidityFacts
    leaf4974LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4974CoverageChecked :
    coverageCheck (innerAD leaf4974Box) leaf4974InnerLog = true := by
  rfl'

private theorem leaf4974InnerLogValid :
    leaf4974InnerLog.Valid 8 (innerAD leaf4974Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf4974CoverageChecked

private noncomputable def leaf4974InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629419/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4974InputLogOnePlusV_eq :
    leaf4974InputLogOnePlusV = outerEnclosure 24
      (leaf4974Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4974RoundedFacts : LeafRoundedFacts 8
    leaf4974Certificate.logOnePlusV leaf4974InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4974InputLogOnePlusV_eq }

private noncomputable def leaf4974Inputs : Inputs :=
  inputsOfCaches globalInput sk220RoundedInputs
    chi288InputQChi innerPair249Input
    leaf4974InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4974LowerChecked :
    lowerCheck 24 leaf4974Box leaf4974Inputs = true := by
  rfl'

private theorem leaf4974CoversExact : CoversExact 8
    leaf4974Box leaf4974Certificate leaf4974InnerLog leaf4974Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk220RoundedFacts chi288RoundedFacts
    innerPair249RoundedFacts leaf4974RoundedFacts (by rfl)

private theorem leaf4974FlatSound : Sound leaf4974Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4974CertificateValid
    leaf4974InnerLogValid leaf4974CoversExact leaf4974LowerChecked

private noncomputable def leaf4975Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (237/64), chiLo := (19/64), chiHi := (77/256) }

private noncomputable def leaf4975Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742451/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714804992) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2249090383/2147483648) }, upper := { exponent := 1, mantissa := (34633/32768) } }, logOuter := sk221LogOuterCertificate, logK := sk221LogKCertificate, logChi := chi285LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432217343/137429609984) } }, logDArg := sk221LogDArgCertificate }

private noncomputable def leaf4975InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4975LocalValidity :
    LeafFacts leaf4975Box leaf4975Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4975Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714804992) }) = true
      norm_num [leaf4975Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4975CertificateValid :
    WideCertificateValid leaf4975Box leaf4975Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk221ValidityFacts chi285ValidityFacts
    leaf4975LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4975CoverageChecked :
    coverageCheck (innerAD leaf4975Box) leaf4975InnerLog = true := by
  rfl'

private theorem leaf4975InnerLogValid :
    leaf4975InnerLog.Valid 8 (innerAD leaf4975Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4975CoverageChecked

private noncomputable def leaf4975InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629399/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4975InputLogOnePlusV_eq :
    leaf4975InputLogOnePlusV = outerEnclosure 24
      (leaf4975Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4975RoundedFacts : LeafRoundedFacts 8
    leaf4975Certificate.logOnePlusV leaf4975InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4975InputLogOnePlusV_eq }

private noncomputable def leaf4975Inputs : Inputs :=
  inputsOfCaches globalInput sk221RoundedInputs
    chi285InputQChi innerPair242Input
    leaf4975InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4975LowerChecked :
    lowerCheck 24 leaf4975Box leaf4975Inputs = true := by
  rfl'

private theorem leaf4975CoversExact : CoversExact 8
    leaf4975Box leaf4975Certificate leaf4975InnerLog leaf4975Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk221RoundedFacts chi285RoundedFacts
    innerPair242RoundedFacts leaf4975RoundedFacts (by rfl)

private theorem leaf4975FlatSound : Sound leaf4975Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4975CertificateValid
    leaf4975InnerLogValid leaf4975CoversExact leaf4975LowerChecked

private noncomputable def leaf4976Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (237/64), kHi := (119/32), chiLo := (19/64), chiHi := (77/256) }

private noncomputable def leaf4976Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742453/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714785280) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2254070813/2147483648) }, upper := { exponent := 1, mantissa := (17355/16384) } }, logOuter := sk222LogOuterCertificate, logK := sk222LogKCertificate, logChi := chi285LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432197631/137429570560) } }, logDArg := sk222LogDArgCertificate }

private noncomputable def leaf4976InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4976LocalValidity :
    LeafFacts leaf4976Box leaf4976Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4976Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714785280) }) = true
      norm_num [leaf4976Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4976CertificateValid :
    WideCertificateValid leaf4976Box leaf4976Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk222ValidityFacts chi285ValidityFacts
    leaf4976LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4976CoverageChecked :
    coverageCheck (innerAD leaf4976Box) leaf4976InnerLog = true := by
  rfl'

private theorem leaf4976InnerLogValid :
    leaf4976InnerLog.Valid 8 (innerAD leaf4976Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4976CoverageChecked

private noncomputable def leaf4976InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629401/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4976InputLogOnePlusV_eq :
    leaf4976InputLogOnePlusV = outerEnclosure 24
      (leaf4976Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4976RoundedFacts : LeafRoundedFacts 8
    leaf4976Certificate.logOnePlusV leaf4976InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4976InputLogOnePlusV_eq }

private noncomputable def leaf4976Inputs : Inputs :=
  inputsOfCaches globalInput sk222RoundedInputs
    chi285InputQChi innerPair242Input
    leaf4976InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4976LowerChecked :
    lowerCheck 24 leaf4976Box leaf4976Inputs = true := by
  rfl'

private theorem leaf4976CoversExact : CoversExact 8
    leaf4976Box leaf4976Certificate leaf4976InnerLog leaf4976Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk222RoundedFacts chi285RoundedFacts
    innerPair242RoundedFacts leaf4976RoundedFacts (by rfl)

private theorem leaf4976FlatSound : Sound leaf4976Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4976CertificateValid
    leaf4976InnerLogValid leaf4976CoversExact leaf4976LowerChecked

private noncomputable def leaf4977Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (237/64), chiLo := (77/256), chiHi := (39/128) }

private noncomputable def leaf4977Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742453/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714744320) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2264555933/2147483648) }, upper := { exponent := 1, mantissa := (17435/16384) } }, logOuter := sk221LogOuterCertificate, logK := sk221LogKCertificate, logChi := chi286LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432156671/137429488640) } }, logDArg := sk221LogDArgCertificate }

private noncomputable def leaf4977InnerLog : WideLogData :=
  innerPair243Data

set_option maxRecDepth 1000000 in
private theorem leaf4977LocalValidity :
    LeafFacts leaf4977Box leaf4977Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4977Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714744320) }) = true
      norm_num [leaf4977Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4977CertificateValid :
    WideCertificateValid leaf4977Box leaf4977Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk221ValidityFacts chi286ValidityFacts
    leaf4977LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4977CoverageChecked :
    coverageCheck (innerAD leaf4977Box) leaf4977InnerLog = true := by
  rfl'

private theorem leaf4977InnerLogValid :
    leaf4977InnerLog.Valid 8 (innerAD leaf4977Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint74PositiveFacts.valid leaf4977CoverageChecked

private noncomputable def leaf4977InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814703/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4977InputLogOnePlusV_eq :
    leaf4977InputLogOnePlusV = outerEnclosure 24
      (leaf4977Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4977RoundedFacts : LeafRoundedFacts 8
    leaf4977Certificate.logOnePlusV leaf4977InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4977InputLogOnePlusV_eq }

private noncomputable def leaf4977Inputs : Inputs :=
  inputsOfCaches globalInput sk221RoundedInputs
    chi286InputQChi innerPair243Input
    leaf4977InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4977LowerChecked :
    lowerCheck 24 leaf4977Box leaf4977Inputs = true := by
  rfl'

private theorem leaf4977CoversExact : CoversExact 8
    leaf4977Box leaf4977Certificate leaf4977InnerLog leaf4977Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk221RoundedFacts chi286RoundedFacts
    innerPair243RoundedFacts leaf4977RoundedFacts (by rfl)

private theorem leaf4977FlatSound : Sound leaf4977Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4977CertificateValid
    leaf4977InnerLogValid leaf4977CoversExact leaf4977LowerChecked

private noncomputable def leaf4978Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (237/64), kHi := (119/32), chiLo := (77/256), chiHi := (39/128) }

private noncomputable def leaf4978Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742455/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714724352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2269601895/2147483648) }, upper := { exponent := 1, mantissa := (8737/8192) } }, logOuter := sk222LogOuterCertificate, logK := sk222LogKCertificate, logChi := chi286LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432136703/137429448704) } }, logDArg := sk222LogDArgCertificate }

private noncomputable def leaf4978InnerLog : WideLogData :=
  innerPair243Data

set_option maxRecDepth 1000000 in
private theorem leaf4978LocalValidity :
    LeafFacts leaf4978Box leaf4978Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4978Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714724352) }) = true
      norm_num [leaf4978Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4978CertificateValid :
    WideCertificateValid leaf4978Box leaf4978Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk222ValidityFacts chi286ValidityFacts
    leaf4978LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4978CoverageChecked :
    coverageCheck (innerAD leaf4978Box) leaf4978InnerLog = true := by
  rfl'

private theorem leaf4978InnerLogValid :
    leaf4978InnerLog.Valid 8 (innerAD leaf4978Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint74PositiveFacts.valid leaf4978CoverageChecked

private noncomputable def leaf4978InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629409/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4978InputLogOnePlusV_eq :
    leaf4978InputLogOnePlusV = outerEnclosure 24
      (leaf4978Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4978RoundedFacts : LeafRoundedFacts 8
    leaf4978Certificate.logOnePlusV leaf4978InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4978InputLogOnePlusV_eq }

private noncomputable def leaf4978Inputs : Inputs :=
  inputsOfCaches globalInput sk222RoundedInputs
    chi286InputQChi innerPair243Input
    leaf4978InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4978LowerChecked :
    lowerCheck 24 leaf4978Box leaf4978Inputs = true := by
  rfl'

private theorem leaf4978CoversExact : CoversExact 8
    leaf4978Box leaf4978Certificate leaf4978InnerLog leaf4978Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk222RoundedFacts chi286RoundedFacts
    innerPair243RoundedFacts leaf4978RoundedFacts (by rfl)

private theorem leaf4978FlatSound : Sound leaf4978Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4978CertificateValid
    leaf4978InnerLogValid leaf4978CoversExact leaf4978LowerChecked

private noncomputable def leaf4979Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (239/64), chiLo := (19/64), chiHi := (77/256) }

private noncomputable def leaf4979Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742455/1073741824) }, vSqrt := { lower := (8191/8192), upper := (7635268039/7634973952) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2259051243/2147483648) }, upper := { exponent := 1, mantissa := (34787/32768) } }, logOuter := sk223LogOuterCertificate, logK := sk223LogKCertificate, logChi := chi285LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (15270241991/15269947904) } }, logDArg := sk223LogDArgCertificate }

private noncomputable def leaf4979InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4979LocalValidity :
    LeafFacts leaf4979Box leaf4979Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4979Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (7635268039/7634973952) }) = true
      norm_num [leaf4979Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4979CertificateValid :
    WideCertificateValid leaf4979Box leaf4979Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk223ValidityFacts chi285ValidityFacts
    leaf4979LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4979CoverageChecked :
    coverageCheck (innerAD leaf4979Box) leaf4979InnerLog = true := by
  rfl'

private theorem leaf4979InnerLogValid :
    leaf4979InnerLog.Valid 8 (innerAD leaf4979Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4979CoverageChecked

private noncomputable def leaf4979InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907351/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4979InputLogOnePlusV_eq :
    leaf4979InputLogOnePlusV = outerEnclosure 24
      (leaf4979Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4979RoundedFacts : LeafRoundedFacts 8
    leaf4979Certificate.logOnePlusV leaf4979InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4979InputLogOnePlusV_eq }

private noncomputable def leaf4979Inputs : Inputs :=
  inputsOfCaches globalInput sk223RoundedInputs
    chi285InputQChi innerPair242Input
    leaf4979InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4979LowerChecked :
    lowerCheck 24 leaf4979Box leaf4979Inputs = true := by
  rfl'

private theorem leaf4979CoversExact : CoversExact 8
    leaf4979Box leaf4979Certificate leaf4979InnerLog leaf4979Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk223RoundedFacts chi285RoundedFacts
    innerPair242RoundedFacts leaf4979RoundedFacts (by rfl)

private theorem leaf4979FlatSound : Sound leaf4979Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4979CertificateValid
    leaf4979InnerLogValid leaf4979CoversExact leaf4979LowerChecked

private noncomputable def leaf4980Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (239/64), kHi := (15/4), chiLo := (19/64), chiHi := (77/256) }

private noncomputable def leaf4980Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742457/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714745856) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2264031673/2147483648) }, upper := { exponent := 1, mantissa := (2179/2048) } }, logOuter := sk224LogOuterCertificate, logK := sk224LogKCertificate, logChi := chi285LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432158207/137429491712) } }, logDArg := sk224LogDArgCertificate }

private noncomputable def leaf4980InnerLog : WideLogData :=
  innerPair551Data

set_option maxRecDepth 1000000 in
private theorem leaf4980LocalValidity :
    LeafFacts leaf4980Box leaf4980Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4980Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714745856) }) = true
      norm_num [leaf4980Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4980CertificateValid :
    WideCertificateValid leaf4980Box leaf4980Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk224ValidityFacts chi285ValidityFacts
    leaf4980LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4980CoverageChecked :
    coverageCheck (innerAD leaf4980Box) leaf4980InnerLog = true := by
  rfl'

private theorem leaf4980InnerLogValid :
    leaf4980InnerLog.Valid 8 (innerAD leaf4980Box) :=
  wideLogDataValid_of_cachedCheck endpoint284PositiveFacts
    endpoint289PositiveFacts.valid leaf4980CoverageChecked

private noncomputable def leaf4980InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814703/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4980InputLogOnePlusV_eq :
    leaf4980InputLogOnePlusV = outerEnclosure 24
      (leaf4980Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4980RoundedFacts : LeafRoundedFacts 8
    leaf4980Certificate.logOnePlusV leaf4980InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4980InputLogOnePlusV_eq }

private noncomputable def leaf4980Inputs : Inputs :=
  inputsOfCaches globalInput sk224RoundedInputs
    chi285InputQChi innerPair551Input
    leaf4980InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4980LowerChecked :
    lowerCheck 24 leaf4980Box leaf4980Inputs = true := by
  rfl'

private theorem leaf4980CoversExact : CoversExact 8
    leaf4980Box leaf4980Certificate leaf4980InnerLog leaf4980Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk224RoundedFacts chi285RoundedFacts
    innerPair551RoundedFacts leaf4980RoundedFacts (by rfl)

private theorem leaf4980FlatSound : Sound leaf4980Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4980CertificateValid
    leaf4980InnerLogValid leaf4980CoversExact leaf4980LowerChecked

private noncomputable def leaf4981Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (239/64), chiLo := (77/256), chiHi := (39/128) }

private noncomputable def leaf4981Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742457/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714704384) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2274647857/2147483648) }, upper := { exponent := 1, mantissa := (17513/16384) } }, logOuter := sk223LogOuterCertificate, logK := sk223LogKCertificate, logChi := chi286LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432116735/137429408768) } }, logDArg := sk223LogDArgCertificate }

private noncomputable def leaf4981InnerLog : WideLogData :=
  innerPair243Data

set_option maxRecDepth 1000000 in
private theorem leaf4981LocalValidity :
    LeafFacts leaf4981Box leaf4981Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4981Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714704384) }) = true
      norm_num [leaf4981Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4981CertificateValid :
    WideCertificateValid leaf4981Box leaf4981Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk223ValidityFacts chi286ValidityFacts
    leaf4981LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4981CoverageChecked :
    coverageCheck (innerAD leaf4981Box) leaf4981InnerLog = true := by
  rfl'

private theorem leaf4981InnerLogValid :
    leaf4981InnerLog.Valid 8 (innerAD leaf4981Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint74PositiveFacts.valid leaf4981CoverageChecked

private noncomputable def leaf4981InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629411/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4981InputLogOnePlusV_eq :
    leaf4981InputLogOnePlusV = outerEnclosure 24
      (leaf4981Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4981RoundedFacts : LeafRoundedFacts 8
    leaf4981Certificate.logOnePlusV leaf4981InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4981InputLogOnePlusV_eq }

private noncomputable def leaf4981Inputs : Inputs :=
  inputsOfCaches globalInput sk223RoundedInputs
    chi286InputQChi innerPair243Input
    leaf4981InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4981LowerChecked :
    lowerCheck 24 leaf4981Box leaf4981Inputs = true := by
  rfl'

private theorem leaf4981CoversExact : CoversExact 8
    leaf4981Box leaf4981Certificate leaf4981InnerLog leaf4981Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk223RoundedFacts chi286RoundedFacts
    innerPair243RoundedFacts leaf4981RoundedFacts (by rfl)

private theorem leaf4981FlatSound : Sound leaf4981Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4981CertificateValid
    leaf4981InnerLogValid leaf4981CoversExact leaf4981LowerChecked

private noncomputable def leaf4982Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (239/64), kHi := (15/4), chiLo := (77/256), chiHi := (39/128) }

private noncomputable def leaf4982Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742459/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9816773193/9816383488) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2279693819/2147483648) }, upper := { exponent := 1, mantissa := (1097/1024) } }, logOuter := sk224LogOuterCertificate, logK := sk224LogKCertificate, logChi := chi286LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (19633156681/19632766976) } }, logDArg := sk224LogDArgCertificate }

private noncomputable def leaf4982InnerLog : WideLogData :=
  innerPair243Data

set_option maxRecDepth 1000000 in
private theorem leaf4982LocalValidity :
    LeafFacts leaf4982Box leaf4982Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4982Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9816773193/9816383488) }) = true
      norm_num [leaf4982Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4982CertificateValid :
    WideCertificateValid leaf4982Box leaf4982Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk224ValidityFacts chi286ValidityFacts
    leaf4982LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4982CoverageChecked :
    coverageCheck (innerAD leaf4982Box) leaf4982InnerLog = true := by
  rfl'

private theorem leaf4982InnerLogValid :
    leaf4982InnerLog.Valid 8 (innerAD leaf4982Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint74PositiveFacts.valid leaf4982CoverageChecked

private noncomputable def leaf4982InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814707/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4982InputLogOnePlusV_eq :
    leaf4982InputLogOnePlusV = outerEnclosure 24
      (leaf4982Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4982RoundedFacts : LeafRoundedFacts 8
    leaf4982Certificate.logOnePlusV leaf4982InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4982InputLogOnePlusV_eq }

private noncomputable def leaf4982Inputs : Inputs :=
  inputsOfCaches globalInput sk224RoundedInputs
    chi286InputQChi innerPair243Input
    leaf4982InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4982LowerChecked :
    lowerCheck 24 leaf4982Box leaf4982Inputs = true := by
  rfl'

private theorem leaf4982CoversExact : CoversExact 8
    leaf4982Box leaf4982Certificate leaf4982InnerLog leaf4982Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk224RoundedFacts chi286RoundedFacts
    innerPair243RoundedFacts leaf4982RoundedFacts (by rfl)

private theorem leaf4982FlatSound : Sound leaf4982Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4982CertificateValid
    leaf4982InnerLogValid leaf4982CoversExact leaf4982LowerChecked

private noncomputable def leaf4983Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (237/64), chiLo := (39/128), chiHi := (79/256) }

private noncomputable def leaf4983Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742455/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714683648) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2280021483/2147483648) }, upper := { exponent := 1, mantissa := (35107/32768) } }, logOuter := sk221LogOuterCertificate, logK := sk221LogKCertificate, logChi := chi287LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432095999/137429367296) } }, logDArg := sk221LogDArgCertificate }

private noncomputable def leaf4983InnerLog : WideLogData :=
  innerPair243Data

set_option maxRecDepth 1000000 in
private theorem leaf4983LocalValidity :
    LeafFacts leaf4983Box leaf4983Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4983Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714683648) }) = true
      norm_num [leaf4983Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4983CertificateValid :
    WideCertificateValid leaf4983Box leaf4983Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk221ValidityFacts chi287ValidityFacts
    leaf4983LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4983CoverageChecked :
    coverageCheck (innerAD leaf4983Box) leaf4983InnerLog = true := by
  rfl'

private theorem leaf4983InnerLogValid :
    leaf4983InnerLog.Valid 8 (innerAD leaf4983Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint74PositiveFacts.valid leaf4983CoverageChecked

private noncomputable def leaf4983InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814707/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4983InputLogOnePlusV_eq :
    leaf4983InputLogOnePlusV = outerEnclosure 24
      (leaf4983Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4983RoundedFacts : LeafRoundedFacts 8
    leaf4983Certificate.logOnePlusV leaf4983InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4983InputLogOnePlusV_eq }

private noncomputable def leaf4983Inputs : Inputs :=
  inputsOfCaches globalInput sk221RoundedInputs
    chi287InputQChi innerPair243Input
    leaf4983InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4983LowerChecked :
    lowerCheck 24 leaf4983Box leaf4983Inputs = true := by
  rfl'

private theorem leaf4983CoversExact : CoversExact 8
    leaf4983Box leaf4983Certificate leaf4983InnerLog leaf4983Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk221RoundedFacts chi287RoundedFacts
    innerPair243RoundedFacts leaf4983RoundedFacts (by rfl)

private theorem leaf4983FlatSound : Sound leaf4983Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4983CertificateValid
    leaf4983InnerLogValid leaf4983CoversExact leaf4983LowerChecked

private noncomputable def leaf4984Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (237/64), kHi := (119/32), chiLo := (39/128), chiHi := (79/256) }

private noncomputable def leaf4984Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742457/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22905804117/22904887808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2285132977/2147483648) }, upper := { exponent := 1, mantissa := (17593/16384) } }, logOuter := sk222LogOuterCertificate, logK := sk222LogKCertificate, logChi := chi287LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45810691925/45809775616) } }, logDArg := sk222LogDArgCertificate }

private noncomputable def leaf4984InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf4984LocalValidity :
    LeafFacts leaf4984Box leaf4984Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4984Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22905804117/22904887808) }) = true
      norm_num [leaf4984Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4984CertificateValid :
    WideCertificateValid leaf4984Box leaf4984Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk222ValidityFacts chi287ValidityFacts
    leaf4984LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4984CoverageChecked :
    coverageCheck (innerAD leaf4984Box) leaf4984InnerLog = true := by
  rfl'

private theorem leaf4984InnerLogValid :
    leaf4984InnerLog.Valid 8 (innerAD leaf4984Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf4984CoverageChecked

private noncomputable def leaf4984InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453677/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf4984InputLogOnePlusV_eq :
    leaf4984InputLogOnePlusV = outerEnclosure 24
      (leaf4984Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4984RoundedFacts : LeafRoundedFacts 8
    leaf4984Certificate.logOnePlusV leaf4984InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4984InputLogOnePlusV_eq }

private noncomputable def leaf4984Inputs : Inputs :=
  inputsOfCaches globalInput sk222RoundedInputs
    chi287InputQChi innerPair249Input
    leaf4984InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4984LowerChecked :
    lowerCheck 24 leaf4984Box leaf4984Inputs = true := by
  rfl'

private theorem leaf4984CoversExact : CoversExact 8
    leaf4984Box leaf4984Certificate leaf4984InnerLog leaf4984Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk222RoundedFacts chi287RoundedFacts
    innerPair249RoundedFacts leaf4984RoundedFacts (by rfl)

private theorem leaf4984FlatSound : Sound leaf4984Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4984CertificateValid
    leaf4984InnerLogValid leaf4984CoversExact leaf4984LowerChecked

private noncomputable def leaf4985Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (237/64), chiLo := (79/256), chiHi := (5/16) }

private noncomputable def leaf4985Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742457/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714622976) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2295487033/2147483648) }, upper := { exponent := 1, mantissa := (2209/2048) } }, logOuter := sk221LogOuterCertificate, logK := sk221LogKCertificate, logChi := chi288LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432035327/137429245952) } }, logDArg := sk221LogDArgCertificate }

private noncomputable def leaf4985InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf4985LocalValidity :
    LeafFacts leaf4985Box leaf4985Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4985Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714622976) }) = true
      norm_num [leaf4985Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4985CertificateValid :
    WideCertificateValid leaf4985Box leaf4985Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk221ValidityFacts chi288ValidityFacts
    leaf4985LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4985CoverageChecked :
    coverageCheck (innerAD leaf4985Box) leaf4985InnerLog = true := by
  rfl'

private theorem leaf4985InnerLogValid :
    leaf4985InnerLog.Valid 8 (innerAD leaf4985Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf4985CoverageChecked

private noncomputable def leaf4985InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629421/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4985InputLogOnePlusV_eq :
    leaf4985InputLogOnePlusV = outerEnclosure 24
      (leaf4985Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4985RoundedFacts : LeafRoundedFacts 8
    leaf4985Certificate.logOnePlusV leaf4985InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4985InputLogOnePlusV_eq }

private noncomputable def leaf4985Inputs : Inputs :=
  inputsOfCaches globalInput sk221RoundedInputs
    chi288InputQChi innerPair249Input
    leaf4985InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4985LowerChecked :
    lowerCheck 24 leaf4985Box leaf4985Inputs = true := by
  rfl'

private theorem leaf4985CoversExact : CoversExact 8
    leaf4985Box leaf4985Certificate leaf4985InnerLog leaf4985Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk221RoundedFacts chi288RoundedFacts
    innerPair249RoundedFacts leaf4985RoundedFacts (by rfl)

private theorem leaf4985FlatSound : Sound leaf4985Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4985CertificateValid
    leaf4985InnerLogValid leaf4985CoversExact leaf4985LowerChecked

private noncomputable def leaf4986Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (237/64), kHi := (119/32), chiLo := (79/256), chiHi := (5/16) }

private noncomputable def leaf4986Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742459/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714602496) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2300664059/2147483648) }, upper := { exponent := 1, mantissa := (1107/1024) } }, logOuter := sk222LogOuterCertificate, logK := sk222LogKCertificate, logChi := chi288LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432014847/137429204992) } }, logDArg := sk222LogDArgCertificate }

private noncomputable def leaf4986InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf4986LocalValidity :
    LeafFacts leaf4986Box leaf4986Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4986Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714602496) }) = true
      norm_num [leaf4986Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4986CertificateValid :
    WideCertificateValid leaf4986Box leaf4986Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk222ValidityFacts chi288ValidityFacts
    leaf4986LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4986CoverageChecked :
    coverageCheck (innerAD leaf4986Box) leaf4986InnerLog = true := by
  rfl'

private theorem leaf4986InnerLogValid :
    leaf4986InnerLog.Valid 8 (innerAD leaf4986Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf4986CoverageChecked

private noncomputable def leaf4986InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726839/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf4986InputLogOnePlusV_eq :
    leaf4986InputLogOnePlusV = outerEnclosure 24
      (leaf4986Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4986RoundedFacts : LeafRoundedFacts 8
    leaf4986Certificate.logOnePlusV leaf4986InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4986InputLogOnePlusV_eq }

private noncomputable def leaf4986Inputs : Inputs :=
  inputsOfCaches globalInput sk222RoundedInputs
    chi288InputQChi innerPair249Input
    leaf4986InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4986LowerChecked :
    lowerCheck 24 leaf4986Box leaf4986Inputs = true := by
  rfl'

private theorem leaf4986CoversExact : CoversExact 8
    leaf4986Box leaf4986Certificate leaf4986InnerLog leaf4986Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk222RoundedFacts chi288RoundedFacts
    innerPair249RoundedFacts leaf4986RoundedFacts (by rfl)

private theorem leaf4986FlatSound : Sound leaf4986Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4986CertificateValid
    leaf4986InnerLogValid leaf4986CoversExact leaf4986LowerChecked

private noncomputable def leaf4987Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (239/64), chiLo := (39/128), chiHi := (79/256) }

private noncomputable def leaf4987Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742459/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9816773193/9816377600) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2290244471/2147483648) }, upper := { exponent := 1, mantissa := (35265/32768) } }, logOuter := sk223LogOuterCertificate, logK := sk223LogKCertificate, logChi := chi287LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (19633150793/19632755200) } }, logDArg := sk223LogDArgCertificate }

private noncomputable def leaf4987InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf4987LocalValidity :
    LeafFacts leaf4987Box leaf4987Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4987Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9816773193/9816377600) }) = true
      norm_num [leaf4987Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4987CertificateValid :
    WideCertificateValid leaf4987Box leaf4987Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk223ValidityFacts chi287ValidityFacts
    leaf4987LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4987CoverageChecked :
    coverageCheck (innerAD leaf4987Box) leaf4987InnerLog = true := by
  rfl'

private theorem leaf4987InnerLogValid :
    leaf4987InnerLog.Valid 8 (innerAD leaf4987Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf4987CoverageChecked

private noncomputable def leaf4987InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629419/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4987InputLogOnePlusV_eq :
    leaf4987InputLogOnePlusV = outerEnclosure 24
      (leaf4987Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4987RoundedFacts : LeafRoundedFacts 8
    leaf4987Certificate.logOnePlusV leaf4987InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4987InputLogOnePlusV_eq }

private noncomputable def leaf4987Inputs : Inputs :=
  inputsOfCaches globalInput sk223RoundedInputs
    chi287InputQChi innerPair249Input
    leaf4987InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4987LowerChecked :
    lowerCheck 24 leaf4987Box leaf4987Inputs = true := by
  rfl'

private theorem leaf4987CoversExact : CoversExact 8
    leaf4987Box leaf4987Certificate leaf4987InnerLog leaf4987Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk223RoundedFacts chi287RoundedFacts
    innerPair249RoundedFacts leaf4987RoundedFacts (by rfl)

private theorem leaf4987FlatSound : Sound leaf4987Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4987CertificateValid
    leaf4987InnerLogValid leaf4987CoversExact leaf4987LowerChecked

private noncomputable def leaf4988Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (239/64), kHi := (15/4), chiLo := (39/128), chiHi := (79/256) }

private noncomputable def leaf4988Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742461/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714622976) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2295355965/2147483648) }, upper := { exponent := 1, mantissa := (2209/2048) } }, logOuter := sk224LogOuterCertificate, logK := sk224LogKCertificate, logChi := chi287LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432035327/137429245952) } }, logDArg := sk224LogDArgCertificate }

private noncomputable def leaf4988InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf4988LocalValidity :
    LeafFacts leaf4988Box leaf4988Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4988Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714622976) }) = true
      norm_num [leaf4988Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4988CertificateValid :
    WideCertificateValid leaf4988Box leaf4988Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk224ValidityFacts chi287ValidityFacts
    leaf4988LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4988CoverageChecked :
    coverageCheck (innerAD leaf4988Box) leaf4988InnerLog = true := by
  rfl'

private theorem leaf4988InnerLogValid :
    leaf4988InnerLog.Valid 8 (innerAD leaf4988Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf4988CoverageChecked

private noncomputable def leaf4988InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629421/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4988InputLogOnePlusV_eq :
    leaf4988InputLogOnePlusV = outerEnclosure 24
      (leaf4988Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4988RoundedFacts : LeafRoundedFacts 8
    leaf4988Certificate.logOnePlusV leaf4988InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4988InputLogOnePlusV_eq }

private noncomputable def leaf4988Inputs : Inputs :=
  inputsOfCaches globalInput sk224RoundedInputs
    chi287InputQChi innerPair249Input
    leaf4988InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4988LowerChecked :
    lowerCheck 24 leaf4988Box leaf4988Inputs = true := by
  rfl'

private theorem leaf4988CoversExact : CoversExact 8
    leaf4988Box leaf4988Certificate leaf4988InnerLog leaf4988Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk224RoundedFacts chi287RoundedFacts
    innerPair249RoundedFacts leaf4988RoundedFacts (by rfl)

private theorem leaf4988FlatSound : Sound leaf4988Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4988CertificateValid
    leaf4988InnerLogValid leaf4988CoversExact leaf4988LowerChecked

private noncomputable def leaf4989Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (239/64), chiLo := (79/256), chiHi := (5/16) }

private noncomputable def leaf4989Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742461/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22905804117/22904860672) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2305841085/2147483648) }, upper := { exponent := 1, mantissa := (2219/2048) } }, logOuter := sk223LogOuterCertificate, logK := sk223LogKCertificate, logChi := chi288LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45810664789/45809721344) } }, logDArg := sk223LogDArgCertificate }

private noncomputable def leaf4989InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf4989LocalValidity :
    LeafFacts leaf4989Box leaf4989Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4989Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22905804117/22904860672) }) = true
      norm_num [leaf4989Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4989CertificateValid :
    WideCertificateValid leaf4989Box leaf4989Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk223ValidityFacts chi288ValidityFacts
    leaf4989LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4989CoverageChecked :
    coverageCheck (innerAD leaf4989Box) leaf4989InnerLog = true := by
  rfl'

private theorem leaf4989InnerLogValid :
    leaf4989InnerLog.Valid 8 (innerAD leaf4989Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf4989CoverageChecked

private noncomputable def leaf4989InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814713/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4989InputLogOnePlusV_eq :
    leaf4989InputLogOnePlusV = outerEnclosure 24
      (leaf4989Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4989RoundedFacts : LeafRoundedFacts 8
    leaf4989Certificate.logOnePlusV leaf4989InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4989InputLogOnePlusV_eq }

private noncomputable def leaf4989Inputs : Inputs :=
  inputsOfCaches globalInput sk223RoundedInputs
    chi288InputQChi innerPair249Input
    leaf4989InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4989LowerChecked :
    lowerCheck 24 leaf4989Box leaf4989Inputs = true := by
  rfl'

private theorem leaf4989CoversExact : CoversExact 8
    leaf4989Box leaf4989Certificate leaf4989InnerLog leaf4989Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk223RoundedFacts chi288RoundedFacts
    innerPair249RoundedFacts leaf4989RoundedFacts (by rfl)

private theorem leaf4989FlatSound : Sound leaf4989Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4989CertificateValid
    leaf4989InnerLogValid leaf4989CoversExact leaf4989LowerChecked

private noncomputable def leaf4990Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (239/64), kHi := (15/4), chiLo := (79/256), chiHi := (5/16) }

private noncomputable def leaf4990Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742463/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714561536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2311018111/2147483648) }, upper := { exponent := 1, mantissa := (139/128) } }, logOuter := sk224LogOuterCertificate, logK := sk224LogKCertificate, logChi := chi288LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431973887/137429123072) } }, logDArg := sk224LogDArgCertificate }

private noncomputable def leaf4990InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf4990LocalValidity :
    LeafFacts leaf4990Box leaf4990Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4990Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714561536) }) = true
      norm_num [leaf4990Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4990CertificateValid :
    WideCertificateValid leaf4990Box leaf4990Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk224ValidityFacts chi288ValidityFacts
    leaf4990LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4990CoverageChecked :
    coverageCheck (innerAD leaf4990Box) leaf4990InnerLog = true := by
  rfl'

private theorem leaf4990InnerLogValid :
    leaf4990InnerLog.Valid 8 (innerAD leaf4990Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf4990CoverageChecked

private noncomputable def leaf4990InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629429/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4990InputLogOnePlusV_eq :
    leaf4990InputLogOnePlusV = outerEnclosure 24
      (leaf4990Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4990RoundedFacts : LeafRoundedFacts 8
    leaf4990Certificate.logOnePlusV leaf4990InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4990InputLogOnePlusV_eq }

private noncomputable def leaf4990Inputs : Inputs :=
  inputsOfCaches globalInput sk224RoundedInputs
    chi288InputQChi innerPair249Input
    leaf4990InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4990LowerChecked :
    lowerCheck 24 leaf4990Box leaf4990Inputs = true := by
  rfl'

private theorem leaf4990CoversExact : CoversExact 8
    leaf4990Box leaf4990Certificate leaf4990InnerLog leaf4990Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk224RoundedFacts chi288RoundedFacts
    innerPair249RoundedFacts leaf4990RoundedFacts (by rfl)

private theorem leaf4990FlatSound : Sound leaf4990Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4990CertificateValid
    leaf4990InnerLogValid leaf4990CoversExact leaf4990LowerChecked

private noncomputable def component101Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (9/32), chiHi := (73/256) }

set_option maxRecDepth 1000000 in
private theorem component101Node0_sound : Sound component101Node0Box :=
  sound_of_literal_split component101Node0Box leaf4927Box leaf4928Box
    .k (233/64) (by rfl) (by rfl)
    leaf4927FlatSound leaf4928FlatSound

private noncomputable def component101Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (73/256), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component101Node1_sound : Sound component101Node1Box :=
  sound_of_literal_split component101Node1Box leaf4929Box leaf4930Box
    .k (233/64) (by rfl) (by rfl)
    leaf4929FlatSound leaf4930FlatSound

private noncomputable def component101Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (9/32), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component101Node2_sound : Sound component101Node2Box :=
  sound_of_literal_split component101Node2Box component101Node0Box component101Node1Box
    .chi (73/256) (by rfl) (by rfl)
    component101Node0_sound component101Node1_sound

private noncomputable def component101Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (9/32), chiHi := (73/256) }

set_option maxRecDepth 1000000 in
private theorem component101Node3_sound : Sound component101Node3Box :=
  sound_of_literal_split component101Node3Box leaf4931Box leaf4932Box
    .k (235/64) (by rfl) (by rfl)
    leaf4931FlatSound leaf4932FlatSound

private noncomputable def component101Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (73/256), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component101Node4_sound : Sound component101Node4Box :=
  sound_of_literal_split component101Node4Box leaf4933Box leaf4934Box
    .k (235/64) (by rfl) (by rfl)
    leaf4933FlatSound leaf4934FlatSound

private noncomputable def component101Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (9/32), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component101Node5_sound : Sound component101Node5Box :=
  sound_of_literal_split component101Node5Box component101Node3Box component101Node4Box
    .chi (73/256) (by rfl) (by rfl)
    component101Node3_sound component101Node4_sound

private noncomputable def component101Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (9/32), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component101Node6_sound : Sound component101Node6Box :=
  sound_of_literal_split component101Node6Box component101Node2Box component101Node5Box
    .k (117/32) (by rfl) (by rfl)
    component101Node2_sound component101Node5_sound

private noncomputable def component101Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (37/128), chiHi := (75/256) }

set_option maxRecDepth 1000000 in
private theorem component101Node7_sound : Sound component101Node7Box :=
  sound_of_literal_split component101Node7Box leaf4935Box leaf4936Box
    .k (233/64) (by rfl) (by rfl)
    leaf4935FlatSound leaf4936FlatSound

private noncomputable def component101Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (75/256), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component101Node8_sound : Sound component101Node8Box :=
  sound_of_literal_split component101Node8Box leaf4937Box leaf4938Box
    .k (233/64) (by rfl) (by rfl)
    leaf4937FlatSound leaf4938FlatSound

private noncomputable def component101Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (37/128), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component101Node9_sound : Sound component101Node9Box :=
  sound_of_literal_split component101Node9Box component101Node7Box component101Node8Box
    .chi (75/256) (by rfl) (by rfl)
    component101Node7_sound component101Node8_sound

private noncomputable def component101Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (37/128), chiHi := (75/256) }

set_option maxRecDepth 1000000 in
private theorem component101Node10_sound : Sound component101Node10Box :=
  sound_of_literal_split component101Node10Box leaf4939Box leaf4940Box
    .k (235/64) (by rfl) (by rfl)
    leaf4939FlatSound leaf4940FlatSound

private noncomputable def component101Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (75/256), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component101Node11_sound : Sound component101Node11Box :=
  sound_of_literal_split component101Node11Box leaf4941Box leaf4942Box
    .k (235/64) (by rfl) (by rfl)
    leaf4941FlatSound leaf4942FlatSound

private noncomputable def component101Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (37/128), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component101Node12_sound : Sound component101Node12Box :=
  sound_of_literal_split component101Node12Box component101Node10Box component101Node11Box
    .chi (75/256) (by rfl) (by rfl)
    component101Node10_sound component101Node11_sound

private noncomputable def component101Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (37/128), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component101Node13_sound : Sound component101Node13Box :=
  sound_of_literal_split component101Node13Box component101Node9Box component101Node12Box
    .k (117/32) (by rfl) (by rfl)
    component101Node9_sound component101Node12_sound

private noncomputable def component101Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (9/32), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component101Node14_sound : Sound component101Node14Box :=
  sound_of_literal_split component101Node14Box component101Node6Box component101Node13Box
    .chi (37/128) (by rfl) (by rfl)
    component101Node6_sound component101Node13_sound

private noncomputable def component101Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (9/32), chiHi := (73/256) }

set_option maxRecDepth 1000000 in
private theorem component101Node15_sound : Sound component101Node15Box :=
  sound_of_literal_split component101Node15Box leaf4943Box leaf4944Box
    .k (237/64) (by rfl) (by rfl)
    leaf4943FlatSound leaf4944FlatSound

private noncomputable def component101Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (73/256), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component101Node16_sound : Sound component101Node16Box :=
  sound_of_literal_split component101Node16Box leaf4945Box leaf4946Box
    .k (237/64) (by rfl) (by rfl)
    leaf4945FlatSound leaf4946FlatSound

private noncomputable def component101Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (9/32), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component101Node17_sound : Sound component101Node17Box :=
  sound_of_literal_split component101Node17Box component101Node15Box component101Node16Box
    .chi (73/256) (by rfl) (by rfl)
    component101Node15_sound component101Node16_sound

private noncomputable def component101Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (9/32), chiHi := (73/256) }

set_option maxRecDepth 1000000 in
private theorem component101Node18_sound : Sound component101Node18Box :=
  sound_of_literal_split component101Node18Box leaf4947Box leaf4948Box
    .k (239/64) (by rfl) (by rfl)
    leaf4947FlatSound leaf4948FlatSound

private noncomputable def component101Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (73/256), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component101Node19_sound : Sound component101Node19Box :=
  sound_of_literal_split component101Node19Box leaf4949Box leaf4950Box
    .k (239/64) (by rfl) (by rfl)
    leaf4949FlatSound leaf4950FlatSound

private noncomputable def component101Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (9/32), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component101Node20_sound : Sound component101Node20Box :=
  sound_of_literal_split component101Node20Box component101Node18Box component101Node19Box
    .chi (73/256) (by rfl) (by rfl)
    component101Node18_sound component101Node19_sound

private noncomputable def component101Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (9/32), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component101Node21_sound : Sound component101Node21Box :=
  sound_of_literal_split component101Node21Box component101Node17Box component101Node20Box
    .k (119/32) (by rfl) (by rfl)
    component101Node17_sound component101Node20_sound

private noncomputable def component101Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (37/128), chiHi := (75/256) }

set_option maxRecDepth 1000000 in
private theorem component101Node22_sound : Sound component101Node22Box :=
  sound_of_literal_split component101Node22Box leaf4951Box leaf4952Box
    .k (237/64) (by rfl) (by rfl)
    leaf4951FlatSound leaf4952FlatSound

private noncomputable def component101Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (75/256), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component101Node23_sound : Sound component101Node23Box :=
  sound_of_literal_split component101Node23Box leaf4953Box leaf4954Box
    .k (237/64) (by rfl) (by rfl)
    leaf4953FlatSound leaf4954FlatSound

private noncomputable def component101Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (37/128), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component101Node24_sound : Sound component101Node24Box :=
  sound_of_literal_split component101Node24Box component101Node22Box component101Node23Box
    .chi (75/256) (by rfl) (by rfl)
    component101Node22_sound component101Node23_sound

private noncomputable def component101Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (37/128), chiHi := (75/256) }

set_option maxRecDepth 1000000 in
private theorem component101Node25_sound : Sound component101Node25Box :=
  sound_of_literal_split component101Node25Box leaf4955Box leaf4956Box
    .k (239/64) (by rfl) (by rfl)
    leaf4955FlatSound leaf4956FlatSound

private noncomputable def component101Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (75/256), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component101Node26_sound : Sound component101Node26Box :=
  sound_of_literal_split component101Node26Box leaf4957Box leaf4958Box
    .k (239/64) (by rfl) (by rfl)
    leaf4957FlatSound leaf4958FlatSound

private noncomputable def component101Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (37/128), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component101Node27_sound : Sound component101Node27Box :=
  sound_of_literal_split component101Node27Box component101Node25Box component101Node26Box
    .chi (75/256) (by rfl) (by rfl)
    component101Node25_sound component101Node26_sound

private noncomputable def component101Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (37/128), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component101Node28_sound : Sound component101Node28Box :=
  sound_of_literal_split component101Node28Box component101Node24Box component101Node27Box
    .k (119/32) (by rfl) (by rfl)
    component101Node24_sound component101Node27_sound

private noncomputable def component101Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (9/32), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component101Node29_sound : Sound component101Node29Box :=
  sound_of_literal_split component101Node29Box component101Node21Box component101Node28Box
    .chi (37/128) (by rfl) (by rfl)
    component101Node21_sound component101Node28_sound

private noncomputable def component101Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (9/32), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component101Node30_sound : Sound component101Node30Box :=
  sound_of_literal_split component101Node30Box component101Node14Box component101Node29Box
    .k (59/16) (by rfl) (by rfl)
    component101Node14_sound component101Node29_sound

private noncomputable def component101Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (19/64), chiHi := (77/256) }

set_option maxRecDepth 1000000 in
private theorem component101Node31_sound : Sound component101Node31Box :=
  sound_of_literal_split component101Node31Box leaf4959Box leaf4960Box
    .k (233/64) (by rfl) (by rfl)
    leaf4959FlatSound leaf4960FlatSound

private noncomputable def component101Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (77/256), chiHi := (39/128) }

set_option maxRecDepth 1000000 in
private theorem component101Node32_sound : Sound component101Node32Box :=
  sound_of_literal_split component101Node32Box leaf4961Box leaf4962Box
    .k (233/64) (by rfl) (by rfl)
    leaf4961FlatSound leaf4962FlatSound

private noncomputable def component101Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (19/64), chiHi := (39/128) }

set_option maxRecDepth 1000000 in
private theorem component101Node33_sound : Sound component101Node33Box :=
  sound_of_literal_split component101Node33Box component101Node31Box component101Node32Box
    .chi (77/256) (by rfl) (by rfl)
    component101Node31_sound component101Node32_sound

private noncomputable def component101Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (19/64), chiHi := (77/256) }

set_option maxRecDepth 1000000 in
private theorem component101Node34_sound : Sound component101Node34Box :=
  sound_of_literal_split component101Node34Box leaf4963Box leaf4964Box
    .k (235/64) (by rfl) (by rfl)
    leaf4963FlatSound leaf4964FlatSound

private noncomputable def component101Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (77/256), chiHi := (39/128) }

set_option maxRecDepth 1000000 in
private theorem component101Node35_sound : Sound component101Node35Box :=
  sound_of_literal_split component101Node35Box leaf4965Box leaf4966Box
    .k (235/64) (by rfl) (by rfl)
    leaf4965FlatSound leaf4966FlatSound

private noncomputable def component101Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (19/64), chiHi := (39/128) }

set_option maxRecDepth 1000000 in
private theorem component101Node36_sound : Sound component101Node36Box :=
  sound_of_literal_split component101Node36Box component101Node34Box component101Node35Box
    .chi (77/256) (by rfl) (by rfl)
    component101Node34_sound component101Node35_sound

private noncomputable def component101Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (19/64), chiHi := (39/128) }

set_option maxRecDepth 1000000 in
private theorem component101Node37_sound : Sound component101Node37Box :=
  sound_of_literal_split component101Node37Box component101Node33Box component101Node36Box
    .k (117/32) (by rfl) (by rfl)
    component101Node33_sound component101Node36_sound

private noncomputable def component101Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (39/128), chiHi := (79/256) }

set_option maxRecDepth 1000000 in
private theorem component101Node38_sound : Sound component101Node38Box :=
  sound_of_literal_split component101Node38Box leaf4967Box leaf4968Box
    .k (233/64) (by rfl) (by rfl)
    leaf4967FlatSound leaf4968FlatSound

private noncomputable def component101Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (79/256), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component101Node39_sound : Sound component101Node39Box :=
  sound_of_literal_split component101Node39Box leaf4969Box leaf4970Box
    .k (233/64) (by rfl) (by rfl)
    leaf4969FlatSound leaf4970FlatSound

private noncomputable def component101Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (39/128), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component101Node40_sound : Sound component101Node40Box :=
  sound_of_literal_split component101Node40Box component101Node38Box component101Node39Box
    .chi (79/256) (by rfl) (by rfl)
    component101Node38_sound component101Node39_sound

private noncomputable def component101Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (39/128), chiHi := (79/256) }

set_option maxRecDepth 1000000 in
private theorem component101Node41_sound : Sound component101Node41Box :=
  sound_of_literal_split component101Node41Box leaf4971Box leaf4972Box
    .k (235/64) (by rfl) (by rfl)
    leaf4971FlatSound leaf4972FlatSound

private noncomputable def component101Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (79/256), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component101Node42_sound : Sound component101Node42Box :=
  sound_of_literal_split component101Node42Box leaf4973Box leaf4974Box
    .k (235/64) (by rfl) (by rfl)
    leaf4973FlatSound leaf4974FlatSound

private noncomputable def component101Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (39/128), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component101Node43_sound : Sound component101Node43Box :=
  sound_of_literal_split component101Node43Box component101Node41Box component101Node42Box
    .chi (79/256) (by rfl) (by rfl)
    component101Node41_sound component101Node42_sound

private noncomputable def component101Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (39/128), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component101Node44_sound : Sound component101Node44Box :=
  sound_of_literal_split component101Node44Box component101Node40Box component101Node43Box
    .k (117/32) (by rfl) (by rfl)
    component101Node40_sound component101Node43_sound

private noncomputable def component101Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (19/64), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component101Node45_sound : Sound component101Node45Box :=
  sound_of_literal_split component101Node45Box component101Node37Box component101Node44Box
    .chi (39/128) (by rfl) (by rfl)
    component101Node37_sound component101Node44_sound

private noncomputable def component101Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (19/64), chiHi := (77/256) }

set_option maxRecDepth 1000000 in
private theorem component101Node46_sound : Sound component101Node46Box :=
  sound_of_literal_split component101Node46Box leaf4975Box leaf4976Box
    .k (237/64) (by rfl) (by rfl)
    leaf4975FlatSound leaf4976FlatSound

private noncomputable def component101Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (77/256), chiHi := (39/128) }

set_option maxRecDepth 1000000 in
private theorem component101Node47_sound : Sound component101Node47Box :=
  sound_of_literal_split component101Node47Box leaf4977Box leaf4978Box
    .k (237/64) (by rfl) (by rfl)
    leaf4977FlatSound leaf4978FlatSound

private noncomputable def component101Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (19/64), chiHi := (39/128) }

set_option maxRecDepth 1000000 in
private theorem component101Node48_sound : Sound component101Node48Box :=
  sound_of_literal_split component101Node48Box component101Node46Box component101Node47Box
    .chi (77/256) (by rfl) (by rfl)
    component101Node46_sound component101Node47_sound

private noncomputable def component101Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (19/64), chiHi := (77/256) }

set_option maxRecDepth 1000000 in
private theorem component101Node49_sound : Sound component101Node49Box :=
  sound_of_literal_split component101Node49Box leaf4979Box leaf4980Box
    .k (239/64) (by rfl) (by rfl)
    leaf4979FlatSound leaf4980FlatSound

private noncomputable def component101Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (77/256), chiHi := (39/128) }

set_option maxRecDepth 1000000 in
private theorem component101Node50_sound : Sound component101Node50Box :=
  sound_of_literal_split component101Node50Box leaf4981Box leaf4982Box
    .k (239/64) (by rfl) (by rfl)
    leaf4981FlatSound leaf4982FlatSound

private noncomputable def component101Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (19/64), chiHi := (39/128) }

set_option maxRecDepth 1000000 in
private theorem component101Node51_sound : Sound component101Node51Box :=
  sound_of_literal_split component101Node51Box component101Node49Box component101Node50Box
    .chi (77/256) (by rfl) (by rfl)
    component101Node49_sound component101Node50_sound

private noncomputable def component101Node52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (19/64), chiHi := (39/128) }

set_option maxRecDepth 1000000 in
private theorem component101Node52_sound : Sound component101Node52Box :=
  sound_of_literal_split component101Node52Box component101Node48Box component101Node51Box
    .k (119/32) (by rfl) (by rfl)
    component101Node48_sound component101Node51_sound

private noncomputable def component101Node53Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (39/128), chiHi := (79/256) }

set_option maxRecDepth 1000000 in
private theorem component101Node53_sound : Sound component101Node53Box :=
  sound_of_literal_split component101Node53Box leaf4983Box leaf4984Box
    .k (237/64) (by rfl) (by rfl)
    leaf4983FlatSound leaf4984FlatSound

private noncomputable def component101Node54Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (79/256), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component101Node54_sound : Sound component101Node54Box :=
  sound_of_literal_split component101Node54Box leaf4985Box leaf4986Box
    .k (237/64) (by rfl) (by rfl)
    leaf4985FlatSound leaf4986FlatSound

private noncomputable def component101Node55Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (39/128), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component101Node55_sound : Sound component101Node55Box :=
  sound_of_literal_split component101Node55Box component101Node53Box component101Node54Box
    .chi (79/256) (by rfl) (by rfl)
    component101Node53_sound component101Node54_sound

private noncomputable def component101Node56Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (39/128), chiHi := (79/256) }

set_option maxRecDepth 1000000 in
private theorem component101Node56_sound : Sound component101Node56Box :=
  sound_of_literal_split component101Node56Box leaf4987Box leaf4988Box
    .k (239/64) (by rfl) (by rfl)
    leaf4987FlatSound leaf4988FlatSound

private noncomputable def component101Node57Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (79/256), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component101Node57_sound : Sound component101Node57Box :=
  sound_of_literal_split component101Node57Box leaf4989Box leaf4990Box
    .k (239/64) (by rfl) (by rfl)
    leaf4989FlatSound leaf4990FlatSound

private noncomputable def component101Node58Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (39/128), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component101Node58_sound : Sound component101Node58Box :=
  sound_of_literal_split component101Node58Box component101Node56Box component101Node57Box
    .chi (79/256) (by rfl) (by rfl)
    component101Node56_sound component101Node57_sound

private noncomputable def component101Node59Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (39/128), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component101Node59_sound : Sound component101Node59Box :=
  sound_of_literal_split component101Node59Box component101Node55Box component101Node58Box
    .k (119/32) (by rfl) (by rfl)
    component101Node55_sound component101Node58_sound

private noncomputable def component101Node60Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (19/64), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component101Node60_sound : Sound component101Node60Box :=
  sound_of_literal_split component101Node60Box component101Node52Box component101Node59Box
    .chi (39/128) (by rfl) (by rfl)
    component101Node52_sound component101Node59_sound

private noncomputable def component101Node61Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (19/64), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component101Node61_sound : Sound component101Node61Box :=
  sound_of_literal_split component101Node61Box component101Node45Box component101Node60Box
    .k (59/16) (by rfl) (by rfl)
    component101Node45_sound component101Node60_sound

noncomputable def component101Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (9/32), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
theorem component101_sound : Sound component101Box :=
  sound_of_literal_split component101Box component101Node30Box component101Node61Box
    .chi (19/64) (by rfl) (by rfl)
    component101Node30_sound component101Node61_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
