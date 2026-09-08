import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch5
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch5
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch8
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch9
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheSKBatch2
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

private noncomputable def leaf4877Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (225/64), chiLo := (9/32), chiHi := (73/256) }

private noncomputable def leaf4877Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742419/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715271936) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2130608559/1073741824) }, upper := { exponent := 1, mantissa := (32809/32768) } }, logOuter := sk213LogOuterCertificate, logK := sk213LogKCertificate, logChi := chi281LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432684287/137430543872) } }, logDArg := sk213LogDArgCertificate }

private noncomputable def leaf4877InnerLog : WideLogData :=
  innerPair110Data

set_option maxRecDepth 1000000 in
private theorem leaf4877LocalValidity :
    LeafFacts leaf4877Box leaf4877Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4877Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715271936) }) = true
      norm_num [leaf4877Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4877CertificateValid :
    WideCertificateValid leaf4877Box leaf4877Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk213ValidityFacts chi281ValidityFacts
    leaf4877LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4877CoverageChecked :
    coverageCheck (innerAD leaf4877Box) leaf4877InnerLog = true := by
  rfl'

private theorem leaf4877InnerLogValid :
    leaf4877InnerLog.Valid 8 (innerAD leaf4877Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint72PositiveFacts.valid leaf4877CoverageChecked

private noncomputable def leaf4877InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814671/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4877InputLogOnePlusV_eq :
    leaf4877InputLogOnePlusV = outerEnclosure 24
      (leaf4877Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4877RoundedFacts : LeafRoundedFacts 8
    leaf4877Certificate.logOnePlusV leaf4877InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4877InputLogOnePlusV_eq }

private noncomputable def leaf4877Inputs : Inputs :=
  inputsOfCaches globalInput sk213RoundedInputs
    chi281InputQChi innerPair110Input
    leaf4877InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4877LowerChecked :
    lowerCheck 24 leaf4877Box leaf4877Inputs = true := by
  rfl'

private theorem leaf4877CoversExact : CoversExact 8
    leaf4877Box leaf4877Certificate leaf4877InnerLog leaf4877Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk213RoundedFacts chi281RoundedFacts
    innerPair110RoundedFacts leaf4877RoundedFacts (by rfl)

private theorem leaf4877FlatSound : Sound leaf4877Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4877CertificateValid
    leaf4877InnerLogValid leaf4877CoversExact leaf4877LowerChecked

private noncomputable def leaf4878Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (225/64), kHi := (113/32), chiLo := (9/32), chiHi := (73/256) }

private noncomputable def leaf4878Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742421/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22905804117/22905084416) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2135326861/1073741824) }, upper := { exponent := 1, mantissa := (16441/16384) } }, logOuter := sk214LogOuterCertificate, logK := sk214LogKCertificate, logChi := chi281LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45810888533/45810168832) } }, logDArg := sk214LogDArgCertificate }

private noncomputable def leaf4878InnerLog : WideLogData :=
  innerPair110Data

set_option maxRecDepth 1000000 in
private theorem leaf4878LocalValidity :
    LeafFacts leaf4878Box leaf4878Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4878Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22905804117/22905084416) }) = true
      norm_num [leaf4878Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4878CertificateValid :
    WideCertificateValid leaf4878Box leaf4878Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk214ValidityFacts chi281ValidityFacts
    leaf4878LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4878CoverageChecked :
    coverageCheck (innerAD leaf4878Box) leaf4878InnerLog = true := by
  rfl'

private theorem leaf4878InnerLogValid :
    leaf4878InnerLog.Valid 8 (innerAD leaf4878Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint72PositiveFacts.valid leaf4878CoverageChecked

private noncomputable def leaf4878InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (363417/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf4878InputLogOnePlusV_eq :
    leaf4878InputLogOnePlusV = outerEnclosure 24
      (leaf4878Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4878RoundedFacts : LeafRoundedFacts 8
    leaf4878Certificate.logOnePlusV leaf4878InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4878InputLogOnePlusV_eq }

private noncomputable def leaf4878Inputs : Inputs :=
  inputsOfCaches globalInput sk214RoundedInputs
    chi281InputQChi innerPair110Input
    leaf4878InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4878LowerChecked :
    lowerCheck 24 leaf4878Box leaf4878Inputs = true := by
  rfl'

private theorem leaf4878CoversExact : CoversExact 8
    leaf4878Box leaf4878Certificate leaf4878InnerLog leaf4878Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk214RoundedFacts chi281RoundedFacts
    innerPair110RoundedFacts leaf4878RoundedFacts (by rfl)

private theorem leaf4878FlatSound : Sound leaf4878Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4878CertificateValid
    leaf4878InnerLogValid leaf4878CoversExact leaf4878LowerChecked

private noncomputable def leaf4879Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (225/64), chiLo := (73/256), chiHi := (37/128) }

private noncomputable def leaf4879Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742421/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715214336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2145287725/1073741824) }, upper := { exponent := 1, mantissa := (16517/16384) } }, logOuter := sk213LogOuterCertificate, logK := sk213LogKCertificate, logChi := chi282LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432626687/137430428672) } }, logDArg := sk213LogDArgCertificate }

private noncomputable def leaf4879InnerLog : WideLogData :=
  innerPair110Data

set_option maxRecDepth 1000000 in
private theorem leaf4879LocalValidity :
    LeafFacts leaf4879Box leaf4879Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4879Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715214336) }) = true
      norm_num [leaf4879Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4879CertificateValid :
    WideCertificateValid leaf4879Box leaf4879Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk213ValidityFacts chi282ValidityFacts
    leaf4879LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4879CoverageChecked :
    coverageCheck (innerAD leaf4879Box) leaf4879InnerLog = true := by
  rfl'

private theorem leaf4879InnerLogValid :
    leaf4879InnerLog.Valid 8 (innerAD leaf4879Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint72PositiveFacts.valid leaf4879CoverageChecked

private noncomputable def leaf4879InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629349/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4879InputLogOnePlusV_eq :
    leaf4879InputLogOnePlusV = outerEnclosure 24
      (leaf4879Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4879RoundedFacts : LeafRoundedFacts 8
    leaf4879Certificate.logOnePlusV leaf4879InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4879InputLogOnePlusV_eq }

private noncomputable def leaf4879Inputs : Inputs :=
  inputsOfCaches globalInput sk213RoundedInputs
    chi282InputQChi innerPair110Input
    leaf4879InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4879LowerChecked :
    lowerCheck 24 leaf4879Box leaf4879Inputs = true := by
  rfl'

private theorem leaf4879CoversExact : CoversExact 8
    leaf4879Box leaf4879Certificate leaf4879InnerLog leaf4879Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk213RoundedFacts chi282RoundedFacts
    innerPair110RoundedFacts leaf4879RoundedFacts (by rfl)

private theorem leaf4879FlatSound : Sound leaf4879Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4879CertificateValid
    leaf4879InnerLogValid leaf4879CoversExact leaf4879LowerChecked

private noncomputable def leaf4880Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (225/64), kHi := (113/32), chiLo := (73/256), chiHi := (37/128) }

private noncomputable def leaf4880Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742423/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715195392) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2150071559/2147483648) }, upper := { exponent := 1, mantissa := (8277/8192) } }, logOuter := sk214LogOuterCertificate, logK := sk214LogKCertificate, logChi := chi282LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432607743/137430390784) } }, logDArg := sk214LogDArgCertificate }

private noncomputable def leaf4880InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4880LocalValidity :
    LeafFacts leaf4880Box leaf4880Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4880Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715195392) }) = true
      norm_num [leaf4880Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4880CertificateValid :
    WideCertificateValid leaf4880Box leaf4880Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk214ValidityFacts chi282ValidityFacts
    leaf4880LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4880CoverageChecked :
    coverageCheck (innerAD leaf4880Box) leaf4880InnerLog = true := by
  rfl'

private theorem leaf4880InnerLogValid :
    leaf4880InnerLog.Valid 8 (innerAD leaf4880Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4880CoverageChecked

private noncomputable def leaf4880InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629351/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4880InputLogOnePlusV_eq :
    leaf4880InputLogOnePlusV = outerEnclosure 24
      (leaf4880Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4880RoundedFacts : LeafRoundedFacts 8
    leaf4880Certificate.logOnePlusV leaf4880InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4880InputLogOnePlusV_eq }

private noncomputable def leaf4880Inputs : Inputs :=
  inputsOfCaches globalInput sk214RoundedInputs
    chi282InputQChi innerPair116Input
    leaf4880InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4880LowerChecked :
    lowerCheck 24 leaf4880Box leaf4880Inputs = true := by
  rfl'

private theorem leaf4880CoversExact : CoversExact 8
    leaf4880Box leaf4880Certificate leaf4880InnerLog leaf4880Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk214RoundedFacts chi282RoundedFacts
    innerPair116RoundedFacts leaf4880RoundedFacts (by rfl)

private theorem leaf4880FlatSound : Sound leaf4880Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4880CertificateValid
    leaf4880InnerLogValid leaf4880CoversExact leaf4880LowerChecked

private noncomputable def leaf4881Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (227/64), chiLo := (9/32), chiHi := (73/256) }

private noncomputable def leaf4881Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742423/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9816773193/9816462080) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2140045163/1073741824) }, upper := { exponent := 1, mantissa := (32955/32768) } }, logOuter := sk211LogOuterCertificate, logK := sk211LogKCertificate, logChi := chi281LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (19633235273/19632924160) } }, logDArg := sk211LogDArgCertificate }

private noncomputable def leaf4881InnerLog : WideLogData :=
  innerPair110Data

set_option maxRecDepth 1000000 in
private theorem leaf4881LocalValidity :
    LeafFacts leaf4881Box leaf4881Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4881Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9816773193/9816462080) }) = true
      norm_num [leaf4881Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4881CertificateValid :
    WideCertificateValid leaf4881Box leaf4881Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk211ValidityFacts chi281ValidityFacts
    leaf4881LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4881CoverageChecked :
    coverageCheck (innerAD leaf4881Box) leaf4881InnerLog = true := by
  rfl'

private theorem leaf4881InnerLogValid :
    leaf4881InnerLog.Valid 8 (innerAD leaf4881Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint72PositiveFacts.valid leaf4881CoverageChecked

private noncomputable def leaf4881InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629347/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4881InputLogOnePlusV_eq :
    leaf4881InputLogOnePlusV = outerEnclosure 24
      (leaf4881Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4881RoundedFacts : LeafRoundedFacts 8
    leaf4881Certificate.logOnePlusV leaf4881InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4881InputLogOnePlusV_eq }

private noncomputable def leaf4881Inputs : Inputs :=
  inputsOfCaches globalInput sk211RoundedInputs
    chi281InputQChi innerPair110Input
    leaf4881InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4881LowerChecked :
    lowerCheck 24 leaf4881Box leaf4881Inputs = true := by
  rfl'

private theorem leaf4881CoversExact : CoversExact 8
    leaf4881Box leaf4881Certificate leaf4881InnerLog leaf4881Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk211RoundedFacts chi281RoundedFacts
    innerPair110RoundedFacts leaf4881RoundedFacts (by rfl)

private theorem leaf4881FlatSound : Sound leaf4881Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4881CertificateValid
    leaf4881InnerLogValid leaf4881CoversExact leaf4881LowerChecked

private noncomputable def leaf4882Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (227/64), kHi := (57/16), chiLo := (9/32), chiHi := (73/256) }

private noncomputable def leaf4882Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742425/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715215872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2144763465/1073741824) }, upper := { exponent := 1, mantissa := (8257/8192) } }, logOuter := sk212LogOuterCertificate, logK := sk212LogKCertificate, logChi := chi281LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432628223/137430431744) } }, logDArg := sk212LogDArgCertificate }

private noncomputable def leaf4882InnerLog : WideLogData :=
  innerPair110Data

set_option maxRecDepth 1000000 in
private theorem leaf4882LocalValidity :
    LeafFacts leaf4882Box leaf4882Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4882Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715215872) }) = true
      norm_num [leaf4882Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4882CertificateValid :
    WideCertificateValid leaf4882Box leaf4882Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk212ValidityFacts chi281ValidityFacts
    leaf4882LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4882CoverageChecked :
    coverageCheck (innerAD leaf4882Box) leaf4882InnerLog = true := by
  rfl'

private theorem leaf4882InnerLogValid :
    leaf4882InnerLog.Valid 8 (innerAD leaf4882Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint72PositiveFacts.valid leaf4882CoverageChecked

private noncomputable def leaf4882InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629349/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4882InputLogOnePlusV_eq :
    leaf4882InputLogOnePlusV = outerEnclosure 24
      (leaf4882Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4882RoundedFacts : LeafRoundedFacts 8
    leaf4882Certificate.logOnePlusV leaf4882InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4882InputLogOnePlusV_eq }

private noncomputable def leaf4882Inputs : Inputs :=
  inputsOfCaches globalInput sk212RoundedInputs
    chi281InputQChi innerPair110Input
    leaf4882InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4882LowerChecked :
    lowerCheck 24 leaf4882Box leaf4882Inputs = true := by
  rfl'

private theorem leaf4882CoversExact : CoversExact 8
    leaf4882Box leaf4882Certificate leaf4882InnerLog leaf4882Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk212RoundedFacts chi281RoundedFacts
    innerPair110RoundedFacts leaf4882RoundedFacts (by rfl)

private theorem leaf4882FlatSound : Sound leaf4882Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4882CertificateValid
    leaf4882InnerLogValid leaf4882CoversExact leaf4882LowerChecked

private noncomputable def leaf4883Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (227/64), chiLo := (73/256), chiHi := (37/128) }

private noncomputable def leaf4883Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742425/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22905804117/22905058816) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2154855393/2147483648) }, upper := { exponent := 1, mantissa := (16591/16384) } }, logOuter := sk211LogOuterCertificate, logK := sk211LogKCertificate, logChi := chi282LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45810862933/45810117632) } }, logDArg := sk211LogDArgCertificate }

private noncomputable def leaf4883InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4883LocalValidity :
    LeafFacts leaf4883Box leaf4883Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4883Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22905804117/22905058816) }) = true
      norm_num [leaf4883Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4883CertificateValid :
    WideCertificateValid leaf4883Box leaf4883Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk211ValidityFacts chi282ValidityFacts
    leaf4883LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4883CoverageChecked :
    coverageCheck (innerAD leaf4883Box) leaf4883InnerLog = true := by
  rfl'

private theorem leaf4883InnerLogValid :
    leaf4883InnerLog.Valid 8 (innerAD leaf4883Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4883CoverageChecked

private noncomputable def leaf4883InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814677/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4883InputLogOnePlusV_eq :
    leaf4883InputLogOnePlusV = outerEnclosure 24
      (leaf4883Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4883RoundedFacts : LeafRoundedFacts 8
    leaf4883Certificate.logOnePlusV leaf4883InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4883InputLogOnePlusV_eq }

private noncomputable def leaf4883Inputs : Inputs :=
  inputsOfCaches globalInput sk211RoundedInputs
    chi282InputQChi innerPair116Input
    leaf4883InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4883LowerChecked :
    lowerCheck 24 leaf4883Box leaf4883Inputs = true := by
  rfl'

private theorem leaf4883CoversExact : CoversExact 8
    leaf4883Box leaf4883Certificate leaf4883InnerLog leaf4883Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk211RoundedFacts chi282RoundedFacts
    innerPair116RoundedFacts leaf4883RoundedFacts (by rfl)

private theorem leaf4883FlatSound : Sound leaf4883Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4883CertificateValid
    leaf4883InnerLogValid leaf4883CoversExact leaf4883LowerChecked

private noncomputable def leaf4884Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (227/64), kHi := (57/16), chiLo := (73/256), chiHi := (37/128) }

private noncomputable def leaf4884Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742427/1073741824) }, vSqrt := { lower := (8191/8192), upper := (316670103/316659712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2159639227/2147483648) }, upper := { exponent := 1, mantissa := (4157/4096) } }, logOuter := sk212LogOuterCertificate, logK := sk212LogKCertificate, logChi := chi282LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (633329815/633319424) } }, logDArg := sk212LogDArgCertificate }

private noncomputable def leaf4884InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4884LocalValidity :
    LeafFacts leaf4884Box leaf4884Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4884Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (316670103/316659712) }) = true
      norm_num [leaf4884Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4884CertificateValid :
    WideCertificateValid leaf4884Box leaf4884Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk212ValidityFacts chi282ValidityFacts
    leaf4884LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4884CoverageChecked :
    coverageCheck (innerAD leaf4884Box) leaf4884InnerLog = true := by
  rfl'

private theorem leaf4884InnerLogValid :
    leaf4884InnerLog.Valid 8 (innerAD leaf4884Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4884CoverageChecked

private noncomputable def leaf4884InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907339/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4884InputLogOnePlusV_eq :
    leaf4884InputLogOnePlusV = outerEnclosure 24
      (leaf4884Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4884RoundedFacts : LeafRoundedFacts 8
    leaf4884Certificate.logOnePlusV leaf4884InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4884InputLogOnePlusV_eq }

private noncomputable def leaf4884Inputs : Inputs :=
  inputsOfCaches globalInput sk212RoundedInputs
    chi282InputQChi innerPair116Input
    leaf4884InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4884LowerChecked :
    lowerCheck 24 leaf4884Box leaf4884Inputs = true := by
  rfl'

private theorem leaf4884CoversExact : CoversExact 8
    leaf4884Box leaf4884Certificate leaf4884InnerLog leaf4884Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk212RoundedFacts chi282RoundedFacts
    innerPair116RoundedFacts leaf4884RoundedFacts (by rfl)

private theorem leaf4884FlatSound : Sound leaf4884Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4884CertificateValid
    leaf4884InnerLogValid leaf4884CoversExact leaf4884LowerChecked

private noncomputable def leaf4885Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (37/128), chiHi := (75/256) }

private noncomputable def leaf4885Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871287/536870912) }, vSqrt := { lower := (8191/8192), upper := (227541209/227533568) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1079966987/1073741824) }, upper := { exponent := 1, mantissa := (16667/16384) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi283LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (455074777/455067136) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf4885InnerLog : WideLogData :=
  innerPair624Data

set_option maxRecDepth 1000000 in
private theorem leaf4885LocalValidity :
    LeafFacts leaf4885Box leaf4885Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4885Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (227541209/227533568) }) = true
      norm_num [leaf4885Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4885CertificateValid :
    WideCertificateValid leaf4885Box leaf4885Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi283ValidityFacts
    leaf4885LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4885CoverageChecked :
    coverageCheck (innerAD leaf4885Box) leaf4885InnerLog = true := by
  rfl'

private theorem leaf4885InnerLogValid :
    leaf4885InnerLog.Valid 8 (innerAD leaf4885Box) :=
  wideLogDataValid_of_cachedCheck endpoint351PositiveFacts
    endpoint352PositiveFacts.valid leaf4885CoverageChecked

private noncomputable def leaf4885InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814681/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4885InputLogOnePlusV_eq :
    leaf4885InputLogOnePlusV = outerEnclosure 24
      (leaf4885Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4885RoundedFacts : LeafRoundedFacts 8
    leaf4885Certificate.logOnePlusV leaf4885InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4885InputLogOnePlusV_eq }

private noncomputable def leaf4885Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi283InputQChi innerPair624Input
    leaf4885InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4885LowerChecked :
    lowerCheck 24 leaf4885Box leaf4885Inputs = true := by
  rfl'

private theorem leaf4885CoversExact : CoversExact 8
    leaf4885Box leaf4885Certificate leaf4885InnerLog leaf4885Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi283RoundedFacts
    innerPair624RoundedFacts leaf4885RoundedFacts (by rfl)

private theorem leaf4885FlatSound : Sound leaf4885Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4885CertificateValid
    leaf4885InnerLogValid leaf4885CoversExact leaf4885LowerChecked

private noncomputable def leaf4886Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (75/256), chiHi := (19/64) }

private noncomputable def leaf4886Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871289/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357539840) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1087306569/1073741824) }, upper := { exponent := 1, mantissa := (4195/4096) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi284LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68716262399/68715079680) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf4886InnerLog : WideLogData :=
  innerPair553Data

set_option maxRecDepth 1000000 in
private theorem leaf4886LocalValidity :
    LeafFacts leaf4886Box leaf4886Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4886Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357539840) }) = true
      norm_num [leaf4886Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4886CertificateValid :
    WideCertificateValid leaf4886Box leaf4886Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi284ValidityFacts
    leaf4886LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4886CoverageChecked :
    coverageCheck (innerAD leaf4886Box) leaf4886InnerLog = true := by
  rfl'

private theorem leaf4886InnerLogValid :
    leaf4886InnerLog.Valid 8 (innerAD leaf4886Box) :=
  wideLogDataValid_of_cachedCheck endpoint285PositiveFacts
    endpoint288PositiveFacts.valid leaf4886CoverageChecked

private noncomputable def leaf4886InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814685/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4886InputLogOnePlusV_eq :
    leaf4886InputLogOnePlusV = outerEnclosure 24
      (leaf4886Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4886RoundedFacts : LeafRoundedFacts 8
    leaf4886Certificate.logOnePlusV leaf4886InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4886InputLogOnePlusV_eq }

private noncomputable def leaf4886Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi284InputQChi innerPair553Input
    leaf4886InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4886LowerChecked :
    lowerCheck 24 leaf4886Box leaf4886Inputs = true := by
  rfl'

private theorem leaf4886CoversExact : CoversExact 8
    leaf4886Box leaf4886Certificate leaf4886InnerLog leaf4886Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi284RoundedFacts
    innerPair553RoundedFacts leaf4886RoundedFacts (by rfl)

private theorem leaf4886FlatSound : Sound leaf4886Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4886CertificateValid
    leaf4886InnerLogValid leaf4886CoversExact leaf4886LowerChecked

private noncomputable def leaf4887Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (227/64), chiLo := (37/128), chiHi := (75/256) }

private noncomputable def leaf4887Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742427/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715118336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2169665623/2147483648) }, upper := { exponent := 1, mantissa := (33409/32768) } }, logOuter := sk211LogOuterCertificate, logK := sk211LogKCertificate, logChi := chi283LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432530687/137430236672) } }, logDArg := sk211LogDArgCertificate }

private noncomputable def leaf4887InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4887LocalValidity :
    LeafFacts leaf4887Box leaf4887Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4887Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715118336) }) = true
      norm_num [leaf4887Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4887CertificateValid :
    WideCertificateValid leaf4887Box leaf4887Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk211ValidityFacts chi283ValidityFacts
    leaf4887LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4887CoverageChecked :
    coverageCheck (innerAD leaf4887Box) leaf4887InnerLog = true := by
  rfl'

private theorem leaf4887InnerLogValid :
    leaf4887InnerLog.Valid 8 (innerAD leaf4887Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4887CoverageChecked

private noncomputable def leaf4887InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629361/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4887InputLogOnePlusV_eq :
    leaf4887InputLogOnePlusV = outerEnclosure 24
      (leaf4887Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4887RoundedFacts : LeafRoundedFacts 8
    leaf4887Certificate.logOnePlusV leaf4887InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4887InputLogOnePlusV_eq }

private noncomputable def leaf4887Inputs : Inputs :=
  inputsOfCaches globalInput sk211RoundedInputs
    chi283InputQChi innerPair116Input
    leaf4887InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4887LowerChecked :
    lowerCheck 24 leaf4887Box leaf4887Inputs = true := by
  rfl'

private theorem leaf4887CoversExact : CoversExact 8
    leaf4887Box leaf4887Certificate leaf4887InnerLog leaf4887Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk211RoundedFacts chi283RoundedFacts
    innerPair116RoundedFacts leaf4887RoundedFacts (by rfl)

private theorem leaf4887FlatSound : Sound leaf4887Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4887CertificateValid
    leaf4887InnerLogValid leaf4887CoversExact leaf4887LowerChecked

private noncomputable def leaf4888Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (227/64), kHi := (57/16), chiLo := (37/128), chiHi := (75/256) }

private noncomputable def leaf4888Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742429/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715099136) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2174514989/2147483648) }, upper := { exponent := 1, mantissa := (8371/8192) } }, logOuter := sk212LogOuterCertificate, logK := sk212LogKCertificate, logChi := chi283LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432511487/137430198272) } }, logDArg := sk212LogDArgCertificate }

private noncomputable def leaf4888InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4888LocalValidity :
    LeafFacts leaf4888Box leaf4888Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4888Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715099136) }) = true
      norm_num [leaf4888Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4888CertificateValid :
    WideCertificateValid leaf4888Box leaf4888Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk212ValidityFacts chi283ValidityFacts
    leaf4888LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4888CoverageChecked :
    coverageCheck (innerAD leaf4888Box) leaf4888InnerLog = true := by
  rfl'

private theorem leaf4888InnerLogValid :
    leaf4888InnerLog.Valid 8 (innerAD leaf4888Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4888CoverageChecked

private noncomputable def leaf4888InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629363/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4888InputLogOnePlusV_eq :
    leaf4888InputLogOnePlusV = outerEnclosure 24
      (leaf4888Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4888RoundedFacts : LeafRoundedFacts 8
    leaf4888Certificate.logOnePlusV leaf4888InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4888InputLogOnePlusV_eq }

private noncomputable def leaf4888Inputs : Inputs :=
  inputsOfCaches globalInput sk212RoundedInputs
    chi283InputQChi innerPair116Input
    leaf4888InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4888LowerChecked :
    lowerCheck 24 leaf4888Box leaf4888Inputs = true := by
  rfl'

private theorem leaf4888CoversExact : CoversExact 8
    leaf4888Box leaf4888Certificate leaf4888InnerLog leaf4888Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk212RoundedFacts chi283RoundedFacts
    innerPair116RoundedFacts leaf4888RoundedFacts (by rfl)

private theorem leaf4888FlatSound : Sound leaf4888Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4888CertificateValid
    leaf4888InnerLogValid leaf4888CoversExact leaf4888LowerChecked

private noncomputable def leaf4889Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (227/64), chiLo := (75/256), chiHi := (19/64) }

private noncomputable def leaf4889Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742429/1073741824) }, vSqrt := { lower := (8191/8192), upper := (455082201/455066624) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2184475853/2147483648) }, upper := { exponent := 1, mantissa := (8409/8192) } }, logOuter := sk211LogOuterCertificate, logK := sk211LogKCertificate, logChi := chi284LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (910148825/910133248) } }, logDArg := sk211LogDArgCertificate }

private noncomputable def leaf4889InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4889LocalValidity :
    LeafFacts leaf4889Box leaf4889Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4889Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (455082201/455066624) }) = true
      norm_num [leaf4889Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4889CertificateValid :
    WideCertificateValid leaf4889Box leaf4889Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk211ValidityFacts chi284ValidityFacts
    leaf4889LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4889CoverageChecked :
    coverageCheck (innerAD leaf4889Box) leaf4889InnerLog = true := by
  rfl'

private theorem leaf4889InnerLogValid :
    leaf4889InnerLog.Valid 8 (innerAD leaf4889Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4889CoverageChecked

private noncomputable def leaf4889InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453671/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf4889InputLogOnePlusV_eq :
    leaf4889InputLogOnePlusV = outerEnclosure 24
      (leaf4889Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4889RoundedFacts : LeafRoundedFacts 8
    leaf4889Certificate.logOnePlusV leaf4889InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4889InputLogOnePlusV_eq }

private noncomputable def leaf4889Inputs : Inputs :=
  inputsOfCaches globalInput sk211RoundedInputs
    chi284InputQChi innerPair116Input
    leaf4889InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4889LowerChecked :
    lowerCheck 24 leaf4889Box leaf4889Inputs = true := by
  rfl'

private theorem leaf4889CoversExact : CoversExact 8
    leaf4889Box leaf4889Certificate leaf4889InnerLog leaf4889Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk211RoundedFacts chi284RoundedFacts
    innerPair116RoundedFacts leaf4889RoundedFacts (by rfl)

private theorem leaf4889FlatSound : Sound leaf4889Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4889CertificateValid
    leaf4889InnerLogValid leaf4889CoversExact leaf4889LowerChecked

private noncomputable def leaf4890Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (227/64), kHi := (57/16), chiLo := (75/256), chiHi := (19/64) }

private noncomputable def leaf4890Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742431/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715040768) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2189390751/2147483648) }, upper := { exponent := 1, mantissa := (2107/2048) } }, logOuter := sk212LogOuterCertificate, logK := sk212LogKCertificate, logChi := chi284LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432453119/137430081536) } }, logDArg := sk212LogDArgCertificate }

private noncomputable def leaf4890InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4890LocalValidity :
    LeafFacts leaf4890Box leaf4890Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4890Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715040768) }) = true
      norm_num [leaf4890Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4890CertificateValid :
    WideCertificateValid leaf4890Box leaf4890Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk212ValidityFacts chi284ValidityFacts
    leaf4890LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4890CoverageChecked :
    coverageCheck (innerAD leaf4890Box) leaf4890InnerLog = true := by
  rfl'

private theorem leaf4890InnerLogValid :
    leaf4890InnerLog.Valid 8 (innerAD leaf4890Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4890CoverageChecked

private noncomputable def leaf4890InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814685/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4890InputLogOnePlusV_eq :
    leaf4890InputLogOnePlusV = outerEnclosure 24
      (leaf4890Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4890RoundedFacts : LeafRoundedFacts 8
    leaf4890Certificate.logOnePlusV leaf4890InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4890InputLogOnePlusV_eq }

private noncomputable def leaf4890Inputs : Inputs :=
  inputsOfCaches globalInput sk212RoundedInputs
    chi284InputQChi innerPair116Input
    leaf4890InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4890LowerChecked :
    lowerCheck 24 leaf4890Box leaf4890Inputs = true := by
  rfl'

private theorem leaf4890CoversExact : CoversExact 8
    leaf4890Box leaf4890Certificate leaf4890InnerLog leaf4890Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk212RoundedFacts chi284RoundedFacts
    innerPair116RoundedFacts leaf4890RoundedFacts (by rfl)

private theorem leaf4890FlatSound : Sound leaf4890Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4890CertificateValid
    leaf4890InnerLogValid leaf4890CoversExact leaf4890LowerChecked

private noncomputable def leaf4891Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (229/64), chiLo := (9/32), chiHi := (73/256) }

private noncomputable def leaf4891Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742427/1073741824) }, vSqrt := { lower := (8191/8192), upper := (738896907/738873088) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2149481767/2147483648) }, upper := { exponent := 1, mantissa := (33101/32768) } }, logOuter := sk215LogOuterCertificate, logK := sk215LogKCertificate, logChi := chi281LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (1477769995/1477746176) } }, logDArg := sk215LogDArgCertificate }

private noncomputable def leaf4891InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4891LocalValidity :
    LeafFacts leaf4891Box leaf4891Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4891Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (738896907/738873088) }) = true
      norm_num [leaf4891Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4891CertificateValid :
    WideCertificateValid leaf4891Box leaf4891Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk215ValidityFacts chi281ValidityFacts
    leaf4891LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4891CoverageChecked :
    coverageCheck (innerAD leaf4891Box) leaf4891InnerLog = true := by
  rfl'

private theorem leaf4891InnerLogValid :
    leaf4891InnerLog.Valid 8 (innerAD leaf4891Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4891CoverageChecked

private noncomputable def leaf4891InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629351/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4891InputLogOnePlusV_eq :
    leaf4891InputLogOnePlusV = outerEnclosure 24
      (leaf4891Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4891RoundedFacts : LeafRoundedFacts 8
    leaf4891Certificate.logOnePlusV leaf4891InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4891InputLogOnePlusV_eq }

private noncomputable def leaf4891Inputs : Inputs :=
  inputsOfCaches globalInput sk215RoundedInputs
    chi281InputQChi innerPair116Input
    leaf4891InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4891LowerChecked :
    lowerCheck 24 leaf4891Box leaf4891Inputs = true := by
  rfl'

private theorem leaf4891CoversExact : CoversExact 8
    leaf4891Box leaf4891Certificate leaf4891InnerLog leaf4891Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk215RoundedFacts chi281RoundedFacts
    innerPair116RoundedFacts leaf4891RoundedFacts (by rfl)

private theorem leaf4891FlatSound : Sound leaf4891Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4891CertificateValid
    leaf4891InnerLogValid leaf4891CoversExact leaf4891LowerChecked

private noncomputable def leaf4892Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (229/64), kHi := (115/32), chiLo := (9/32), chiHi := (73/256) }

private noncomputable def leaf4892Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742429/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715178496) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2154200069/2147483648) }, upper := { exponent := 1, mantissa := (16587/16384) } }, logOuter := sk216LogOuterCertificate, logK := sk216LogKCertificate, logChi := chi281LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432590847/137430356992) } }, logDArg := sk216LogDArgCertificate }

private noncomputable def leaf4892InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4892LocalValidity :
    LeafFacts leaf4892Box leaf4892Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4892Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715178496) }) = true
      norm_num [leaf4892Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4892CertificateValid :
    WideCertificateValid leaf4892Box leaf4892Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk216ValidityFacts chi281ValidityFacts
    leaf4892LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4892CoverageChecked :
    coverageCheck (innerAD leaf4892Box) leaf4892InnerLog = true := by
  rfl'

private theorem leaf4892InnerLogValid :
    leaf4892InnerLog.Valid 8 (innerAD leaf4892Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4892CoverageChecked

private noncomputable def leaf4892InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629353/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4892InputLogOnePlusV_eq :
    leaf4892InputLogOnePlusV = outerEnclosure 24
      (leaf4892Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4892RoundedFacts : LeafRoundedFacts 8
    leaf4892Certificate.logOnePlusV leaf4892InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4892InputLogOnePlusV_eq }

private noncomputable def leaf4892Inputs : Inputs :=
  inputsOfCaches globalInput sk216RoundedInputs
    chi281InputQChi innerPair116Input
    leaf4892InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4892LowerChecked :
    lowerCheck 24 leaf4892Box leaf4892Inputs = true := by
  rfl'

private theorem leaf4892CoversExact : CoversExact 8
    leaf4892Box leaf4892Certificate leaf4892InnerLog leaf4892Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk216RoundedFacts chi281RoundedFacts
    innerPair116RoundedFacts leaf4892RoundedFacts (by rfl)

private theorem leaf4892FlatSound : Sound leaf4892Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4892CertificateValid
    leaf4892InnerLogValid leaf4892CoversExact leaf4892LowerChecked

private noncomputable def leaf4893Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (229/64), chiLo := (73/256), chiHi := (37/128) }

private noncomputable def leaf4893Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742429/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715138560) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2164423061/2147483648) }, upper := { exponent := 1, mantissa := (16665/16384) } }, logOuter := sk215LogOuterCertificate, logK := sk215LogKCertificate, logChi := chi282LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432550911/137430277120) } }, logDArg := sk215LogDArgCertificate }

private noncomputable def leaf4893InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4893LocalValidity :
    LeafFacts leaf4893Box leaf4893Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4893Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715138560) }) = true
      norm_num [leaf4893Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4893CertificateValid :
    WideCertificateValid leaf4893Box leaf4893Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk215ValidityFacts chi282ValidityFacts
    leaf4893LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4893CoverageChecked :
    coverageCheck (innerAD leaf4893Box) leaf4893InnerLog = true := by
  rfl'

private theorem leaf4893InnerLogValid :
    leaf4893InnerLog.Valid 8 (innerAD leaf4893Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4893CoverageChecked

private noncomputable def leaf4893InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814679/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4893InputLogOnePlusV_eq :
    leaf4893InputLogOnePlusV = outerEnclosure 24
      (leaf4893Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4893RoundedFacts : LeafRoundedFacts 8
    leaf4893Certificate.logOnePlusV leaf4893InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4893InputLogOnePlusV_eq }

private noncomputable def leaf4893Inputs : Inputs :=
  inputsOfCaches globalInput sk215RoundedInputs
    chi282InputQChi innerPair116Input
    leaf4893InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4893LowerChecked :
    lowerCheck 24 leaf4893Box leaf4893Inputs = true := by
  rfl'

private theorem leaf4893CoversExact : CoversExact 8
    leaf4893Box leaf4893Certificate leaf4893InnerLog leaf4893Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk215RoundedFacts chi282RoundedFacts
    innerPair116RoundedFacts leaf4893RoundedFacts (by rfl)

private theorem leaf4893FlatSound : Sound leaf4893Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4893CertificateValid
    leaf4893InnerLogValid leaf4893CoversExact leaf4893LowerChecked

private noncomputable def leaf4894Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (229/64), kHi := (115/32), chiLo := (73/256), chiHi := (37/128) }

private noncomputable def leaf4894Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742431/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22905804117/22905039872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2169206895/2147483648) }, upper := { exponent := 1, mantissa := (8351/8192) } }, logOuter := sk216LogOuterCertificate, logK := sk216LogKCertificate, logChi := chi282LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45810843989/45810079744) } }, logDArg := sk216LogDArgCertificate }

private noncomputable def leaf4894InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4894LocalValidity :
    LeafFacts leaf4894Box leaf4894Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4894Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22905804117/22905039872) }) = true
      norm_num [leaf4894Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4894CertificateValid :
    WideCertificateValid leaf4894Box leaf4894Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk216ValidityFacts chi282ValidityFacts
    leaf4894LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4894CoverageChecked :
    coverageCheck (innerAD leaf4894Box) leaf4894InnerLog = true := by
  rfl'

private theorem leaf4894InnerLogValid :
    leaf4894InnerLog.Valid 8 (innerAD leaf4894Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4894CoverageChecked

private noncomputable def leaf4894InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629361/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4894InputLogOnePlusV_eq :
    leaf4894InputLogOnePlusV = outerEnclosure 24
      (leaf4894Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4894RoundedFacts : LeafRoundedFacts 8
    leaf4894Certificate.logOnePlusV leaf4894InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4894InputLogOnePlusV_eq }

private noncomputable def leaf4894Inputs : Inputs :=
  inputsOfCaches globalInput sk216RoundedInputs
    chi282InputQChi innerPair116Input
    leaf4894InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4894LowerChecked :
    lowerCheck 24 leaf4894Box leaf4894Inputs = true := by
  rfl'

private theorem leaf4894CoversExact : CoversExact 8
    leaf4894Box leaf4894Certificate leaf4894InnerLog leaf4894Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk216RoundedFacts chi282RoundedFacts
    innerPair116RoundedFacts leaf4894RoundedFacts (by rfl)

private theorem leaf4894FlatSound : Sound leaf4894Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4894CertificateValid
    leaf4894InnerLogValid leaf4894CoversExact leaf4894LowerChecked

private noncomputable def leaf4895Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (231/64), chiLo := (9/32), chiHi := (73/256) }

private noncomputable def leaf4895Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742431/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715159808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2158918371/2147483648) }, upper := { exponent := 1, mantissa := (33247/32768) } }, logOuter := sk209LogOuterCertificate, logK := sk209LogKCertificate, logChi := chi281LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432572159/137430319616) } }, logDArg := sk209LogDArgCertificate }

private noncomputable def leaf4895InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4895LocalValidity :
    LeafFacts leaf4895Box leaf4895Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4895Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715159808) }) = true
      norm_num [leaf4895Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4895CertificateValid :
    WideCertificateValid leaf4895Box leaf4895Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk209ValidityFacts chi281ValidityFacts
    leaf4895LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4895CoverageChecked :
    coverageCheck (innerAD leaf4895Box) leaf4895InnerLog = true := by
  rfl'

private theorem leaf4895InnerLogValid :
    leaf4895InnerLog.Valid 8 (innerAD leaf4895Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4895CoverageChecked

private noncomputable def leaf4895InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907339/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4895InputLogOnePlusV_eq :
    leaf4895InputLogOnePlusV = outerEnclosure 24
      (leaf4895Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4895RoundedFacts : LeafRoundedFacts 8
    leaf4895Certificate.logOnePlusV leaf4895InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4895InputLogOnePlusV_eq }

private noncomputable def leaf4895Inputs : Inputs :=
  inputsOfCaches globalInput sk209RoundedInputs
    chi281InputQChi innerPair116Input
    leaf4895InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4895LowerChecked :
    lowerCheck 24 leaf4895Box leaf4895Inputs = true := by
  rfl'

private theorem leaf4895CoversExact : CoversExact 8
    leaf4895Box leaf4895Certificate leaf4895InnerLog leaf4895Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk209RoundedFacts chi281RoundedFacts
    innerPair116RoundedFacts leaf4895RoundedFacts (by rfl)

private theorem leaf4895FlatSound : Sound leaf4895Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4895CertificateValid
    leaf4895InnerLogValid leaf4895CoversExact leaf4895LowerChecked

private noncomputable def leaf4896Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (231/64), kHi := (29/8), chiLo := (9/32), chiHi := (73/256) }

private noncomputable def leaf4896Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742433/1073741824) }, vSqrt := { lower := (8191/8192), upper := (7635268039/7635015680) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2163636673/2147483648) }, upper := { exponent := 1, mantissa := (4165/4096) } }, logOuter := sk210LogOuterCertificate, logK := sk210LogKCertificate, logChi := chi281LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (15270283719/15270031360) } }, logDArg := sk210LogDArgCertificate }

private noncomputable def leaf4896InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4896LocalValidity :
    LeafFacts leaf4896Box leaf4896Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4896Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (7635268039/7635015680) }) = true
      norm_num [leaf4896Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4896CertificateValid :
    WideCertificateValid leaf4896Box leaf4896Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk210ValidityFacts chi281ValidityFacts
    leaf4896LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4896CoverageChecked :
    coverageCheck (innerAD leaf4896Box) leaf4896InnerLog = true := by
  rfl'

private theorem leaf4896InnerLogValid :
    leaf4896InnerLog.Valid 8 (innerAD leaf4896Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4896CoverageChecked

private noncomputable def leaf4896InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814679/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4896InputLogOnePlusV_eq :
    leaf4896InputLogOnePlusV = outerEnclosure 24
      (leaf4896Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4896RoundedFacts : LeafRoundedFacts 8
    leaf4896Certificate.logOnePlusV leaf4896InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4896InputLogOnePlusV_eq }

private noncomputable def leaf4896Inputs : Inputs :=
  inputsOfCaches globalInput sk210RoundedInputs
    chi281InputQChi innerPair116Input
    leaf4896InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4896LowerChecked :
    lowerCheck 24 leaf4896Box leaf4896Inputs = true := by
  rfl'

private theorem leaf4896CoversExact : CoversExact 8
    leaf4896Box leaf4896Certificate leaf4896InnerLog leaf4896Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk210RoundedFacts chi281RoundedFacts
    innerPair116RoundedFacts leaf4896RoundedFacts (by rfl)

private theorem leaf4896FlatSound : Sound leaf4896Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4896CertificateValid
    leaf4896InnerLogValid leaf4896CoversExact leaf4896LowerChecked

private noncomputable def leaf4897Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (231/64), chiLo := (73/256), chiHi := (37/128) }

private noncomputable def leaf4897Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742433/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715100672) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2173990729/2147483648) }, upper := { exponent := 1, mantissa := (16739/16384) } }, logOuter := sk209LogOuterCertificate, logK := sk209LogKCertificate, logChi := chi282LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432513023/137430201344) } }, logDArg := sk209LogDArgCertificate }

private noncomputable def leaf4897InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4897LocalValidity :
    LeafFacts leaf4897Box leaf4897Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4897Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715100672) }) = true
      norm_num [leaf4897Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4897CertificateValid :
    WideCertificateValid leaf4897Box leaf4897Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk209ValidityFacts chi282ValidityFacts
    leaf4897LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4897CoverageChecked :
    coverageCheck (innerAD leaf4897Box) leaf4897InnerLog = true := by
  rfl'

private theorem leaf4897InnerLogValid :
    leaf4897InnerLog.Valid 8 (innerAD leaf4897Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4897CoverageChecked

private noncomputable def leaf4897InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629363/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4897InputLogOnePlusV_eq :
    leaf4897InputLogOnePlusV = outerEnclosure 24
      (leaf4897Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4897RoundedFacts : LeafRoundedFacts 8
    leaf4897Certificate.logOnePlusV leaf4897InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4897InputLogOnePlusV_eq }

private noncomputable def leaf4897Inputs : Inputs :=
  inputsOfCaches globalInput sk209RoundedInputs
    chi282InputQChi innerPair116Input
    leaf4897InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4897LowerChecked :
    lowerCheck 24 leaf4897Box leaf4897Inputs = true := by
  rfl'

private theorem leaf4897CoversExact : CoversExact 8
    leaf4897Box leaf4897Certificate leaf4897InnerLog leaf4897Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk209RoundedFacts chi282RoundedFacts
    innerPair116RoundedFacts leaf4897RoundedFacts (by rfl)

private theorem leaf4897FlatSound : Sound leaf4897Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4897CertificateValid
    leaf4897InnerLogValid leaf4897CoversExact leaf4897LowerChecked

private noncomputable def leaf4898Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (231/64), kHi := (29/8), chiLo := (73/256), chiHi := (37/128) }

private noncomputable def leaf4898Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742435/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715081728) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2178774563/2147483648) }, upper := { exponent := 1, mantissa := (2097/2048) } }, logOuter := sk210LogOuterCertificate, logK := sk210LogKCertificate, logChi := chi282LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432494079/137430163456) } }, logDArg := sk210LogDArgCertificate }

private noncomputable def leaf4898InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4898LocalValidity :
    LeafFacts leaf4898Box leaf4898Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4898Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715081728) }) = true
      norm_num [leaf4898Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4898CertificateValid :
    WideCertificateValid leaf4898Box leaf4898Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk210ValidityFacts chi282ValidityFacts
    leaf4898LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4898CoverageChecked :
    coverageCheck (innerAD leaf4898Box) leaf4898InnerLog = true := by
  rfl'

private theorem leaf4898InnerLogValid :
    leaf4898InnerLog.Valid 8 (innerAD leaf4898Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4898CoverageChecked

private noncomputable def leaf4898InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629365/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4898InputLogOnePlusV_eq :
    leaf4898InputLogOnePlusV = outerEnclosure 24
      (leaf4898Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4898RoundedFacts : LeafRoundedFacts 8
    leaf4898Certificate.logOnePlusV leaf4898InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4898InputLogOnePlusV_eq }

private noncomputable def leaf4898Inputs : Inputs :=
  inputsOfCaches globalInput sk210RoundedInputs
    chi282InputQChi innerPair116Input
    leaf4898InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4898LowerChecked :
    lowerCheck 24 leaf4898Box leaf4898Inputs = true := by
  rfl'

private theorem leaf4898CoversExact : CoversExact 8
    leaf4898Box leaf4898Certificate leaf4898InnerLog leaf4898Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk210RoundedFacts chi282RoundedFacts
    innerPair116RoundedFacts leaf4898RoundedFacts (by rfl)

private theorem leaf4898FlatSound : Sound leaf4898Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4898CertificateValid
    leaf4898InnerLogValid leaf4898CoversExact leaf4898LowerChecked

private noncomputable def leaf4899Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (229/64), chiLo := (37/128), chiHi := (75/256) }

private noncomputable def leaf4899Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742431/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715079936) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2179364355/2147483648) }, upper := { exponent := 1, mantissa := (33559/32768) } }, logOuter := sk215LogOuterCertificate, logK := sk215LogKCertificate, logChi := chi283LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432492287/137430159872) } }, logDArg := sk215LogDArgCertificate }

private noncomputable def leaf4899InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4899LocalValidity :
    LeafFacts leaf4899Box leaf4899Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4899Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715079936) }) = true
      norm_num [leaf4899Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4899CertificateValid :
    WideCertificateValid leaf4899Box leaf4899Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk215ValidityFacts chi283ValidityFacts
    leaf4899LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4899CoverageChecked :
    coverageCheck (innerAD leaf4899Box) leaf4899InnerLog = true := by
  rfl'

private theorem leaf4899InnerLogValid :
    leaf4899InnerLog.Valid 8 (innerAD leaf4899Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4899CoverageChecked

private noncomputable def leaf4899InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629365/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4899InputLogOnePlusV_eq :
    leaf4899InputLogOnePlusV = outerEnclosure 24
      (leaf4899Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4899RoundedFacts : LeafRoundedFacts 8
    leaf4899Certificate.logOnePlusV leaf4899InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4899InputLogOnePlusV_eq }

private noncomputable def leaf4899Inputs : Inputs :=
  inputsOfCaches globalInput sk215RoundedInputs
    chi283InputQChi innerPair116Input
    leaf4899InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4899LowerChecked :
    lowerCheck 24 leaf4899Box leaf4899Inputs = true := by
  rfl'

private theorem leaf4899CoversExact : CoversExact 8
    leaf4899Box leaf4899Certificate leaf4899InnerLog leaf4899Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk215RoundedFacts chi283RoundedFacts
    innerPair116RoundedFacts leaf4899RoundedFacts (by rfl)

private theorem leaf4899FlatSound : Sound leaf4899Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4899CertificateValid
    leaf4899InnerLogValid leaf4899CoversExact leaf4899LowerChecked

private noncomputable def leaf4900Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (229/64), kHi := (115/32), chiLo := (37/128), chiHi := (75/256) }

private noncomputable def leaf4900Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742433/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9816773193/9816437248) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2184213721/2147483648) }, upper := { exponent := 1, mantissa := (16817/16384) } }, logOuter := sk216LogOuterCertificate, logK := sk216LogKCertificate, logChi := chi283LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (19633210441/19632874496) } }, logDArg := sk216LogDArgCertificate }

private noncomputable def leaf4900InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4900LocalValidity :
    LeafFacts leaf4900Box leaf4900Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4900Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9816773193/9816437248) }) = true
      norm_num [leaf4900Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4900CertificateValid :
    WideCertificateValid leaf4900Box leaf4900Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk216ValidityFacts chi283ValidityFacts
    leaf4900LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4900CoverageChecked :
    coverageCheck (innerAD leaf4900Box) leaf4900InnerLog = true := by
  rfl'

private theorem leaf4900InnerLogValid :
    leaf4900InnerLog.Valid 8 (innerAD leaf4900Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4900CoverageChecked

private noncomputable def leaf4900InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453671/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf4900InputLogOnePlusV_eq :
    leaf4900InputLogOnePlusV = outerEnclosure 24
      (leaf4900Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4900RoundedFacts : LeafRoundedFacts 8
    leaf4900Certificate.logOnePlusV leaf4900InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4900InputLogOnePlusV_eq }

private noncomputable def leaf4900Inputs : Inputs :=
  inputsOfCaches globalInput sk216RoundedInputs
    chi283InputQChi innerPair116Input
    leaf4900InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4900LowerChecked :
    lowerCheck 24 leaf4900Box leaf4900Inputs = true := by
  rfl'

private theorem leaf4900CoversExact : CoversExact 8
    leaf4900Box leaf4900Certificate leaf4900InnerLog leaf4900Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk216RoundedFacts chi283RoundedFacts
    innerPair116RoundedFacts leaf4900RoundedFacts (by rfl)

private theorem leaf4900FlatSound : Sound leaf4900Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4900CertificateValid
    leaf4900InnerLogValid leaf4900CoversExact leaf4900LowerChecked

private noncomputable def leaf4901Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (229/64), chiLo := (75/256), chiHi := (19/64) }

private noncomputable def leaf4901Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742433/1073741824) }, vSqrt := { lower := (8191/8192), upper := (1090752577/1090714624) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2194305649/2147483648) }, upper := { exponent := 1, mantissa := (8447/8192) } }, logOuter := sk215LogOuterCertificate, logK := sk215LogKCertificate, logChi := chi284LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (2181467201/2181429248) } }, logDArg := sk215LogDArgCertificate }

private noncomputable def leaf4901InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4901LocalValidity :
    LeafFacts leaf4901Box leaf4901Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4901Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (1090752577/1090714624) }) = true
      norm_num [leaf4901Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4901CertificateValid :
    WideCertificateValid leaf4901Box leaf4901Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk215ValidityFacts chi284ValidityFacts
    leaf4901LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4901CoverageChecked :
    coverageCheck (innerAD leaf4901Box) leaf4901InnerLog = true := by
  rfl'

private theorem leaf4901InnerLogValid :
    leaf4901InnerLog.Valid 8 (innerAD leaf4901Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4901CoverageChecked

private noncomputable def leaf4901InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629373/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4901InputLogOnePlusV_eq :
    leaf4901InputLogOnePlusV = outerEnclosure 24
      (leaf4901Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4901RoundedFacts : LeafRoundedFacts 8
    leaf4901Certificate.logOnePlusV leaf4901InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4901InputLogOnePlusV_eq }

private noncomputable def leaf4901Inputs : Inputs :=
  inputsOfCaches globalInput sk215RoundedInputs
    chi284InputQChi innerPair116Input
    leaf4901InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4901LowerChecked :
    lowerCheck 24 leaf4901Box leaf4901Inputs = true := by
  rfl'

private theorem leaf4901CoversExact : CoversExact 8
    leaf4901Box leaf4901Certificate leaf4901InnerLog leaf4901Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk215RoundedFacts chi284RoundedFacts
    innerPair116RoundedFacts leaf4901RoundedFacts (by rfl)

private theorem leaf4901FlatSound : Sound leaf4901Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4901CertificateValid
    leaf4901InnerLogValid leaf4901CoversExact leaf4901LowerChecked

private noncomputable def leaf4902Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (229/64), kHi := (115/32), chiLo := (75/256), chiHi := (19/64) }

private noncomputable def leaf4902Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742435/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715001856) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2199220547/2147483648) }, upper := { exponent := 1, mantissa := (4233/4096) } }, logOuter := sk216LogOuterCertificate, logK := sk216LogKCertificate, logChi := chi284LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432414207/137430003712) } }, logDArg := sk216LogDArgCertificate }

private noncomputable def leaf4902InnerLog : WideLogData :=
  innerPair117Data

set_option maxRecDepth 1000000 in
private theorem leaf4902LocalValidity :
    LeafFacts leaf4902Box leaf4902Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4902Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715001856) }) = true
      norm_num [leaf4902Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4902CertificateValid :
    WideCertificateValid leaf4902Box leaf4902Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk216ValidityFacts chi284ValidityFacts
    leaf4902LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4902CoverageChecked :
    coverageCheck (innerAD leaf4902Box) leaf4902InnerLog = true := by
  rfl'

private theorem leaf4902InnerLogValid :
    leaf4902InnerLog.Valid 8 (innerAD leaf4902Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint73PositiveFacts.valid leaf4902CoverageChecked

private noncomputable def leaf4902InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629375/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4902InputLogOnePlusV_eq :
    leaf4902InputLogOnePlusV = outerEnclosure 24
      (leaf4902Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4902RoundedFacts : LeafRoundedFacts 8
    leaf4902Certificate.logOnePlusV leaf4902InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4902InputLogOnePlusV_eq }

private noncomputable def leaf4902Inputs : Inputs :=
  inputsOfCaches globalInput sk216RoundedInputs
    chi284InputQChi innerPair117Input
    leaf4902InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4902LowerChecked :
    lowerCheck 24 leaf4902Box leaf4902Inputs = true := by
  rfl'

private theorem leaf4902CoversExact : CoversExact 8
    leaf4902Box leaf4902Certificate leaf4902InnerLog leaf4902Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk216RoundedFacts chi284RoundedFacts
    innerPair117RoundedFacts leaf4902RoundedFacts (by rfl)

private theorem leaf4902FlatSound : Sound leaf4902Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4902CertificateValid
    leaf4902InnerLogValid leaf4902CoversExact leaf4902LowerChecked

private noncomputable def leaf4903Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (231/64), chiLo := (37/128), chiHi := (75/256) }

private noncomputable def leaf4903Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742435/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715041536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2189063087/2147483648) }, upper := { exponent := 1, mantissa := (33709/32768) } }, logOuter := sk209LogOuterCertificate, logK := sk209LogKCertificate, logChi := chi283LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432453887/137430083072) } }, logDArg := sk209LogDArgCertificate }

private noncomputable def leaf4903InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4903LocalValidity :
    LeafFacts leaf4903Box leaf4903Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4903Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715041536) }) = true
      norm_num [leaf4903Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4903CertificateValid :
    WideCertificateValid leaf4903Box leaf4903Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk209ValidityFacts chi283ValidityFacts
    leaf4903LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4903CoverageChecked :
    coverageCheck (innerAD leaf4903Box) leaf4903InnerLog = true := by
  rfl'

private theorem leaf4903InnerLogValid :
    leaf4903InnerLog.Valid 8 (innerAD leaf4903Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4903CoverageChecked

private noncomputable def leaf4903InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814685/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4903InputLogOnePlusV_eq :
    leaf4903InputLogOnePlusV = outerEnclosure 24
      (leaf4903Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4903RoundedFacts : LeafRoundedFacts 8
    leaf4903Certificate.logOnePlusV leaf4903InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4903InputLogOnePlusV_eq }

private noncomputable def leaf4903Inputs : Inputs :=
  inputsOfCaches globalInput sk209RoundedInputs
    chi283InputQChi innerPair116Input
    leaf4903InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4903LowerChecked :
    lowerCheck 24 leaf4903Box leaf4903Inputs = true := by
  rfl'

private theorem leaf4903CoversExact : CoversExact 8
    leaf4903Box leaf4903Certificate leaf4903InnerLog leaf4903Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk209RoundedFacts chi283RoundedFacts
    innerPair116RoundedFacts leaf4903RoundedFacts (by rfl)

private theorem leaf4903FlatSound : Sound leaf4903Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4903CertificateValid
    leaf4903InnerLogValid leaf4903CoversExact leaf4903LowerChecked

private noncomputable def leaf4904Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (231/64), kHi := (29/8), chiLo := (37/128), chiHi := (75/256) }

private noncomputable def leaf4904Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742437/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715022336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2193912453/2147483648) }, upper := { exponent := 1, mantissa := (4223/4096) } }, logOuter := sk210LogOuterCertificate, logK := sk210LogKCertificate, logChi := chi283LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432434687/137430044672) } }, logDArg := sk210LogDArgCertificate }

private noncomputable def leaf4904InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4904LocalValidity :
    LeafFacts leaf4904Box leaf4904Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4904Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715022336) }) = true
      norm_num [leaf4904Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4904CertificateValid :
    WideCertificateValid leaf4904Box leaf4904Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk210ValidityFacts chi283ValidityFacts
    leaf4904LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4904CoverageChecked :
    coverageCheck (innerAD leaf4904Box) leaf4904InnerLog = true := by
  rfl'

private theorem leaf4904InnerLogValid :
    leaf4904InnerLog.Valid 8 (innerAD leaf4904Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4904CoverageChecked

private noncomputable def leaf4904InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629373/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4904InputLogOnePlusV_eq :
    leaf4904InputLogOnePlusV = outerEnclosure 24
      (leaf4904Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4904RoundedFacts : LeafRoundedFacts 8
    leaf4904Certificate.logOnePlusV leaf4904InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4904InputLogOnePlusV_eq }

private noncomputable def leaf4904Inputs : Inputs :=
  inputsOfCaches globalInput sk210RoundedInputs
    chi283InputQChi innerPair116Input
    leaf4904InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4904LowerChecked :
    lowerCheck 24 leaf4904Box leaf4904Inputs = true := by
  rfl'

private theorem leaf4904CoversExact : CoversExact 8
    leaf4904Box leaf4904Certificate leaf4904InnerLog leaf4904Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk210RoundedFacts chi283RoundedFacts
    innerPair116RoundedFacts leaf4904RoundedFacts (by rfl)

private theorem leaf4904FlatSound : Sound leaf4904Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4904CertificateValid
    leaf4904InnerLogValid leaf4904CoversExact leaf4904LowerChecked

private noncomputable def leaf4905Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (231/64), chiLo := (75/256), chiHi := (19/64) }

private noncomputable def leaf4905Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742437/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714982400) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2204135445/2147483648) }, upper := { exponent := 1, mantissa := (8485/8192) } }, logOuter := sk209LogOuterCertificate, logK := sk209LogKCertificate, logChi := chi284LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432394751/137429964800) } }, logDArg := sk209LogDArgCertificate }

private noncomputable def leaf4905InnerLog : WideLogData :=
  innerPair117Data

set_option maxRecDepth 1000000 in
private theorem leaf4905LocalValidity :
    LeafFacts leaf4905Box leaf4905Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4905Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714982400) }) = true
      norm_num [leaf4905Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4905CertificateValid :
    WideCertificateValid leaf4905Box leaf4905Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk209ValidityFacts chi284ValidityFacts
    leaf4905LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4905CoverageChecked :
    coverageCheck (innerAD leaf4905Box) leaf4905InnerLog = true := by
  rfl'

private theorem leaf4905InnerLogValid :
    leaf4905InnerLog.Valid 8 (innerAD leaf4905Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint73PositiveFacts.valid leaf4905CoverageChecked

private noncomputable def leaf4905InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629377/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4905InputLogOnePlusV_eq :
    leaf4905InputLogOnePlusV = outerEnclosure 24
      (leaf4905Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4905RoundedFacts : LeafRoundedFacts 8
    leaf4905Certificate.logOnePlusV leaf4905InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4905InputLogOnePlusV_eq }

private noncomputable def leaf4905Inputs : Inputs :=
  inputsOfCaches globalInput sk209RoundedInputs
    chi284InputQChi innerPair117Input
    leaf4905InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4905LowerChecked :
    lowerCheck 24 leaf4905Box leaf4905Inputs = true := by
  rfl'

private theorem leaf4905CoversExact : CoversExact 8
    leaf4905Box leaf4905Certificate leaf4905InnerLog leaf4905Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk209RoundedFacts chi284RoundedFacts
    innerPair117RoundedFacts leaf4905RoundedFacts (by rfl)

private theorem leaf4905FlatSound : Sound leaf4905Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4905CertificateValid
    leaf4905InnerLogValid leaf4905CoversExact leaf4905LowerChecked

private noncomputable def leaf4906Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (231/64), kHi := (29/8), chiLo := (75/256), chiHi := (19/64) }

private noncomputable def leaf4906Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742439/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22905804117/22904987648) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2209050343/2147483648) }, upper := { exponent := 1, mantissa := (1063/1024) } }, logOuter := sk210LogOuterCertificate, logK := sk210LogKCertificate, logChi := chi284LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45810791765/45809975296) } }, logDArg := sk210LogDArgCertificate }

private noncomputable def leaf4906InnerLog : WideLogData :=
  innerPair117Data

set_option maxRecDepth 1000000 in
private theorem leaf4906LocalValidity :
    LeafFacts leaf4906Box leaf4906Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4906Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22905804117/22904987648) }) = true
      norm_num [leaf4906Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4906CertificateValid :
    WideCertificateValid leaf4906Box leaf4906Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk210ValidityFacts chi284ValidityFacts
    leaf4906LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4906CoverageChecked :
    coverageCheck (innerAD leaf4906Box) leaf4906InnerLog = true := by
  rfl'

private theorem leaf4906InnerLogValid :
    leaf4906InnerLog.Valid 8 (innerAD leaf4906Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint73PositiveFacts.valid leaf4906CoverageChecked

private noncomputable def leaf4906InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907345/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4906InputLogOnePlusV_eq :
    leaf4906InputLogOnePlusV = outerEnclosure 24
      (leaf4906Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4906RoundedFacts : LeafRoundedFacts 8
    leaf4906Certificate.logOnePlusV leaf4906InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4906InputLogOnePlusV_eq }

private noncomputable def leaf4906Inputs : Inputs :=
  inputsOfCaches globalInput sk210RoundedInputs
    chi284InputQChi innerPair117Input
    leaf4906InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4906LowerChecked :
    lowerCheck 24 leaf4906Box leaf4906Inputs = true := by
  rfl'

private theorem leaf4906CoversExact : CoversExact 8
    leaf4906Box leaf4906Certificate leaf4906InnerLog leaf4906Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk210RoundedFacts chi284RoundedFacts
    innerPair117RoundedFacts leaf4906RoundedFacts (by rfl)

private theorem leaf4906FlatSound : Sound leaf4906Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4906CertificateValid
    leaf4906InnerLogValid leaf4906CoversExact leaf4906LowerChecked

private noncomputable def leaf4907Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (19/64), chiHi := (77/256) }

private noncomputable def leaf4907Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871291/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357510912) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1094646151/1073741824) }, upper := { exponent := 1, mantissa := (16893/16384) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi285LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68716233471/68715021824) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf4907InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4907LocalValidity :
    LeafFacts leaf4907Box leaf4907Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4907Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357510912) }) = true
      norm_num [leaf4907Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4907CertificateValid :
    WideCertificateValid leaf4907Box leaf4907Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi285ValidityFacts
    leaf4907LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4907CoverageChecked :
    coverageCheck (innerAD leaf4907Box) leaf4907InnerLog = true := by
  rfl'

private theorem leaf4907InnerLogValid :
    leaf4907InnerLog.Valid 8 (innerAD leaf4907Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4907CoverageChecked

private noncomputable def leaf4907InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629377/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4907InputLogOnePlusV_eq :
    leaf4907InputLogOnePlusV = outerEnclosure 24
      (leaf4907Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4907RoundedFacts : LeafRoundedFacts 8
    leaf4907Certificate.logOnePlusV leaf4907InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4907InputLogOnePlusV_eq }

private noncomputable def leaf4907Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi285InputQChi innerPair116Input
    leaf4907InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4907LowerChecked :
    lowerCheck 24 leaf4907Box leaf4907Inputs = true := by
  rfl'

private theorem leaf4907CoversExact : CoversExact 8
    leaf4907Box leaf4907Certificate leaf4907InnerLog leaf4907Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi285RoundedFacts
    innerPair116RoundedFacts leaf4907RoundedFacts (by rfl)

private theorem leaf4907FlatSound : Sound leaf4907Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4907CertificateValid
    leaf4907InnerLogValid leaf4907CoversExact leaf4907LowerChecked

private noncomputable def leaf4908Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (77/256), chiHi := (39/128) }

private noncomputable def leaf4908Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871293/536870912) }, vSqrt := { lower := (8191/8192), upper := (288728761/288718336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1101985733/1073741824) }, upper := { exponent := 1, mantissa := (8503/8192) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi286LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (577447097/577436672) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf4908InnerLog : WideLogData :=
  innerPair327Data

set_option maxRecDepth 1000000 in
private theorem leaf4908LocalValidity :
    LeafFacts leaf4908Box leaf4908Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4908Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (288728761/288718336) }) = true
      norm_num [leaf4908Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4908CertificateValid :
    WideCertificateValid leaf4908Box leaf4908Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi286ValidityFacts
    leaf4908LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4908CoverageChecked :
    coverageCheck (innerAD leaf4908Box) leaf4908InnerLog = true := by
  rfl'

private theorem leaf4908InnerLogValid :
    leaf4908InnerLog.Valid 8 (innerAD leaf4908Box) :=
  wideLogDataValid_of_cachedCheck endpoint87PositiveFacts
    endpoint86PositiveFacts.valid leaf4908CoverageChecked

private noncomputable def leaf4908InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453673/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf4908InputLogOnePlusV_eq :
    leaf4908InputLogOnePlusV = outerEnclosure 24
      (leaf4908Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4908RoundedFacts : LeafRoundedFacts 8
    leaf4908Certificate.logOnePlusV leaf4908InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4908InputLogOnePlusV_eq }

private noncomputable def leaf4908Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi286InputQChi innerPair327Input
    leaf4908InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4908LowerChecked :
    lowerCheck 24 leaf4908Box leaf4908Inputs = true := by
  rfl'

private theorem leaf4908CoversExact : CoversExact 8
    leaf4908Box leaf4908Certificate leaf4908InnerLog leaf4908Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi286RoundedFacts
    innerPair327RoundedFacts leaf4908RoundedFacts (by rfl)

private theorem leaf4908FlatSound : Sound leaf4908Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4908CertificateValid
    leaf4908InnerLogValid leaf4908CoversExact leaf4908LowerChecked

private noncomputable def leaf4909Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (19/64), chiHi := (77/256) }

private noncomputable def leaf4909Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871293/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357491200) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1099626581/1073741824) }, upper := { exponent := 1, mantissa := (8485/8192) } }, logOuter := sk168LogOuterCertificate, logK := sk168LogKCertificate, logChi := chi285LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68716213759/68714982400) } }, logDArg := sk168LogDArgCertificate }

private noncomputable def leaf4909InnerLog : WideLogData :=
  innerPair625Data

set_option maxRecDepth 1000000 in
private theorem leaf4909LocalValidity :
    LeafFacts leaf4909Box leaf4909Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4909Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357491200) }) = true
      norm_num [leaf4909Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4909CertificateValid :
    WideCertificateValid leaf4909Box leaf4909Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk168ValidityFacts chi285ValidityFacts
    leaf4909LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4909CoverageChecked :
    coverageCheck (innerAD leaf4909Box) leaf4909InnerLog = true := by
  rfl'

private theorem leaf4909InnerLogValid :
    leaf4909InnerLog.Valid 8 (innerAD leaf4909Box) :=
  wideLogDataValid_of_cachedCheck endpoint353PositiveFacts
    endpoint354PositiveFacts.valid leaf4909CoverageChecked

private noncomputable def leaf4909InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629381/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4909InputLogOnePlusV_eq :
    leaf4909InputLogOnePlusV = outerEnclosure 24
      (leaf4909Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4909RoundedFacts : LeafRoundedFacts 8
    leaf4909Certificate.logOnePlusV leaf4909InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4909InputLogOnePlusV_eq }

private noncomputable def leaf4909Inputs : Inputs :=
  inputsOfCaches globalInput sk168RoundedInputs
    chi285InputQChi innerPair625Input
    leaf4909InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4909LowerChecked :
    lowerCheck 24 leaf4909Box leaf4909Inputs = true := by
  rfl'

private theorem leaf4909CoversExact : CoversExact 8
    leaf4909Box leaf4909Certificate leaf4909InnerLog leaf4909Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk168RoundedFacts chi285RoundedFacts
    innerPair625RoundedFacts leaf4909RoundedFacts (by rfl)

private theorem leaf4909FlatSound : Sound leaf4909Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4909CertificateValid
    leaf4909InnerLogValid leaf4909CoversExact leaf4909LowerChecked

private noncomputable def leaf4910Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (77/256), chiHi := (39/128) }

private noncomputable def leaf4910Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871295/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357462016) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1107031695/1073741824) }, upper := { exponent := 1, mantissa := (4271/4096) } }, logOuter := sk168LogOuterCertificate, logK := sk168LogKCertificate, logChi := chi286LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68716184575/68714924032) } }, logDArg := sk168LogDArgCertificate }

private noncomputable def leaf4910InnerLog : WideLogData :=
  innerPair608Data

set_option maxRecDepth 1000000 in
private theorem leaf4910LocalValidity :
    LeafFacts leaf4910Box leaf4910Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4910Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357462016) }) = true
      norm_num [leaf4910Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4910CertificateValid :
    WideCertificateValid leaf4910Box leaf4910Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk168ValidityFacts chi286ValidityFacts
    leaf4910LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4910CoverageChecked :
    coverageCheck (innerAD leaf4910Box) leaf4910InnerLog = true := by
  rfl'

private theorem leaf4910InnerLogValid :
    leaf4910InnerLog.Valid 8 (innerAD leaf4910Box) :=
  wideLogDataValid_of_cachedCheck endpoint332PositiveFacts
    endpoint355PositiveFacts.valid leaf4910CoverageChecked

private noncomputable def leaf4910InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629389/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4910InputLogOnePlusV_eq :
    leaf4910InputLogOnePlusV = outerEnclosure 24
      (leaf4910Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4910RoundedFacts : LeafRoundedFacts 8
    leaf4910Certificate.logOnePlusV leaf4910InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4910InputLogOnePlusV_eq }

private noncomputable def leaf4910Inputs : Inputs :=
  inputsOfCaches globalInput sk168RoundedInputs
    chi286InputQChi innerPair608Input
    leaf4910InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4910LowerChecked :
    lowerCheck 24 leaf4910Box leaf4910Inputs = true := by
  rfl'

private theorem leaf4910CoversExact : CoversExact 8
    leaf4910Box leaf4910Certificate leaf4910InnerLog leaf4910Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk168RoundedFacts chi286RoundedFacts
    innerPair608RoundedFacts leaf4910RoundedFacts (by rfl)

private theorem leaf4910FlatSound : Sound leaf4910Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4910CertificateValid
    leaf4910InnerLogValid leaf4910CoversExact leaf4910LowerChecked

private noncomputable def leaf4911Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (39/128), chiHi := (79/256) }

private noncomputable def leaf4911Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871295/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357453056) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1109325315/1073741824) }, upper := { exponent := 1, mantissa := (17119/16384) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi287LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68716175615/68714906112) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf4911InnerLog : WideLogData :=
  innerPair248Data

set_option maxRecDepth 1000000 in
private theorem leaf4911LocalValidity :
    LeafFacts leaf4911Box leaf4911Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4911Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357453056) }) = true
      norm_num [leaf4911Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4911CertificateValid :
    WideCertificateValid leaf4911Box leaf4911Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi287ValidityFacts
    leaf4911LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4911CoverageChecked :
    coverageCheck (innerAD leaf4911Box) leaf4911InnerLog = true := by
  rfl'

private theorem leaf4911InnerLogValid :
    leaf4911InnerLog.Valid 8 (innerAD leaf4911Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint284PositiveFacts.valid leaf4911CoverageChecked

private noncomputable def leaf4911InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629391/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4911InputLogOnePlusV_eq :
    leaf4911InputLogOnePlusV = outerEnclosure 24
      (leaf4911Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4911RoundedFacts : LeafRoundedFacts 8
    leaf4911Certificate.logOnePlusV leaf4911InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4911InputLogOnePlusV_eq }

private noncomputable def leaf4911Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi287InputQChi innerPair248Input
    leaf4911InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4911LowerChecked :
    lowerCheck 24 leaf4911Box leaf4911Inputs = true := by
  rfl'

private theorem leaf4911CoversExact : CoversExact 8
    leaf4911Box leaf4911Certificate leaf4911InnerLog leaf4911Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi287RoundedFacts
    innerPair248RoundedFacts leaf4911RoundedFacts (by rfl)

private theorem leaf4911FlatSound : Sound leaf4911Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4911CertificateValid
    leaf4911InnerLogValid leaf4911CoversExact leaf4911LowerChecked

private noncomputable def leaf4912Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (79/256), chiHi := (5/16) }

private noncomputable def leaf4912Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871297/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357424128) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1116664897/1073741824) }, upper := { exponent := 1, mantissa := (1077/1024) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi288LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68716146687/68714848256) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf4912InnerLog : WideLogData :=
  innerPair323Data

set_option maxRecDepth 1000000 in
private theorem leaf4912LocalValidity :
    LeafFacts leaf4912Box leaf4912Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4912Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357424128) }) = true
      norm_num [leaf4912Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4912CertificateValid :
    WideCertificateValid leaf4912Box leaf4912Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi288ValidityFacts
    leaf4912LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4912CoverageChecked :
    coverageCheck (innerAD leaf4912Box) leaf4912InnerLog = true := by
  rfl'

private theorem leaf4912InnerLogValid :
    leaf4912InnerLog.Valid 8 (innerAD leaf4912Box) :=
  wideLogDataValid_of_cachedCheck endpoint86PositiveFacts
    endpoint89PositiveFacts.valid leaf4912CoverageChecked

private noncomputable def leaf4912InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814699/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4912InputLogOnePlusV_eq :
    leaf4912InputLogOnePlusV = outerEnclosure 24
      (leaf4912Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4912RoundedFacts : LeafRoundedFacts 8
    leaf4912Certificate.logOnePlusV leaf4912InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4912InputLogOnePlusV_eq }

private noncomputable def leaf4912Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi288InputQChi innerPair323Input
    leaf4912InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4912LowerChecked :
    lowerCheck 24 leaf4912Box leaf4912Inputs = true := by
  rfl'

private theorem leaf4912CoversExact : CoversExact 8
    leaf4912Box leaf4912Certificate leaf4912InnerLog leaf4912Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi288RoundedFacts
    innerPair323RoundedFacts leaf4912RoundedFacts (by rfl)

private theorem leaf4912FlatSound : Sound leaf4912Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4912CertificateValid
    leaf4912InnerLogValid leaf4912CoversExact leaf4912LowerChecked

private noncomputable def leaf4913Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (39/128), chiHi := (79/256) }

private noncomputable def leaf4913Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871297/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357432832) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1114436809/1073741824) }, upper := { exponent := 1, mantissa := (8599/8192) } }, logOuter := sk168LogOuterCertificate, logK := sk168LogKCertificate, logChi := chi287LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68716155391/68714865664) } }, logDArg := sk168LogDArgCertificate }

private noncomputable def leaf4913InnerLog : WideLogData :=
  innerPair627Data

set_option maxRecDepth 1000000 in
private theorem leaf4913LocalValidity :
    LeafFacts leaf4913Box leaf4913Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4913Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357432832) }) = true
      norm_num [leaf4913Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4913CertificateValid :
    WideCertificateValid leaf4913Box leaf4913Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk168ValidityFacts chi287ValidityFacts
    leaf4913LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4913CoverageChecked :
    coverageCheck (innerAD leaf4913Box) leaf4913InnerLog = true := by
  rfl'

private theorem leaf4913InnerLogValid :
    leaf4913InnerLog.Valid 8 (innerAD leaf4913Box) :=
  wideLogDataValid_of_cachedCheck endpoint356PositiveFacts
    endpoint357PositiveFacts.valid leaf4913CoverageChecked

private noncomputable def leaf4913InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907349/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4913InputLogOnePlusV_eq :
    leaf4913InputLogOnePlusV = outerEnclosure 24
      (leaf4913Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4913RoundedFacts : LeafRoundedFacts 8
    leaf4913Certificate.logOnePlusV leaf4913InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4913InputLogOnePlusV_eq }

private noncomputable def leaf4913Inputs : Inputs :=
  inputsOfCaches globalInput sk168RoundedInputs
    chi287InputQChi innerPair627Input
    leaf4913InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4913LowerChecked :
    lowerCheck 24 leaf4913Box leaf4913Inputs = true := by
  rfl'

private theorem leaf4913CoversExact : CoversExact 8
    leaf4913Box leaf4913Certificate leaf4913InnerLog leaf4913Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk168RoundedFacts chi287RoundedFacts
    innerPair627RoundedFacts leaf4913RoundedFacts (by rfl)

private theorem leaf4913FlatSound : Sound leaf4913Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4913CertificateValid
    leaf4913InnerLogValid leaf4913CoversExact leaf4913LowerChecked

private noncomputable def leaf4914Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (79/256), chiHi := (5/16) }

private noncomputable def leaf4914Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871299/536870912) }, vSqrt := { lower := (8191/8192), upper := (2021101327/2021023744) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1121841923/1073741824) }, upper := { exponent := 1, mantissa := (541/512) } }, logOuter := sk168LogOuterCertificate, logK := sk168LogKCertificate, logChi := chi288LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (4042125071/4042047488) } }, logDArg := sk168LogDArgCertificate }

private noncomputable def leaf4914InnerLog : WideLogData :=
  innerPair626Data

set_option maxRecDepth 1000000 in
private theorem leaf4914LocalValidity :
    LeafFacts leaf4914Box leaf4914Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4914Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (2021101327/2021023744) }) = true
      norm_num [leaf4914Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4914CertificateValid :
    WideCertificateValid leaf4914Box leaf4914Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk168ValidityFacts chi288ValidityFacts
    leaf4914LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4914CoverageChecked :
    coverageCheck (innerAD leaf4914Box) leaf4914InnerLog = true := by
  rfl'

private theorem leaf4914InnerLogValid :
    leaf4914InnerLog.Valid 8 (innerAD leaf4914Box) :=
  wideLogDataValid_of_cachedCheck endpoint355PositiveFacts
    endpoint358PositiveFacts.valid leaf4914CoverageChecked

private noncomputable def leaf4914InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629403/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4914InputLogOnePlusV_eq :
    leaf4914InputLogOnePlusV = outerEnclosure 24
      (leaf4914Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4914RoundedFacts : LeafRoundedFacts 8
    leaf4914Certificate.logOnePlusV leaf4914InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4914InputLogOnePlusV_eq }

private noncomputable def leaf4914Inputs : Inputs :=
  inputsOfCaches globalInput sk168RoundedInputs
    chi288InputQChi innerPair626Input
    leaf4914InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4914LowerChecked :
    lowerCheck 24 leaf4914Box leaf4914Inputs = true := by
  rfl'

private theorem leaf4914CoversExact : CoversExact 8
    leaf4914Box leaf4914Certificate leaf4914InnerLog leaf4914Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk168RoundedFacts chi288RoundedFacts
    innerPair626RoundedFacts leaf4914RoundedFacts (by rfl)

private theorem leaf4914FlatSound : Sound leaf4914Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4914CertificateValid
    leaf4914InnerLogValid leaf4914CoversExact leaf4914LowerChecked

private noncomputable def leaf4915Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (229/64), chiLo := (19/64), chiHi := (77/256) }

private noncomputable def leaf4915Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742435/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714962688) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2209246943/2147483648) }, upper := { exponent := 1, mantissa := (34017/32768) } }, logOuter := sk215LogOuterCertificate, logK := sk215LogKCertificate, logChi := chi285LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432375039/137429925376) } }, logDArg := sk215LogDArgCertificate }

private noncomputable def leaf4915InnerLog : WideLogData :=
  innerPair117Data

set_option maxRecDepth 1000000 in
private theorem leaf4915LocalValidity :
    LeafFacts leaf4915Box leaf4915Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4915Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714962688) }) = true
      norm_num [leaf4915Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4915CertificateValid :
    WideCertificateValid leaf4915Box leaf4915Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk215ValidityFacts chi285ValidityFacts
    leaf4915LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4915CoverageChecked :
    coverageCheck (innerAD leaf4915Box) leaf4915InnerLog = true := by
  rfl'

private theorem leaf4915InnerLogValid :
    leaf4915InnerLog.Valid 8 (innerAD leaf4915Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint73PositiveFacts.valid leaf4915CoverageChecked

private noncomputable def leaf4915InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907345/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4915InputLogOnePlusV_eq :
    leaf4915InputLogOnePlusV = outerEnclosure 24
      (leaf4915Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4915RoundedFacts : LeafRoundedFacts 8
    leaf4915Certificate.logOnePlusV leaf4915InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4915InputLogOnePlusV_eq }

private noncomputable def leaf4915Inputs : Inputs :=
  inputsOfCaches globalInput sk215RoundedInputs
    chi285InputQChi innerPair117Input
    leaf4915InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4915LowerChecked :
    lowerCheck 24 leaf4915Box leaf4915Inputs = true := by
  rfl'

private theorem leaf4915CoversExact : CoversExact 8
    leaf4915Box leaf4915Certificate leaf4915InnerLog leaf4915Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk215RoundedFacts chi285RoundedFacts
    innerPair117RoundedFacts leaf4915RoundedFacts (by rfl)

private theorem leaf4915FlatSound : Sound leaf4915Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4915CertificateValid
    leaf4915InnerLogValid leaf4915CoversExact leaf4915LowerChecked

private noncomputable def leaf4916Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (229/64), kHi := (115/32), chiLo := (19/64), chiHi := (77/256) }

private noncomputable def leaf4916Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742437/1073741824) }, vSqrt := { lower := (8191/8192), upper := (7635268039/7634993664) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2214227373/2147483648) }, upper := { exponent := 1, mantissa := (17047/16384) } }, logOuter := sk216LogOuterCertificate, logK := sk216LogKCertificate, logChi := chi285LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (15270261703/15269987328) } }, logDArg := sk216LogDArgCertificate }

private noncomputable def leaf4916InnerLog : WideLogData :=
  innerPair117Data

set_option maxRecDepth 1000000 in
private theorem leaf4916LocalValidity :
    LeafFacts leaf4916Box leaf4916Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4916Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (7635268039/7634993664) }) = true
      norm_num [leaf4916Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4916CertificateValid :
    WideCertificateValid leaf4916Box leaf4916Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk216ValidityFacts chi285ValidityFacts
    leaf4916LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4916CoverageChecked :
    coverageCheck (innerAD leaf4916Box) leaf4916InnerLog = true := by
  rfl'

private theorem leaf4916InnerLogValid :
    leaf4916InnerLog.Valid 8 (innerAD leaf4916Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint73PositiveFacts.valid leaf4916CoverageChecked

private noncomputable def leaf4916InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814691/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4916InputLogOnePlusV_eq :
    leaf4916InputLogOnePlusV = outerEnclosure 24
      (leaf4916Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4916RoundedFacts : LeafRoundedFacts 8
    leaf4916Certificate.logOnePlusV leaf4916InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4916InputLogOnePlusV_eq }

private noncomputable def leaf4916Inputs : Inputs :=
  inputsOfCaches globalInput sk216RoundedInputs
    chi285InputQChi innerPair117Input
    leaf4916InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4916LowerChecked :
    lowerCheck 24 leaf4916Box leaf4916Inputs = true := by
  rfl'

private theorem leaf4916CoversExact : CoversExact 8
    leaf4916Box leaf4916Certificate leaf4916InnerLog leaf4916Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk216RoundedFacts chi285RoundedFacts
    innerPair117RoundedFacts leaf4916RoundedFacts (by rfl)

private theorem leaf4916FlatSound : Sound leaf4916Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4916CertificateValid
    leaf4916InnerLogValid leaf4916CoversExact leaf4916LowerChecked

private noncomputable def leaf4917Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (77/256), chiHi := (39/128) }

private noncomputable def leaf4917Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871297/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357442048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1112077657/1073741824) }, upper := { exponent := 1, mantissa := (8581/8192) } }, logOuter := sk161LogOuterCertificate, logK := sk161LogKCertificate, logChi := chi286LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68716164607/68714884096) } }, logDArg := sk161LogDArgCertificate }

private noncomputable def leaf4917InnerLog : WideLogData :=
  innerPair606Data

set_option maxRecDepth 1000000 in
private theorem leaf4917LocalValidity :
    LeafFacts leaf4917Box leaf4917Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4917Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357442048) }) = true
      norm_num [leaf4917Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4917CertificateValid :
    WideCertificateValid leaf4917Box leaf4917Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk161ValidityFacts chi286ValidityFacts
    leaf4917LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4917CoverageChecked :
    coverageCheck (innerAD leaf4917Box) leaf4917InnerLog = true := by
  rfl'

private theorem leaf4917InnerLogValid :
    leaf4917InnerLog.Valid 8 (innerAD leaf4917Box) :=
  wideLogDataValid_of_cachedCheck endpoint331PositiveFacts
    endpoint359PositiveFacts.valid leaf4917CoverageChecked

private noncomputable def leaf4917InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629393/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4917InputLogOnePlusV_eq :
    leaf4917InputLogOnePlusV = outerEnclosure 24
      (leaf4917Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4917RoundedFacts : LeafRoundedFacts 8
    leaf4917Certificate.logOnePlusV leaf4917InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4917InputLogOnePlusV_eq }

private noncomputable def leaf4917Inputs : Inputs :=
  inputsOfCaches globalInput sk161RoundedInputs
    chi286InputQChi innerPair606Input
    leaf4917InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4917LowerChecked :
    lowerCheck 24 leaf4917Box leaf4917Inputs = true := by
  rfl'

private theorem leaf4917CoversExact : CoversExact 8
    leaf4917Box leaf4917Certificate leaf4917InnerLog leaf4917Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk161RoundedFacts chi286RoundedFacts
    innerPair606RoundedFacts leaf4917RoundedFacts (by rfl)

private theorem leaf4917FlatSound : Sound leaf4917Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4917CertificateValid
    leaf4917InnerLogValid leaf4917CoversExact leaf4917LowerChecked

private noncomputable def leaf4918Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (231/64), chiLo := (19/64), chiHi := (77/256) }

private noncomputable def leaf4918Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742439/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714923264) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2219207803/2147483648) }, upper := { exponent := 1, mantissa := (34171/32768) } }, logOuter := sk209LogOuterCertificate, logK := sk209LogKCertificate, logChi := chi285LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432335615/137429846528) } }, logDArg := sk209LogDArgCertificate }

private noncomputable def leaf4918InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4918LocalValidity :
    LeafFacts leaf4918Box leaf4918Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4918Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714923264) }) = true
      norm_num [leaf4918Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4918CertificateValid :
    WideCertificateValid leaf4918Box leaf4918Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk209ValidityFacts chi285ValidityFacts
    leaf4918LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4918CoverageChecked :
    coverageCheck (innerAD leaf4918Box) leaf4918InnerLog = true := by
  rfl'

private theorem leaf4918InnerLogValid :
    leaf4918InnerLog.Valid 8 (innerAD leaf4918Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4918CoverageChecked

private noncomputable def leaf4918InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629385/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4918InputLogOnePlusV_eq :
    leaf4918InputLogOnePlusV = outerEnclosure 24
      (leaf4918Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4918RoundedFacts : LeafRoundedFacts 8
    leaf4918Certificate.logOnePlusV leaf4918InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4918InputLogOnePlusV_eq }

private noncomputable def leaf4918Inputs : Inputs :=
  inputsOfCaches globalInput sk209RoundedInputs
    chi285InputQChi innerPair242Input
    leaf4918InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4918LowerChecked :
    lowerCheck 24 leaf4918Box leaf4918Inputs = true := by
  rfl'

private theorem leaf4918CoversExact : CoversExact 8
    leaf4918Box leaf4918Certificate leaf4918InnerLog leaf4918Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk209RoundedFacts chi285RoundedFacts
    innerPair242RoundedFacts leaf4918RoundedFacts (by rfl)

private theorem leaf4918FlatSound : Sound leaf4918Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4918CertificateValid
    leaf4918InnerLogValid leaf4918CoversExact leaf4918LowerChecked

private noncomputable def leaf4919Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (231/64), kHi := (29/8), chiLo := (19/64), chiHi := (77/256) }

private noncomputable def leaf4919Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742441/1073741824) }, vSqrt := { lower := (8191/8192), upper := (2216690721/2216609792) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2224188233/2147483648) }, upper := { exponent := 1, mantissa := (4281/4096) } }, logOuter := sk210LogOuterCertificate, logK := sk210LogKCertificate, logChi := chi285LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (4433300513/4433219584) } }, logDArg := sk210LogDArgCertificate }

private noncomputable def leaf4919InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4919LocalValidity :
    LeafFacts leaf4919Box leaf4919Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4919Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (2216690721/2216609792) }) = true
      norm_num [leaf4919Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4919CertificateValid :
    WideCertificateValid leaf4919Box leaf4919Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk210ValidityFacts chi285ValidityFacts
    leaf4919LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4919CoverageChecked :
    coverageCheck (innerAD leaf4919Box) leaf4919InnerLog = true := by
  rfl'

private theorem leaf4919InnerLogValid :
    leaf4919InnerLog.Valid 8 (innerAD leaf4919Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4919CoverageChecked

private noncomputable def leaf4919InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629387/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4919InputLogOnePlusV_eq :
    leaf4919InputLogOnePlusV = outerEnclosure 24
      (leaf4919Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4919RoundedFacts : LeafRoundedFacts 8
    leaf4919Certificate.logOnePlusV leaf4919InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4919InputLogOnePlusV_eq }

private noncomputable def leaf4919Inputs : Inputs :=
  inputsOfCaches globalInput sk210RoundedInputs
    chi285InputQChi innerPair242Input
    leaf4919InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4919LowerChecked :
    lowerCheck 24 leaf4919Box leaf4919Inputs = true := by
  rfl'

private theorem leaf4919CoversExact : CoversExact 8
    leaf4919Box leaf4919Certificate leaf4919InnerLog leaf4919Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk210RoundedFacts chi285RoundedFacts
    innerPair242RoundedFacts leaf4919RoundedFacts (by rfl)

private theorem leaf4919FlatSound : Sound leaf4919Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4919CertificateValid
    leaf4919InnerLogValid leaf4919CoversExact leaf4919LowerChecked

private noncomputable def leaf4920Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (231/64), chiLo := (77/256), chiHi := (39/128) }

private noncomputable def leaf4920Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742441/1073741824) }, vSqrt := { lower := (8191/8192), upper := (1598079357/1598020096) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2234280161/2147483648) }, upper := { exponent := 1, mantissa := (17201/16384) } }, logOuter := sk209LogOuterCertificate, logK := sk209LogKCertificate, logChi := chi286LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (3196099453/3196040192) } }, logDArg := sk209LogDArgCertificate }

private noncomputable def leaf4920InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4920LocalValidity :
    LeafFacts leaf4920Box leaf4920Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4920Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (1598079357/1598020096) }) = true
      norm_num [leaf4920Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4920CertificateValid :
    WideCertificateValid leaf4920Box leaf4920Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk209ValidityFacts chi286ValidityFacts
    leaf4920LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4920CoverageChecked :
    coverageCheck (innerAD leaf4920Box) leaf4920InnerLog = true := by
  rfl'

private theorem leaf4920InnerLogValid :
    leaf4920InnerLog.Valid 8 (innerAD leaf4920Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4920CoverageChecked

private noncomputable def leaf4920InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726837/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf4920InputLogOnePlusV_eq :
    leaf4920InputLogOnePlusV = outerEnclosure 24
      (leaf4920Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4920RoundedFacts : LeafRoundedFacts 8
    leaf4920Certificate.logOnePlusV leaf4920InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4920InputLogOnePlusV_eq }

private noncomputable def leaf4920Inputs : Inputs :=
  inputsOfCaches globalInput sk209RoundedInputs
    chi286InputQChi innerPair242Input
    leaf4920InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4920LowerChecked :
    lowerCheck 24 leaf4920Box leaf4920Inputs = true := by
  rfl'

private theorem leaf4920CoversExact : CoversExact 8
    leaf4920Box leaf4920Certificate leaf4920InnerLog leaf4920Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk209RoundedFacts chi286RoundedFacts
    innerPair242RoundedFacts leaf4920RoundedFacts (by rfl)

private theorem leaf4920FlatSound : Sound leaf4920Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4920CertificateValid
    leaf4920InnerLogValid leaf4920CoversExact leaf4920LowerChecked

private noncomputable def leaf4921Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (231/64), kHi := (29/8), chiLo := (77/256), chiHi := (39/128) }

private noncomputable def leaf4921Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742443/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714844160) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2239326123/2147483648) }, upper := { exponent := 1, mantissa := (2155/2048) } }, logOuter := sk210LogOuterCertificate, logK := sk210LogKCertificate, logChi := chi286LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432256511/137429688320) } }, logDArg := sk210LogDArgCertificate }

private noncomputable def leaf4921InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4921LocalValidity :
    LeafFacts leaf4921Box leaf4921Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4921Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714844160) }) = true
      norm_num [leaf4921Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4921CertificateValid :
    WideCertificateValid leaf4921Box leaf4921Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk210ValidityFacts chi286ValidityFacts
    leaf4921LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4921CoverageChecked :
    coverageCheck (innerAD leaf4921Box) leaf4921InnerLog = true := by
  rfl'

private theorem leaf4921InnerLogValid :
    leaf4921InnerLog.Valid 8 (innerAD leaf4921Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4921CoverageChecked

private noncomputable def leaf4921InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814697/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4921InputLogOnePlusV_eq :
    leaf4921InputLogOnePlusV = outerEnclosure 24
      (leaf4921Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4921RoundedFacts : LeafRoundedFacts 8
    leaf4921Certificate.logOnePlusV leaf4921InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4921InputLogOnePlusV_eq }

private noncomputable def leaf4921Inputs : Inputs :=
  inputsOfCaches globalInput sk210RoundedInputs
    chi286InputQChi innerPair242Input
    leaf4921InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4921LowerChecked :
    lowerCheck 24 leaf4921Box leaf4921Inputs = true := by
  rfl'

private theorem leaf4921CoversExact : CoversExact 8
    leaf4921Box leaf4921Certificate leaf4921InnerLog leaf4921Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk210RoundedFacts chi286RoundedFacts
    innerPair242RoundedFacts leaf4921RoundedFacts (by rfl)

private theorem leaf4921FlatSound : Sound leaf4921Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4921CertificateValid
    leaf4921InnerLogValid leaf4921CoversExact leaf4921LowerChecked

private noncomputable def leaf4922Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (39/128), chiHi := (79/256) }

private noncomputable def leaf4922Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871299/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357412608) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1119548303/1073741824) }, upper := { exponent := 1, mantissa := (17277/16384) } }, logOuter := sk161LogOuterCertificate, logK := sk161LogKCertificate, logChi := chi287LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68716135167/68714825216) } }, logDArg := sk161LogDArgCertificate }

private noncomputable def leaf4922InnerLog : WideLogData :=
  innerPair323Data

set_option maxRecDepth 1000000 in
private theorem leaf4922LocalValidity :
    LeafFacts leaf4922Box leaf4922Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4922Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357412608) }) = true
      norm_num [leaf4922Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4922CertificateValid :
    WideCertificateValid leaf4922Box leaf4922Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk161ValidityFacts chi287ValidityFacts
    leaf4922LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4922CoverageChecked :
    coverageCheck (innerAD leaf4922Box) leaf4922InnerLog = true := by
  rfl'

private theorem leaf4922InnerLogValid :
    leaf4922InnerLog.Valid 8 (innerAD leaf4922Box) :=
  wideLogDataValid_of_cachedCheck endpoint86PositiveFacts
    endpoint89PositiveFacts.valid leaf4922CoverageChecked

private noncomputable def leaf4922InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629401/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4922InputLogOnePlusV_eq :
    leaf4922InputLogOnePlusV = outerEnclosure 24
      (leaf4922Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4922RoundedFacts : LeafRoundedFacts 8
    leaf4922Certificate.logOnePlusV leaf4922InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4922InputLogOnePlusV_eq }

private noncomputable def leaf4922Inputs : Inputs :=
  inputsOfCaches globalInput sk161RoundedInputs
    chi287InputQChi innerPair323Input
    leaf4922InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4922LowerChecked :
    lowerCheck 24 leaf4922Box leaf4922Inputs = true := by
  rfl'

private theorem leaf4922CoversExact : CoversExact 8
    leaf4922Box leaf4922Certificate leaf4922InnerLog leaf4922Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk161RoundedFacts chi287RoundedFacts
    innerPair323RoundedFacts leaf4922RoundedFacts (by rfl)

private theorem leaf4922FlatSound : Sound leaf4922Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4922CertificateValid
    leaf4922InnerLogValid leaf4922CoversExact leaf4922LowerChecked

private noncomputable def leaf4923Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (79/256), chiHi := (5/16) }

private noncomputable def leaf4923Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871301/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357383168) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1127018949/1073741824) }, upper := { exponent := 1, mantissa := (1087/1024) } }, logOuter := sk161LogOuterCertificate, logK := sk161LogKCertificate, logChi := chi288LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68716105727/68714766336) } }, logDArg := sk161LogDArgCertificate }

private noncomputable def leaf4923InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4923LocalValidity :
    LeafFacts leaf4923Box leaf4923Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4923Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357383168) }) = true
      norm_num [leaf4923Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4923CertificateValid :
    WideCertificateValid leaf4923Box leaf4923Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk161ValidityFacts chi288ValidityFacts
    leaf4923LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4923CoverageChecked :
    coverageCheck (innerAD leaf4923Box) leaf4923InnerLog = true := by
  rfl'

private theorem leaf4923InnerLogValid :
    leaf4923InnerLog.Valid 8 (innerAD leaf4923Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4923CoverageChecked

private noncomputable def leaf4923InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (363419/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf4923InputLogOnePlusV_eq :
    leaf4923InputLogOnePlusV = outerEnclosure 24
      (leaf4923Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4923RoundedFacts : LeafRoundedFacts 8
    leaf4923Certificate.logOnePlusV leaf4923InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4923InputLogOnePlusV_eq }

private noncomputable def leaf4923Inputs : Inputs :=
  inputsOfCaches globalInput sk161RoundedInputs
    chi288InputQChi innerPair242Input
    leaf4923InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4923LowerChecked :
    lowerCheck 24 leaf4923Box leaf4923Inputs = true := by
  rfl'

private theorem leaf4923CoversExact : CoversExact 8
    leaf4923Box leaf4923Certificate leaf4923InnerLog leaf4923Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk161RoundedFacts chi288RoundedFacts
    innerPair242RoundedFacts leaf4923RoundedFacts (by rfl)

private theorem leaf4923FlatSound : Sound leaf4923Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4923CertificateValid
    leaf4923InnerLogValid leaf4923CoversExact leaf4923LowerChecked

private noncomputable def leaf4924Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (231/64), chiLo := (39/128), chiHi := (79/256) }

private noncomputable def leaf4924Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742443/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714804992) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2249352519/2147483648) }, upper := { exponent := 1, mantissa := (34633/32768) } }, logOuter := sk209LogOuterCertificate, logK := sk209LogKCertificate, logChi := chi287LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432217343/137429609984) } }, logDArg := sk209LogDArgCertificate }

private noncomputable def leaf4924InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4924LocalValidity :
    LeafFacts leaf4924Box leaf4924Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4924Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714804992) }) = true
      norm_num [leaf4924Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4924CertificateValid :
    WideCertificateValid leaf4924Box leaf4924Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk209ValidityFacts chi287ValidityFacts
    leaf4924LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4924CoverageChecked :
    coverageCheck (innerAD leaf4924Box) leaf4924InnerLog = true := by
  rfl'

private theorem leaf4924InnerLogValid :
    leaf4924InnerLog.Valid 8 (innerAD leaf4924Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4924CoverageChecked

private noncomputable def leaf4924InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629399/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4924InputLogOnePlusV_eq :
    leaf4924InputLogOnePlusV = outerEnclosure 24
      (leaf4924Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4924RoundedFacts : LeafRoundedFacts 8
    leaf4924Certificate.logOnePlusV leaf4924InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4924InputLogOnePlusV_eq }

private noncomputable def leaf4924Inputs : Inputs :=
  inputsOfCaches globalInput sk209RoundedInputs
    chi287InputQChi innerPair242Input
    leaf4924InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4924LowerChecked :
    lowerCheck 24 leaf4924Box leaf4924Inputs = true := by
  rfl'

private theorem leaf4924CoversExact : CoversExact 8
    leaf4924Box leaf4924Certificate leaf4924InnerLog leaf4924Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk209RoundedFacts chi287RoundedFacts
    innerPair242RoundedFacts leaf4924RoundedFacts (by rfl)

private theorem leaf4924FlatSound : Sound leaf4924Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4924CertificateValid
    leaf4924InnerLogValid leaf4924CoversExact leaf4924LowerChecked

private noncomputable def leaf4925Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (231/64), kHi := (29/8), chiLo := (39/128), chiHi := (79/256) }

private noncomputable def leaf4925Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742445/1073741824) }, vSqrt := { lower := (8191/8192), upper := (3272257731/3272132608) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2254464013/2147483648) }, upper := { exponent := 1, mantissa := (4339/4096) } }, logOuter := sk210LogOuterCertificate, logK := sk210LogKCertificate, logChi := chi287LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (6544390339/6544265216) } }, logDArg := sk210LogDArgCertificate }

private noncomputable def leaf4925InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4925LocalValidity :
    LeafFacts leaf4925Box leaf4925Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4925Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (3272257731/3272132608) }) = true
      norm_num [leaf4925Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4925CertificateValid :
    WideCertificateValid leaf4925Box leaf4925Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk210ValidityFacts chi287ValidityFacts
    leaf4925LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4925CoverageChecked :
    coverageCheck (innerAD leaf4925Box) leaf4925InnerLog = true := by
  rfl'

private theorem leaf4925InnerLogValid :
    leaf4925InnerLog.Valid 8 (innerAD leaf4925Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4925CoverageChecked

private noncomputable def leaf4925InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814701/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4925InputLogOnePlusV_eq :
    leaf4925InputLogOnePlusV = outerEnclosure 24
      (leaf4925Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4925RoundedFacts : LeafRoundedFacts 8
    leaf4925Certificate.logOnePlusV leaf4925InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4925InputLogOnePlusV_eq }

private noncomputable def leaf4925Inputs : Inputs :=
  inputsOfCaches globalInput sk210RoundedInputs
    chi287InputQChi innerPair242Input
    leaf4925InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4925LowerChecked :
    lowerCheck 24 leaf4925Box leaf4925Inputs = true := by
  rfl'

private theorem leaf4925CoversExact : CoversExact 8
    leaf4925Box leaf4925Certificate leaf4925InnerLog leaf4925Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk210RoundedFacts chi287RoundedFacts
    innerPair242RoundedFacts leaf4925RoundedFacts (by rfl)

private theorem leaf4925FlatSound : Sound leaf4925Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4925CertificateValid
    leaf4925InnerLogValid leaf4925CoversExact leaf4925LowerChecked

private noncomputable def leaf4926Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (79/256), chiHi := (5/16) }

private noncomputable def leaf4926Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871303/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357362688) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1132195975/1073741824) }, upper := { exponent := 1, mantissa := (273/256) } }, logOuter := sk162LogOuterCertificate, logK := sk162LogKCertificate, logChi := chi288LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68716085247/68714725376) } }, logDArg := sk162LogDArgCertificate }

private noncomputable def leaf4926InnerLog : WideLogData :=
  innerPair610Data

set_option maxRecDepth 1000000 in
private theorem leaf4926LocalValidity :
    LeafFacts leaf4926Box leaf4926Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4926Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357362688) }) = true
      norm_num [leaf4926Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4926CertificateValid :
    WideCertificateValid leaf4926Box leaf4926Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk162ValidityFacts chi288ValidityFacts
    leaf4926LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4926CoverageChecked :
    coverageCheck (innerAD leaf4926Box) leaf4926InnerLog = true := by
  rfl'

private theorem leaf4926InnerLogValid :
    leaf4926InnerLog.Valid 8 (innerAD leaf4926Box) :=
  wideLogDataValid_of_cachedCheck endpoint335PositiveFacts
    endpoint360PositiveFacts.valid leaf4926CoverageChecked

private noncomputable def leaf4926InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629413/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4926InputLogOnePlusV_eq :
    leaf4926InputLogOnePlusV = outerEnclosure 24
      (leaf4926Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4926RoundedFacts : LeafRoundedFacts 8
    leaf4926Certificate.logOnePlusV leaf4926InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4926InputLogOnePlusV_eq }

private noncomputable def leaf4926Inputs : Inputs :=
  inputsOfCaches globalInput sk162RoundedInputs
    chi288InputQChi innerPair610Input
    leaf4926InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4926LowerChecked :
    lowerCheck 24 leaf4926Box leaf4926Inputs = true := by
  rfl'

private theorem leaf4926CoversExact : CoversExact 8
    leaf4926Box leaf4926Certificate leaf4926InnerLog leaf4926Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk162RoundedFacts chi288RoundedFacts
    innerPair610RoundedFacts leaf4926RoundedFacts (by rfl)

private theorem leaf4926FlatSound : Sound leaf4926Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4926CertificateValid
    leaf4926InnerLogValid leaf4926CoversExact leaf4926LowerChecked

private noncomputable def component100Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (9/32), chiHi := (73/256) }

set_option maxRecDepth 1000000 in
private theorem component100Node0_sound : Sound component100Node0Box :=
  sound_of_literal_split component100Node0Box leaf4877Box leaf4878Box
    .k (225/64) (by rfl) (by rfl)
    leaf4877FlatSound leaf4878FlatSound

private noncomputable def component100Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (73/256), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component100Node1_sound : Sound component100Node1Box :=
  sound_of_literal_split component100Node1Box leaf4879Box leaf4880Box
    .k (225/64) (by rfl) (by rfl)
    leaf4879FlatSound leaf4880FlatSound

private noncomputable def component100Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (9/32), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component100Node2_sound : Sound component100Node2Box :=
  sound_of_literal_split component100Node2Box component100Node0Box component100Node1Box
    .chi (73/256) (by rfl) (by rfl)
    component100Node0_sound component100Node1_sound

private noncomputable def component100Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (9/32), chiHi := (73/256) }

set_option maxRecDepth 1000000 in
private theorem component100Node3_sound : Sound component100Node3Box :=
  sound_of_literal_split component100Node3Box leaf4881Box leaf4882Box
    .k (227/64) (by rfl) (by rfl)
    leaf4881FlatSound leaf4882FlatSound

private noncomputable def component100Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (73/256), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component100Node4_sound : Sound component100Node4Box :=
  sound_of_literal_split component100Node4Box leaf4883Box leaf4884Box
    .k (227/64) (by rfl) (by rfl)
    leaf4883FlatSound leaf4884FlatSound

private noncomputable def component100Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (9/32), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component100Node5_sound : Sound component100Node5Box :=
  sound_of_literal_split component100Node5Box component100Node3Box component100Node4Box
    .chi (73/256) (by rfl) (by rfl)
    component100Node3_sound component100Node4_sound

private noncomputable def component100Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (9/32), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component100Node6_sound : Sound component100Node6Box :=
  sound_of_literal_split component100Node6Box component100Node2Box component100Node5Box
    .k (113/32) (by rfl) (by rfl)
    component100Node2_sound component100Node5_sound

private noncomputable def component100Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (37/128), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component100Node7_sound : Sound component100Node7Box :=
  sound_of_literal_split component100Node7Box leaf4885Box leaf4886Box
    .chi (75/256) (by rfl) (by rfl)
    leaf4885FlatSound leaf4886FlatSound

private noncomputable def component100Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (37/128), chiHi := (75/256) }

set_option maxRecDepth 1000000 in
private theorem component100Node8_sound : Sound component100Node8Box :=
  sound_of_literal_split component100Node8Box leaf4887Box leaf4888Box
    .k (227/64) (by rfl) (by rfl)
    leaf4887FlatSound leaf4888FlatSound

private noncomputable def component100Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (75/256), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component100Node9_sound : Sound component100Node9Box :=
  sound_of_literal_split component100Node9Box leaf4889Box leaf4890Box
    .k (227/64) (by rfl) (by rfl)
    leaf4889FlatSound leaf4890FlatSound

private noncomputable def component100Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (37/128), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component100Node10_sound : Sound component100Node10Box :=
  sound_of_literal_split component100Node10Box component100Node8Box component100Node9Box
    .chi (75/256) (by rfl) (by rfl)
    component100Node8_sound component100Node9_sound

private noncomputable def component100Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (37/128), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component100Node11_sound : Sound component100Node11Box :=
  sound_of_literal_split component100Node11Box component100Node7Box component100Node10Box
    .k (113/32) (by rfl) (by rfl)
    component100Node7_sound component100Node10_sound

private noncomputable def component100Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (9/32), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component100Node12_sound : Sound component100Node12Box :=
  sound_of_literal_split component100Node12Box component100Node6Box component100Node11Box
    .chi (37/128) (by rfl) (by rfl)
    component100Node6_sound component100Node11_sound

private noncomputable def component100Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (9/32), chiHi := (73/256) }

set_option maxRecDepth 1000000 in
private theorem component100Node13_sound : Sound component100Node13Box :=
  sound_of_literal_split component100Node13Box leaf4891Box leaf4892Box
    .k (229/64) (by rfl) (by rfl)
    leaf4891FlatSound leaf4892FlatSound

private noncomputable def component100Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (73/256), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component100Node14_sound : Sound component100Node14Box :=
  sound_of_literal_split component100Node14Box leaf4893Box leaf4894Box
    .k (229/64) (by rfl) (by rfl)
    leaf4893FlatSound leaf4894FlatSound

private noncomputable def component100Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (9/32), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component100Node15_sound : Sound component100Node15Box :=
  sound_of_literal_split component100Node15Box component100Node13Box component100Node14Box
    .chi (73/256) (by rfl) (by rfl)
    component100Node13_sound component100Node14_sound

private noncomputable def component100Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (9/32), chiHi := (73/256) }

set_option maxRecDepth 1000000 in
private theorem component100Node16_sound : Sound component100Node16Box :=
  sound_of_literal_split component100Node16Box leaf4895Box leaf4896Box
    .k (231/64) (by rfl) (by rfl)
    leaf4895FlatSound leaf4896FlatSound

private noncomputable def component100Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (73/256), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component100Node17_sound : Sound component100Node17Box :=
  sound_of_literal_split component100Node17Box leaf4897Box leaf4898Box
    .k (231/64) (by rfl) (by rfl)
    leaf4897FlatSound leaf4898FlatSound

private noncomputable def component100Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (9/32), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component100Node18_sound : Sound component100Node18Box :=
  sound_of_literal_split component100Node18Box component100Node16Box component100Node17Box
    .chi (73/256) (by rfl) (by rfl)
    component100Node16_sound component100Node17_sound

private noncomputable def component100Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (9/32), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component100Node19_sound : Sound component100Node19Box :=
  sound_of_literal_split component100Node19Box component100Node15Box component100Node18Box
    .k (115/32) (by rfl) (by rfl)
    component100Node15_sound component100Node18_sound

private noncomputable def component100Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (37/128), chiHi := (75/256) }

set_option maxRecDepth 1000000 in
private theorem component100Node20_sound : Sound component100Node20Box :=
  sound_of_literal_split component100Node20Box leaf4899Box leaf4900Box
    .k (229/64) (by rfl) (by rfl)
    leaf4899FlatSound leaf4900FlatSound

private noncomputable def component100Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (75/256), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component100Node21_sound : Sound component100Node21Box :=
  sound_of_literal_split component100Node21Box leaf4901Box leaf4902Box
    .k (229/64) (by rfl) (by rfl)
    leaf4901FlatSound leaf4902FlatSound

private noncomputable def component100Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (37/128), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component100Node22_sound : Sound component100Node22Box :=
  sound_of_literal_split component100Node22Box component100Node20Box component100Node21Box
    .chi (75/256) (by rfl) (by rfl)
    component100Node20_sound component100Node21_sound

private noncomputable def component100Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (37/128), chiHi := (75/256) }

set_option maxRecDepth 1000000 in
private theorem component100Node23_sound : Sound component100Node23Box :=
  sound_of_literal_split component100Node23Box leaf4903Box leaf4904Box
    .k (231/64) (by rfl) (by rfl)
    leaf4903FlatSound leaf4904FlatSound

private noncomputable def component100Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (75/256), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component100Node24_sound : Sound component100Node24Box :=
  sound_of_literal_split component100Node24Box leaf4905Box leaf4906Box
    .k (231/64) (by rfl) (by rfl)
    leaf4905FlatSound leaf4906FlatSound

private noncomputable def component100Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (37/128), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component100Node25_sound : Sound component100Node25Box :=
  sound_of_literal_split component100Node25Box component100Node23Box component100Node24Box
    .chi (75/256) (by rfl) (by rfl)
    component100Node23_sound component100Node24_sound

private noncomputable def component100Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (37/128), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component100Node26_sound : Sound component100Node26Box :=
  sound_of_literal_split component100Node26Box component100Node22Box component100Node25Box
    .k (115/32) (by rfl) (by rfl)
    component100Node22_sound component100Node25_sound

private noncomputable def component100Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (9/32), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component100Node27_sound : Sound component100Node27Box :=
  sound_of_literal_split component100Node27Box component100Node19Box component100Node26Box
    .chi (37/128) (by rfl) (by rfl)
    component100Node19_sound component100Node26_sound

private noncomputable def component100Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (9/32), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component100Node28_sound : Sound component100Node28Box :=
  sound_of_literal_split component100Node28Box component100Node12Box component100Node27Box
    .k (57/16) (by rfl) (by rfl)
    component100Node12_sound component100Node27_sound

private noncomputable def component100Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (19/64), chiHi := (39/128) }

set_option maxRecDepth 1000000 in
private theorem component100Node29_sound : Sound component100Node29Box :=
  sound_of_literal_split component100Node29Box leaf4907Box leaf4908Box
    .chi (77/256) (by rfl) (by rfl)
    leaf4907FlatSound leaf4908FlatSound

private noncomputable def component100Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (19/64), chiHi := (39/128) }

set_option maxRecDepth 1000000 in
private theorem component100Node30_sound : Sound component100Node30Box :=
  sound_of_literal_split component100Node30Box leaf4909Box leaf4910Box
    .chi (77/256) (by rfl) (by rfl)
    leaf4909FlatSound leaf4910FlatSound

private noncomputable def component100Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (19/64), chiHi := (39/128) }

set_option maxRecDepth 1000000 in
private theorem component100Node31_sound : Sound component100Node31Box :=
  sound_of_literal_split component100Node31Box component100Node29Box component100Node30Box
    .k (113/32) (by rfl) (by rfl)
    component100Node29_sound component100Node30_sound

private noncomputable def component100Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (39/128), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component100Node32_sound : Sound component100Node32Box :=
  sound_of_literal_split component100Node32Box leaf4911Box leaf4912Box
    .chi (79/256) (by rfl) (by rfl)
    leaf4911FlatSound leaf4912FlatSound

private noncomputable def component100Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (39/128), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component100Node33_sound : Sound component100Node33Box :=
  sound_of_literal_split component100Node33Box leaf4913Box leaf4914Box
    .chi (79/256) (by rfl) (by rfl)
    leaf4913FlatSound leaf4914FlatSound

private noncomputable def component100Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (39/128), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component100Node34_sound : Sound component100Node34Box :=
  sound_of_literal_split component100Node34Box component100Node32Box component100Node33Box
    .k (113/32) (by rfl) (by rfl)
    component100Node32_sound component100Node33_sound

private noncomputable def component100Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (19/64), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component100Node35_sound : Sound component100Node35Box :=
  sound_of_literal_split component100Node35Box component100Node31Box component100Node34Box
    .chi (39/128) (by rfl) (by rfl)
    component100Node31_sound component100Node34_sound

private noncomputable def component100Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (19/64), chiHi := (77/256) }

set_option maxRecDepth 1000000 in
private theorem component100Node36_sound : Sound component100Node36Box :=
  sound_of_literal_split component100Node36Box leaf4915Box leaf4916Box
    .k (229/64) (by rfl) (by rfl)
    leaf4915FlatSound leaf4916FlatSound

private noncomputable def component100Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (19/64), chiHi := (39/128) }

set_option maxRecDepth 1000000 in
private theorem component100Node37_sound : Sound component100Node37Box :=
  sound_of_literal_split component100Node37Box component100Node36Box leaf4917Box
    .chi (77/256) (by rfl) (by rfl)
    component100Node36_sound leaf4917FlatSound

private noncomputable def component100Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (19/64), chiHi := (77/256) }

set_option maxRecDepth 1000000 in
private theorem component100Node38_sound : Sound component100Node38Box :=
  sound_of_literal_split component100Node38Box leaf4918Box leaf4919Box
    .k (231/64) (by rfl) (by rfl)
    leaf4918FlatSound leaf4919FlatSound

private noncomputable def component100Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (77/256), chiHi := (39/128) }

set_option maxRecDepth 1000000 in
private theorem component100Node39_sound : Sound component100Node39Box :=
  sound_of_literal_split component100Node39Box leaf4920Box leaf4921Box
    .k (231/64) (by rfl) (by rfl)
    leaf4920FlatSound leaf4921FlatSound

private noncomputable def component100Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (19/64), chiHi := (39/128) }

set_option maxRecDepth 1000000 in
private theorem component100Node40_sound : Sound component100Node40Box :=
  sound_of_literal_split component100Node40Box component100Node38Box component100Node39Box
    .chi (77/256) (by rfl) (by rfl)
    component100Node38_sound component100Node39_sound

private noncomputable def component100Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (19/64), chiHi := (39/128) }

set_option maxRecDepth 1000000 in
private theorem component100Node41_sound : Sound component100Node41Box :=
  sound_of_literal_split component100Node41Box component100Node37Box component100Node40Box
    .k (115/32) (by rfl) (by rfl)
    component100Node37_sound component100Node40_sound

private noncomputable def component100Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (39/128), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component100Node42_sound : Sound component100Node42Box :=
  sound_of_literal_split component100Node42Box leaf4922Box leaf4923Box
    .chi (79/256) (by rfl) (by rfl)
    leaf4922FlatSound leaf4923FlatSound

private noncomputable def component100Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (39/128), chiHi := (79/256) }

set_option maxRecDepth 1000000 in
private theorem component100Node43_sound : Sound component100Node43Box :=
  sound_of_literal_split component100Node43Box leaf4924Box leaf4925Box
    .k (231/64) (by rfl) (by rfl)
    leaf4924FlatSound leaf4925FlatSound

private noncomputable def component100Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (39/128), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component100Node44_sound : Sound component100Node44Box :=
  sound_of_literal_split component100Node44Box component100Node43Box leaf4926Box
    .chi (79/256) (by rfl) (by rfl)
    component100Node43_sound leaf4926FlatSound

private noncomputable def component100Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (39/128), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component100Node45_sound : Sound component100Node45Box :=
  sound_of_literal_split component100Node45Box component100Node42Box component100Node44Box
    .k (115/32) (by rfl) (by rfl)
    component100Node42_sound component100Node44_sound

private noncomputable def component100Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (19/64), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component100Node46_sound : Sound component100Node46Box :=
  sound_of_literal_split component100Node46Box component100Node41Box component100Node45Box
    .chi (39/128) (by rfl) (by rfl)
    component100Node41_sound component100Node45_sound

private noncomputable def component100Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (19/64), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component100Node47_sound : Sound component100Node47Box :=
  sound_of_literal_split component100Node47Box component100Node35Box component100Node46Box
    .k (57/16) (by rfl) (by rfl)
    component100Node35_sound component100Node46_sound

noncomputable def component100Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (9/32), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
theorem component100_sound : Sound component100Box :=
  sound_of_literal_split component100Box component100Node28Box component100Node47Box
    .chi (19/64) (by rfl) (by rfl)
    component100Node28_sound component100Node47_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
