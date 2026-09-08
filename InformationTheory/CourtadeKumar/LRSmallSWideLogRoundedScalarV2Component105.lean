import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch5
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch5
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch8
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch9
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

private noncomputable def leaf5183Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (249/64), chiLo := (9/32), chiHi := (73/256) }

private noncomputable def leaf5183Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742467/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714823424) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2243847807/2147483648) }, upper := { exponent := 1, mantissa := (34561/32768) } }, logOuter := sk233LogOuterCertificate, logK := sk233LogKCertificate, logChi := chi281LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432235775/137429646848) } }, logDArg := sk233LogDArgCertificate }

private noncomputable def leaf5183InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf5183LocalValidity :
    LeafFacts leaf5183Box leaf5183Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5183Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714823424) }) = true
      norm_num [leaf5183Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5183CertificateValid :
    WideCertificateValid leaf5183Box leaf5183Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk233ValidityFacts chi281ValidityFacts
    leaf5183LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5183CoverageChecked :
    coverageCheck (innerAD leaf5183Box) leaf5183InnerLog = true := by
  rfl'

private theorem leaf5183InnerLogValid :
    leaf5183InnerLog.Valid 8 (innerAD leaf5183Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf5183CoverageChecked

private noncomputable def leaf5183InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629397/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5183InputLogOnePlusV_eq :
    leaf5183InputLogOnePlusV = outerEnclosure 24
      (leaf5183Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5183RoundedFacts : LeafRoundedFacts 8
    leaf5183Certificate.logOnePlusV leaf5183InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5183InputLogOnePlusV_eq }

private noncomputable def leaf5183Inputs : Inputs :=
  inputsOfCaches globalInput sk233RoundedInputs
    chi281InputQChi innerPair242Input
    leaf5183InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5183LowerChecked :
    lowerCheck 24 leaf5183Box leaf5183Inputs = true := by
  rfl'

private theorem leaf5183CoversExact : CoversExact 8
    leaf5183Box leaf5183Certificate leaf5183InnerLog leaf5183Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk233RoundedFacts chi281RoundedFacts
    innerPair242RoundedFacts leaf5183RoundedFacts (by rfl)

private theorem leaf5183FlatSound : Sound leaf5183Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5183CertificateValid
    leaf5183InnerLogValid leaf5183CoversExact leaf5183LowerChecked

private noncomputable def leaf5184Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (249/64), kHi := (125/32), chiLo := (9/32), chiHi := (73/256) }

private noncomputable def leaf5184Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742469/1073741824) }, vSqrt := { lower := (8191/8192), upper := (7635268039/7634978304) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2248566109/2147483648) }, upper := { exponent := 1, mantissa := (17317/16384) } }, logOuter := sk234LogOuterCertificate, logK := sk234LogKCertificate, logChi := chi281LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (15270246343/15269956608) } }, logDArg := sk234LogDArgCertificate }

private noncomputable def leaf5184InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf5184LocalValidity :
    LeafFacts leaf5184Box leaf5184Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5184Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (7635268039/7634978304) }) = true
      norm_num [leaf5184Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5184CertificateValid :
    WideCertificateValid leaf5184Box leaf5184Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk234ValidityFacts chi281ValidityFacts
    leaf5184LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5184CoverageChecked :
    coverageCheck (innerAD leaf5184Box) leaf5184InnerLog = true := by
  rfl'

private theorem leaf5184InnerLogValid :
    leaf5184InnerLog.Valid 8 (innerAD leaf5184Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf5184CoverageChecked

private noncomputable def leaf5184InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629399/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5184InputLogOnePlusV_eq :
    leaf5184InputLogOnePlusV = outerEnclosure 24
      (leaf5184Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5184RoundedFacts : LeafRoundedFacts 8
    leaf5184Certificate.logOnePlusV leaf5184InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5184InputLogOnePlusV_eq }

private noncomputable def leaf5184Inputs : Inputs :=
  inputsOfCaches globalInput sk234RoundedInputs
    chi281InputQChi innerPair242Input
    leaf5184InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5184LowerChecked :
    lowerCheck 24 leaf5184Box leaf5184Inputs = true := by
  rfl'

private theorem leaf5184CoversExact : CoversExact 8
    leaf5184Box leaf5184Certificate leaf5184InnerLog leaf5184Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk234RoundedFacts chi281RoundedFacts
    innerPair242RoundedFacts leaf5184RoundedFacts (by rfl)

private theorem leaf5184FlatSound : Sound leaf5184Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5184CertificateValid
    leaf5184InnerLogValid leaf5184CoversExact leaf5184LowerChecked

private noncomputable def leaf5185Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (249/64), chiLo := (73/256), chiHi := (37/128) }

private noncomputable def leaf5185Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742469/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9816773193/9816394240) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2260099741/2147483648) }, upper := { exponent := 1, mantissa := (17405/16384) } }, logOuter := sk233LogOuterCertificate, logK := sk233LogKCertificate, logChi := chi282LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (19633167433/19632788480) } }, logDArg := sk233LogDArgCertificate }

private noncomputable def leaf5185InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf5185LocalValidity :
    LeafFacts leaf5185Box leaf5185Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5185Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9816773193/9816394240) }) = true
      norm_num [leaf5185Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5185CertificateValid :
    WideCertificateValid leaf5185Box leaf5185Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk233ValidityFacts chi282ValidityFacts
    leaf5185LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5185CoverageChecked :
    coverageCheck (innerAD leaf5185Box) leaf5185InnerLog = true := by
  rfl'

private theorem leaf5185InnerLogValid :
    leaf5185InnerLog.Valid 8 (innerAD leaf5185Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf5185CoverageChecked

private noncomputable def leaf5185InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629405/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5185InputLogOnePlusV_eq :
    leaf5185InputLogOnePlusV = outerEnclosure 24
      (leaf5185Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5185RoundedFacts : LeafRoundedFacts 8
    leaf5185Certificate.logOnePlusV leaf5185InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5185InputLogOnePlusV_eq }

private noncomputable def leaf5185Inputs : Inputs :=
  inputsOfCaches globalInput sk233RoundedInputs
    chi282InputQChi innerPair242Input
    leaf5185InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5185LowerChecked :
    lowerCheck 24 leaf5185Box leaf5185Inputs = true := by
  rfl'

private theorem leaf5185CoversExact : CoversExact 8
    leaf5185Box leaf5185Certificate leaf5185InnerLog leaf5185Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk233RoundedFacts chi282RoundedFacts
    innerPair242RoundedFacts leaf5185RoundedFacts (by rfl)

private theorem leaf5185FlatSound : Sound leaf5185Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5185CertificateValid
    leaf5185InnerLogValid leaf5185CoversExact leaf5185LowerChecked

private noncomputable def leaf5186Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (249/64), kHi := (125/32), chiLo := (73/256), chiHi := (37/128) }

private noncomputable def leaf5186Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742471/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714740736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2264883575/2147483648) }, upper := { exponent := 1, mantissa := (8721/8192) } }, logOuter := sk234LogOuterCertificate, logK := sk234LogKCertificate, logChi := chi282LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432153087/137429481472) } }, logDArg := sk234LogDArgCertificate }

private noncomputable def leaf5186InnerLog : WideLogData :=
  innerPair551Data

set_option maxRecDepth 1000000 in
private theorem leaf5186LocalValidity :
    LeafFacts leaf5186Box leaf5186Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5186Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714740736) }) = true
      norm_num [leaf5186Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5186CertificateValid :
    WideCertificateValid leaf5186Box leaf5186Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk234ValidityFacts chi282ValidityFacts
    leaf5186LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5186CoverageChecked :
    coverageCheck (innerAD leaf5186Box) leaf5186InnerLog = true := by
  rfl'

private theorem leaf5186InnerLogValid :
    leaf5186InnerLog.Valid 8 (innerAD leaf5186Box) :=
  wideLogDataValid_of_cachedCheck endpoint284PositiveFacts
    endpoint289PositiveFacts.valid leaf5186CoverageChecked

private noncomputable def leaf5186InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629407/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5186InputLogOnePlusV_eq :
    leaf5186InputLogOnePlusV = outerEnclosure 24
      (leaf5186Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5186RoundedFacts : LeafRoundedFacts 8
    leaf5186Certificate.logOnePlusV leaf5186InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5186InputLogOnePlusV_eq }

private noncomputable def leaf5186Inputs : Inputs :=
  inputsOfCaches globalInput sk234RoundedInputs
    chi282InputQChi innerPair551Input
    leaf5186InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5186LowerChecked :
    lowerCheck 24 leaf5186Box leaf5186Inputs = true := by
  rfl'

private theorem leaf5186CoversExact : CoversExact 8
    leaf5186Box leaf5186Certificate leaf5186InnerLog leaf5186Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk234RoundedFacts chi282RoundedFacts
    innerPair551RoundedFacts leaf5186RoundedFacts (by rfl)

private theorem leaf5186FlatSound : Sound leaf5186Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5186CertificateValid
    leaf5186InnerLogValid leaf5186CoversExact leaf5186LowerChecked

private noncomputable def leaf5187Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (251/64), chiLo := (9/32), chiHi := (73/256) }

private noncomputable def leaf5187Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742471/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714786048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2253284411/2147483648) }, upper := { exponent := 1, mantissa := (34707/32768) } }, logOuter := sk235LogOuterCertificate, logK := sk235LogKCertificate, logChi := chi281LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432198399/137429572096) } }, logDArg := sk235LogDArgCertificate }

private noncomputable def leaf5187InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf5187LocalValidity :
    LeafFacts leaf5187Box leaf5187Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5187Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714786048) }) = true
      norm_num [leaf5187Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5187CertificateValid :
    WideCertificateValid leaf5187Box leaf5187Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk235ValidityFacts chi281ValidityFacts
    leaf5187LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5187CoverageChecked :
    coverageCheck (innerAD leaf5187Box) leaf5187InnerLog = true := by
  rfl'

private theorem leaf5187InnerLogValid :
    leaf5187InnerLog.Valid 8 (innerAD leaf5187Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf5187CoverageChecked

private noncomputable def leaf5187InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629401/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5187InputLogOnePlusV_eq :
    leaf5187InputLogOnePlusV = outerEnclosure 24
      (leaf5187Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5187RoundedFacts : LeafRoundedFacts 8
    leaf5187Certificate.logOnePlusV leaf5187InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5187InputLogOnePlusV_eq }

private noncomputable def leaf5187Inputs : Inputs :=
  inputsOfCaches globalInput sk235RoundedInputs
    chi281InputQChi innerPair242Input
    leaf5187InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5187LowerChecked :
    lowerCheck 24 leaf5187Box leaf5187Inputs = true := by
  rfl'

private theorem leaf5187CoversExact : CoversExact 8
    leaf5187Box leaf5187Certificate leaf5187InnerLog leaf5187Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk235RoundedFacts chi281RoundedFacts
    innerPair242RoundedFacts leaf5187RoundedFacts (by rfl)

private theorem leaf5187FlatSound : Sound leaf5187Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5187CertificateValid
    leaf5187InnerLogValid leaf5187CoversExact leaf5187LowerChecked

private noncomputable def leaf5188Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (63/16), chiLo := (9/32), chiHi := (73/256) }

private noncomputable def leaf5188Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742473/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714767360) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2258002713/2147483648) }, upper := { exponent := 1, mantissa := (8695/8192) } }, logOuter := sk236LogOuterCertificate, logK := sk236LogKCertificate, logChi := chi281LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432179711/137429534720) } }, logDArg := sk236LogDArgCertificate }

private noncomputable def leaf5188InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf5188LocalValidity :
    LeafFacts leaf5188Box leaf5188Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5188Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714767360) }) = true
      norm_num [leaf5188Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5188CertificateValid :
    WideCertificateValid leaf5188Box leaf5188Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk236ValidityFacts chi281ValidityFacts
    leaf5188LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5188CoverageChecked :
    coverageCheck (innerAD leaf5188Box) leaf5188InnerLog = true := by
  rfl'

private theorem leaf5188InnerLogValid :
    leaf5188InnerLog.Valid 8 (innerAD leaf5188Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf5188CoverageChecked

private noncomputable def leaf5188InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907351/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5188InputLogOnePlusV_eq :
    leaf5188InputLogOnePlusV = outerEnclosure 24
      (leaf5188Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5188RoundedFacts : LeafRoundedFacts 8
    leaf5188Certificate.logOnePlusV leaf5188InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5188InputLogOnePlusV_eq }

private noncomputable def leaf5188Inputs : Inputs :=
  inputsOfCaches globalInput sk236RoundedInputs
    chi281InputQChi innerPair242Input
    leaf5188InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5188LowerChecked :
    lowerCheck 24 leaf5188Box leaf5188Inputs = true := by
  rfl'

private theorem leaf5188CoversExact : CoversExact 8
    leaf5188Box leaf5188Certificate leaf5188InnerLog leaf5188Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk236RoundedFacts chi281RoundedFacts
    innerPair242RoundedFacts leaf5188RoundedFacts (by rfl)

private theorem leaf5188FlatSound : Sound leaf5188Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5188CertificateValid
    leaf5188InnerLogValid leaf5188CoversExact leaf5188LowerChecked

private noncomputable def leaf5189Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (251/64), chiLo := (73/256), chiHi := (37/128) }

private noncomputable def leaf5189Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742473/1073741824) }, vSqrt := { lower := (8191/8192), upper := (7635268039/7634969088) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2269667409/2147483648) }, upper := { exponent := 1, mantissa := (17479/16384) } }, logOuter := sk235LogOuterCertificate, logK := sk235LogKCertificate, logChi := chi282LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (15270237127/15269938176) } }, logDArg := sk235LogDArgCertificate }

private noncomputable def leaf5189InnerLog : WideLogData :=
  innerPair336Data

set_option maxRecDepth 1000000 in
private theorem leaf5189LocalValidity :
    LeafFacts leaf5189Box leaf5189Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5189Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (7635268039/7634969088) }) = true
      norm_num [leaf5189Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5189CertificateValid :
    WideCertificateValid leaf5189Box leaf5189Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk235ValidityFacts chi282ValidityFacts
    leaf5189LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5189CoverageChecked :
    coverageCheck (innerAD leaf5189Box) leaf5189InnerLog = true := by
  rfl'

private theorem leaf5189InnerLogValid :
    leaf5189InnerLog.Valid 8 (innerAD leaf5189Box) :=
  wideLogDataValid_of_cachedCheck endpoint89PositiveFacts
    endpoint289PositiveFacts.valid leaf5189CoverageChecked

private noncomputable def leaf5189InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629409/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5189InputLogOnePlusV_eq :
    leaf5189InputLogOnePlusV = outerEnclosure 24
      (leaf5189Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5189RoundedFacts : LeafRoundedFacts 8
    leaf5189Certificate.logOnePlusV leaf5189InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5189InputLogOnePlusV_eq }

private noncomputable def leaf5189Inputs : Inputs :=
  inputsOfCaches globalInput sk235RoundedInputs
    chi282InputQChi innerPair336Input
    leaf5189InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5189LowerChecked :
    lowerCheck 24 leaf5189Box leaf5189Inputs = true := by
  rfl'

private theorem leaf5189CoversExact : CoversExact 8
    leaf5189Box leaf5189Certificate leaf5189InnerLog leaf5189Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk235RoundedFacts chi282RoundedFacts
    innerPair336RoundedFacts leaf5189RoundedFacts (by rfl)

private theorem leaf5189FlatSound : Sound leaf5189Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5189CertificateValid
    leaf5189InnerLogValid leaf5189CoversExact leaf5189LowerChecked

private noncomputable def leaf5190Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (63/16), chiLo := (73/256), chiHi := (37/128) }

private noncomputable def leaf5190Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742475/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714702848) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2274451243/2147483648) }, upper := { exponent := 1, mantissa := (4379/4096) } }, logOuter := sk236LogOuterCertificate, logK := sk236LogKCertificate, logChi := chi282LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432115199/137429405696) } }, logDArg := sk236LogDArgCertificate }

private noncomputable def leaf5190InnerLog : WideLogData :=
  innerPair336Data

set_option maxRecDepth 1000000 in
private theorem leaf5190LocalValidity :
    LeafFacts leaf5190Box leaf5190Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5190Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714702848) }) = true
      norm_num [leaf5190Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5190CertificateValid :
    WideCertificateValid leaf5190Box leaf5190Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk236ValidityFacts chi282ValidityFacts
    leaf5190LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5190CoverageChecked :
    coverageCheck (innerAD leaf5190Box) leaf5190InnerLog = true := by
  rfl'

private theorem leaf5190InnerLogValid :
    leaf5190InnerLog.Valid 8 (innerAD leaf5190Box) :=
  wideLogDataValid_of_cachedCheck endpoint89PositiveFacts
    endpoint289PositiveFacts.valid leaf5190CoverageChecked

private noncomputable def leaf5190InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907353/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5190InputLogOnePlusV_eq :
    leaf5190InputLogOnePlusV = outerEnclosure 24
      (leaf5190Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5190RoundedFacts : LeafRoundedFacts 8
    leaf5190Certificate.logOnePlusV leaf5190InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5190InputLogOnePlusV_eq }

private noncomputable def leaf5190Inputs : Inputs :=
  inputsOfCaches globalInput sk236RoundedInputs
    chi282InputQChi innerPair336Input
    leaf5190InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5190LowerChecked :
    lowerCheck 24 leaf5190Box leaf5190Inputs = true := by
  rfl'

private theorem leaf5190CoversExact : CoversExact 8
    leaf5190Box leaf5190Certificate leaf5190InnerLog leaf5190Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk236RoundedFacts chi282RoundedFacts
    innerPair336RoundedFacts leaf5190RoundedFacts (by rfl)

private theorem leaf5190FlatSound : Sound leaf5190Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5190CertificateValid
    leaf5190InnerLogValid leaf5190CoversExact leaf5190LowerChecked

private noncomputable def leaf5191Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (249/64), chiLo := (37/128), chiHi := (75/256) }

private noncomputable def leaf5191Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742471/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714695936) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2276351675/2147483648) }, upper := { exponent := 1, mantissa := (35059/32768) } }, logOuter := sk233LogOuterCertificate, logK := sk233LogKCertificate, logChi := chi283LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432108287/137429391872) } }, logDArg := sk233LogDArgCertificate }

private noncomputable def leaf5191InnerLog : WideLogData :=
  innerPair336Data

set_option maxRecDepth 1000000 in
private theorem leaf5191LocalValidity :
    LeafFacts leaf5191Box leaf5191Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5191Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714695936) }) = true
      norm_num [leaf5191Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5191CertificateValid :
    WideCertificateValid leaf5191Box leaf5191Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk233ValidityFacts chi283ValidityFacts
    leaf5191LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5191CoverageChecked :
    coverageCheck (innerAD leaf5191Box) leaf5191InnerLog = true := by
  rfl'

private theorem leaf5191InnerLogValid :
    leaf5191InnerLog.Valid 8 (innerAD leaf5191Box) :=
  wideLogDataValid_of_cachedCheck endpoint89PositiveFacts
    endpoint289PositiveFacts.valid leaf5191CoverageChecked

private noncomputable def leaf5191InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907353/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5191InputLogOnePlusV_eq :
    leaf5191InputLogOnePlusV = outerEnclosure 24
      (leaf5191Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5191RoundedFacts : LeafRoundedFacts 8
    leaf5191Certificate.logOnePlusV leaf5191InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5191InputLogOnePlusV_eq }

private noncomputable def leaf5191Inputs : Inputs :=
  inputsOfCaches globalInput sk233RoundedInputs
    chi283InputQChi innerPair336Input
    leaf5191InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5191LowerChecked :
    lowerCheck 24 leaf5191Box leaf5191Inputs = true := by
  rfl'

private theorem leaf5191CoversExact : CoversExact 8
    leaf5191Box leaf5191Certificate leaf5191InnerLog leaf5191Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk233RoundedFacts chi283RoundedFacts
    innerPair336RoundedFacts leaf5191RoundedFacts (by rfl)

private theorem leaf5191FlatSound : Sound leaf5191Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5191CertificateValid
    leaf5191InnerLogValid leaf5191CoversExact leaf5191LowerChecked

private noncomputable def leaf5192Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (249/64), kHi := (125/32), chiLo := (37/128), chiHi := (75/256) }

private noncomputable def leaf5192Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742473/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714676736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2281201041/2147483648) }, upper := { exponent := 1, mantissa := (17567/16384) } }, logOuter := sk234LogOuterCertificate, logK := sk234LogKCertificate, logChi := chi283LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432089087/137429353472) } }, logDArg := sk234LogDArgCertificate }

private noncomputable def leaf5192InnerLog : WideLogData :=
  innerPair335Data

set_option maxRecDepth 1000000 in
private theorem leaf5192LocalValidity :
    LeafFacts leaf5192Box leaf5192Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5192Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714676736) }) = true
      norm_num [leaf5192Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5192CertificateValid :
    WideCertificateValid leaf5192Box leaf5192Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk234ValidityFacts chi283ValidityFacts
    leaf5192LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5192CoverageChecked :
    coverageCheck (innerAD leaf5192Box) leaf5192InnerLog = true := by
  rfl'

private theorem leaf5192InnerLogValid :
    leaf5192InnerLog.Valid 8 (innerAD leaf5192Box) :=
  wideLogDataValid_of_cachedCheck endpoint89PositiveFacts
    endpoint88PositiveFacts.valid leaf5192CoverageChecked

private noncomputable def leaf5192InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629415/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5192InputLogOnePlusV_eq :
    leaf5192InputLogOnePlusV = outerEnclosure 24
      (leaf5192Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5192RoundedFacts : LeafRoundedFacts 8
    leaf5192Certificate.logOnePlusV leaf5192InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5192InputLogOnePlusV_eq }

private noncomputable def leaf5192Inputs : Inputs :=
  inputsOfCaches globalInput sk234RoundedInputs
    chi283InputQChi innerPair335Input
    leaf5192InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5192LowerChecked :
    lowerCheck 24 leaf5192Box leaf5192Inputs = true := by
  rfl'

private theorem leaf5192CoversExact : CoversExact 8
    leaf5192Box leaf5192Certificate leaf5192InnerLog leaf5192Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk234RoundedFacts chi283RoundedFacts
    innerPair335RoundedFacts leaf5192RoundedFacts (by rfl)

private theorem leaf5192FlatSound : Sound leaf5192Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5192CertificateValid
    leaf5192InnerLogValid leaf5192CoversExact leaf5192LowerChecked

private noncomputable def leaf5193Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (249/64), chiLo := (75/256), chiHi := (19/64) }

private noncomputable def leaf5193Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742473/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714632192) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2292603609/2147483648) }, upper := { exponent := 1, mantissa := (8827/8192) } }, logOuter := sk233LogOuterCertificate, logK := sk233LogKCertificate, logChi := chi284LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432044543/137429264384) } }, logDArg := sk233LogDArgCertificate }

private noncomputable def leaf5193InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf5193LocalValidity :
    LeafFacts leaf5193Box leaf5193Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5193Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714632192) }) = true
      norm_num [leaf5193Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5193CertificateValid :
    WideCertificateValid leaf5193Box leaf5193Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk233ValidityFacts chi284ValidityFacts
    leaf5193LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5193CoverageChecked :
    coverageCheck (innerAD leaf5193Box) leaf5193InnerLog = true := by
  rfl'

private theorem leaf5193InnerLogValid :
    leaf5193InnerLog.Valid 8 (innerAD leaf5193Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf5193CoverageChecked

private noncomputable def leaf5193InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907355/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5193InputLogOnePlusV_eq :
    leaf5193InputLogOnePlusV = outerEnclosure 24
      (leaf5193Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5193RoundedFacts : LeafRoundedFacts 8
    leaf5193Certificate.logOnePlusV leaf5193InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5193InputLogOnePlusV_eq }

private noncomputable def leaf5193Inputs : Inputs :=
  inputsOfCaches globalInput sk233RoundedInputs
    chi284InputQChi innerPair249Input
    leaf5193InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5193LowerChecked :
    lowerCheck 24 leaf5193Box leaf5193Inputs = true := by
  rfl'

private theorem leaf5193CoversExact : CoversExact 8
    leaf5193Box leaf5193Certificate leaf5193InnerLog leaf5193Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk233RoundedFacts chi284RoundedFacts
    innerPair249RoundedFacts leaf5193RoundedFacts (by rfl)

private theorem leaf5193FlatSound : Sound leaf5193Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5193CertificateValid
    leaf5193InnerLogValid leaf5193CoversExact leaf5193LowerChecked

private noncomputable def leaf5194Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (249/64), kHi := (125/32), chiLo := (75/256), chiHi := (19/64) }

private noncomputable def leaf5194Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742475/1073741824) }, vSqrt := { lower := (8191/8192), upper := (3272257731/3272124416) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2297518507/2147483648) }, upper := { exponent := 1, mantissa := (4423/4096) } }, logOuter := sk234LogOuterCertificate, logK := sk234LogKCertificate, logChi := chi284LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (6544382147/6544248832) } }, logDArg := sk234LogDArgCertificate }

private noncomputable def leaf5194InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf5194LocalValidity :
    LeafFacts leaf5194Box leaf5194Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5194Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (3272257731/3272124416) }) = true
      norm_num [leaf5194Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5194CertificateValid :
    WideCertificateValid leaf5194Box leaf5194Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk234ValidityFacts chi284ValidityFacts
    leaf5194LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5194CoverageChecked :
    coverageCheck (innerAD leaf5194Box) leaf5194InnerLog = true := by
  rfl'

private theorem leaf5194InnerLogValid :
    leaf5194InnerLog.Valid 8 (innerAD leaf5194Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf5194CoverageChecked

private noncomputable def leaf5194InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629423/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5194InputLogOnePlusV_eq :
    leaf5194InputLogOnePlusV = outerEnclosure 24
      (leaf5194Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5194RoundedFacts : LeafRoundedFacts 8
    leaf5194Certificate.logOnePlusV leaf5194InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5194InputLogOnePlusV_eq }

private noncomputable def leaf5194Inputs : Inputs :=
  inputsOfCaches globalInput sk234RoundedInputs
    chi284InputQChi innerPair249Input
    leaf5194InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5194LowerChecked :
    lowerCheck 24 leaf5194Box leaf5194Inputs = true := by
  rfl'

private theorem leaf5194CoversExact : CoversExact 8
    leaf5194Box leaf5194Certificate leaf5194InnerLog leaf5194Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk234RoundedFacts chi284RoundedFacts
    innerPair249RoundedFacts leaf5194RoundedFacts (by rfl)

private theorem leaf5194FlatSound : Sound leaf5194Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5194CertificateValid
    leaf5194InnerLogValid leaf5194CoversExact leaf5194LowerChecked

private noncomputable def leaf5195Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (251/64), chiLo := (37/128), chiHi := (75/256) }

private noncomputable def leaf5195Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742475/1073741824) }, vSqrt := { lower := (8191/8192), upper := (316670103/316657408) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2286050407/2147483648) }, upper := { exponent := 1, mantissa := (35209/32768) } }, logOuter := sk235LogOuterCertificate, logK := sk235LogKCertificate, logChi := chi283LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (633327511/633314816) } }, logDArg := sk235LogDArgCertificate }

private noncomputable def leaf5195InnerLog : WideLogData :=
  innerPair253Data

set_option maxRecDepth 1000000 in
private theorem leaf5195LocalValidity :
    LeafFacts leaf5195Box leaf5195Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5195Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (316670103/316657408) }) = true
      norm_num [leaf5195Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5195CertificateValid :
    WideCertificateValid leaf5195Box leaf5195Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk235ValidityFacts chi283ValidityFacts
    leaf5195LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5195CoverageChecked :
    coverageCheck (innerAD leaf5195Box) leaf5195InnerLog = true := by
  rfl'

private theorem leaf5195InnerLogValid :
    leaf5195InnerLog.Valid 8 (innerAD leaf5195Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint88PositiveFacts.valid leaf5195CoverageChecked

private noncomputable def leaf5195InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629417/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5195InputLogOnePlusV_eq :
    leaf5195InputLogOnePlusV = outerEnclosure 24
      (leaf5195Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5195RoundedFacts : LeafRoundedFacts 8
    leaf5195Certificate.logOnePlusV leaf5195InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5195InputLogOnePlusV_eq }

private noncomputable def leaf5195Inputs : Inputs :=
  inputsOfCaches globalInput sk235RoundedInputs
    chi283InputQChi innerPair253Input
    leaf5195InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5195LowerChecked :
    lowerCheck 24 leaf5195Box leaf5195Inputs = true := by
  rfl'

private theorem leaf5195CoversExact : CoversExact 8
    leaf5195Box leaf5195Certificate leaf5195InnerLog leaf5195Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk235RoundedFacts chi283RoundedFacts
    innerPair253RoundedFacts leaf5195RoundedFacts (by rfl)

private theorem leaf5195FlatSound : Sound leaf5195Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5195CertificateValid
    leaf5195InnerLogValid leaf5195CoversExact leaf5195LowerChecked

private noncomputable def leaf5196Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (63/16), chiLo := (37/128), chiHi := (75/256) }

private noncomputable def leaf5196Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742477/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714638336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2290899773/2147483648) }, upper := { exponent := 1, mantissa := (8821/8192) } }, logOuter := sk236LogOuterCertificate, logK := sk236LogKCertificate, logChi := chi283LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432050687/137429276672) } }, logDArg := sk236LogDArgCertificate }

private noncomputable def leaf5196InnerLog : WideLogData :=
  innerPair253Data

set_option maxRecDepth 1000000 in
private theorem leaf5196LocalValidity :
    LeafFacts leaf5196Box leaf5196Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5196Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714638336) }) = true
      norm_num [leaf5196Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5196CertificateValid :
    WideCertificateValid leaf5196Box leaf5196Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk236ValidityFacts chi283ValidityFacts
    leaf5196LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5196CoverageChecked :
    coverageCheck (innerAD leaf5196Box) leaf5196InnerLog = true := by
  rfl'

private theorem leaf5196InnerLogValid :
    leaf5196InnerLog.Valid 8 (innerAD leaf5196Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint88PositiveFacts.valid leaf5196CoverageChecked

private noncomputable def leaf5196InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629419/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5196InputLogOnePlusV_eq :
    leaf5196InputLogOnePlusV = outerEnclosure 24
      (leaf5196Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5196RoundedFacts : LeafRoundedFacts 8
    leaf5196Certificate.logOnePlusV leaf5196InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5196InputLogOnePlusV_eq }

private noncomputable def leaf5196Inputs : Inputs :=
  inputsOfCaches globalInput sk236RoundedInputs
    chi283InputQChi innerPair253Input
    leaf5196InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5196LowerChecked :
    lowerCheck 24 leaf5196Box leaf5196Inputs = true := by
  rfl'

private theorem leaf5196CoversExact : CoversExact 8
    leaf5196Box leaf5196Certificate leaf5196InnerLog leaf5196Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk236RoundedFacts chi283RoundedFacts
    innerPair253RoundedFacts leaf5196RoundedFacts (by rfl)

private theorem leaf5196FlatSound : Sound leaf5196Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5196CertificateValid
    leaf5196InnerLogValid leaf5196CoversExact leaf5196LowerChecked

private noncomputable def leaf5197Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (251/64), chiLo := (75/256), chiHi := (19/64) }

private noncomputable def leaf5197Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742477/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714593280) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2302433405/2147483648) }, upper := { exponent := 1, mantissa := (8865/8192) } }, logOuter := sk235LogOuterCertificate, logK := sk235LogKCertificate, logChi := chi284LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432005631/137429186560) } }, logDArg := sk235LogDArgCertificate }

private noncomputable def leaf5197InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf5197LocalValidity :
    LeafFacts leaf5197Box leaf5197Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5197Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714593280) }) = true
      norm_num [leaf5197Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5197CertificateValid :
    WideCertificateValid leaf5197Box leaf5197Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk235ValidityFacts chi284ValidityFacts
    leaf5197LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5197CoverageChecked :
    coverageCheck (innerAD leaf5197Box) leaf5197InnerLog = true := by
  rfl'

private theorem leaf5197InnerLogValid :
    leaf5197InnerLog.Valid 8 (innerAD leaf5197Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf5197CoverageChecked

private noncomputable def leaf5197InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629425/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5197InputLogOnePlusV_eq :
    leaf5197InputLogOnePlusV = outerEnclosure 24
      (leaf5197Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5197RoundedFacts : LeafRoundedFacts 8
    leaf5197Certificate.logOnePlusV leaf5197InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5197InputLogOnePlusV_eq }

private noncomputable def leaf5197Inputs : Inputs :=
  inputsOfCaches globalInput sk235RoundedInputs
    chi284InputQChi innerPair249Input
    leaf5197InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5197LowerChecked :
    lowerCheck 24 leaf5197Box leaf5197Inputs = true := by
  rfl'

private theorem leaf5197CoversExact : CoversExact 8
    leaf5197Box leaf5197Certificate leaf5197InnerLog leaf5197Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk235RoundedFacts chi284RoundedFacts
    innerPair249RoundedFacts leaf5197RoundedFacts (by rfl)

private theorem leaf5197FlatSound : Sound leaf5197Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5197CertificateValid
    leaf5197InnerLogValid leaf5197CoversExact leaf5197LowerChecked

private noncomputable def leaf5198Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (63/16), chiLo := (75/256), chiHi := (19/64) }

private noncomputable def leaf5198Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742479/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714573824) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2307348303/2147483648) }, upper := { exponent := 1, mantissa := (2221/2048) } }, logOuter := sk236LogOuterCertificate, logK := sk236LogKCertificate, logChi := chi284LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431986175/137429147648) } }, logDArg := sk236LogDArgCertificate }

private noncomputable def leaf5198InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf5198LocalValidity :
    LeafFacts leaf5198Box leaf5198Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5198Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714573824) }) = true
      norm_num [leaf5198Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5198CertificateValid :
    WideCertificateValid leaf5198Box leaf5198Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk236ValidityFacts chi284ValidityFacts
    leaf5198LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5198CoverageChecked :
    coverageCheck (innerAD leaf5198Box) leaf5198InnerLog = true := by
  rfl'

private theorem leaf5198InnerLogValid :
    leaf5198InnerLog.Valid 8 (innerAD leaf5198Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf5198CoverageChecked

private noncomputable def leaf5198InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629427/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5198InputLogOnePlusV_eq :
    leaf5198InputLogOnePlusV = outerEnclosure 24
      (leaf5198Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5198RoundedFacts : LeafRoundedFacts 8
    leaf5198Certificate.logOnePlusV leaf5198InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5198InputLogOnePlusV_eq }

private noncomputable def leaf5198Inputs : Inputs :=
  inputsOfCaches globalInput sk236RoundedInputs
    chi284InputQChi innerPair249Input
    leaf5198InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5198LowerChecked :
    lowerCheck 24 leaf5198Box leaf5198Inputs = true := by
  rfl'

private theorem leaf5198CoversExact : CoversExact 8
    leaf5198Box leaf5198Certificate leaf5198InnerLog leaf5198Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk236RoundedFacts chi284RoundedFacts
    innerPair249RoundedFacts leaf5198RoundedFacts (by rfl)

private theorem leaf5198FlatSound : Sound leaf5198Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5198CertificateValid
    leaf5198InnerLogValid leaf5198CoversExact leaf5198LowerChecked

private noncomputable def leaf5199Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (9/32), chiHi := (73/256) }

private noncomputable def leaf5199Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742475/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22905804117/22904916224) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2262721015/2147483648) }, upper := { exponent := 1, mantissa := (34853/32768) } }, logOuter := sk237LogOuterCertificate, logK := sk237LogKCertificate, logChi := chi281LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45810720341/45809832448) } }, logDArg := sk237LogDArgCertificate }

private noncomputable def leaf5199InnerLog : WideLogData :=
  innerPair551Data

set_option maxRecDepth 1000000 in
private theorem leaf5199LocalValidity :
    LeafFacts leaf5199Box leaf5199Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5199Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22905804117/22904916224) }) = true
      norm_num [leaf5199Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5199CertificateValid :
    WideCertificateValid leaf5199Box leaf5199Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk237ValidityFacts chi281ValidityFacts
    leaf5199LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5199CoverageChecked :
    coverageCheck (innerAD leaf5199Box) leaf5199InnerLog = true := by
  rfl'

private theorem leaf5199InnerLogValid :
    leaf5199InnerLog.Valid 8 (innerAD leaf5199Box) :=
  wideLogDataValid_of_cachedCheck endpoint284PositiveFacts
    endpoint289PositiveFacts.valid leaf5199CoverageChecked

private noncomputable def leaf5199InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814703/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5199InputLogOnePlusV_eq :
    leaf5199InputLogOnePlusV = outerEnclosure 24
      (leaf5199Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5199RoundedFacts : LeafRoundedFacts 8
    leaf5199Certificate.logOnePlusV leaf5199InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5199InputLogOnePlusV_eq }

private noncomputable def leaf5199Inputs : Inputs :=
  inputsOfCaches globalInput sk237RoundedInputs
    chi281InputQChi innerPair551Input
    leaf5199InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5199LowerChecked :
    lowerCheck 24 leaf5199Box leaf5199Inputs = true := by
  rfl'

private theorem leaf5199CoversExact : CoversExact 8
    leaf5199Box leaf5199Certificate leaf5199InnerLog leaf5199Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk237RoundedFacts chi281RoundedFacts
    innerPair551RoundedFacts leaf5199RoundedFacts (by rfl)

private theorem leaf5199FlatSound : Sound leaf5199Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5199CertificateValid
    leaf5199InnerLogValid leaf5199CoversExact leaf5199LowerChecked

private noncomputable def leaf5200Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (9/32), chiHi := (73/256) }

private noncomputable def leaf5200Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742477/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714729984) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2267439317/2147483648) }, upper := { exponent := 1, mantissa := (17463/16384) } }, logOuter := sk238LogOuterCertificate, logK := sk238LogKCertificate, logChi := chi281LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432142335/137429459968) } }, logDArg := sk238LogDArgCertificate }

private noncomputable def leaf5200InnerLog : WideLogData :=
  innerPair336Data

set_option maxRecDepth 1000000 in
private theorem leaf5200LocalValidity :
    LeafFacts leaf5200Box leaf5200Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5200Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714729984) }) = true
      norm_num [leaf5200Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5200CertificateValid :
    WideCertificateValid leaf5200Box leaf5200Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk238ValidityFacts chi281ValidityFacts
    leaf5200LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5200CoverageChecked :
    coverageCheck (innerAD leaf5200Box) leaf5200InnerLog = true := by
  rfl'

private theorem leaf5200InnerLogValid :
    leaf5200InnerLog.Valid 8 (innerAD leaf5200Box) :=
  wideLogDataValid_of_cachedCheck endpoint89PositiveFacts
    endpoint289PositiveFacts.valid leaf5200CoverageChecked

private noncomputable def leaf5200InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (363419/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf5200InputLogOnePlusV_eq :
    leaf5200InputLogOnePlusV = outerEnclosure 24
      (leaf5200Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5200RoundedFacts : LeafRoundedFacts 8
    leaf5200Certificate.logOnePlusV leaf5200InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5200InputLogOnePlusV_eq }

private noncomputable def leaf5200Inputs : Inputs :=
  inputsOfCaches globalInput sk238RoundedInputs
    chi281InputQChi innerPair336Input
    leaf5200InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5200LowerChecked :
    lowerCheck 24 leaf5200Box leaf5200Inputs = true := by
  rfl'

private theorem leaf5200CoversExact : CoversExact 8
    leaf5200Box leaf5200Certificate leaf5200InnerLog leaf5200Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk238RoundedFacts chi281RoundedFacts
    innerPair336RoundedFacts leaf5200RoundedFacts (by rfl)

private theorem leaf5200FlatSound : Sound leaf5200Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5200CertificateValid
    leaf5200InnerLogValid leaf5200CoversExact leaf5200LowerChecked

private noncomputable def leaf5201Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (73/256), chiHi := (37/128) }

private noncomputable def leaf5201Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742477/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714683904) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2279235077/2147483648) }, upper := { exponent := 1, mantissa := (17553/16384) } }, logOuter := sk237LogOuterCertificate, logK := sk237LogKCertificate, logChi := chi282LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432096255/137429367808) } }, logDArg := sk237LogDArgCertificate }

private noncomputable def leaf5201InnerLog : WideLogData :=
  innerPair335Data

set_option maxRecDepth 1000000 in
private theorem leaf5201LocalValidity :
    LeafFacts leaf5201Box leaf5201Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5201Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714683904) }) = true
      norm_num [leaf5201Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5201CertificateValid :
    WideCertificateValid leaf5201Box leaf5201Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk237ValidityFacts chi282ValidityFacts
    leaf5201LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5201CoverageChecked :
    coverageCheck (innerAD leaf5201Box) leaf5201InnerLog = true := by
  rfl'

private theorem leaf5201InnerLogValid :
    leaf5201InnerLog.Valid 8 (innerAD leaf5201Box) :=
  wideLogDataValid_of_cachedCheck endpoint89PositiveFacts
    endpoint88PositiveFacts.valid leaf5201CoverageChecked

private noncomputable def leaf5201InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814707/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5201InputLogOnePlusV_eq :
    leaf5201InputLogOnePlusV = outerEnclosure 24
      (leaf5201Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5201RoundedFacts : LeafRoundedFacts 8
    leaf5201Certificate.logOnePlusV leaf5201InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5201InputLogOnePlusV_eq }

private noncomputable def leaf5201Inputs : Inputs :=
  inputsOfCaches globalInput sk237RoundedInputs
    chi282InputQChi innerPair335Input
    leaf5201InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5201LowerChecked :
    lowerCheck 24 leaf5201Box leaf5201Inputs = true := by
  rfl'

private theorem leaf5201CoversExact : CoversExact 8
    leaf5201Box leaf5201Certificate leaf5201InnerLog leaf5201Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk237RoundedFacts chi282RoundedFacts
    innerPair335RoundedFacts leaf5201RoundedFacts (by rfl)

private theorem leaf5201FlatSound : Sound leaf5201Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5201CertificateValid
    leaf5201InnerLogValid leaf5201CoversExact leaf5201LowerChecked

private noncomputable def leaf5202Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (73/256), chiHi := (37/128) }

private noncomputable def leaf5202Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742479/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22905804117/22904888320) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2284018911/2147483648) }, upper := { exponent := 1, mantissa := (8795/8192) } }, logOuter := sk238LogOuterCertificate, logK := sk238LogKCertificate, logChi := chi282LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45810692437/45809776640) } }, logDArg := sk238LogDArgCertificate }

private noncomputable def leaf5202InnerLog : WideLogData :=
  innerPair253Data

set_option maxRecDepth 1000000 in
private theorem leaf5202LocalValidity :
    LeafFacts leaf5202Box leaf5202Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5202Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22905804117/22904888320) }) = true
      norm_num [leaf5202Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5202CertificateValid :
    WideCertificateValid leaf5202Box leaf5202Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk238ValidityFacts chi282ValidityFacts
    leaf5202LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5202CoverageChecked :
    coverageCheck (innerAD leaf5202Box) leaf5202InnerLog = true := by
  rfl'

private theorem leaf5202InnerLogValid :
    leaf5202InnerLog.Valid 8 (innerAD leaf5202Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint88PositiveFacts.valid leaf5202CoverageChecked

private noncomputable def leaf5202InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453677/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf5202InputLogOnePlusV_eq :
    leaf5202InputLogOnePlusV = outerEnclosure 24
      (leaf5202Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5202RoundedFacts : LeafRoundedFacts 8
    leaf5202Certificate.logOnePlusV leaf5202InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5202InputLogOnePlusV_eq }

private noncomputable def leaf5202Inputs : Inputs :=
  inputsOfCaches globalInput sk238RoundedInputs
    chi282InputQChi innerPair253Input
    leaf5202InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5202LowerChecked :
    lowerCheck 24 leaf5202Box leaf5202Inputs = true := by
  rfl'

private theorem leaf5202CoversExact : CoversExact 8
    leaf5202Box leaf5202Certificate leaf5202InnerLog leaf5202Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk238RoundedFacts chi282RoundedFacts
    innerPair253RoundedFacts leaf5202RoundedFacts (by rfl)

private theorem leaf5202FlatSound : Sound leaf5202Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5202CertificateValid
    leaf5202InnerLogValid leaf5202CoversExact leaf5202LowerChecked

private noncomputable def leaf5203Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (9/32), chiHi := (73/256) }

private noncomputable def leaf5203Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742479/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9816773193/9816387328) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2272157619/2147483648) }, upper := { exponent := 1, mantissa := (34999/32768) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi281LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (19633160521/19632774656) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf5203InnerLog : WideLogData :=
  innerPair336Data

set_option maxRecDepth 1000000 in
private theorem leaf5203LocalValidity :
    LeafFacts leaf5203Box leaf5203Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5203Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9816773193/9816387328) }) = true
      norm_num [leaf5203Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5203CertificateValid :
    WideCertificateValid leaf5203Box leaf5203Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi281ValidityFacts
    leaf5203LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5203CoverageChecked :
    coverageCheck (innerAD leaf5203Box) leaf5203InnerLog = true := by
  rfl'

private theorem leaf5203InnerLogValid :
    leaf5203InnerLog.Valid 8 (innerAD leaf5203Box) :=
  wideLogDataValid_of_cachedCheck endpoint89PositiveFacts
    endpoint289PositiveFacts.valid leaf5203CoverageChecked

private noncomputable def leaf5203InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814705/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5203InputLogOnePlusV_eq :
    leaf5203InputLogOnePlusV = outerEnclosure 24
      (leaf5203Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5203RoundedFacts : LeafRoundedFacts 8
    leaf5203Certificate.logOnePlusV leaf5203InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5203InputLogOnePlusV_eq }

private noncomputable def leaf5203Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi281InputQChi innerPair336Input
    leaf5203InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5203LowerChecked :
    lowerCheck 24 leaf5203Box leaf5203Inputs = true := by
  rfl'

private theorem leaf5203CoversExact : CoversExact 8
    leaf5203Box leaf5203Certificate leaf5203InnerLog leaf5203Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi281RoundedFacts
    innerPair336RoundedFacts leaf5203RoundedFacts (by rfl)

private theorem leaf5203FlatSound : Sound leaf5203Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5203CertificateValid
    leaf5203InnerLogValid leaf5203CoversExact leaf5203LowerChecked

private noncomputable def leaf5204Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (9/32), chiHi := (73/256) }

private noncomputable def leaf5204Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742481/1073741824) }, vSqrt := { lower := (65527/65536), upper := (22905804117/22904897536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2276875921/2147483648) }, upper := { exponent := 1, mantissa := (137/128) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi281LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (45810701653/45809795072) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf5204InnerLog : WideLogData :=
  innerPair336Data

set_option maxRecDepth 1000000 in
private theorem leaf5204LocalValidity :
    LeafFacts leaf5204Box leaf5204Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5204Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (22905804117/22904897536) }) = true
      norm_num [leaf5204Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5204CertificateValid :
    WideCertificateValid leaf5204Box leaf5204Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi281ValidityFacts
    leaf5204LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5204CoverageChecked :
    coverageCheck (innerAD leaf5204Box) leaf5204InnerLog = true := by
  rfl'

private theorem leaf5204InnerLogValid :
    leaf5204InnerLog.Valid 8 (innerAD leaf5204Box) :=
  wideLogDataValid_of_cachedCheck endpoint89PositiveFacts
    endpoint289PositiveFacts.valid leaf5204CoverageChecked

private noncomputable def leaf5204InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629413/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5204InputLogOnePlusV_eq :
    leaf5204InputLogOnePlusV = outerEnclosure 24
      (leaf5204Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5204RoundedFacts : LeafRoundedFacts 8
    leaf5204Certificate.logOnePlusV leaf5204InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5204InputLogOnePlusV_eq }

private noncomputable def leaf5204Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi281InputQChi innerPair336Input
    leaf5204InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5204LowerChecked :
    lowerCheck 24 leaf5204Box leaf5204Inputs = true := by
  rfl'

private theorem leaf5204CoversExact : CoversExact 8
    leaf5204Box leaf5204Certificate leaf5204InnerLog leaf5204Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi281RoundedFacts
    innerPair336RoundedFacts leaf5204RoundedFacts (by rfl)

private theorem leaf5204FlatSound : Sound leaf5204Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5204CertificateValid
    leaf5204InnerLogValid leaf5204CoversExact leaf5204LowerChecked

private noncomputable def leaf5205Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (73/256), chiHi := (37/128) }

private noncomputable def leaf5205Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742481/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714646016) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2288802745/2147483648) }, upper := { exponent := 1, mantissa := (17627/16384) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi282LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432058367/137429292032) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf5205InnerLog : WideLogData :=
  innerPair253Data

set_option maxRecDepth 1000000 in
private theorem leaf5205LocalValidity :
    LeafFacts leaf5205Box leaf5205Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5205Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714646016) }) = true
      norm_num [leaf5205Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5205CertificateValid :
    WideCertificateValid leaf5205Box leaf5205Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi282ValidityFacts
    leaf5205LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5205CoverageChecked :
    coverageCheck (innerAD leaf5205Box) leaf5205InnerLog = true := by
  rfl'

private theorem leaf5205InnerLogValid :
    leaf5205InnerLog.Valid 8 (innerAD leaf5205Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint88PositiveFacts.valid leaf5205CoverageChecked

private noncomputable def leaf5205InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814709/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5205InputLogOnePlusV_eq :
    leaf5205InputLogOnePlusV = outerEnclosure 24
      (leaf5205Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5205RoundedFacts : LeafRoundedFacts 8
    leaf5205Certificate.logOnePlusV leaf5205InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5205InputLogOnePlusV_eq }

private noncomputable def leaf5205Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi282InputQChi innerPair253Input
    leaf5205InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5205LowerChecked :
    lowerCheck 24 leaf5205Box leaf5205Inputs = true := by
  rfl'

private theorem leaf5205CoversExact : CoversExact 8
    leaf5205Box leaf5205Certificate leaf5205InnerLog leaf5205Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi282RoundedFacts
    innerPair253RoundedFacts leaf5205RoundedFacts (by rfl)

private theorem leaf5205FlatSound : Sound leaf5205Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5205CertificateValid
    leaf5205InnerLogValid leaf5205CoversExact leaf5205LowerChecked

private noncomputable def leaf5206Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (73/256), chiHi := (37/128) }

private noncomputable def leaf5206Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742483/1073741824) }, vSqrt := { lower := (65527/65536), upper := (9816773193/9816375296) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2293586579/2147483648) }, upper := { exponent := 1, mantissa := (69/64) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi282LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (19633148489/19632750592) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf5206InnerLog : WideLogData :=
  innerPair253Data

set_option maxRecDepth 1000000 in
private theorem leaf5206LocalValidity :
    LeafFacts leaf5206Box leaf5206Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5206Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (9816773193/9816375296) }) = true
      norm_num [leaf5206Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5206CertificateValid :
    WideCertificateValid leaf5206Box leaf5206Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi282ValidityFacts
    leaf5206LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5206CoverageChecked :
    coverageCheck (innerAD leaf5206Box) leaf5206InnerLog = true := by
  rfl'

private theorem leaf5206InnerLogValid :
    leaf5206InnerLog.Valid 8 (innerAD leaf5206Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint88PositiveFacts.valid leaf5206CoverageChecked

private noncomputable def leaf5206InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629421/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5206InputLogOnePlusV_eq :
    leaf5206InputLogOnePlusV = outerEnclosure 24
      (leaf5206Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5206RoundedFacts : LeafRoundedFacts 8
    leaf5206Certificate.logOnePlusV leaf5206InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5206InputLogOnePlusV_eq }

private noncomputable def leaf5206Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi282InputQChi innerPair253Input
    leaf5206InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5206LowerChecked :
    lowerCheck 24 leaf5206Box leaf5206Inputs = true := by
  rfl'

private theorem leaf5206CoversExact : CoversExact 8
    leaf5206Box leaf5206Certificate leaf5206InnerLog leaf5206Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi282RoundedFacts
    innerPair253RoundedFacts leaf5206RoundedFacts (by rfl)

private theorem leaf5206FlatSound : Sound leaf5206Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5206CertificateValid
    leaf5206InnerLogValid leaf5206CoversExact leaf5206LowerChecked

private noncomputable def leaf5207Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (37/128), chiHi := (75/256) }

private noncomputable def leaf5207Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742479/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714619136) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2295749139/2147483648) }, upper := { exponent := 1, mantissa := (35359/32768) } }, logOuter := sk237LogOuterCertificate, logK := sk237LogKCertificate, logChi := chi283LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432031487/137429238272) } }, logDArg := sk237LogDArgCertificate }

private noncomputable def leaf5207InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf5207LocalValidity :
    LeafFacts leaf5207Box leaf5207Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5207Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714619136) }) = true
      norm_num [leaf5207Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5207CertificateValid :
    WideCertificateValid leaf5207Box leaf5207Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk237ValidityFacts chi283ValidityFacts
    leaf5207LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5207CoverageChecked :
    coverageCheck (innerAD leaf5207Box) leaf5207InnerLog = true := by
  rfl'

private theorem leaf5207InnerLogValid :
    leaf5207InnerLog.Valid 8 (innerAD leaf5207Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf5207CoverageChecked

private noncomputable def leaf5207InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814711/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5207InputLogOnePlusV_eq :
    leaf5207InputLogOnePlusV = outerEnclosure 24
      (leaf5207Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5207RoundedFacts : LeafRoundedFacts 8
    leaf5207Certificate.logOnePlusV leaf5207InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5207InputLogOnePlusV_eq }

private noncomputable def leaf5207Inputs : Inputs :=
  inputsOfCaches globalInput sk237RoundedInputs
    chi283InputQChi innerPair249Input
    leaf5207InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5207LowerChecked :
    lowerCheck 24 leaf5207Box leaf5207Inputs = true := by
  rfl'

private theorem leaf5207CoversExact : CoversExact 8
    leaf5207Box leaf5207Certificate leaf5207InnerLog leaf5207Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk237RoundedFacts chi283RoundedFacts
    innerPair249RoundedFacts leaf5207RoundedFacts (by rfl)

private theorem leaf5207FlatSound : Sound leaf5207Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5207CertificateValid
    leaf5207InnerLogValid leaf5207CoversExact leaf5207LowerChecked

private noncomputable def leaf5208Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (37/128), chiHi := (75/256) }

private noncomputable def leaf5208Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742481/1073741824) }, vSqrt := { lower := (8191/8192), upper := (1598079357/1598013952) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2300598505/2147483648) }, upper := { exponent := 1, mantissa := (17717/16384) } }, logOuter := sk238LogOuterCertificate, logK := sk238LogKCertificate, logChi := chi283LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (3196093309/3196027904) } }, logDArg := sk238LogDArgCertificate }

private noncomputable def leaf5208InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf5208LocalValidity :
    LeafFacts leaf5208Box leaf5208Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5208Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (1598079357/1598013952) }) = true
      norm_num [leaf5208Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5208CertificateValid :
    WideCertificateValid leaf5208Box leaf5208Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk238ValidityFacts chi283ValidityFacts
    leaf5208LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5208CoverageChecked :
    coverageCheck (innerAD leaf5208Box) leaf5208InnerLog = true := by
  rfl'

private theorem leaf5208InnerLogValid :
    leaf5208InnerLog.Valid 8 (innerAD leaf5208Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf5208CoverageChecked

private noncomputable def leaf5208InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726839/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf5208InputLogOnePlusV_eq :
    leaf5208InputLogOnePlusV = outerEnclosure 24
      (leaf5208Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5208RoundedFacts : LeafRoundedFacts 8
    leaf5208Certificate.logOnePlusV leaf5208InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5208InputLogOnePlusV_eq }

private noncomputable def leaf5208Inputs : Inputs :=
  inputsOfCaches globalInput sk238RoundedInputs
    chi283InputQChi innerPair249Input
    leaf5208InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5208LowerChecked :
    lowerCheck 24 leaf5208Box leaf5208Inputs = true := by
  rfl'

private theorem leaf5208CoversExact : CoversExact 8
    leaf5208Box leaf5208Certificate leaf5208InnerLog leaf5208Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk238RoundedFacts chi283RoundedFacts
    innerPair249RoundedFacts leaf5208RoundedFacts (by rfl)

private theorem leaf5208FlatSound : Sound leaf5208Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5208CertificateValid
    leaf5208InnerLogValid leaf5208CoversExact leaf5208LowerChecked

private noncomputable def leaf5209Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (75/256), chiHi := (19/64) }

private noncomputable def leaf5209Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742481/1073741824) }, vSqrt := { lower := (8191/8192), upper := (738896907/738866176) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2312263201/2147483648) }, upper := { exponent := 1, mantissa := (8903/8192) } }, logOuter := sk237LogOuterCertificate, logK := sk237LogKCertificate, logChi := chi284LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (1477763083/1477732352) } }, logDArg := sk237LogDArgCertificate }

private noncomputable def leaf5209InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf5209LocalValidity :
    LeafFacts leaf5209Box leaf5209Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5209Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (738896907/738866176) }) = true
      norm_num [leaf5209Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5209CertificateValid :
    WideCertificateValid leaf5209Box leaf5209Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk237ValidityFacts chi284ValidityFacts
    leaf5209LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5209CoverageChecked :
    coverageCheck (innerAD leaf5209Box) leaf5209InnerLog = true := by
  rfl'

private theorem leaf5209InnerLogValid :
    leaf5209InnerLog.Valid 8 (innerAD leaf5209Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf5209CoverageChecked

private noncomputable def leaf5209InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814715/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5209InputLogOnePlusV_eq :
    leaf5209InputLogOnePlusV = outerEnclosure 24
      (leaf5209Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5209RoundedFacts : LeafRoundedFacts 8
    leaf5209Certificate.logOnePlusV leaf5209InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5209InputLogOnePlusV_eq }

private noncomputable def leaf5209Inputs : Inputs :=
  inputsOfCaches globalInput sk237RoundedInputs
    chi284InputQChi innerPair249Input
    leaf5209InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5209LowerChecked :
    lowerCheck 24 leaf5209Box leaf5209Inputs = true := by
  rfl'

private theorem leaf5209CoversExact : CoversExact 8
    leaf5209Box leaf5209Certificate leaf5209InnerLog leaf5209Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk237RoundedFacts chi284RoundedFacts
    innerPair249RoundedFacts leaf5209RoundedFacts (by rfl)

private theorem leaf5209FlatSound : Sound leaf5209Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5209CertificateValid
    leaf5209InnerLogValid leaf5209CoversExact leaf5209LowerChecked

private noncomputable def leaf5210Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (75/256), chiHi := (19/64) }

private noncomputable def leaf5210Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742483/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714534912) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2317178099/2147483648) }, upper := { exponent := 1, mantissa := (4461/4096) } }, logOuter := sk238LogOuterCertificate, logK := sk238LogKCertificate, logChi := chi284LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431947263/137429069824) } }, logDArg := sk238LogDArgCertificate }

private noncomputable def leaf5210InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf5210LocalValidity :
    LeafFacts leaf5210Box leaf5210Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5210Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714534912) }) = true
      norm_num [leaf5210Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5210CertificateValid :
    WideCertificateValid leaf5210Box leaf5210Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk238ValidityFacts chi284ValidityFacts
    leaf5210LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5210CoverageChecked :
    coverageCheck (innerAD leaf5210Box) leaf5210InnerLog = true := by
  rfl'

private theorem leaf5210InnerLogValid :
    leaf5210InnerLog.Valid 8 (innerAD leaf5210Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf5210CoverageChecked

private noncomputable def leaf5210InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453679/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf5210InputLogOnePlusV_eq :
    leaf5210InputLogOnePlusV = outerEnclosure 24
      (leaf5210Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5210RoundedFacts : LeafRoundedFacts 8
    leaf5210Certificate.logOnePlusV leaf5210InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5210InputLogOnePlusV_eq }

private noncomputable def leaf5210Inputs : Inputs :=
  inputsOfCaches globalInput sk238RoundedInputs
    chi284InputQChi innerPair249Input
    leaf5210InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5210LowerChecked :
    lowerCheck 24 leaf5210Box leaf5210Inputs = true := by
  rfl'

private theorem leaf5210CoversExact : CoversExact 8
    leaf5210Box leaf5210Certificate leaf5210InnerLog leaf5210Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk238RoundedFacts chi284RoundedFacts
    innerPair249RoundedFacts leaf5210RoundedFacts (by rfl)

private theorem leaf5210FlatSound : Sound leaf5210Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5210CertificateValid
    leaf5210InnerLogValid leaf5210CoversExact leaf5210LowerChecked

private noncomputable def leaf5211Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (37/128), chiHi := (75/256) }

private noncomputable def leaf5211Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742483/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714580736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2305447871/2147483648) }, upper := { exponent := 1, mantissa := (35509/32768) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi283LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431993087/137429161472) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf5211InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf5211LocalValidity :
    LeafFacts leaf5211Box leaf5211Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5211Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714580736) }) = true
      norm_num [leaf5211Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5211CertificateValid :
    WideCertificateValid leaf5211Box leaf5211Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi283ValidityFacts
    leaf5211LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5211CoverageChecked :
    coverageCheck (innerAD leaf5211Box) leaf5211InnerLog = true := by
  rfl'

private theorem leaf5211InnerLogValid :
    leaf5211InnerLog.Valid 8 (innerAD leaf5211Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf5211CoverageChecked

private noncomputable def leaf5211InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814713/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5211InputLogOnePlusV_eq :
    leaf5211InputLogOnePlusV = outerEnclosure 24
      (leaf5211Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5211RoundedFacts : LeafRoundedFacts 8
    leaf5211Certificate.logOnePlusV leaf5211InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5211InputLogOnePlusV_eq }

private noncomputable def leaf5211Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi283InputQChi innerPair249Input
    leaf5211InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5211LowerChecked :
    lowerCheck 24 leaf5211Box leaf5211Inputs = true := by
  rfl'

private theorem leaf5211CoversExact : CoversExact 8
    leaf5211Box leaf5211Certificate leaf5211InnerLog leaf5211Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi283RoundedFacts
    innerPair249RoundedFacts leaf5211RoundedFacts (by rfl)

private theorem leaf5211FlatSound : Sound leaf5211Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5211CertificateValid
    leaf5211InnerLogValid leaf5211CoversExact leaf5211LowerChecked

private noncomputable def leaf5212Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (37/128), chiHi := (75/256) }

private noncomputable def leaf5212Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742485/1073741824) }, vSqrt := { lower := (65527/65536), upper := (68717412351/68714561536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2310297237/2147483648) }, upper := { exponent := 1, mantissa := (139/128) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi283LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (137431973887/137429123072) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf5212InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf5212LocalValidity :
    LeafFacts leaf5212Box leaf5212Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5212Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (68717412351/68714561536) }) = true
      norm_num [leaf5212Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5212CertificateValid :
    WideCertificateValid leaf5212Box leaf5212Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi283ValidityFacts
    leaf5212LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5212CoverageChecked :
    coverageCheck (innerAD leaf5212Box) leaf5212InnerLog = true := by
  rfl'

private theorem leaf5212InnerLogValid :
    leaf5212InnerLog.Valid 8 (innerAD leaf5212Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf5212CoverageChecked

private noncomputable def leaf5212InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629429/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5212InputLogOnePlusV_eq :
    leaf5212InputLogOnePlusV = outerEnclosure 24
      (leaf5212Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5212RoundedFacts : LeafRoundedFacts 8
    leaf5212Certificate.logOnePlusV leaf5212InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5212InputLogOnePlusV_eq }

private noncomputable def leaf5212Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi283InputQChi innerPair249Input
    leaf5212InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5212LowerChecked :
    lowerCheck 24 leaf5212Box leaf5212Inputs = true := by
  rfl'

private theorem leaf5212CoversExact : CoversExact 8
    leaf5212Box leaf5212Certificate leaf5212InnerLog leaf5212Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi283RoundedFacts
    innerPair249RoundedFacts leaf5212RoundedFacts (by rfl)

private theorem leaf5212FlatSound : Sound leaf5212Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5212CertificateValid
    leaf5212InnerLogValid leaf5212CoversExact leaf5212LowerChecked

private noncomputable def leaf5213Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (75/256), chiHi := (19/64) }

private noncomputable def leaf5213Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742485/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714515456) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2322092997/2147483648) }, upper := { exponent := 1, mantissa := (8941/8192) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi284LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431927807/137429030912) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf5213InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf5213LocalValidity :
    LeafFacts leaf5213Box leaf5213Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5213Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714515456) }) = true
      norm_num [leaf5213Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5213CertificateValid :
    WideCertificateValid leaf5213Box leaf5213Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi284ValidityFacts
    leaf5213LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5213CoverageChecked :
    coverageCheck (innerAD leaf5213Box) leaf5213InnerLog = true := by
  rfl'

private theorem leaf5213InnerLogValid :
    leaf5213InnerLog.Valid 8 (innerAD leaf5213Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf5213CoverageChecked

private noncomputable def leaf5213InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814717/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5213InputLogOnePlusV_eq :
    leaf5213InputLogOnePlusV = outerEnclosure 24
      (leaf5213Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5213RoundedFacts : LeafRoundedFacts 8
    leaf5213Certificate.logOnePlusV leaf5213InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5213InputLogOnePlusV_eq }

private noncomputable def leaf5213Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi284InputQChi innerPair249Input
    leaf5213InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5213LowerChecked :
    lowerCheck 24 leaf5213Box leaf5213Inputs = true := by
  rfl'

private theorem leaf5213CoversExact : CoversExact 8
    leaf5213Box leaf5213Certificate leaf5213InnerLog leaf5213Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi284RoundedFacts
    innerPair249RoundedFacts leaf5213RoundedFacts (by rfl)

private theorem leaf5213FlatSound : Sound leaf5213Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5213CertificateValid
    leaf5213InnerLogValid leaf5213CoversExact leaf5213LowerChecked

private noncomputable def leaf5214Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (75/256), chiHi := (19/64) }

private noncomputable def leaf5214Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742487/1073741824) }, vSqrt := { lower := (65527/65536), upper := (7635268039/7634944000) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2327007895/2147483648) }, upper := { exponent := 1, mantissa := (35/32) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi284LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (15270212039/15269888000) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf5214InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf5214LocalValidity :
    LeafFacts leaf5214Box leaf5214Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5214Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (7635268039/7634944000) }) = true
      norm_num [leaf5214Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5214CertificateValid :
    WideCertificateValid leaf5214Box leaf5214Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi284ValidityFacts
    leaf5214LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5214CoverageChecked :
    coverageCheck (innerAD leaf5214Box) leaf5214InnerLog = true := by
  rfl'

private theorem leaf5214InnerLogValid :
    leaf5214InnerLog.Valid 8 (innerAD leaf5214Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf5214CoverageChecked

private noncomputable def leaf5214InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629437/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5214InputLogOnePlusV_eq :
    leaf5214InputLogOnePlusV = outerEnclosure 24
      (leaf5214Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5214RoundedFacts : LeafRoundedFacts 8
    leaf5214Certificate.logOnePlusV leaf5214InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5214InputLogOnePlusV_eq }

private noncomputable def leaf5214Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi284InputQChi innerPair249Input
    leaf5214InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5214LowerChecked :
    lowerCheck 24 leaf5214Box leaf5214Inputs = true := by
  rfl'

private theorem leaf5214CoversExact : CoversExact 8
    leaf5214Box leaf5214Certificate leaf5214InnerLog leaf5214Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi284RoundedFacts
    innerPair249RoundedFacts leaf5214RoundedFacts (by rfl)

private theorem leaf5214FlatSound : Sound leaf5214Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5214CertificateValid
    leaf5214InnerLogValid leaf5214CoversExact leaf5214LowerChecked

private noncomputable def leaf5215Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (249/64), chiLo := (19/64), chiHi := (77/256) }

private noncomputable def leaf5215Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742475/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714568448) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2308855543/2147483648) }, upper := { exponent := 1, mantissa := (35557/32768) } }, logOuter := sk233LogOuterCertificate, logK := sk233LogKCertificate, logChi := chi285LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431980799/137429136896) } }, logDArg := sk233LogDArgCertificate }

private noncomputable def leaf5215InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf5215LocalValidity :
    LeafFacts leaf5215Box leaf5215Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5215Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714568448) }) = true
      norm_num [leaf5215Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5215CertificateValid :
    WideCertificateValid leaf5215Box leaf5215Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk233ValidityFacts chi285ValidityFacts
    leaf5215LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5215CoverageChecked :
    coverageCheck (innerAD leaf5215Box) leaf5215InnerLog = true := by
  rfl'

private theorem leaf5215InnerLogValid :
    leaf5215InnerLog.Valid 8 (innerAD leaf5215Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf5215CoverageChecked

private noncomputable def leaf5215InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907357/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5215InputLogOnePlusV_eq :
    leaf5215InputLogOnePlusV = outerEnclosure 24
      (leaf5215Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5215RoundedFacts : LeafRoundedFacts 8
    leaf5215Certificate.logOnePlusV leaf5215InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5215InputLogOnePlusV_eq }

private noncomputable def leaf5215Inputs : Inputs :=
  inputsOfCaches globalInput sk233RoundedInputs
    chi285InputQChi innerPair249Input
    leaf5215InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5215LowerChecked :
    lowerCheck 24 leaf5215Box leaf5215Inputs = true := by
  rfl'

private theorem leaf5215CoversExact : CoversExact 8
    leaf5215Box leaf5215Certificate leaf5215InnerLog leaf5215Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk233RoundedFacts chi285RoundedFacts
    innerPair249RoundedFacts leaf5215RoundedFacts (by rfl)

private theorem leaf5215FlatSound : Sound leaf5215Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5215CertificateValid
    leaf5215InnerLogValid leaf5215CoversExact leaf5215LowerChecked

private noncomputable def leaf5216Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (249/64), kHi := (125/32), chiLo := (19/64), chiHi := (77/256) }

private noncomputable def leaf5216Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742477/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714548736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2313835973/2147483648) }, upper := { exponent := 1, mantissa := (17817/16384) } }, logOuter := sk234LogOuterCertificate, logK := sk234LogKCertificate, logChi := chi285LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431961087/137429097472) } }, logDArg := sk234LogDArgCertificate }

private noncomputable def leaf5216InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf5216LocalValidity :
    LeafFacts leaf5216Box leaf5216Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5216Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714548736) }) = true
      norm_num [leaf5216Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5216CertificateValid :
    WideCertificateValid leaf5216Box leaf5216Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk234ValidityFacts chi285ValidityFacts
    leaf5216LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5216CoverageChecked :
    coverageCheck (innerAD leaf5216Box) leaf5216InnerLog = true := by
  rfl'

private theorem leaf5216InnerLogValid :
    leaf5216InnerLog.Valid 8 (innerAD leaf5216Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf5216CoverageChecked

private noncomputable def leaf5216InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814715/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5216InputLogOnePlusV_eq :
    leaf5216InputLogOnePlusV = outerEnclosure 24
      (leaf5216Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5216RoundedFacts : LeafRoundedFacts 8
    leaf5216Certificate.logOnePlusV leaf5216InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5216InputLogOnePlusV_eq }

private noncomputable def leaf5216Inputs : Inputs :=
  inputsOfCaches globalInput sk234RoundedInputs
    chi285InputQChi innerPair249Input
    leaf5216InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5216LowerChecked :
    lowerCheck 24 leaf5216Box leaf5216Inputs = true := by
  rfl'

private theorem leaf5216CoversExact : CoversExact 8
    leaf5216Box leaf5216Certificate leaf5216InnerLog leaf5216Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk234RoundedFacts chi285RoundedFacts
    innerPair249RoundedFacts leaf5216RoundedFacts (by rfl)

private theorem leaf5216FlatSound : Sound leaf5216Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5216CertificateValid
    leaf5216InnerLogValid leaf5216CoversExact leaf5216LowerChecked

private noncomputable def leaf5217Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (249/64), chiLo := (77/256), chiHi := (39/128) }

private noncomputable def leaf5217Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742477/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714504704) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2325107477/2147483648) }, upper := { exponent := 1, mantissa := (17903/16384) } }, logOuter := sk233LogOuterCertificate, logK := sk233LogKCertificate, logChi := chi286LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431917055/137429009408) } }, logDArg := sk233LogDArgCertificate }

private noncomputable def leaf5217InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf5217LocalValidity :
    LeafFacts leaf5217Box leaf5217Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5217Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714504704) }) = true
      norm_num [leaf5217Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5217CertificateValid :
    WideCertificateValid leaf5217Box leaf5217Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk233ValidityFacts chi286ValidityFacts
    leaf5217LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5217CoverageChecked :
    coverageCheck (innerAD leaf5217Box) leaf5217InnerLog = true := by
  rfl'

private theorem leaf5217InnerLogValid :
    leaf5217InnerLog.Valid 8 (innerAD leaf5217Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf5217CoverageChecked

private noncomputable def leaf5217InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907359/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5217InputLogOnePlusV_eq :
    leaf5217InputLogOnePlusV = outerEnclosure 24
      (leaf5217Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5217RoundedFacts : LeafRoundedFacts 8
    leaf5217Certificate.logOnePlusV leaf5217InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5217InputLogOnePlusV_eq }

private noncomputable def leaf5217Inputs : Inputs :=
  inputsOfCaches globalInput sk233RoundedInputs
    chi286InputQChi innerPair249Input
    leaf5217InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5217LowerChecked :
    lowerCheck 24 leaf5217Box leaf5217Inputs = true := by
  rfl'

private theorem leaf5217CoversExact : CoversExact 8
    leaf5217Box leaf5217Certificate leaf5217InnerLog leaf5217Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk233RoundedFacts chi286RoundedFacts
    innerPair249RoundedFacts leaf5217RoundedFacts (by rfl)

private theorem leaf5217FlatSound : Sound leaf5217Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5217CertificateValid
    leaf5217InnerLogValid leaf5217CoversExact leaf5217LowerChecked

private noncomputable def leaf5218Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (249/64), kHi := (125/32), chiLo := (77/256), chiHi := (39/128) }

private noncomputable def leaf5218Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742479/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714484736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2330153439/2147483648) }, upper := { exponent := 1, mantissa := (8971/8192) } }, logOuter := sk234LogOuterCertificate, logK := sk234LogKCertificate, logChi := chi286LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431897087/137428969472) } }, logDArg := sk234LogDArgCertificate }

private noncomputable def leaf5218InnerLog : WideLogData :=
  innerPair332Data

set_option maxRecDepth 1000000 in
private theorem leaf5218LocalValidity :
    LeafFacts leaf5218Box leaf5218Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5218Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714484736) }) = true
      norm_num [leaf5218Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5218CertificateValid :
    WideCertificateValid leaf5218Box leaf5218Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk234ValidityFacts chi286ValidityFacts
    leaf5218LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5218CoverageChecked :
    coverageCheck (innerAD leaf5218Box) leaf5218InnerLog = true := by
  rfl'

private theorem leaf5218InnerLogValid :
    leaf5218InnerLog.Valid 8 (innerAD leaf5218Box) :=
  wideLogDataValid_of_cachedCheck endpoint88PositiveFacts
    endpoint291PositiveFacts.valid leaf5218CoverageChecked

private noncomputable def leaf5218InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814719/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5218InputLogOnePlusV_eq :
    leaf5218InputLogOnePlusV = outerEnclosure 24
      (leaf5218Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5218RoundedFacts : LeafRoundedFacts 8
    leaf5218Certificate.logOnePlusV leaf5218InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5218InputLogOnePlusV_eq }

private noncomputable def leaf5218Inputs : Inputs :=
  inputsOfCaches globalInput sk234RoundedInputs
    chi286InputQChi innerPair332Input
    leaf5218InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5218LowerChecked :
    lowerCheck 24 leaf5218Box leaf5218Inputs = true := by
  rfl'

private theorem leaf5218CoversExact : CoversExact 8
    leaf5218Box leaf5218Certificate leaf5218InnerLog leaf5218Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk234RoundedFacts chi286RoundedFacts
    innerPair332RoundedFacts leaf5218RoundedFacts (by rfl)

private theorem leaf5218FlatSound : Sound leaf5218Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5218CertificateValid
    leaf5218InnerLogValid leaf5218CoversExact leaf5218LowerChecked

private noncomputable def leaf5219Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (251/64), chiLo := (19/64), chiHi := (77/256) }

private noncomputable def leaf5219Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742479/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22905804117/22904843008) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2318816403/2147483648) }, upper := { exponent := 1, mantissa := (35711/32768) } }, logOuter := sk235LogOuterCertificate, logK := sk235LogKCertificate, logChi := chi285LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45810647125/45809686016) } }, logDArg := sk235LogDArgCertificate }

private noncomputable def leaf5219InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf5219LocalValidity :
    LeafFacts leaf5219Box leaf5219Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5219Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22905804117/22904843008) }) = true
      norm_num [leaf5219Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5219CertificateValid :
    WideCertificateValid leaf5219Box leaf5219Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk235ValidityFacts chi285ValidityFacts
    leaf5219LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5219CoverageChecked :
    coverageCheck (innerAD leaf5219Box) leaf5219InnerLog = true := by
  rfl'

private theorem leaf5219InnerLogValid :
    leaf5219InnerLog.Valid 8 (innerAD leaf5219Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf5219CoverageChecked

private noncomputable def leaf5219InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629433/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5219InputLogOnePlusV_eq :
    leaf5219InputLogOnePlusV = outerEnclosure 24
      (leaf5219Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5219RoundedFacts : LeafRoundedFacts 8
    leaf5219Certificate.logOnePlusV leaf5219InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5219InputLogOnePlusV_eq }

private noncomputable def leaf5219Inputs : Inputs :=
  inputsOfCaches globalInput sk235RoundedInputs
    chi285InputQChi innerPair249Input
    leaf5219InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5219LowerChecked :
    lowerCheck 24 leaf5219Box leaf5219Inputs = true := by
  rfl'

private theorem leaf5219CoversExact : CoversExact 8
    leaf5219Box leaf5219Certificate leaf5219InnerLog leaf5219Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk235RoundedFacts chi285RoundedFacts
    innerPair249RoundedFacts leaf5219RoundedFacts (by rfl)

private theorem leaf5219FlatSound : Sound leaf5219Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5219CertificateValid
    leaf5219InnerLogValid leaf5219CoversExact leaf5219LowerChecked

private noncomputable def leaf5220Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (63/16), chiLo := (19/64), chiHi := (77/256) }

private noncomputable def leaf5220Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742481/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714509312) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2323796833/2147483648) }, upper := { exponent := 1, mantissa := (8947/8192) } }, logOuter := sk236LogOuterCertificate, logK := sk236LogKCertificate, logChi := chi285LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431921663/137429018624) } }, logDArg := sk236LogDArgCertificate }

private noncomputable def leaf5220InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf5220LocalValidity :
    LeafFacts leaf5220Box leaf5220Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5220Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714509312) }) = true
      norm_num [leaf5220Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5220CertificateValid :
    WideCertificateValid leaf5220Box leaf5220Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk236ValidityFacts chi285ValidityFacts
    leaf5220LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5220CoverageChecked :
    coverageCheck (innerAD leaf5220Box) leaf5220InnerLog = true := by
  rfl'

private theorem leaf5220InnerLogValid :
    leaf5220InnerLog.Valid 8 (innerAD leaf5220Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf5220CoverageChecked

private noncomputable def leaf5220InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629435/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5220InputLogOnePlusV_eq :
    leaf5220InputLogOnePlusV = outerEnclosure 24
      (leaf5220Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5220RoundedFacts : LeafRoundedFacts 8
    leaf5220Certificate.logOnePlusV leaf5220InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5220InputLogOnePlusV_eq }

private noncomputable def leaf5220Inputs : Inputs :=
  inputsOfCaches globalInput sk236RoundedInputs
    chi285InputQChi innerPair249Input
    leaf5220InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5220LowerChecked :
    lowerCheck 24 leaf5220Box leaf5220Inputs = true := by
  rfl'

private theorem leaf5220CoversExact : CoversExact 8
    leaf5220Box leaf5220Certificate leaf5220InnerLog leaf5220Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk236RoundedFacts chi285RoundedFacts
    innerPair249RoundedFacts leaf5220RoundedFacts (by rfl)

private theorem leaf5220FlatSound : Sound leaf5220Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5220CertificateValid
    leaf5220InnerLogValid leaf5220CoversExact leaf5220LowerChecked

private noncomputable def leaf5221Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (251/64), chiLo := (77/256), chiHi := (39/128) }

private noncomputable def leaf5221Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742481/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714464768) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2335199401/2147483648) }, upper := { exponent := 1, mantissa := (17981/16384) } }, logOuter := sk235LogOuterCertificate, logK := sk235LogKCertificate, logChi := chi286LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431877119/137428929536) } }, logDArg := sk235LogDArgCertificate }

private noncomputable def leaf5221InnerLog : WideLogData :=
  innerPair612Data

set_option maxRecDepth 1000000 in
private theorem leaf5221LocalValidity :
    LeafFacts leaf5221Box leaf5221Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5221Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714464768) }) = true
      norm_num [leaf5221Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5221CertificateValid :
    WideCertificateValid leaf5221Box leaf5221Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk235ValidityFacts chi286ValidityFacts
    leaf5221LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5221CoverageChecked :
    coverageCheck (innerAD leaf5221Box) leaf5221InnerLog = true := by
  rfl'

private theorem leaf5221InnerLogValid :
    leaf5221InnerLog.Valid 8 (innerAD leaf5221Box) :=
  wideLogDataValid_of_cachedCheck endpoint337PositiveFacts
    endpoint291PositiveFacts.valid leaf5221CoverageChecked

private noncomputable def leaf5221InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629441/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5221InputLogOnePlusV_eq :
    leaf5221InputLogOnePlusV = outerEnclosure 24
      (leaf5221Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5221RoundedFacts : LeafRoundedFacts 8
    leaf5221Certificate.logOnePlusV leaf5221InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5221InputLogOnePlusV_eq }

private noncomputable def leaf5221Inputs : Inputs :=
  inputsOfCaches globalInput sk235RoundedInputs
    chi286InputQChi innerPair612Input
    leaf5221InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5221LowerChecked :
    lowerCheck 24 leaf5221Box leaf5221Inputs = true := by
  rfl'

private theorem leaf5221CoversExact : CoversExact 8
    leaf5221Box leaf5221Certificate leaf5221InnerLog leaf5221Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk235RoundedFacts chi286RoundedFacts
    innerPair612RoundedFacts leaf5221RoundedFacts (by rfl)

private theorem leaf5221FlatSound : Sound leaf5221Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5221CertificateValid
    leaf5221InnerLogValid leaf5221CoversExact leaf5221LowerChecked

private noncomputable def leaf5222Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (63/16), chiLo := (77/256), chiHi := (39/128) }

private noncomputable def leaf5222Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742483/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714444800) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2340245363/2147483648) }, upper := { exponent := 1, mantissa := (4505/4096) } }, logOuter := sk236LogOuterCertificate, logK := sk236LogKCertificate, logChi := chi286LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431857151/137428889600) } }, logDArg := sk236LogDArgCertificate }

private noncomputable def leaf5222InnerLog : WideLogData :=
  innerPair612Data

set_option maxRecDepth 1000000 in
private theorem leaf5222LocalValidity :
    LeafFacts leaf5222Box leaf5222Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5222Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714444800) }) = true
      norm_num [leaf5222Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5222CertificateValid :
    WideCertificateValid leaf5222Box leaf5222Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk236ValidityFacts chi286ValidityFacts
    leaf5222LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5222CoverageChecked :
    coverageCheck (innerAD leaf5222Box) leaf5222InnerLog = true := by
  rfl'

private theorem leaf5222InnerLogValid :
    leaf5222InnerLog.Valid 8 (innerAD leaf5222Box) :=
  wideLogDataValid_of_cachedCheck endpoint337PositiveFacts
    endpoint291PositiveFacts.valid leaf5222CoverageChecked

private noncomputable def leaf5222InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629443/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5222InputLogOnePlusV_eq :
    leaf5222InputLogOnePlusV = outerEnclosure 24
      (leaf5222Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5222RoundedFacts : LeafRoundedFacts 8
    leaf5222Certificate.logOnePlusV leaf5222InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5222InputLogOnePlusV_eq }

private noncomputable def leaf5222Inputs : Inputs :=
  inputsOfCaches globalInput sk236RoundedInputs
    chi286InputQChi innerPair612Input
    leaf5222InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5222LowerChecked :
    lowerCheck 24 leaf5222Box leaf5222Inputs = true := by
  rfl'

private theorem leaf5222CoversExact : CoversExact 8
    leaf5222Box leaf5222Certificate leaf5222InnerLog leaf5222Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk236RoundedFacts chi286RoundedFacts
    innerPair612RoundedFacts leaf5222RoundedFacts (by rfl)

private theorem leaf5222FlatSound : Sound leaf5222Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5222CertificateValid
    leaf5222InnerLogValid leaf5222CoversExact leaf5222LowerChecked

private noncomputable def leaf5223Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (249/64), chiLo := (39/128), chiHi := (79/256) }

private noncomputable def leaf5223Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742479/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714440960) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2341359411/2147483648) }, upper := { exponent := 1, mantissa := (36055/32768) } }, logOuter := sk233LogOuterCertificate, logK := sk233LogKCertificate, logChi := chi287LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431853311/137428881920) } }, logDArg := sk233LogDArgCertificate }

private noncomputable def leaf5223InnerLog : WideLogData :=
  innerPair612Data

set_option maxRecDepth 1000000 in
private theorem leaf5223LocalValidity :
    LeafFacts leaf5223Box leaf5223Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5223Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714440960) }) = true
      norm_num [leaf5223Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5223CertificateValid :
    WideCertificateValid leaf5223Box leaf5223Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk233ValidityFacts chi287ValidityFacts
    leaf5223LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5223CoverageChecked :
    coverageCheck (innerAD leaf5223Box) leaf5223InnerLog = true := by
  rfl'

private theorem leaf5223InnerLogValid :
    leaf5223InnerLog.Valid 8 (innerAD leaf5223Box) :=
  wideLogDataValid_of_cachedCheck endpoint337PositiveFacts
    endpoint291PositiveFacts.valid leaf5223CoverageChecked

private noncomputable def leaf5223InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629443/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5223InputLogOnePlusV_eq :
    leaf5223InputLogOnePlusV = outerEnclosure 24
      (leaf5223Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5223RoundedFacts : LeafRoundedFacts 8
    leaf5223Certificate.logOnePlusV leaf5223InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5223InputLogOnePlusV_eq }

private noncomputable def leaf5223Inputs : Inputs :=
  inputsOfCaches globalInput sk233RoundedInputs
    chi287InputQChi innerPair612Input
    leaf5223InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5223LowerChecked :
    lowerCheck 24 leaf5223Box leaf5223Inputs = true := by
  rfl'

private theorem leaf5223CoversExact : CoversExact 8
    leaf5223Box leaf5223Certificate leaf5223InnerLog leaf5223Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk233RoundedFacts chi287RoundedFacts
    innerPair612RoundedFacts leaf5223RoundedFacts (by rfl)

private theorem leaf5223FlatSound : Sound leaf5223Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5223CertificateValid
    leaf5223InnerLogValid leaf5223CoversExact leaf5223LowerChecked

private noncomputable def leaf5224Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (249/64), kHi := (125/32), chiLo := (39/128), chiHi := (79/256) }

private noncomputable def leaf5224Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742481/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22905804117/22904806912) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2346470905/2147483648) }, upper := { exponent := 1, mantissa := (18067/16384) } }, logOuter := sk234LogOuterCertificate, logK := sk234LogKCertificate, logChi := chi287LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45810611029/45809613824) } }, logDArg := sk234LogDArgCertificate }

private noncomputable def leaf5224InnerLog : WideLogData :=
  innerPair250Data

set_option maxRecDepth 1000000 in
private theorem leaf5224LocalValidity :
    LeafFacts leaf5224Box leaf5224Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5224Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22905804117/22904806912) }) = true
      norm_num [leaf5224Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5224CertificateValid :
    WideCertificateValid leaf5224Box leaf5224Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk234ValidityFacts chi287ValidityFacts
    leaf5224LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5224CoverageChecked :
    coverageCheck (innerAD leaf5224Box) leaf5224InnerLog = true := by
  rfl'

private theorem leaf5224InnerLogValid :
    leaf5224InnerLog.Valid 8 (innerAD leaf5224Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint75PositiveFacts.valid leaf5224CoverageChecked

private noncomputable def leaf5224InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814723/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5224InputLogOnePlusV_eq :
    leaf5224InputLogOnePlusV = outerEnclosure 24
      (leaf5224Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5224RoundedFacts : LeafRoundedFacts 8
    leaf5224Certificate.logOnePlusV leaf5224InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5224InputLogOnePlusV_eq }

private noncomputable def leaf5224Inputs : Inputs :=
  inputsOfCaches globalInput sk234RoundedInputs
    chi287InputQChi innerPair250Input
    leaf5224InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5224LowerChecked :
    lowerCheck 24 leaf5224Box leaf5224Inputs = true := by
  rfl'

private theorem leaf5224CoversExact : CoversExact 8
    leaf5224Box leaf5224Certificate leaf5224InnerLog leaf5224Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk234RoundedFacts chi287RoundedFacts
    innerPair250RoundedFacts leaf5224RoundedFacts (by rfl)

private theorem leaf5224FlatSound : Sound leaf5224Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5224CertificateValid
    leaf5224InnerLogValid leaf5224CoversExact leaf5224LowerChecked

private noncomputable def leaf5225Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (249/64), chiLo := (79/256), chiHi := (5/16) }

private noncomputable def leaf5225Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742481/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714377216) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2357611345/2147483648) }, upper := { exponent := 1, mantissa := (2269/2048) } }, logOuter := sk233LogOuterCertificate, logK := sk233LogKCertificate, logChi := chi288LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431789567/137428754432) } }, logDArg := sk233LogDArgCertificate }

private noncomputable def leaf5225InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf5225LocalValidity :
    LeafFacts leaf5225Box leaf5225Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5225Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714377216) }) = true
      norm_num [leaf5225Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5225CertificateValid :
    WideCertificateValid leaf5225Box leaf5225Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk233ValidityFacts chi288ValidityFacts
    leaf5225LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5225CoverageChecked :
    coverageCheck (innerAD leaf5225Box) leaf5225InnerLog = true := by
  rfl'

private theorem leaf5225InnerLogValid :
    leaf5225InnerLog.Valid 8 (innerAD leaf5225Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf5225CoverageChecked

private noncomputable def leaf5225InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629451/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5225InputLogOnePlusV_eq :
    leaf5225InputLogOnePlusV = outerEnclosure 24
      (leaf5225Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5225RoundedFacts : LeafRoundedFacts 8
    leaf5225Certificate.logOnePlusV leaf5225InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5225InputLogOnePlusV_eq }

private noncomputable def leaf5225Inputs : Inputs :=
  inputsOfCaches globalInput sk233RoundedInputs
    chi288InputQChi innerPair256Input
    leaf5225InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5225LowerChecked :
    lowerCheck 24 leaf5225Box leaf5225Inputs = true := by
  rfl'

private theorem leaf5225CoversExact : CoversExact 8
    leaf5225Box leaf5225Certificate leaf5225InnerLog leaf5225Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk233RoundedFacts chi288RoundedFacts
    innerPair256RoundedFacts leaf5225RoundedFacts (by rfl)

private theorem leaf5225FlatSound : Sound leaf5225Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5225CertificateValid
    leaf5225InnerLogValid leaf5225CoversExact leaf5225LowerChecked

private noncomputable def leaf5226Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (249/64), kHi := (125/32), chiLo := (79/256), chiHi := (5/16) }

private noncomputable def leaf5226Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742483/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714356736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2362788371/2147483648) }, upper := { exponent := 1, mantissa := (1137/1024) } }, logOuter := sk234LogOuterCertificate, logK := sk234LogKCertificate, logChi := chi288LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431769087/137428713472) } }, logDArg := sk234LogDArgCertificate }

private noncomputable def leaf5226InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf5226LocalValidity :
    LeafFacts leaf5226Box leaf5226Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5226Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714356736) }) = true
      norm_num [leaf5226Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5226CertificateValid :
    WideCertificateValid leaf5226Box leaf5226Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk234ValidityFacts chi288ValidityFacts
    leaf5226LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5226CoverageChecked :
    coverageCheck (innerAD leaf5226Box) leaf5226InnerLog = true := by
  rfl'

private theorem leaf5226InnerLogValid :
    leaf5226InnerLog.Valid 8 (innerAD leaf5226Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf5226CoverageChecked

private noncomputable def leaf5226InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814727/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5226InputLogOnePlusV_eq :
    leaf5226InputLogOnePlusV = outerEnclosure 24
      (leaf5226Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5226RoundedFacts : LeafRoundedFacts 8
    leaf5226Certificate.logOnePlusV leaf5226InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5226InputLogOnePlusV_eq }

private noncomputable def leaf5226Inputs : Inputs :=
  inputsOfCaches globalInput sk234RoundedInputs
    chi288InputQChi innerPair256Input
    leaf5226InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5226LowerChecked :
    lowerCheck 24 leaf5226Box leaf5226Inputs = true := by
  rfl'

private theorem leaf5226CoversExact : CoversExact 8
    leaf5226Box leaf5226Certificate leaf5226InnerLog leaf5226Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk234RoundedFacts chi288RoundedFacts
    innerPair256RoundedFacts leaf5226RoundedFacts (by rfl)

private theorem leaf5226FlatSound : Sound leaf5226Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5226CertificateValid
    leaf5226InnerLogValid leaf5226CoversExact leaf5226LowerChecked

private noncomputable def leaf5227Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (251/64), chiLo := (39/128), chiHi := (79/256) }

private noncomputable def leaf5227Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742483/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714400512) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2351582399/2147483648) }, upper := { exponent := 1, mantissa := (36213/32768) } }, logOuter := sk235LogOuterCertificate, logK := sk235LogKCertificate, logChi := chi287LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431812863/137428801024) } }, logDArg := sk235LogDArgCertificate }

private noncomputable def leaf5227InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf5227LocalValidity :
    LeafFacts leaf5227Box leaf5227Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5227Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714400512) }) = true
      norm_num [leaf5227Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5227CertificateValid :
    WideCertificateValid leaf5227Box leaf5227Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk235ValidityFacts chi287ValidityFacts
    leaf5227LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5227CoverageChecked :
    coverageCheck (innerAD leaf5227Box) leaf5227InnerLog = true := by
  rfl'

private theorem leaf5227InnerLogValid :
    leaf5227InnerLog.Valid 8 (innerAD leaf5227Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf5227CoverageChecked

private noncomputable def leaf5227InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453681/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf5227InputLogOnePlusV_eq :
    leaf5227InputLogOnePlusV = outerEnclosure 24
      (leaf5227Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5227RoundedFacts : LeafRoundedFacts 8
    leaf5227Certificate.logOnePlusV leaf5227InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5227InputLogOnePlusV_eq }

private noncomputable def leaf5227Inputs : Inputs :=
  inputsOfCaches globalInput sk235RoundedInputs
    chi287InputQChi innerPair256Input
    leaf5227InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5227LowerChecked :
    lowerCheck 24 leaf5227Box leaf5227Inputs = true := by
  rfl'

private theorem leaf5227CoversExact : CoversExact 8
    leaf5227Box leaf5227Certificate leaf5227InnerLog leaf5227Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk235RoundedFacts chi287RoundedFacts
    innerPair256RoundedFacts leaf5227RoundedFacts (by rfl)

private theorem leaf5227FlatSound : Sound leaf5227Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5227CertificateValid
    leaf5227InnerLogValid leaf5227CoversExact leaf5227LowerChecked

private noncomputable def leaf5228Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (63/16), chiLo := (39/128), chiHi := (79/256) }

private noncomputable def leaf5228Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742485/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714380288) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2356693893/2147483648) }, upper := { exponent := 1, mantissa := (9073/8192) } }, logOuter := sk236LogOuterCertificate, logK := sk236LogKCertificate, logChi := chi287LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431792639/137428760576) } }, logDArg := sk236LogDArgCertificate }

private noncomputable def leaf5228InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf5228LocalValidity :
    LeafFacts leaf5228Box leaf5228Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5228Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714380288) }) = true
      norm_num [leaf5228Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5228CertificateValid :
    WideCertificateValid leaf5228Box leaf5228Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk236ValidityFacts chi287ValidityFacts
    leaf5228LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5228CoverageChecked :
    coverageCheck (innerAD leaf5228Box) leaf5228InnerLog = true := by
  rfl'

private theorem leaf5228InnerLogValid :
    leaf5228InnerLog.Valid 8 (innerAD leaf5228Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf5228CoverageChecked

private noncomputable def leaf5228InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629451/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5228InputLogOnePlusV_eq :
    leaf5228InputLogOnePlusV = outerEnclosure 24
      (leaf5228Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5228RoundedFacts : LeafRoundedFacts 8
    leaf5228Certificate.logOnePlusV leaf5228InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5228InputLogOnePlusV_eq }

private noncomputable def leaf5228Inputs : Inputs :=
  inputsOfCaches globalInput sk236RoundedInputs
    chi287InputQChi innerPair256Input
    leaf5228InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5228LowerChecked :
    lowerCheck 24 leaf5228Box leaf5228Inputs = true := by
  rfl'

private theorem leaf5228CoversExact : CoversExact 8
    leaf5228Box leaf5228Certificate leaf5228InnerLog leaf5228Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk236RoundedFacts chi287RoundedFacts
    innerPair256RoundedFacts leaf5228RoundedFacts (by rfl)

private theorem leaf5228FlatSound : Sound leaf5228Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5228CertificateValid
    leaf5228InnerLogValid leaf5228CoversExact leaf5228LowerChecked

private noncomputable def leaf5229Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (251/64), chiLo := (79/256), chiHi := (5/16) }

private noncomputable def leaf5229Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742485/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22905804117/22904778752) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2367965397/2147483648) }, upper := { exponent := 1, mantissa := (2279/2048) } }, logOuter := sk235LogOuterCertificate, logK := sk235LogKCertificate, logChi := chi288LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45810582869/45809557504) } }, logDArg := sk235LogDArgCertificate }

private noncomputable def leaf5229InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf5229LocalValidity :
    LeafFacts leaf5229Box leaf5229Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5229Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22905804117/22904778752) }) = true
      norm_num [leaf5229Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5229CertificateValid :
    WideCertificateValid leaf5229Box leaf5229Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk235ValidityFacts chi288ValidityFacts
    leaf5229LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5229CoverageChecked :
    coverageCheck (innerAD leaf5229Box) leaf5229InnerLog = true := by
  rfl'

private theorem leaf5229InnerLogValid :
    leaf5229InnerLog.Valid 8 (innerAD leaf5229Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf5229CoverageChecked

private noncomputable def leaf5229InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726841/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf5229InputLogOnePlusV_eq :
    leaf5229InputLogOnePlusV = outerEnclosure 24
      (leaf5229Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5229RoundedFacts : LeafRoundedFacts 8
    leaf5229Certificate.logOnePlusV leaf5229InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5229InputLogOnePlusV_eq }

private noncomputable def leaf5229Inputs : Inputs :=
  inputsOfCaches globalInput sk235RoundedInputs
    chi288InputQChi innerPair256Input
    leaf5229InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5229LowerChecked :
    lowerCheck 24 leaf5229Box leaf5229Inputs = true := by
  rfl'

private theorem leaf5229CoversExact : CoversExact 8
    leaf5229Box leaf5229Certificate leaf5229InnerLog leaf5229Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk235RoundedFacts chi288RoundedFacts
    innerPair256RoundedFacts leaf5229RoundedFacts (by rfl)

private theorem leaf5229FlatSound : Sound leaf5229Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5229CertificateValid
    leaf5229InnerLogValid leaf5229CoversExact leaf5229LowerChecked

private noncomputable def leaf5230Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (63/16), chiLo := (79/256), chiHi := (5/16) }

private noncomputable def leaf5230Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742487/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714315776) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2373142423/2147483648) }, upper := { exponent := 1, mantissa := (571/512) } }, logOuter := sk236LogOuterCertificate, logK := sk236LogKCertificate, logChi := chi288LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431728127/137428631552) } }, logDArg := sk236LogDArgCertificate }

private noncomputable def leaf5230InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf5230LocalValidity :
    LeafFacts leaf5230Box leaf5230Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5230Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714315776) }) = true
      norm_num [leaf5230Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5230CertificateValid :
    WideCertificateValid leaf5230Box leaf5230Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk236ValidityFacts chi288ValidityFacts
    leaf5230LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5230CoverageChecked :
    coverageCheck (innerAD leaf5230Box) leaf5230InnerLog = true := by
  rfl'

private theorem leaf5230InnerLogValid :
    leaf5230InnerLog.Valid 8 (innerAD leaf5230Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf5230CoverageChecked

private noncomputable def leaf5230InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629459/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5230InputLogOnePlusV_eq :
    leaf5230InputLogOnePlusV = outerEnclosure 24
      (leaf5230Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5230RoundedFacts : LeafRoundedFacts 8
    leaf5230Certificate.logOnePlusV leaf5230InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5230InputLogOnePlusV_eq }

private noncomputable def leaf5230Inputs : Inputs :=
  inputsOfCaches globalInput sk236RoundedInputs
    chi288InputQChi innerPair256Input
    leaf5230InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5230LowerChecked :
    lowerCheck 24 leaf5230Box leaf5230Inputs = true := by
  rfl'

private theorem leaf5230CoversExact : CoversExact 8
    leaf5230Box leaf5230Certificate leaf5230InnerLog leaf5230Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk236RoundedFacts chi288RoundedFacts
    innerPair256RoundedFacts leaf5230RoundedFacts (by rfl)

private theorem leaf5230FlatSound : Sound leaf5230Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5230CertificateValid
    leaf5230InnerLogValid leaf5230CoversExact leaf5230LowerChecked

private noncomputable def leaf5231Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (19/64), chiHi := (77/256) }

private noncomputable def leaf5231Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742483/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714489600) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2328777263/2147483648) }, upper := { exponent := 1, mantissa := (35865/32768) } }, logOuter := sk237LogOuterCertificate, logK := sk237LogKCertificate, logChi := chi285LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431901951/137428979200) } }, logDArg := sk237LogDArgCertificate }

private noncomputable def leaf5231InnerLog : WideLogData :=
  innerPair332Data

set_option maxRecDepth 1000000 in
private theorem leaf5231LocalValidity :
    LeafFacts leaf5231Box leaf5231Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5231Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714489600) }) = true
      norm_num [leaf5231Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5231CertificateValid :
    WideCertificateValid leaf5231Box leaf5231Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk237ValidityFacts chi285ValidityFacts
    leaf5231LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5231CoverageChecked :
    coverageCheck (innerAD leaf5231Box) leaf5231InnerLog = true := by
  rfl'

private theorem leaf5231InnerLogValid :
    leaf5231InnerLog.Valid 8 (innerAD leaf5231Box) :=
  wideLogDataValid_of_cachedCheck endpoint88PositiveFacts
    endpoint291PositiveFacts.valid leaf5231CoverageChecked

private noncomputable def leaf5231InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814719/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5231InputLogOnePlusV_eq :
    leaf5231InputLogOnePlusV = outerEnclosure 24
      (leaf5231Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5231RoundedFacts : LeafRoundedFacts 8
    leaf5231Certificate.logOnePlusV leaf5231InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5231InputLogOnePlusV_eq }

private noncomputable def leaf5231Inputs : Inputs :=
  inputsOfCaches globalInput sk237RoundedInputs
    chi285InputQChi innerPair332Input
    leaf5231InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5231LowerChecked :
    lowerCheck 24 leaf5231Box leaf5231Inputs = true := by
  rfl'

private theorem leaf5231CoversExact : CoversExact 8
    leaf5231Box leaf5231Certificate leaf5231InnerLog leaf5231Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk237RoundedFacts chi285RoundedFacts
    innerPair332RoundedFacts leaf5231RoundedFacts (by rfl)

private theorem leaf5231FlatSound : Sound leaf5231Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5231CertificateValid
    leaf5231InnerLogValid leaf5231CoversExact leaf5231LowerChecked

private noncomputable def leaf5232Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (19/64), chiHi := (77/256) }

private noncomputable def leaf5232Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742485/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22905804117/22904823296) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2333757693/2147483648) }, upper := { exponent := 1, mantissa := (17971/16384) } }, logOuter := sk238LogOuterCertificate, logK := sk238LogKCertificate, logChi := chi285LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45810627413/45809646592) } }, logDArg := sk238LogDArgCertificate }

private noncomputable def leaf5232InnerLog : WideLogData :=
  innerPair612Data

set_option maxRecDepth 1000000 in
private theorem leaf5232LocalValidity :
    LeafFacts leaf5232Box leaf5232Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5232Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22905804117/22904823296) }) = true
      norm_num [leaf5232Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5232CertificateValid :
    WideCertificateValid leaf5232Box leaf5232Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk238ValidityFacts chi285ValidityFacts
    leaf5232LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5232CoverageChecked :
    coverageCheck (innerAD leaf5232Box) leaf5232InnerLog = true := by
  rfl'

private theorem leaf5232InnerLogValid :
    leaf5232InnerLog.Valid 8 (innerAD leaf5232Box) :=
  wideLogDataValid_of_cachedCheck endpoint337PositiveFacts
    endpoint291PositiveFacts.valid leaf5232CoverageChecked

private noncomputable def leaf5232InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (90855/131072) }

set_option maxRecDepth 1000000 in
private theorem leaf5232InputLogOnePlusV_eq :
    leaf5232InputLogOnePlusV = outerEnclosure 24
      (leaf5232Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5232RoundedFacts : LeafRoundedFacts 8
    leaf5232Certificate.logOnePlusV leaf5232InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5232InputLogOnePlusV_eq }

private noncomputable def leaf5232Inputs : Inputs :=
  inputsOfCaches globalInput sk238RoundedInputs
    chi285InputQChi innerPair612Input
    leaf5232InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5232LowerChecked :
    lowerCheck 24 leaf5232Box leaf5232Inputs = true := by
  rfl'

private theorem leaf5232CoversExact : CoversExact 8
    leaf5232Box leaf5232Certificate leaf5232InnerLog leaf5232Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk238RoundedFacts chi285RoundedFacts
    innerPair612RoundedFacts leaf5232RoundedFacts (by rfl)

private theorem leaf5232FlatSound : Sound leaf5232Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5232CertificateValid
    leaf5232InnerLogValid leaf5232CoversExact leaf5232LowerChecked

private noncomputable def leaf5233Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (77/256), chiHi := (39/128) }

private noncomputable def leaf5233Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742485/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714424832) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2345291325/2147483648) }, upper := { exponent := 1, mantissa := (18059/16384) } }, logOuter := sk237LogOuterCertificate, logK := sk237LogKCertificate, logChi := chi286LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431837183/137428849664) } }, logDArg := sk237LogDArgCertificate }

private noncomputable def leaf5233InnerLog : WideLogData :=
  innerPair611Data

set_option maxRecDepth 1000000 in
private theorem leaf5233LocalValidity :
    LeafFacts leaf5233Box leaf5233Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5233Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714424832) }) = true
      norm_num [leaf5233Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5233CertificateValid :
    WideCertificateValid leaf5233Box leaf5233Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk237ValidityFacts chi286ValidityFacts
    leaf5233LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5233CoverageChecked :
    coverageCheck (innerAD leaf5233Box) leaf5233InnerLog = true := by
  rfl'

private theorem leaf5233InnerLogValid :
    leaf5233InnerLog.Valid 8 (innerAD leaf5233Box) :=
  wideLogDataValid_of_cachedCheck endpoint337PositiveFacts
    endpoint80PositiveFacts.valid leaf5233CoverageChecked

private noncomputable def leaf5233InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629445/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5233InputLogOnePlusV_eq :
    leaf5233InputLogOnePlusV = outerEnclosure 24
      (leaf5233Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5233RoundedFacts : LeafRoundedFacts 8
    leaf5233Certificate.logOnePlusV leaf5233InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5233InputLogOnePlusV_eq }

private noncomputable def leaf5233Inputs : Inputs :=
  inputsOfCaches globalInput sk237RoundedInputs
    chi286InputQChi innerPair611Input
    leaf5233InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5233LowerChecked :
    lowerCheck 24 leaf5233Box leaf5233Inputs = true := by
  rfl'

private theorem leaf5233CoversExact : CoversExact 8
    leaf5233Box leaf5233Certificate leaf5233InnerLog leaf5233Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk237RoundedFacts chi286RoundedFacts
    innerPair611RoundedFacts leaf5233RoundedFacts (by rfl)

private theorem leaf5233FlatSound : Sound leaf5233Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5233CertificateValid
    leaf5233InnerLogValid leaf5233CoversExact leaf5233LowerChecked

private noncomputable def leaf5234Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (77/256), chiHi := (39/128) }

private noncomputable def leaf5234Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742487/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9816773193/9816343552) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2350337287/2147483648) }, upper := { exponent := 1, mantissa := (9049/8192) } }, logOuter := sk238LogOuterCertificate, logK := sk238LogKCertificate, logChi := chi286LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (19633116745/19632687104) } }, logDArg := sk238LogDArgCertificate }

private noncomputable def leaf5234InnerLog : WideLogData :=
  innerPair259Data

set_option maxRecDepth 1000000 in
private theorem leaf5234LocalValidity :
    LeafFacts leaf5234Box leaf5234Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5234Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9816773193/9816343552) }) = true
      norm_num [leaf5234Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5234CertificateValid :
    WideCertificateValid leaf5234Box leaf5234Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk238ValidityFacts chi286ValidityFacts
    leaf5234LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5234CoverageChecked :
    coverageCheck (innerAD leaf5234Box) leaf5234InnerLog = true := by
  rfl'

private theorem leaf5234InnerLogValid :
    leaf5234InnerLog.Valid 8 (innerAD leaf5234Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint80PositiveFacts.valid leaf5234CoverageChecked

private noncomputable def leaf5234InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453681/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf5234InputLogOnePlusV_eq :
    leaf5234InputLogOnePlusV = outerEnclosure 24
      (leaf5234Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5234RoundedFacts : LeafRoundedFacts 8
    leaf5234Certificate.logOnePlusV leaf5234InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5234InputLogOnePlusV_eq }

private noncomputable def leaf5234Inputs : Inputs :=
  inputsOfCaches globalInput sk238RoundedInputs
    chi286InputQChi innerPair259Input
    leaf5234InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5234LowerChecked :
    lowerCheck 24 leaf5234Box leaf5234Inputs = true := by
  rfl'

private theorem leaf5234CoversExact : CoversExact 8
    leaf5234Box leaf5234Certificate leaf5234InnerLog leaf5234Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk238RoundedFacts chi286RoundedFacts
    innerPair259RoundedFacts leaf5234RoundedFacts (by rfl)

private theorem leaf5234FlatSound : Sound leaf5234Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5234CertificateValid
    leaf5234InnerLogValid leaf5234CoversExact leaf5234LowerChecked

private noncomputable def leaf5235Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (19/64), chiHi := (77/256) }

private noncomputable def leaf5235Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742487/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714450176) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2338738123/2147483648) }, upper := { exponent := 1, mantissa := (36019/32768) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi285LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431862527/137428900352) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf5235InnerLog : WideLogData :=
  innerPair612Data

set_option maxRecDepth 1000000 in
private theorem leaf5235LocalValidity :
    LeafFacts leaf5235Box leaf5235Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5235Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714450176) }) = true
      norm_num [leaf5235Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5235CertificateValid :
    WideCertificateValid leaf5235Box leaf5235Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi285ValidityFacts
    leaf5235LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5235CoverageChecked :
    coverageCheck (innerAD leaf5235Box) leaf5235InnerLog = true := by
  rfl'

private theorem leaf5235InnerLogValid :
    leaf5235InnerLog.Valid 8 (innerAD leaf5235Box) :=
  wideLogDataValid_of_cachedCheck endpoint337PositiveFacts
    endpoint291PositiveFacts.valid leaf5235CoverageChecked

private noncomputable def leaf5235InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814721/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5235InputLogOnePlusV_eq :
    leaf5235InputLogOnePlusV = outerEnclosure 24
      (leaf5235Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5235RoundedFacts : LeafRoundedFacts 8
    leaf5235Certificate.logOnePlusV leaf5235InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5235InputLogOnePlusV_eq }

private noncomputable def leaf5235Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi285InputQChi innerPair612Input
    leaf5235InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5235LowerChecked :
    lowerCheck 24 leaf5235Box leaf5235Inputs = true := by
  rfl'

private theorem leaf5235CoversExact : CoversExact 8
    leaf5235Box leaf5235Certificate leaf5235InnerLog leaf5235Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi285RoundedFacts
    innerPair612RoundedFacts leaf5235RoundedFacts (by rfl)

private theorem leaf5235FlatSound : Sound leaf5235Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5235CertificateValid
    leaf5235InnerLogValid leaf5235CoversExact leaf5235LowerChecked

private noncomputable def leaf5236Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (19/64), chiHi := (77/256) }

private noncomputable def leaf5236Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742489/1073741824) }, vSqrt := { lower := (65527/65536), upper := (68717412351/68714430464) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2343718553/2147483648) }, upper := { exponent := 1, mantissa := (141/128) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi285LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (137431842815/137428860928) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf5236InnerLog : WideLogData :=
  innerPair612Data

set_option maxRecDepth 1000000 in
private theorem leaf5236LocalValidity :
    LeafFacts leaf5236Box leaf5236Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5236Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (68717412351/68714430464) }) = true
      norm_num [leaf5236Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5236CertificateValid :
    WideCertificateValid leaf5236Box leaf5236Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi285ValidityFacts
    leaf5236LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5236CoverageChecked :
    coverageCheck (innerAD leaf5236Box) leaf5236InnerLog = true := by
  rfl'

private theorem leaf5236InnerLogValid :
    leaf5236InnerLog.Valid 8 (innerAD leaf5236Box) :=
  wideLogDataValid_of_cachedCheck endpoint337PositiveFacts
    endpoint291PositiveFacts.valid leaf5236CoverageChecked

private noncomputable def leaf5236InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629445/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5236InputLogOnePlusV_eq :
    leaf5236InputLogOnePlusV = outerEnclosure 24
      (leaf5236Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5236RoundedFacts : LeafRoundedFacts 8
    leaf5236Certificate.logOnePlusV leaf5236InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5236InputLogOnePlusV_eq }

private noncomputable def leaf5236Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi285InputQChi innerPair612Input
    leaf5236InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5236LowerChecked :
    lowerCheck 24 leaf5236Box leaf5236Inputs = true := by
  rfl'

private theorem leaf5236CoversExact : CoversExact 8
    leaf5236Box leaf5236Certificate leaf5236InnerLog leaf5236Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi285RoundedFacts
    innerPair612RoundedFacts leaf5236RoundedFacts (by rfl)

private theorem leaf5236FlatSound : Sound leaf5236Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5236CertificateValid
    leaf5236InnerLogValid leaf5236CoversExact leaf5236LowerChecked

private noncomputable def leaf5237Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (77/256), chiHi := (39/128) }

private noncomputable def leaf5237Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742489/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714384896) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2355383249/2147483648) }, upper := { exponent := 1, mantissa := (18137/16384) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi286LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431797247/137428769792) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf5237InnerLog : WideLogData :=
  innerPair259Data

set_option maxRecDepth 1000000 in
private theorem leaf5237LocalValidity :
    LeafFacts leaf5237Box leaf5237Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5237Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714384896) }) = true
      norm_num [leaf5237Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5237CertificateValid :
    WideCertificateValid leaf5237Box leaf5237Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi286ValidityFacts
    leaf5237LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5237CoverageChecked :
    coverageCheck (innerAD leaf5237Box) leaf5237InnerLog = true := by
  rfl'

private theorem leaf5237InnerLogValid :
    leaf5237InnerLog.Valid 8 (innerAD leaf5237Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint80PositiveFacts.valid leaf5237CoverageChecked

private noncomputable def leaf5237InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814725/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5237InputLogOnePlusV_eq :
    leaf5237InputLogOnePlusV = outerEnclosure 24
      (leaf5237Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5237RoundedFacts : LeafRoundedFacts 8
    leaf5237Certificate.logOnePlusV leaf5237InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5237InputLogOnePlusV_eq }

private noncomputable def leaf5237Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi286InputQChi innerPair259Input
    leaf5237InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5237LowerChecked :
    lowerCheck 24 leaf5237Box leaf5237Inputs = true := by
  rfl'

private theorem leaf5237CoversExact : CoversExact 8
    leaf5237Box leaf5237Certificate leaf5237InnerLog leaf5237Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi286RoundedFacts
    innerPair259RoundedFacts leaf5237RoundedFacts (by rfl)

private theorem leaf5237FlatSound : Sound leaf5237Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5237CertificateValid
    leaf5237InnerLogValid leaf5237CoversExact leaf5237LowerChecked

private noncomputable def leaf5238Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (77/256), chiHi := (39/128) }

private noncomputable def leaf5238Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742491/1073741824) }, vSqrt := { lower := (65527/65536), upper := (68717412351/68714364928) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2360429211/2147483648) }, upper := { exponent := 1, mantissa := (71/64) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi286LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (137431777279/137428729856) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf5238InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf5238LocalValidity :
    LeafFacts leaf5238Box leaf5238Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5238Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (68717412351/68714364928) }) = true
      norm_num [leaf5238Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5238CertificateValid :
    WideCertificateValid leaf5238Box leaf5238Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi286ValidityFacts
    leaf5238LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5238CoverageChecked :
    coverageCheck (innerAD leaf5238Box) leaf5238InnerLog = true := by
  rfl'

private theorem leaf5238InnerLogValid :
    leaf5238InnerLog.Valid 8 (innerAD leaf5238Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf5238CoverageChecked

private noncomputable def leaf5238InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629453/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5238InputLogOnePlusV_eq :
    leaf5238InputLogOnePlusV = outerEnclosure 24
      (leaf5238Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5238RoundedFacts : LeafRoundedFacts 8
    leaf5238Certificate.logOnePlusV leaf5238InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5238InputLogOnePlusV_eq }

private noncomputable def leaf5238Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi286InputQChi innerPair256Input
    leaf5238InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5238LowerChecked :
    lowerCheck 24 leaf5238Box leaf5238Inputs = true := by
  rfl'

private theorem leaf5238CoversExact : CoversExact 8
    leaf5238Box leaf5238Certificate leaf5238InnerLog leaf5238Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi286RoundedFacts
    innerPair256RoundedFacts leaf5238RoundedFacts (by rfl)

private theorem leaf5238FlatSound : Sound leaf5238Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5238CertificateValid
    leaf5238InnerLogValid leaf5238CoversExact leaf5238LowerChecked

private noncomputable def leaf5239Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (39/128), chiHi := (79/256) }

private noncomputable def leaf5239Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742487/1073741824) }, vSqrt := { lower := (8191/8192), upper := (1090752577/1090704128) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2361805387/2147483648) }, upper := { exponent := 1, mantissa := (36371/32768) } }, logOuter := sk237LogOuterCertificate, logK := sk237LogKCertificate, logChi := chi287LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (2181456705/2181408256) } }, logDArg := sk237LogDArgCertificate }

private noncomputable def leaf5239InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf5239LocalValidity :
    LeafFacts leaf5239Box leaf5239Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5239Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (1090752577/1090704128) }) = true
      norm_num [leaf5239Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5239CertificateValid :
    WideCertificateValid leaf5239Box leaf5239Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk237ValidityFacts chi287ValidityFacts
    leaf5239LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5239CoverageChecked :
    coverageCheck (innerAD leaf5239Box) leaf5239InnerLog = true := by
  rfl'

private theorem leaf5239InnerLogValid :
    leaf5239InnerLog.Valid 8 (innerAD leaf5239Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf5239CoverageChecked

private noncomputable def leaf5239InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629453/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5239InputLogOnePlusV_eq :
    leaf5239InputLogOnePlusV = outerEnclosure 24
      (leaf5239Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5239RoundedFacts : LeafRoundedFacts 8
    leaf5239Certificate.logOnePlusV leaf5239InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5239InputLogOnePlusV_eq }

private noncomputable def leaf5239Inputs : Inputs :=
  inputsOfCaches globalInput sk237RoundedInputs
    chi287InputQChi innerPair256Input
    leaf5239InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5239LowerChecked :
    lowerCheck 24 leaf5239Box leaf5239Inputs = true := by
  rfl'

private theorem leaf5239CoversExact : CoversExact 8
    leaf5239Box leaf5239Certificate leaf5239InnerLog leaf5239Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk237RoundedFacts chi287RoundedFacts
    innerPair256RoundedFacts leaf5239RoundedFacts (by rfl)

private theorem leaf5239FlatSound : Sound leaf5239Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5239CertificateValid
    leaf5239InnerLogValid leaf5239CoversExact leaf5239LowerChecked

private noncomputable def leaf5240Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (39/128), chiHi := (79/256) }

private noncomputable def leaf5240Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742489/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714339840) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2366916881/2147483648) }, upper := { exponent := 1, mantissa := (18225/16384) } }, logOuter := sk238LogOuterCertificate, logK := sk238LogKCertificate, logChi := chi287LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431752191/137428679680) } }, logDArg := sk238LogDArgCertificate }

private noncomputable def leaf5240InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf5240LocalValidity :
    LeafFacts leaf5240Box leaf5240Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5240Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714339840) }) = true
      norm_num [leaf5240Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5240CertificateValid :
    WideCertificateValid leaf5240Box leaf5240Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk238ValidityFacts chi287ValidityFacts
    leaf5240LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5240CoverageChecked :
    coverageCheck (innerAD leaf5240Box) leaf5240InnerLog = true := by
  rfl'

private theorem leaf5240InnerLogValid :
    leaf5240InnerLog.Valid 8 (innerAD leaf5240Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf5240CoverageChecked

private noncomputable def leaf5240InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726841/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf5240InputLogOnePlusV_eq :
    leaf5240InputLogOnePlusV = outerEnclosure 24
      (leaf5240Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5240RoundedFacts : LeafRoundedFacts 8
    leaf5240Certificate.logOnePlusV leaf5240InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5240InputLogOnePlusV_eq }

private noncomputable def leaf5240Inputs : Inputs :=
  inputsOfCaches globalInput sk238RoundedInputs
    chi287InputQChi innerPair256Input
    leaf5240InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5240LowerChecked :
    lowerCheck 24 leaf5240Box leaf5240Inputs = true := by
  rfl'

private theorem leaf5240CoversExact : CoversExact 8
    leaf5240Box leaf5240Certificate leaf5240InnerLog leaf5240Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk238RoundedFacts chi287RoundedFacts
    innerPair256RoundedFacts leaf5240RoundedFacts (by rfl)

private theorem leaf5240FlatSound : Sound leaf5240Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5240CertificateValid
    leaf5240InnerLogValid leaf5240CoversExact leaf5240LowerChecked

private noncomputable def leaf5241Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (79/256), chiHi := (5/16) }

private noncomputable def leaf5241Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742489/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714295296) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2378319449/2147483648) }, upper := { exponent := 1, mantissa := (2289/2048) } }, logOuter := sk237LogOuterCertificate, logK := sk237LogKCertificate, logChi := chi288LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431707647/137428590592) } }, logDArg := sk237LogDArgCertificate }

private noncomputable def leaf5241InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf5241LocalValidity :
    LeafFacts leaf5241Box leaf5241Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5241Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714295296) }) = true
      norm_num [leaf5241Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5241CertificateValid :
    WideCertificateValid leaf5241Box leaf5241Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk237ValidityFacts chi288ValidityFacts
    leaf5241LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5241CoverageChecked :
    coverageCheck (innerAD leaf5241Box) leaf5241InnerLog = true := by
  rfl'

private theorem leaf5241InnerLogValid :
    leaf5241InnerLog.Valid 8 (innerAD leaf5241Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf5241CoverageChecked

private noncomputable def leaf5241InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629461/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5241InputLogOnePlusV_eq :
    leaf5241InputLogOnePlusV = outerEnclosure 24
      (leaf5241Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5241RoundedFacts : LeafRoundedFacts 8
    leaf5241Certificate.logOnePlusV leaf5241InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5241InputLogOnePlusV_eq }

private noncomputable def leaf5241Inputs : Inputs :=
  inputsOfCaches globalInput sk237RoundedInputs
    chi288InputQChi innerPair256Input
    leaf5241InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5241LowerChecked :
    lowerCheck 24 leaf5241Box leaf5241Inputs = true := by
  rfl'

private theorem leaf5241CoversExact : CoversExact 8
    leaf5241Box leaf5241Certificate leaf5241InnerLog leaf5241Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk237RoundedFacts chi288RoundedFacts
    innerPair256RoundedFacts leaf5241RoundedFacts (by rfl)

private theorem leaf5241FlatSound : Sound leaf5241Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5241CertificateValid
    leaf5241InnerLogValid leaf5241CoversExact leaf5241LowerChecked

private noncomputable def leaf5242Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (79/256), chiHi := (5/16) }

private noncomputable def leaf5242Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742491/1073741824) }, vSqrt := { lower := (8191/8192), upper := (7635268039/7634919424) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2383496475/2147483648) }, upper := { exponent := 1, mantissa := (1147/1024) } }, logOuter := sk238LogOuterCertificate, logK := sk238LogKCertificate, logChi := chi288LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (15270187463/15269838848) } }, logDArg := sk238LogDArgCertificate }

private noncomputable def leaf5242InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf5242LocalValidity :
    LeafFacts leaf5242Box leaf5242Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5242Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (7635268039/7634919424) }) = true
      norm_num [leaf5242Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5242CertificateValid :
    WideCertificateValid leaf5242Box leaf5242Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk238ValidityFacts chi288ValidityFacts
    leaf5242LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5242CoverageChecked :
    coverageCheck (innerAD leaf5242Box) leaf5242InnerLog = true := by
  rfl'

private theorem leaf5242InnerLogValid :
    leaf5242InnerLog.Valid 8 (innerAD leaf5242Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf5242CoverageChecked

private noncomputable def leaf5242InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453683/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf5242InputLogOnePlusV_eq :
    leaf5242InputLogOnePlusV = outerEnclosure 24
      (leaf5242Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5242RoundedFacts : LeafRoundedFacts 8
    leaf5242Certificate.logOnePlusV leaf5242InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5242InputLogOnePlusV_eq }

private noncomputable def leaf5242Inputs : Inputs :=
  inputsOfCaches globalInput sk238RoundedInputs
    chi288InputQChi innerPair256Input
    leaf5242InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5242LowerChecked :
    lowerCheck 24 leaf5242Box leaf5242Inputs = true := by
  rfl'

private theorem leaf5242CoversExact : CoversExact 8
    leaf5242Box leaf5242Certificate leaf5242InnerLog leaf5242Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk238RoundedFacts chi288RoundedFacts
    innerPair256RoundedFacts leaf5242RoundedFacts (by rfl)

private theorem leaf5242FlatSound : Sound leaf5242Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5242CertificateValid
    leaf5242InnerLogValid leaf5242CoversExact leaf5242LowerChecked

private noncomputable def leaf5243Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (39/128), chiHi := (79/256) }

private noncomputable def leaf5243Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742491/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714319616) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2372028375/2147483648) }, upper := { exponent := 1, mantissa := (36529/32768) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi287LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431731967/137428639232) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf5243InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf5243LocalValidity :
    LeafFacts leaf5243Box leaf5243Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5243Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714319616) }) = true
      norm_num [leaf5243Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5243CertificateValid :
    WideCertificateValid leaf5243Box leaf5243Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi287ValidityFacts
    leaf5243LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5243CoverageChecked :
    coverageCheck (innerAD leaf5243Box) leaf5243InnerLog = true := by
  rfl'

private theorem leaf5243InnerLogValid :
    leaf5243InnerLog.Valid 8 (innerAD leaf5243Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf5243CoverageChecked

private noncomputable def leaf5243InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814729/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5243InputLogOnePlusV_eq :
    leaf5243InputLogOnePlusV = outerEnclosure 24
      (leaf5243Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5243RoundedFacts : LeafRoundedFacts 8
    leaf5243Certificate.logOnePlusV leaf5243InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5243InputLogOnePlusV_eq }

private noncomputable def leaf5243Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi287InputQChi innerPair256Input
    leaf5243InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5243LowerChecked :
    lowerCheck 24 leaf5243Box leaf5243Inputs = true := by
  rfl'

private theorem leaf5243CoversExact : CoversExact 8
    leaf5243Box leaf5243Certificate leaf5243InnerLog leaf5243Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi287RoundedFacts
    innerPair256RoundedFacts leaf5243RoundedFacts (by rfl)

private theorem leaf5243FlatSound : Sound leaf5243Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5243CertificateValid
    leaf5243InnerLogValid leaf5243CoversExact leaf5243LowerChecked

private noncomputable def leaf5244Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (39/128), chiHi := (79/256) }

private noncomputable def leaf5244Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742493/1073741824) }, vSqrt := { lower := (65527/65536), upper := (22905804117/22904766464) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2377139869/2147483648) }, upper := { exponent := 1, mantissa := (143/128) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi287LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (45810570581/45809532928) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf5244InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf5244LocalValidity :
    LeafFacts leaf5244Box leaf5244Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5244Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (22905804117/22904766464) }) = true
      norm_num [leaf5244Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5244CertificateValid :
    WideCertificateValid leaf5244Box leaf5244Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi287ValidityFacts
    leaf5244LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5244CoverageChecked :
    coverageCheck (innerAD leaf5244Box) leaf5244InnerLog = true := by
  rfl'

private theorem leaf5244InnerLogValid :
    leaf5244InnerLog.Valid 8 (innerAD leaf5244Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf5244CoverageChecked

private noncomputable def leaf5244InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629461/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5244InputLogOnePlusV_eq :
    leaf5244InputLogOnePlusV = outerEnclosure 24
      (leaf5244Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5244RoundedFacts : LeafRoundedFacts 8
    leaf5244Certificate.logOnePlusV leaf5244InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5244InputLogOnePlusV_eq }

private noncomputable def leaf5244Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi287InputQChi innerPair256Input
    leaf5244InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5244LowerChecked :
    lowerCheck 24 leaf5244Box leaf5244Inputs = true := by
  rfl'

private theorem leaf5244CoversExact : CoversExact 8
    leaf5244Box leaf5244Certificate leaf5244InnerLog leaf5244Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi287RoundedFacts
    innerPair256RoundedFacts leaf5244RoundedFacts (by rfl)

private theorem leaf5244FlatSound : Sound leaf5244Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5244CertificateValid
    leaf5244InnerLogValid leaf5244CoversExact leaf5244LowerChecked

private noncomputable def leaf5245Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (79/256), chiHi := (5/16) }

private noncomputable def leaf5245Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742493/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9816773193/9816322048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2388673501/2147483648) }, upper := { exponent := 1, mantissa := (2299/2048) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi288LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (19633095241/19632644096) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf5245InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf5245LocalValidity :
    LeafFacts leaf5245Box leaf5245Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5245Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9816773193/9816322048) }) = true
      norm_num [leaf5245Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5245CertificateValid :
    WideCertificateValid leaf5245Box leaf5245Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi288ValidityFacts
    leaf5245LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5245CoverageChecked :
    coverageCheck (innerAD leaf5245Box) leaf5245InnerLog = true := by
  rfl'

private theorem leaf5245InnerLogValid :
    leaf5245InnerLog.Valid 8 (innerAD leaf5245Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf5245CoverageChecked

private noncomputable def leaf5245InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814733/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5245InputLogOnePlusV_eq :
    leaf5245InputLogOnePlusV = outerEnclosure 24
      (leaf5245Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5245RoundedFacts : LeafRoundedFacts 8
    leaf5245Certificate.logOnePlusV leaf5245InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5245InputLogOnePlusV_eq }

private noncomputable def leaf5245Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi288InputQChi innerPair256Input
    leaf5245InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5245LowerChecked :
    lowerCheck 24 leaf5245Box leaf5245Inputs = true := by
  rfl'

private theorem leaf5245CoversExact : CoversExact 8
    leaf5245Box leaf5245Certificate leaf5245InnerLog leaf5245Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi288RoundedFacts
    innerPair256RoundedFacts leaf5245RoundedFacts (by rfl)

private theorem leaf5245FlatSound : Sound leaf5245Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5245CertificateValid
    leaf5245InnerLogValid leaf5245CoversExact leaf5245LowerChecked

private noncomputable def leaf5246Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (79/256), chiHi := (5/16) }

private noncomputable def leaf5246Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742495/1073741824) }, vSqrt := { lower := (65527/65536), upper := (68717412351/68714233856) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2393850527/2147483648) }, upper := { exponent := 1, mantissa := (9/8) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi288LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (137431646207/137428467712) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf5246InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf5246LocalValidity :
    LeafFacts leaf5246Box leaf5246Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5246Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (68717412351/68714233856) }) = true
      norm_num [leaf5246Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5246CertificateValid :
    WideCertificateValid leaf5246Box leaf5246Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi288ValidityFacts
    leaf5246LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5246CoverageChecked :
    coverageCheck (innerAD leaf5246Box) leaf5246InnerLog = true := by
  rfl'

private theorem leaf5246InnerLogValid :
    leaf5246InnerLog.Valid 8 (innerAD leaf5246Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf5246CoverageChecked

private noncomputable def leaf5246InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629469/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5246InputLogOnePlusV_eq :
    leaf5246InputLogOnePlusV = outerEnclosure 24
      (leaf5246Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5246RoundedFacts : LeafRoundedFacts 8
    leaf5246Certificate.logOnePlusV leaf5246InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5246InputLogOnePlusV_eq }

private noncomputable def leaf5246Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi288InputQChi innerPair256Input
    leaf5246InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5246LowerChecked :
    lowerCheck 24 leaf5246Box leaf5246Inputs = true := by
  rfl'

private theorem leaf5246CoversExact : CoversExact 8
    leaf5246Box leaf5246Certificate leaf5246InnerLog leaf5246Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi288RoundedFacts
    innerPair256RoundedFacts leaf5246RoundedFacts (by rfl)

private theorem leaf5246FlatSound : Sound leaf5246Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5246CertificateValid
    leaf5246InnerLogValid leaf5246CoversExact leaf5246LowerChecked

private noncomputable def component105Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (9/32), chiHi := (73/256) }

set_option maxRecDepth 1000000 in
private theorem component105Node0_sound : Sound component105Node0Box :=
  sound_of_literal_split component105Node0Box leaf5183Box leaf5184Box
    .k (249/64) (by rfl) (by rfl)
    leaf5183FlatSound leaf5184FlatSound

private noncomputable def component105Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (73/256), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component105Node1_sound : Sound component105Node1Box :=
  sound_of_literal_split component105Node1Box leaf5185Box leaf5186Box
    .k (249/64) (by rfl) (by rfl)
    leaf5185FlatSound leaf5186FlatSound

private noncomputable def component105Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (9/32), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component105Node2_sound : Sound component105Node2Box :=
  sound_of_literal_split component105Node2Box component105Node0Box component105Node1Box
    .chi (73/256) (by rfl) (by rfl)
    component105Node0_sound component105Node1_sound

private noncomputable def component105Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (9/32), chiHi := (73/256) }

set_option maxRecDepth 1000000 in
private theorem component105Node3_sound : Sound component105Node3Box :=
  sound_of_literal_split component105Node3Box leaf5187Box leaf5188Box
    .k (251/64) (by rfl) (by rfl)
    leaf5187FlatSound leaf5188FlatSound

private noncomputable def component105Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (73/256), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component105Node4_sound : Sound component105Node4Box :=
  sound_of_literal_split component105Node4Box leaf5189Box leaf5190Box
    .k (251/64) (by rfl) (by rfl)
    leaf5189FlatSound leaf5190FlatSound

private noncomputable def component105Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (9/32), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component105Node5_sound : Sound component105Node5Box :=
  sound_of_literal_split component105Node5Box component105Node3Box component105Node4Box
    .chi (73/256) (by rfl) (by rfl)
    component105Node3_sound component105Node4_sound

private noncomputable def component105Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (9/32), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component105Node6_sound : Sound component105Node6Box :=
  sound_of_literal_split component105Node6Box component105Node2Box component105Node5Box
    .k (125/32) (by rfl) (by rfl)
    component105Node2_sound component105Node5_sound

private noncomputable def component105Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (37/128), chiHi := (75/256) }

set_option maxRecDepth 1000000 in
private theorem component105Node7_sound : Sound component105Node7Box :=
  sound_of_literal_split component105Node7Box leaf5191Box leaf5192Box
    .k (249/64) (by rfl) (by rfl)
    leaf5191FlatSound leaf5192FlatSound

private noncomputable def component105Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (75/256), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component105Node8_sound : Sound component105Node8Box :=
  sound_of_literal_split component105Node8Box leaf5193Box leaf5194Box
    .k (249/64) (by rfl) (by rfl)
    leaf5193FlatSound leaf5194FlatSound

private noncomputable def component105Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (37/128), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component105Node9_sound : Sound component105Node9Box :=
  sound_of_literal_split component105Node9Box component105Node7Box component105Node8Box
    .chi (75/256) (by rfl) (by rfl)
    component105Node7_sound component105Node8_sound

private noncomputable def component105Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (37/128), chiHi := (75/256) }

set_option maxRecDepth 1000000 in
private theorem component105Node10_sound : Sound component105Node10Box :=
  sound_of_literal_split component105Node10Box leaf5195Box leaf5196Box
    .k (251/64) (by rfl) (by rfl)
    leaf5195FlatSound leaf5196FlatSound

private noncomputable def component105Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (75/256), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component105Node11_sound : Sound component105Node11Box :=
  sound_of_literal_split component105Node11Box leaf5197Box leaf5198Box
    .k (251/64) (by rfl) (by rfl)
    leaf5197FlatSound leaf5198FlatSound

private noncomputable def component105Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (37/128), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component105Node12_sound : Sound component105Node12Box :=
  sound_of_literal_split component105Node12Box component105Node10Box component105Node11Box
    .chi (75/256) (by rfl) (by rfl)
    component105Node10_sound component105Node11_sound

private noncomputable def component105Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (37/128), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component105Node13_sound : Sound component105Node13Box :=
  sound_of_literal_split component105Node13Box component105Node9Box component105Node12Box
    .k (125/32) (by rfl) (by rfl)
    component105Node9_sound component105Node12_sound

private noncomputable def component105Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (9/32), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component105Node14_sound : Sound component105Node14Box :=
  sound_of_literal_split component105Node14Box component105Node6Box component105Node13Box
    .chi (37/128) (by rfl) (by rfl)
    component105Node6_sound component105Node13_sound

private noncomputable def component105Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (9/32), chiHi := (73/256) }

set_option maxRecDepth 1000000 in
private theorem component105Node15_sound : Sound component105Node15Box :=
  sound_of_literal_split component105Node15Box leaf5199Box leaf5200Box
    .k (253/64) (by rfl) (by rfl)
    leaf5199FlatSound leaf5200FlatSound

private noncomputable def component105Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (73/256), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component105Node16_sound : Sound component105Node16Box :=
  sound_of_literal_split component105Node16Box leaf5201Box leaf5202Box
    .k (253/64) (by rfl) (by rfl)
    leaf5201FlatSound leaf5202FlatSound

private noncomputable def component105Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (9/32), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component105Node17_sound : Sound component105Node17Box :=
  sound_of_literal_split component105Node17Box component105Node15Box component105Node16Box
    .chi (73/256) (by rfl) (by rfl)
    component105Node15_sound component105Node16_sound

private noncomputable def component105Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (9/32), chiHi := (73/256) }

set_option maxRecDepth 1000000 in
private theorem component105Node18_sound : Sound component105Node18Box :=
  sound_of_literal_split component105Node18Box leaf5203Box leaf5204Box
    .k (255/64) (by rfl) (by rfl)
    leaf5203FlatSound leaf5204FlatSound

private noncomputable def component105Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (73/256), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component105Node19_sound : Sound component105Node19Box :=
  sound_of_literal_split component105Node19Box leaf5205Box leaf5206Box
    .k (255/64) (by rfl) (by rfl)
    leaf5205FlatSound leaf5206FlatSound

private noncomputable def component105Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (9/32), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component105Node20_sound : Sound component105Node20Box :=
  sound_of_literal_split component105Node20Box component105Node18Box component105Node19Box
    .chi (73/256) (by rfl) (by rfl)
    component105Node18_sound component105Node19_sound

private noncomputable def component105Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (9/32), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component105Node21_sound : Sound component105Node21Box :=
  sound_of_literal_split component105Node21Box component105Node17Box component105Node20Box
    .k (127/32) (by rfl) (by rfl)
    component105Node17_sound component105Node20_sound

private noncomputable def component105Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (37/128), chiHi := (75/256) }

set_option maxRecDepth 1000000 in
private theorem component105Node22_sound : Sound component105Node22Box :=
  sound_of_literal_split component105Node22Box leaf5207Box leaf5208Box
    .k (253/64) (by rfl) (by rfl)
    leaf5207FlatSound leaf5208FlatSound

private noncomputable def component105Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (75/256), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component105Node23_sound : Sound component105Node23Box :=
  sound_of_literal_split component105Node23Box leaf5209Box leaf5210Box
    .k (253/64) (by rfl) (by rfl)
    leaf5209FlatSound leaf5210FlatSound

private noncomputable def component105Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (37/128), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component105Node24_sound : Sound component105Node24Box :=
  sound_of_literal_split component105Node24Box component105Node22Box component105Node23Box
    .chi (75/256) (by rfl) (by rfl)
    component105Node22_sound component105Node23_sound

private noncomputable def component105Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (37/128), chiHi := (75/256) }

set_option maxRecDepth 1000000 in
private theorem component105Node25_sound : Sound component105Node25Box :=
  sound_of_literal_split component105Node25Box leaf5211Box leaf5212Box
    .k (255/64) (by rfl) (by rfl)
    leaf5211FlatSound leaf5212FlatSound

private noncomputable def component105Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (75/256), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component105Node26_sound : Sound component105Node26Box :=
  sound_of_literal_split component105Node26Box leaf5213Box leaf5214Box
    .k (255/64) (by rfl) (by rfl)
    leaf5213FlatSound leaf5214FlatSound

private noncomputable def component105Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (37/128), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component105Node27_sound : Sound component105Node27Box :=
  sound_of_literal_split component105Node27Box component105Node25Box component105Node26Box
    .chi (75/256) (by rfl) (by rfl)
    component105Node25_sound component105Node26_sound

private noncomputable def component105Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (37/128), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component105Node28_sound : Sound component105Node28Box :=
  sound_of_literal_split component105Node28Box component105Node24Box component105Node27Box
    .k (127/32) (by rfl) (by rfl)
    component105Node24_sound component105Node27_sound

private noncomputable def component105Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (9/32), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component105Node29_sound : Sound component105Node29Box :=
  sound_of_literal_split component105Node29Box component105Node21Box component105Node28Box
    .chi (37/128) (by rfl) (by rfl)
    component105Node21_sound component105Node28_sound

private noncomputable def component105Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (9/32), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component105Node30_sound : Sound component105Node30Box :=
  sound_of_literal_split component105Node30Box component105Node14Box component105Node29Box
    .k (63/16) (by rfl) (by rfl)
    component105Node14_sound component105Node29_sound

private noncomputable def component105Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (19/64), chiHi := (77/256) }

set_option maxRecDepth 1000000 in
private theorem component105Node31_sound : Sound component105Node31Box :=
  sound_of_literal_split component105Node31Box leaf5215Box leaf5216Box
    .k (249/64) (by rfl) (by rfl)
    leaf5215FlatSound leaf5216FlatSound

private noncomputable def component105Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (77/256), chiHi := (39/128) }

set_option maxRecDepth 1000000 in
private theorem component105Node32_sound : Sound component105Node32Box :=
  sound_of_literal_split component105Node32Box leaf5217Box leaf5218Box
    .k (249/64) (by rfl) (by rfl)
    leaf5217FlatSound leaf5218FlatSound

private noncomputable def component105Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (19/64), chiHi := (39/128) }

set_option maxRecDepth 1000000 in
private theorem component105Node33_sound : Sound component105Node33Box :=
  sound_of_literal_split component105Node33Box component105Node31Box component105Node32Box
    .chi (77/256) (by rfl) (by rfl)
    component105Node31_sound component105Node32_sound

private noncomputable def component105Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (19/64), chiHi := (77/256) }

set_option maxRecDepth 1000000 in
private theorem component105Node34_sound : Sound component105Node34Box :=
  sound_of_literal_split component105Node34Box leaf5219Box leaf5220Box
    .k (251/64) (by rfl) (by rfl)
    leaf5219FlatSound leaf5220FlatSound

private noncomputable def component105Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (77/256), chiHi := (39/128) }

set_option maxRecDepth 1000000 in
private theorem component105Node35_sound : Sound component105Node35Box :=
  sound_of_literal_split component105Node35Box leaf5221Box leaf5222Box
    .k (251/64) (by rfl) (by rfl)
    leaf5221FlatSound leaf5222FlatSound

private noncomputable def component105Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (19/64), chiHi := (39/128) }

set_option maxRecDepth 1000000 in
private theorem component105Node36_sound : Sound component105Node36Box :=
  sound_of_literal_split component105Node36Box component105Node34Box component105Node35Box
    .chi (77/256) (by rfl) (by rfl)
    component105Node34_sound component105Node35_sound

private noncomputable def component105Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (19/64), chiHi := (39/128) }

set_option maxRecDepth 1000000 in
private theorem component105Node37_sound : Sound component105Node37Box :=
  sound_of_literal_split component105Node37Box component105Node33Box component105Node36Box
    .k (125/32) (by rfl) (by rfl)
    component105Node33_sound component105Node36_sound

private noncomputable def component105Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (39/128), chiHi := (79/256) }

set_option maxRecDepth 1000000 in
private theorem component105Node38_sound : Sound component105Node38Box :=
  sound_of_literal_split component105Node38Box leaf5223Box leaf5224Box
    .k (249/64) (by rfl) (by rfl)
    leaf5223FlatSound leaf5224FlatSound

private noncomputable def component105Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (79/256), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component105Node39_sound : Sound component105Node39Box :=
  sound_of_literal_split component105Node39Box leaf5225Box leaf5226Box
    .k (249/64) (by rfl) (by rfl)
    leaf5225FlatSound leaf5226FlatSound

private noncomputable def component105Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (39/128), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component105Node40_sound : Sound component105Node40Box :=
  sound_of_literal_split component105Node40Box component105Node38Box component105Node39Box
    .chi (79/256) (by rfl) (by rfl)
    component105Node38_sound component105Node39_sound

private noncomputable def component105Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (39/128), chiHi := (79/256) }

set_option maxRecDepth 1000000 in
private theorem component105Node41_sound : Sound component105Node41Box :=
  sound_of_literal_split component105Node41Box leaf5227Box leaf5228Box
    .k (251/64) (by rfl) (by rfl)
    leaf5227FlatSound leaf5228FlatSound

private noncomputable def component105Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (79/256), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component105Node42_sound : Sound component105Node42Box :=
  sound_of_literal_split component105Node42Box leaf5229Box leaf5230Box
    .k (251/64) (by rfl) (by rfl)
    leaf5229FlatSound leaf5230FlatSound

private noncomputable def component105Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (39/128), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component105Node43_sound : Sound component105Node43Box :=
  sound_of_literal_split component105Node43Box component105Node41Box component105Node42Box
    .chi (79/256) (by rfl) (by rfl)
    component105Node41_sound component105Node42_sound

private noncomputable def component105Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (39/128), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component105Node44_sound : Sound component105Node44Box :=
  sound_of_literal_split component105Node44Box component105Node40Box component105Node43Box
    .k (125/32) (by rfl) (by rfl)
    component105Node40_sound component105Node43_sound

private noncomputable def component105Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (19/64), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component105Node45_sound : Sound component105Node45Box :=
  sound_of_literal_split component105Node45Box component105Node37Box component105Node44Box
    .chi (39/128) (by rfl) (by rfl)
    component105Node37_sound component105Node44_sound

private noncomputable def component105Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (19/64), chiHi := (77/256) }

set_option maxRecDepth 1000000 in
private theorem component105Node46_sound : Sound component105Node46Box :=
  sound_of_literal_split component105Node46Box leaf5231Box leaf5232Box
    .k (253/64) (by rfl) (by rfl)
    leaf5231FlatSound leaf5232FlatSound

private noncomputable def component105Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (77/256), chiHi := (39/128) }

set_option maxRecDepth 1000000 in
private theorem component105Node47_sound : Sound component105Node47Box :=
  sound_of_literal_split component105Node47Box leaf5233Box leaf5234Box
    .k (253/64) (by rfl) (by rfl)
    leaf5233FlatSound leaf5234FlatSound

private noncomputable def component105Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (19/64), chiHi := (39/128) }

set_option maxRecDepth 1000000 in
private theorem component105Node48_sound : Sound component105Node48Box :=
  sound_of_literal_split component105Node48Box component105Node46Box component105Node47Box
    .chi (77/256) (by rfl) (by rfl)
    component105Node46_sound component105Node47_sound

private noncomputable def component105Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (19/64), chiHi := (77/256) }

set_option maxRecDepth 1000000 in
private theorem component105Node49_sound : Sound component105Node49Box :=
  sound_of_literal_split component105Node49Box leaf5235Box leaf5236Box
    .k (255/64) (by rfl) (by rfl)
    leaf5235FlatSound leaf5236FlatSound

private noncomputable def component105Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (77/256), chiHi := (39/128) }

set_option maxRecDepth 1000000 in
private theorem component105Node50_sound : Sound component105Node50Box :=
  sound_of_literal_split component105Node50Box leaf5237Box leaf5238Box
    .k (255/64) (by rfl) (by rfl)
    leaf5237FlatSound leaf5238FlatSound

private noncomputable def component105Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (19/64), chiHi := (39/128) }

set_option maxRecDepth 1000000 in
private theorem component105Node51_sound : Sound component105Node51Box :=
  sound_of_literal_split component105Node51Box component105Node49Box component105Node50Box
    .chi (77/256) (by rfl) (by rfl)
    component105Node49_sound component105Node50_sound

private noncomputable def component105Node52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (19/64), chiHi := (39/128) }

set_option maxRecDepth 1000000 in
private theorem component105Node52_sound : Sound component105Node52Box :=
  sound_of_literal_split component105Node52Box component105Node48Box component105Node51Box
    .k (127/32) (by rfl) (by rfl)
    component105Node48_sound component105Node51_sound

private noncomputable def component105Node53Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (39/128), chiHi := (79/256) }

set_option maxRecDepth 1000000 in
private theorem component105Node53_sound : Sound component105Node53Box :=
  sound_of_literal_split component105Node53Box leaf5239Box leaf5240Box
    .k (253/64) (by rfl) (by rfl)
    leaf5239FlatSound leaf5240FlatSound

private noncomputable def component105Node54Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (79/256), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component105Node54_sound : Sound component105Node54Box :=
  sound_of_literal_split component105Node54Box leaf5241Box leaf5242Box
    .k (253/64) (by rfl) (by rfl)
    leaf5241FlatSound leaf5242FlatSound

private noncomputable def component105Node55Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (39/128), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component105Node55_sound : Sound component105Node55Box :=
  sound_of_literal_split component105Node55Box component105Node53Box component105Node54Box
    .chi (79/256) (by rfl) (by rfl)
    component105Node53_sound component105Node54_sound

private noncomputable def component105Node56Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (39/128), chiHi := (79/256) }

set_option maxRecDepth 1000000 in
private theorem component105Node56_sound : Sound component105Node56Box :=
  sound_of_literal_split component105Node56Box leaf5243Box leaf5244Box
    .k (255/64) (by rfl) (by rfl)
    leaf5243FlatSound leaf5244FlatSound

private noncomputable def component105Node57Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (79/256), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component105Node57_sound : Sound component105Node57Box :=
  sound_of_literal_split component105Node57Box leaf5245Box leaf5246Box
    .k (255/64) (by rfl) (by rfl)
    leaf5245FlatSound leaf5246FlatSound

private noncomputable def component105Node58Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (39/128), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component105Node58_sound : Sound component105Node58Box :=
  sound_of_literal_split component105Node58Box component105Node56Box component105Node57Box
    .chi (79/256) (by rfl) (by rfl)
    component105Node56_sound component105Node57_sound

private noncomputable def component105Node59Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (39/128), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component105Node59_sound : Sound component105Node59Box :=
  sound_of_literal_split component105Node59Box component105Node55Box component105Node58Box
    .k (127/32) (by rfl) (by rfl)
    component105Node55_sound component105Node58_sound

private noncomputable def component105Node60Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (19/64), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component105Node60_sound : Sound component105Node60Box :=
  sound_of_literal_split component105Node60Box component105Node52Box component105Node59Box
    .chi (39/128) (by rfl) (by rfl)
    component105Node52_sound component105Node59_sound

private noncomputable def component105Node61Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (19/64), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component105Node61_sound : Sound component105Node61Box :=
  sound_of_literal_split component105Node61Box component105Node45Box component105Node60Box
    .k (63/16) (by rfl) (by rfl)
    component105Node45_sound component105Node60_sound

noncomputable def component105Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (9/32), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
theorem component105_sound : Sound component105Box :=
  sound_of_literal_split component105Box component105Node30Box component105Node61Box
    .chi (19/64) (by rfl) (by rfl)
    component105Node30_sound component105Node61_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
