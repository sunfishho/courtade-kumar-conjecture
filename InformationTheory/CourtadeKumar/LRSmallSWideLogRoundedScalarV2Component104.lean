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

private noncomputable def leaf5119Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (241/64), chiLo := (9/32), chiHi := (73/256) }

private noncomputable def leaf5119Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742451/1073741824) }, vSqrt := { lower := (8191/8192), upper := (1090752577/1090713856) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2206101391/2147483648) }, upper := { exponent := 1, mantissa := (33977/32768) } }, logOuter := sk225LogOuterCertificate, logK := sk225LogKCertificate, logChi := chi281LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (2181466433/2181427712) } }, logDArg := sk225LogDArgCertificate }

private noncomputable def leaf5119InnerLog : WideLogData :=
  innerPair327Data

set_option maxRecDepth 1000000 in
private theorem leaf5119LocalValidity :
    LeafFacts leaf5119Box leaf5119Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5119Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (1090752577/1090713856) }) = true
      norm_num [leaf5119Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5119CertificateValid :
    WideCertificateValid leaf5119Box leaf5119Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk225ValidityFacts chi281ValidityFacts
    leaf5119LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5119CoverageChecked :
    coverageCheck (innerAD leaf5119Box) leaf5119InnerLog = true := by
  rfl'

private theorem leaf5119InnerLogValid :
    leaf5119InnerLog.Valid 8 (innerAD leaf5119Box) :=
  wideLogDataValid_of_cachedCheck endpoint87PositiveFacts
    endpoint86PositiveFacts.valid leaf5119CoverageChecked

private noncomputable def leaf5119InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629379/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5119InputLogOnePlusV_eq :
    leaf5119InputLogOnePlusV = outerEnclosure 24
      (leaf5119Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5119RoundedFacts : LeafRoundedFacts 8
    leaf5119Certificate.logOnePlusV leaf5119InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5119InputLogOnePlusV_eq }

private noncomputable def leaf5119Inputs : Inputs :=
  inputsOfCaches globalInput sk225RoundedInputs
    chi281InputQChi innerPair327Input
    leaf5119InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5119LowerChecked :
    lowerCheck 24 leaf5119Box leaf5119Inputs = true := by
  rfl'

private theorem leaf5119CoversExact : CoversExact 8
    leaf5119Box leaf5119Certificate leaf5119InnerLog leaf5119Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk225RoundedFacts chi281RoundedFacts
    innerPair327RoundedFacts leaf5119RoundedFacts (by rfl)

private theorem leaf5119FlatSound : Sound leaf5119Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5119CertificateValid
    leaf5119InnerLogValid leaf5119CoversExact leaf5119LowerChecked

private noncomputable def leaf5120Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (241/64), kHi := (121/32), chiLo := (9/32), chiHi := (73/256) }

private noncomputable def leaf5120Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742453/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714954240) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2210819693/2147483648) }, upper := { exponent := 1, mantissa := (17025/16384) } }, logOuter := sk226LogOuterCertificate, logK := sk226LogKCertificate, logChi := chi281LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432366591/137429908480) } }, logDArg := sk226LogDArgCertificate }

private noncomputable def leaf5120InnerLog : WideLogData :=
  innerPair329Data

set_option maxRecDepth 1000000 in
private theorem leaf5120LocalValidity :
    LeafFacts leaf5120Box leaf5120Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5120Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714954240) }) = true
      norm_num [leaf5120Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5120CertificateValid :
    WideCertificateValid leaf5120Box leaf5120Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk226ValidityFacts chi281ValidityFacts
    leaf5120LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5120CoverageChecked :
    coverageCheck (innerAD leaf5120Box) leaf5120InnerLog = true := by
  rfl'

private theorem leaf5120InnerLogValid :
    leaf5120InnerLog.Valid 8 (innerAD leaf5120Box) :=
  wideLogDataValid_of_cachedCheck endpoint87PositiveFacts
    endpoint284PositiveFacts.valid leaf5120CoverageChecked

private noncomputable def leaf5120InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629381/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5120InputLogOnePlusV_eq :
    leaf5120InputLogOnePlusV = outerEnclosure 24
      (leaf5120Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5120RoundedFacts : LeafRoundedFacts 8
    leaf5120Certificate.logOnePlusV leaf5120InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5120InputLogOnePlusV_eq }

private noncomputable def leaf5120Inputs : Inputs :=
  inputsOfCaches globalInput sk226RoundedInputs
    chi281InputQChi innerPair329Input
    leaf5120InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5120LowerChecked :
    lowerCheck 24 leaf5120Box leaf5120Inputs = true := by
  rfl'

private theorem leaf5120CoversExact : CoversExact 8
    leaf5120Box leaf5120Certificate leaf5120InnerLog leaf5120Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk226RoundedFacts chi281RoundedFacts
    innerPair329RoundedFacts leaf5120RoundedFacts (by rfl)

private theorem leaf5120FlatSound : Sound leaf5120Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5120CertificateValid
    leaf5120InnerLogValid leaf5120CoversExact leaf5120LowerChecked

private noncomputable def leaf5121Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (241/64), chiLo := (73/256), chiHi := (37/128) }

private noncomputable def leaf5121Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742453/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714911232) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2221829069/2147483648) }, upper := { exponent := 1, mantissa := (17109/16384) } }, logOuter := sk225LogOuterCertificate, logK := sk225LogKCertificate, logChi := chi282LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432323583/137429822464) } }, logDArg := sk225LogDArgCertificate }

private noncomputable def leaf5121InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf5121LocalValidity :
    LeafFacts leaf5121Box leaf5121Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5121Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714911232) }) = true
      norm_num [leaf5121Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5121CertificateValid :
    WideCertificateValid leaf5121Box leaf5121Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk225ValidityFacts chi282ValidityFacts
    leaf5121LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5121CoverageChecked :
    coverageCheck (innerAD leaf5121Box) leaf5121InnerLog = true := by
  rfl'

private theorem leaf5121InnerLogValid :
    leaf5121InnerLog.Valid 8 (innerAD leaf5121Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf5121CoverageChecked

private noncomputable def leaf5121InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814693/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5121InputLogOnePlusV_eq :
    leaf5121InputLogOnePlusV = outerEnclosure 24
      (leaf5121Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5121RoundedFacts : LeafRoundedFacts 8
    leaf5121Certificate.logOnePlusV leaf5121InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5121InputLogOnePlusV_eq }

private noncomputable def leaf5121Inputs : Inputs :=
  inputsOfCaches globalInput sk225RoundedInputs
    chi282InputQChi innerPair242Input
    leaf5121InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5121LowerChecked :
    lowerCheck 24 leaf5121Box leaf5121Inputs = true := by
  rfl'

private theorem leaf5121CoversExact : CoversExact 8
    leaf5121Box leaf5121Certificate leaf5121InnerLog leaf5121Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk225RoundedFacts chi282RoundedFacts
    innerPair242RoundedFacts leaf5121RoundedFacts (by rfl)

private theorem leaf5121FlatSound : Sound leaf5121Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5121CertificateValid
    leaf5121InnerLogValid leaf5121CoversExact leaf5121LowerChecked

private noncomputable def leaf5122Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (241/64), kHi := (121/32), chiLo := (73/256), chiHi := (37/128) }

private noncomputable def leaf5122Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742455/1073741824) }, vSqrt := { lower := (8191/8192), upper := (1090752577/1090712576) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2226612903/2147483648) }, upper := { exponent := 1, mantissa := (8573/8192) } }, logOuter := sk226LogOuterCertificate, logK := sk226LogKCertificate, logChi := chi282LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (2181465153/2181425152) } }, logDArg := sk226LogDArgCertificate }

private noncomputable def leaf5122InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf5122LocalValidity :
    LeafFacts leaf5122Box leaf5122Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5122Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (1090752577/1090712576) }) = true
      norm_num [leaf5122Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5122CertificateValid :
    WideCertificateValid leaf5122Box leaf5122Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk226ValidityFacts chi282ValidityFacts
    leaf5122LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5122CoverageChecked :
    coverageCheck (innerAD leaf5122Box) leaf5122InnerLog = true := by
  rfl'

private theorem leaf5122InnerLogValid :
    leaf5122InnerLog.Valid 8 (innerAD leaf5122Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf5122CoverageChecked

private noncomputable def leaf5122InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907347/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5122InputLogOnePlusV_eq :
    leaf5122InputLogOnePlusV = outerEnclosure 24
      (leaf5122Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5122RoundedFacts : LeafRoundedFacts 8
    leaf5122Certificate.logOnePlusV leaf5122InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5122InputLogOnePlusV_eq }

private noncomputable def leaf5122Inputs : Inputs :=
  inputsOfCaches globalInput sk226RoundedInputs
    chi282InputQChi innerPair242Input
    leaf5122InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5122LowerChecked :
    lowerCheck 24 leaf5122Box leaf5122Inputs = true := by
  rfl'

private theorem leaf5122CoversExact : CoversExact 8
    leaf5122Box leaf5122Certificate leaf5122InnerLog leaf5122Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk226RoundedFacts chi282RoundedFacts
    innerPair242RoundedFacts leaf5122RoundedFacts (by rfl)

private theorem leaf5122FlatSound : Sound leaf5122Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5122CertificateValid
    leaf5122InnerLogValid leaf5122CoversExact leaf5122LowerChecked

private noncomputable def leaf5123Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (243/64), chiLo := (9/32), chiHi := (73/256) }

private noncomputable def leaf5123Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742455/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714935552) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2215537995/2147483648) }, upper := { exponent := 1, mantissa := (34123/32768) } }, logOuter := sk227LogOuterCertificate, logK := sk227LogKCertificate, logChi := chi281LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432347903/137429871104) } }, logDArg := sk227LogDArgCertificate }

private noncomputable def leaf5123InnerLog : WideLogData :=
  innerPair248Data

set_option maxRecDepth 1000000 in
private theorem leaf5123LocalValidity :
    LeafFacts leaf5123Box leaf5123Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5123Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714935552) }) = true
      norm_num [leaf5123Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5123CertificateValid :
    WideCertificateValid leaf5123Box leaf5123Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk227ValidityFacts chi281ValidityFacts
    leaf5123LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5123CoverageChecked :
    coverageCheck (innerAD leaf5123Box) leaf5123InnerLog = true := by
  rfl'

private theorem leaf5123InnerLogValid :
    leaf5123InnerLog.Valid 8 (innerAD leaf5123Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint284PositiveFacts.valid leaf5123CoverageChecked

private noncomputable def leaf5123InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629383/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5123InputLogOnePlusV_eq :
    leaf5123InputLogOnePlusV = outerEnclosure 24
      (leaf5123Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5123RoundedFacts : LeafRoundedFacts 8
    leaf5123Certificate.logOnePlusV leaf5123InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5123InputLogOnePlusV_eq }

private noncomputable def leaf5123Inputs : Inputs :=
  inputsOfCaches globalInput sk227RoundedInputs
    chi281InputQChi innerPair248Input
    leaf5123InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5123LowerChecked :
    lowerCheck 24 leaf5123Box leaf5123Inputs = true := by
  rfl'

private theorem leaf5123CoversExact : CoversExact 8
    leaf5123Box leaf5123Certificate leaf5123InnerLog leaf5123Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk227RoundedFacts chi281RoundedFacts
    innerPair248RoundedFacts leaf5123RoundedFacts (by rfl)

private theorem leaf5123FlatSound : Sound leaf5123Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5123CertificateValid
    leaf5123InnerLogValid leaf5123CoversExact leaf5123LowerChecked

private noncomputable def leaf5124Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (243/64), kHi := (61/16), chiLo := (9/32), chiHi := (73/256) }

private noncomputable def leaf5124Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742457/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22905804117/22904972288) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2220256297/2147483648) }, upper := { exponent := 1, mantissa := (8549/8192) } }, logOuter := sk228LogOuterCertificate, logK := sk228LogKCertificate, logChi := chi281LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45810776405/45809944576) } }, logDArg := sk228LogDArgCertificate }

private noncomputable def leaf5124InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf5124LocalValidity :
    LeafFacts leaf5124Box leaf5124Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5124Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22905804117/22904972288) }) = true
      norm_num [leaf5124Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5124CertificateValid :
    WideCertificateValid leaf5124Box leaf5124Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk228ValidityFacts chi281ValidityFacts
    leaf5124LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5124CoverageChecked :
    coverageCheck (innerAD leaf5124Box) leaf5124InnerLog = true := by
  rfl'

private theorem leaf5124InnerLogValid :
    leaf5124InnerLog.Valid 8 (innerAD leaf5124Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf5124CoverageChecked

private noncomputable def leaf5124InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629385/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5124InputLogOnePlusV_eq :
    leaf5124InputLogOnePlusV = outerEnclosure 24
      (leaf5124Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5124RoundedFacts : LeafRoundedFacts 8
    leaf5124Certificate.logOnePlusV leaf5124InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5124InputLogOnePlusV_eq }

private noncomputable def leaf5124Inputs : Inputs :=
  inputsOfCaches globalInput sk228RoundedInputs
    chi281InputQChi innerPair242Input
    leaf5124InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5124LowerChecked :
    lowerCheck 24 leaf5124Box leaf5124Inputs = true := by
  rfl'

private theorem leaf5124CoversExact : CoversExact 8
    leaf5124Box leaf5124Certificate leaf5124InnerLog leaf5124Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk228RoundedFacts chi281RoundedFacts
    innerPair242RoundedFacts leaf5124RoundedFacts (by rfl)

private theorem leaf5124FlatSound : Sound leaf5124Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5124CertificateValid
    leaf5124InnerLogValid leaf5124CoversExact leaf5124LowerChecked

private noncomputable def leaf5125Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (243/64), chiLo := (73/256), chiHi := (37/128) }

private noncomputable def leaf5125Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742457/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714873344) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2231396737/2147483648) }, upper := { exponent := 1, mantissa := (17183/16384) } }, logOuter := sk227LogOuterCertificate, logK := sk227LogKCertificate, logChi := chi282LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432285695/137429746688) } }, logDArg := sk227LogDArgCertificate }

private noncomputable def leaf5125InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf5125LocalValidity :
    LeafFacts leaf5125Box leaf5125Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5125Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714873344) }) = true
      norm_num [leaf5125Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5125CertificateValid :
    WideCertificateValid leaf5125Box leaf5125Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk227ValidityFacts chi282ValidityFacts
    leaf5125LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5125CoverageChecked :
    coverageCheck (innerAD leaf5125Box) leaf5125InnerLog = true := by
  rfl'

private theorem leaf5125InnerLogValid :
    leaf5125InnerLog.Valid 8 (innerAD leaf5125Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf5125CoverageChecked

private noncomputable def leaf5125InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629391/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5125InputLogOnePlusV_eq :
    leaf5125InputLogOnePlusV = outerEnclosure 24
      (leaf5125Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5125RoundedFacts : LeafRoundedFacts 8
    leaf5125Certificate.logOnePlusV leaf5125InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5125InputLogOnePlusV_eq }

private noncomputable def leaf5125Inputs : Inputs :=
  inputsOfCaches globalInput sk227RoundedInputs
    chi282InputQChi innerPair242Input
    leaf5125InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5125LowerChecked :
    lowerCheck 24 leaf5125Box leaf5125Inputs = true := by
  rfl'

private theorem leaf5125CoversExact : CoversExact 8
    leaf5125Box leaf5125Certificate leaf5125InnerLog leaf5125Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk227RoundedFacts chi282RoundedFacts
    innerPair242RoundedFacts leaf5125RoundedFacts (by rfl)

private theorem leaf5125FlatSound : Sound leaf5125Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5125CertificateValid
    leaf5125InnerLogValid leaf5125CoversExact leaf5125LowerChecked

private noncomputable def leaf5126Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (243/64), kHi := (61/16), chiLo := (73/256), chiHi := (37/128) }

private noncomputable def leaf5126Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742459/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714854400) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2236180571/2147483648) }, upper := { exponent := 1, mantissa := (4305/4096) } }, logOuter := sk228LogOuterCertificate, logK := sk228LogKCertificate, logChi := chi282LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432266751/137429708800) } }, logDArg := sk228LogDArgCertificate }

private noncomputable def leaf5126InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf5126LocalValidity :
    LeafFacts leaf5126Box leaf5126Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5126Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714854400) }) = true
      norm_num [leaf5126Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5126CertificateValid :
    WideCertificateValid leaf5126Box leaf5126Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk228ValidityFacts chi282ValidityFacts
    leaf5126LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5126CoverageChecked :
    coverageCheck (innerAD leaf5126Box) leaf5126InnerLog = true := by
  rfl'

private theorem leaf5126InnerLogValid :
    leaf5126InnerLog.Valid 8 (innerAD leaf5126Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf5126CoverageChecked

private noncomputable def leaf5126InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629393/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5126InputLogOnePlusV_eq :
    leaf5126InputLogOnePlusV = outerEnclosure 24
      (leaf5126Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5126RoundedFacts : LeafRoundedFacts 8
    leaf5126Certificate.logOnePlusV leaf5126InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5126InputLogOnePlusV_eq }

private noncomputable def leaf5126Inputs : Inputs :=
  inputsOfCaches globalInput sk228RoundedInputs
    chi282InputQChi innerPair242Input
    leaf5126InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5126LowerChecked :
    lowerCheck 24 leaf5126Box leaf5126Inputs = true := by
  rfl'

private theorem leaf5126CoversExact : CoversExact 8
    leaf5126Box leaf5126Certificate leaf5126InnerLog leaf5126Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk228RoundedFacts chi282RoundedFacts
    innerPair242RoundedFacts leaf5126RoundedFacts (by rfl)

private theorem leaf5126FlatSound : Sound leaf5126Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5126CertificateValid
    leaf5126InnerLogValid leaf5126CoversExact leaf5126LowerChecked

private noncomputable def leaf5127Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (241/64), chiLo := (37/128), chiHi := (75/256) }

private noncomputable def leaf5127Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742455/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714849536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2237556747/2147483648) }, upper := { exponent := 1, mantissa := (34459/32768) } }, logOuter := sk225LogOuterCertificate, logK := sk225LogKCertificate, logChi := chi283LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432261887/137429699072) } }, logDArg := sk225LogDArgCertificate }

private noncomputable def leaf5127InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf5127LocalValidity :
    LeafFacts leaf5127Box leaf5127Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5127Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714849536) }) = true
      norm_num [leaf5127Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5127CertificateValid :
    WideCertificateValid leaf5127Box leaf5127Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk225ValidityFacts chi283ValidityFacts
    leaf5127LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5127CoverageChecked :
    coverageCheck (innerAD leaf5127Box) leaf5127InnerLog = true := by
  rfl'

private theorem leaf5127InnerLogValid :
    leaf5127InnerLog.Valid 8 (innerAD leaf5127Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf5127CoverageChecked

private noncomputable def leaf5127InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814697/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5127InputLogOnePlusV_eq :
    leaf5127InputLogOnePlusV = outerEnclosure 24
      (leaf5127Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5127RoundedFacts : LeafRoundedFacts 8
    leaf5127Certificate.logOnePlusV leaf5127InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5127InputLogOnePlusV_eq }

private noncomputable def leaf5127Inputs : Inputs :=
  inputsOfCaches globalInput sk225RoundedInputs
    chi283InputQChi innerPair242Input
    leaf5127InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5127LowerChecked :
    lowerCheck 24 leaf5127Box leaf5127Inputs = true := by
  rfl'

private theorem leaf5127CoversExact : CoversExact 8
    leaf5127Box leaf5127Certificate leaf5127InnerLog leaf5127Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk225RoundedFacts chi283RoundedFacts
    innerPair242RoundedFacts leaf5127RoundedFacts (by rfl)

private theorem leaf5127FlatSound : Sound leaf5127Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5127CertificateValid
    leaf5127InnerLogValid leaf5127CoversExact leaf5127LowerChecked

private noncomputable def leaf5128Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (241/64), kHi := (121/32), chiLo := (37/128), chiHi := (75/256) }

private noncomputable def leaf5128Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742457/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714830336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2242406113/2147483648) }, upper := { exponent := 1, mantissa := (17267/16384) } }, logOuter := sk226LogOuterCertificate, logK := sk226LogKCertificate, logChi := chi283LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432242687/137429660672) } }, logDArg := sk226LogDArgCertificate }

private noncomputable def leaf5128InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf5128LocalValidity :
    LeafFacts leaf5128Box leaf5128Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5128Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714830336) }) = true
      norm_num [leaf5128Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5128CertificateValid :
    WideCertificateValid leaf5128Box leaf5128Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk226ValidityFacts chi283ValidityFacts
    leaf5128LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5128CoverageChecked :
    coverageCheck (innerAD leaf5128Box) leaf5128InnerLog = true := by
  rfl'

private theorem leaf5128InnerLogValid :
    leaf5128InnerLog.Valid 8 (innerAD leaf5128Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf5128CoverageChecked

private noncomputable def leaf5128InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907349/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5128InputLogOnePlusV_eq :
    leaf5128InputLogOnePlusV = outerEnclosure 24
      (leaf5128Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5128RoundedFacts : LeafRoundedFacts 8
    leaf5128Certificate.logOnePlusV leaf5128InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5128InputLogOnePlusV_eq }

private noncomputable def leaf5128Inputs : Inputs :=
  inputsOfCaches globalInput sk226RoundedInputs
    chi283InputQChi innerPair242Input
    leaf5128InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5128LowerChecked :
    lowerCheck 24 leaf5128Box leaf5128Inputs = true := by
  rfl'

private theorem leaf5128CoversExact : CoversExact 8
    leaf5128Box leaf5128Certificate leaf5128InnerLog leaf5128Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk226RoundedFacts chi283RoundedFacts
    innerPair242RoundedFacts leaf5128RoundedFacts (by rfl)

private theorem leaf5128FlatSound : Sound leaf5128Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5128CertificateValid
    leaf5128InnerLogValid leaf5128CoversExact leaf5128LowerChecked

private noncomputable def leaf5129Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (241/64), chiLo := (75/256), chiHi := (19/64) }

private noncomputable def leaf5129Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742457/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22905804117/22904929280) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2253284425/2147483648) }, upper := { exponent := 1, mantissa := (8675/8192) } }, logOuter := sk225LogOuterCertificate, logK := sk225LogKCertificate, logChi := chi284LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45810733397/45809858560) } }, logDArg := sk225LogDArgCertificate }

private noncomputable def leaf5129InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf5129LocalValidity :
    LeafFacts leaf5129Box leaf5129Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5129Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22905804117/22904929280) }) = true
      norm_num [leaf5129Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5129CertificateValid :
    WideCertificateValid leaf5129Box leaf5129Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk225ValidityFacts chi284ValidityFacts
    leaf5129LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5129CoverageChecked :
    coverageCheck (innerAD leaf5129Box) leaf5129InnerLog = true := by
  rfl'

private theorem leaf5129InnerLogValid :
    leaf5129InnerLog.Valid 8 (innerAD leaf5129Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf5129CoverageChecked

private noncomputable def leaf5129InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629401/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5129InputLogOnePlusV_eq :
    leaf5129InputLogOnePlusV = outerEnclosure 24
      (leaf5129Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5129RoundedFacts : LeafRoundedFacts 8
    leaf5129Certificate.logOnePlusV leaf5129InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5129InputLogOnePlusV_eq }

private noncomputable def leaf5129Inputs : Inputs :=
  inputsOfCaches globalInput sk225RoundedInputs
    chi284InputQChi innerPair242Input
    leaf5129InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5129LowerChecked :
    lowerCheck 24 leaf5129Box leaf5129Inputs = true := by
  rfl'

private theorem leaf5129CoversExact : CoversExact 8
    leaf5129Box leaf5129Certificate leaf5129InnerLog leaf5129Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk225RoundedFacts chi284RoundedFacts
    innerPair242RoundedFacts leaf5129RoundedFacts (by rfl)

private theorem leaf5129FlatSound : Sound leaf5129Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5129CertificateValid
    leaf5129InnerLogValid leaf5129CoversExact leaf5129LowerChecked

private noncomputable def leaf5130Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (241/64), kHi := (121/32), chiLo := (75/256), chiHi := (19/64) }

private noncomputable def leaf5130Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742459/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714768384) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2258199323/2147483648) }, upper := { exponent := 1, mantissa := (4347/4096) } }, logOuter := sk226LogOuterCertificate, logK := sk226LogKCertificate, logChi := chi284LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432180735/137429536768) } }, logDArg := sk226LogDArgCertificate }

private noncomputable def leaf5130InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf5130LocalValidity :
    LeafFacts leaf5130Box leaf5130Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5130Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714768384) }) = true
      norm_num [leaf5130Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5130CertificateValid :
    WideCertificateValid leaf5130Box leaf5130Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk226ValidityFacts chi284ValidityFacts
    leaf5130LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5130CoverageChecked :
    coverageCheck (innerAD leaf5130Box) leaf5130InnerLog = true := by
  rfl'

private theorem leaf5130InnerLogValid :
    leaf5130InnerLog.Valid 8 (innerAD leaf5130Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf5130CoverageChecked

private noncomputable def leaf5130InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907351/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5130InputLogOnePlusV_eq :
    leaf5130InputLogOnePlusV = outerEnclosure 24
      (leaf5130Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5130RoundedFacts : LeafRoundedFacts 8
    leaf5130Certificate.logOnePlusV leaf5130InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5130InputLogOnePlusV_eq }

private noncomputable def leaf5130Inputs : Inputs :=
  inputsOfCaches globalInput sk226RoundedInputs
    chi284InputQChi innerPair242Input
    leaf5130InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5130LowerChecked :
    lowerCheck 24 leaf5130Box leaf5130Inputs = true := by
  rfl'

private theorem leaf5130CoversExact : CoversExact 8
    leaf5130Box leaf5130Certificate leaf5130InnerLog leaf5130Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk226RoundedFacts chi284RoundedFacts
    innerPair242RoundedFacts leaf5130RoundedFacts (by rfl)

private theorem leaf5130FlatSound : Sound leaf5130Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5130CertificateValid
    leaf5130InnerLogValid leaf5130CoversExact leaf5130LowerChecked

private noncomputable def leaf5131Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (243/64), chiLo := (37/128), chiHi := (75/256) }

private noncomputable def leaf5131Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742459/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714811136) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2247255479/2147483648) }, upper := { exponent := 1, mantissa := (34609/32768) } }, logOuter := sk227LogOuterCertificate, logK := sk227LogKCertificate, logChi := chi283LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432223487/137429622272) } }, logDArg := sk227LogDArgCertificate }

private noncomputable def leaf5131InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf5131LocalValidity :
    LeafFacts leaf5131Box leaf5131Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5131Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714811136) }) = true
      norm_num [leaf5131Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5131CertificateValid :
    WideCertificateValid leaf5131Box leaf5131Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk227ValidityFacts chi283ValidityFacts
    leaf5131LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5131CoverageChecked :
    coverageCheck (innerAD leaf5131Box) leaf5131InnerLog = true := by
  rfl'

private theorem leaf5131InnerLogValid :
    leaf5131InnerLog.Valid 8 (innerAD leaf5131Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf5131CoverageChecked

private noncomputable def leaf5131InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814699/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5131InputLogOnePlusV_eq :
    leaf5131InputLogOnePlusV = outerEnclosure 24
      (leaf5131Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5131RoundedFacts : LeafRoundedFacts 8
    leaf5131Certificate.logOnePlusV leaf5131InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5131InputLogOnePlusV_eq }

private noncomputable def leaf5131Inputs : Inputs :=
  inputsOfCaches globalInput sk227RoundedInputs
    chi283InputQChi innerPair242Input
    leaf5131InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5131LowerChecked :
    lowerCheck 24 leaf5131Box leaf5131Inputs = true := by
  rfl'

private theorem leaf5131CoversExact : CoversExact 8
    leaf5131Box leaf5131Certificate leaf5131InnerLog leaf5131Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk227RoundedFacts chi283RoundedFacts
    innerPair242RoundedFacts leaf5131RoundedFacts (by rfl)

private theorem leaf5131FlatSound : Sound leaf5131Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5131CertificateValid
    leaf5131InnerLogValid leaf5131CoversExact leaf5131LowerChecked

private noncomputable def leaf5132Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (243/64), kHi := (61/16), chiLo := (37/128), chiHi := (75/256) }

private noncomputable def leaf5132Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742461/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9816773193/9816398848) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2252104845/2147483648) }, upper := { exponent := 1, mantissa := (8671/8192) } }, logOuter := sk228LogOuterCertificate, logK := sk228LogKCertificate, logChi := chi283LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (19633172041/19632797696) } }, logDArg := sk228LogDArgCertificate }

private noncomputable def leaf5132InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf5132LocalValidity :
    LeafFacts leaf5132Box leaf5132Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5132Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9816773193/9816398848) }) = true
      norm_num [leaf5132Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5132CertificateValid :
    WideCertificateValid leaf5132Box leaf5132Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk228ValidityFacts chi283ValidityFacts
    leaf5132LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5132CoverageChecked :
    coverageCheck (innerAD leaf5132Box) leaf5132InnerLog = true := by
  rfl'

private theorem leaf5132InnerLogValid :
    leaf5132InnerLog.Valid 8 (innerAD leaf5132Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf5132CoverageChecked

private noncomputable def leaf5132InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629401/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5132InputLogOnePlusV_eq :
    leaf5132InputLogOnePlusV = outerEnclosure 24
      (leaf5132Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5132RoundedFacts : LeafRoundedFacts 8
    leaf5132Certificate.logOnePlusV leaf5132InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5132InputLogOnePlusV_eq }

private noncomputable def leaf5132Inputs : Inputs :=
  inputsOfCaches globalInput sk228RoundedInputs
    chi283InputQChi innerPair242Input
    leaf5132InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5132LowerChecked :
    lowerCheck 24 leaf5132Box leaf5132Inputs = true := by
  rfl'

private theorem leaf5132CoversExact : CoversExact 8
    leaf5132Box leaf5132Certificate leaf5132InnerLog leaf5132Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk228RoundedFacts chi283RoundedFacts
    innerPair242RoundedFacts leaf5132RoundedFacts (by rfl)

private theorem leaf5132FlatSound : Sound leaf5132Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5132CertificateValid
    leaf5132InnerLogValid leaf5132CoversExact leaf5132LowerChecked

private noncomputable def leaf5133Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (243/64), chiLo := (75/256), chiHi := (19/64) }

private noncomputable def leaf5133Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742461/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9816773193/9816392704) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2263114221/2147483648) }, upper := { exponent := 1, mantissa := (8713/8192) } }, logOuter := sk227LogOuterCertificate, logK := sk227LogKCertificate, logChi := chi284LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (19633165897/19632785408) } }, logDArg := sk227LogDArgCertificate }

private noncomputable def leaf5133InnerLog : WideLogData :=
  innerPair551Data

set_option maxRecDepth 1000000 in
private theorem leaf5133LocalValidity :
    LeafFacts leaf5133Box leaf5133Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5133Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9816773193/9816392704) }) = true
      norm_num [leaf5133Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5133CertificateValid :
    WideCertificateValid leaf5133Box leaf5133Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk227ValidityFacts chi284ValidityFacts
    leaf5133LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5133CoverageChecked :
    coverageCheck (innerAD leaf5133Box) leaf5133InnerLog = true := by
  rfl'

private theorem leaf5133InnerLogValid :
    leaf5133InnerLog.Valid 8 (innerAD leaf5133Box) :=
  wideLogDataValid_of_cachedCheck endpoint284PositiveFacts
    endpoint289PositiveFacts.valid leaf5133CoverageChecked

private noncomputable def leaf5133InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814703/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5133InputLogOnePlusV_eq :
    leaf5133InputLogOnePlusV = outerEnclosure 24
      (leaf5133Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5133RoundedFacts : LeafRoundedFacts 8
    leaf5133Certificate.logOnePlusV leaf5133InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5133InputLogOnePlusV_eq }

private noncomputable def leaf5133Inputs : Inputs :=
  inputsOfCaches globalInput sk227RoundedInputs
    chi284InputQChi innerPair551Input
    leaf5133InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5133LowerChecked :
    lowerCheck 24 leaf5133Box leaf5133Inputs = true := by
  rfl'

private theorem leaf5133CoversExact : CoversExact 8
    leaf5133Box leaf5133Certificate leaf5133InnerLog leaf5133Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk227RoundedFacts chi284RoundedFacts
    innerPair551RoundedFacts leaf5133RoundedFacts (by rfl)

private theorem leaf5133FlatSound : Sound leaf5133Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5133CertificateValid
    leaf5133InnerLogValid leaf5133CoversExact leaf5133LowerChecked

private noncomputable def leaf5134Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (243/64), kHi := (61/16), chiLo := (75/256), chiHi := (19/64) }

private noncomputable def leaf5134Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742463/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22905804117/22904909824) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2268029119/2147483648) }, upper := { exponent := 1, mantissa := (2183/2048) } }, logOuter := sk228LogOuterCertificate, logK := sk228LogKCertificate, logChi := chi284LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45810713941/45809819648) } }, logDArg := sk228LogDArgCertificate }

private noncomputable def leaf5134InnerLog : WideLogData :=
  innerPair336Data

set_option maxRecDepth 1000000 in
private theorem leaf5134LocalValidity :
    LeafFacts leaf5134Box leaf5134Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5134Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22905804117/22904909824) }) = true
      norm_num [leaf5134Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5134CertificateValid :
    WideCertificateValid leaf5134Box leaf5134Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk228ValidityFacts chi284ValidityFacts
    leaf5134LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5134CoverageChecked :
    coverageCheck (innerAD leaf5134Box) leaf5134InnerLog = true := by
  rfl'

private theorem leaf5134InnerLogValid :
    leaf5134InnerLog.Valid 8 (innerAD leaf5134Box) :=
  wideLogDataValid_of_cachedCheck endpoint89PositiveFacts
    endpoint289PositiveFacts.valid leaf5134CoverageChecked

private noncomputable def leaf5134InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (363419/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf5134InputLogOnePlusV_eq :
    leaf5134InputLogOnePlusV = outerEnclosure 24
      (leaf5134Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5134RoundedFacts : LeafRoundedFacts 8
    leaf5134Certificate.logOnePlusV leaf5134InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5134InputLogOnePlusV_eq }

private noncomputable def leaf5134Inputs : Inputs :=
  inputsOfCaches globalInput sk228RoundedInputs
    chi284InputQChi innerPair336Input
    leaf5134InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5134LowerChecked :
    lowerCheck 24 leaf5134Box leaf5134Inputs = true := by
  rfl'

private theorem leaf5134CoversExact : CoversExact 8
    leaf5134Box leaf5134Certificate leaf5134InnerLog leaf5134Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk228RoundedFacts chi284RoundedFacts
    innerPair336RoundedFacts leaf5134RoundedFacts (by rfl)

private theorem leaf5134FlatSound : Sound leaf5134Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5134CertificateValid
    leaf5134InnerLogValid leaf5134CoversExact leaf5134LowerChecked

private noncomputable def leaf5135Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (245/64), chiLo := (9/32), chiHi := (73/256) }

private noncomputable def leaf5135Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742459/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714898176) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2224974599/2147483648) }, upper := { exponent := 1, mantissa := (34269/32768) } }, logOuter := sk229LogOuterCertificate, logK := sk229LogKCertificate, logChi := chi281LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432310527/137429796352) } }, logDArg := sk229LogDArgCertificate }

private noncomputable def leaf5135InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf5135LocalValidity :
    LeafFacts leaf5135Box leaf5135Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5135Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714898176) }) = true
      norm_num [leaf5135Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5135CertificateValid :
    WideCertificateValid leaf5135Box leaf5135Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk229ValidityFacts chi281ValidityFacts
    leaf5135LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5135CoverageChecked :
    coverageCheck (innerAD leaf5135Box) leaf5135InnerLog = true := by
  rfl'

private theorem leaf5135InnerLogValid :
    leaf5135InnerLog.Valid 8 (innerAD leaf5135Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf5135CoverageChecked

private noncomputable def leaf5135InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907347/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5135InputLogOnePlusV_eq :
    leaf5135InputLogOnePlusV = outerEnclosure 24
      (leaf5135Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5135RoundedFacts : LeafRoundedFacts 8
    leaf5135Certificate.logOnePlusV leaf5135InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5135InputLogOnePlusV_eq }

private noncomputable def leaf5135Inputs : Inputs :=
  inputsOfCaches globalInput sk229RoundedInputs
    chi281InputQChi innerPair242Input
    leaf5135InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5135LowerChecked :
    lowerCheck 24 leaf5135Box leaf5135Inputs = true := by
  rfl'

private theorem leaf5135CoversExact : CoversExact 8
    leaf5135Box leaf5135Certificate leaf5135InnerLog leaf5135Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk229RoundedFacts chi281RoundedFacts
    innerPair242RoundedFacts leaf5135RoundedFacts (by rfl)

private theorem leaf5135FlatSound : Sound leaf5135Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5135CertificateValid
    leaf5135InnerLogValid leaf5135CoversExact leaf5135LowerChecked

private noncomputable def leaf5136Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (245/64), kHi := (123/32), chiLo := (9/32), chiHi := (73/256) }

private noncomputable def leaf5136Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742461/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714879488) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2229692901/2147483648) }, upper := { exponent := 1, mantissa := (17171/16384) } }, logOuter := sk230LogOuterCertificate, logK := sk230LogKCertificate, logChi := chi281LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432291839/137429758976) } }, logDArg := sk230LogDArgCertificate }

private noncomputable def leaf5136InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf5136LocalValidity :
    LeafFacts leaf5136Box leaf5136Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5136Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714879488) }) = true
      norm_num [leaf5136Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5136CertificateValid :
    WideCertificateValid leaf5136Box leaf5136Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk230ValidityFacts chi281ValidityFacts
    leaf5136LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5136CoverageChecked :
    coverageCheck (innerAD leaf5136Box) leaf5136InnerLog = true := by
  rfl'

private theorem leaf5136InnerLogValid :
    leaf5136InnerLog.Valid 8 (innerAD leaf5136Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf5136CoverageChecked

private noncomputable def leaf5136InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814695/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5136InputLogOnePlusV_eq :
    leaf5136InputLogOnePlusV = outerEnclosure 24
      (leaf5136Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5136RoundedFacts : LeafRoundedFacts 8
    leaf5136Certificate.logOnePlusV leaf5136InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5136InputLogOnePlusV_eq }

private noncomputable def leaf5136Inputs : Inputs :=
  inputsOfCaches globalInput sk230RoundedInputs
    chi281InputQChi innerPair242Input
    leaf5136InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5136LowerChecked :
    lowerCheck 24 leaf5136Box leaf5136Inputs = true := by
  rfl'

private theorem leaf5136CoversExact : CoversExact 8
    leaf5136Box leaf5136Certificate leaf5136InnerLog leaf5136Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk230RoundedFacts chi281RoundedFacts
    innerPair242RoundedFacts leaf5136RoundedFacts (by rfl)

private theorem leaf5136FlatSound : Sound leaf5136Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5136CertificateValid
    leaf5136InnerLogValid leaf5136CoversExact leaf5136LowerChecked

private noncomputable def leaf5137Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (245/64), chiLo := (73/256), chiHi := (37/128) }

private noncomputable def leaf5137Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742461/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22905804117/22904945152) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2240964405/2147483648) }, upper := { exponent := 1, mantissa := (17257/16384) } }, logOuter := sk229LogOuterCertificate, logK := sk229LogKCertificate, logChi := chi282LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45810749269/45809890304) } }, logDArg := sk229LogDArgCertificate }

private noncomputable def leaf5137InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf5137LocalValidity :
    LeafFacts leaf5137Box leaf5137Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5137Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22905804117/22904945152) }) = true
      norm_num [leaf5137Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5137CertificateValid :
    WideCertificateValid leaf5137Box leaf5137Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk229ValidityFacts chi282ValidityFacts
    leaf5137LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5137CoverageChecked :
    coverageCheck (innerAD leaf5137Box) leaf5137InnerLog = true := by
  rfl'

private theorem leaf5137InnerLogValid :
    leaf5137InnerLog.Valid 8 (innerAD leaf5137Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf5137CoverageChecked

private noncomputable def leaf5137InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629395/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5137InputLogOnePlusV_eq :
    leaf5137InputLogOnePlusV = outerEnclosure 24
      (leaf5137Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5137RoundedFacts : LeafRoundedFacts 8
    leaf5137Certificate.logOnePlusV leaf5137InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5137InputLogOnePlusV_eq }

private noncomputable def leaf5137Inputs : Inputs :=
  inputsOfCaches globalInput sk229RoundedInputs
    chi282InputQChi innerPair242Input
    leaf5137InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5137LowerChecked :
    lowerCheck 24 leaf5137Box leaf5137Inputs = true := by
  rfl'

private theorem leaf5137CoversExact : CoversExact 8
    leaf5137Box leaf5137Certificate leaf5137InnerLog leaf5137Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk229RoundedFacts chi282RoundedFacts
    innerPair242RoundedFacts leaf5137RoundedFacts (by rfl)

private theorem leaf5137FlatSound : Sound leaf5137Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5137CertificateValid
    leaf5137InnerLogValid leaf5137CoversExact leaf5137LowerChecked

private noncomputable def leaf5138Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (245/64), kHi := (123/32), chiLo := (73/256), chiHi := (37/128) }

private noncomputable def leaf5138Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742463/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714816512) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2245748239/2147483648) }, upper := { exponent := 1, mantissa := (8647/8192) } }, logOuter := sk230LogOuterCertificate, logK := sk230LogKCertificate, logChi := chi282LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432228863/137429633024) } }, logDArg := sk230LogDArgCertificate }

private noncomputable def leaf5138InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf5138LocalValidity :
    LeafFacts leaf5138Box leaf5138Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5138Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714816512) }) = true
      norm_num [leaf5138Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5138CertificateValid :
    WideCertificateValid leaf5138Box leaf5138Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk230ValidityFacts chi282ValidityFacts
    leaf5138LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5138CoverageChecked :
    coverageCheck (innerAD leaf5138Box) leaf5138InnerLog = true := by
  rfl'

private theorem leaf5138InnerLogValid :
    leaf5138InnerLog.Valid 8 (innerAD leaf5138Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf5138CoverageChecked

private noncomputable def leaf5138InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814699/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5138InputLogOnePlusV_eq :
    leaf5138InputLogOnePlusV = outerEnclosure 24
      (leaf5138Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5138RoundedFacts : LeafRoundedFacts 8
    leaf5138Certificate.logOnePlusV leaf5138InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5138InputLogOnePlusV_eq }

private noncomputable def leaf5138Inputs : Inputs :=
  inputsOfCaches globalInput sk230RoundedInputs
    chi282InputQChi innerPair242Input
    leaf5138InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5138LowerChecked :
    lowerCheck 24 leaf5138Box leaf5138Inputs = true := by
  rfl'

private theorem leaf5138CoversExact : CoversExact 8
    leaf5138Box leaf5138Certificate leaf5138InnerLog leaf5138Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk230RoundedFacts chi282RoundedFacts
    innerPair242RoundedFacts leaf5138RoundedFacts (by rfl)

private theorem leaf5138FlatSound : Sound leaf5138Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5138CertificateValid
    leaf5138InnerLogValid leaf5138CoversExact leaf5138LowerChecked

private noncomputable def leaf5139Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (247/64), chiLo := (9/32), chiHi := (73/256) }

private noncomputable def leaf5139Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742463/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22905804117/22904953600) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2234411203/2147483648) }, upper := { exponent := 1, mantissa := (34415/32768) } }, logOuter := sk231LogOuterCertificate, logK := sk231LogKCertificate, logChi := chi281LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45810757717/45809907200) } }, logDArg := sk231LogDArgCertificate }

private noncomputable def leaf5139InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf5139LocalValidity :
    LeafFacts leaf5139Box leaf5139Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5139Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22905804117/22904953600) }) = true
      norm_num [leaf5139Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5139CertificateValid :
    WideCertificateValid leaf5139Box leaf5139Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk231ValidityFacts chi281ValidityFacts
    leaf5139LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5139CoverageChecked :
    coverageCheck (innerAD leaf5139Box) leaf5139InnerLog = true := by
  rfl'

private theorem leaf5139InnerLogValid :
    leaf5139InnerLog.Valid 8 (innerAD leaf5139Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf5139CoverageChecked

private noncomputable def leaf5139InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726837/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf5139InputLogOnePlusV_eq :
    leaf5139InputLogOnePlusV = outerEnclosure 24
      (leaf5139Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5139RoundedFacts : LeafRoundedFacts 8
    leaf5139Certificate.logOnePlusV leaf5139InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5139InputLogOnePlusV_eq }

private noncomputable def leaf5139Inputs : Inputs :=
  inputsOfCaches globalInput sk231RoundedInputs
    chi281InputQChi innerPair242Input
    leaf5139InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5139LowerChecked :
    lowerCheck 24 leaf5139Box leaf5139Inputs = true := by
  rfl'

private theorem leaf5139CoversExact : CoversExact 8
    leaf5139Box leaf5139Certificate leaf5139InnerLog leaf5139Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk231RoundedFacts chi281RoundedFacts
    innerPair242RoundedFacts leaf5139RoundedFacts (by rfl)

private theorem leaf5139FlatSound : Sound leaf5139Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5139CertificateValid
    leaf5139InnerLogValid leaf5139CoversExact leaf5139LowerChecked

private noncomputable def leaf5140Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (247/64), kHi := (31/8), chiLo := (9/32), chiHi := (73/256) }

private noncomputable def leaf5140Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742465/1073741824) }, vSqrt := { lower := (8191/8192), upper := (228297051/228288512) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2239129505/2147483648) }, upper := { exponent := 1, mantissa := (4311/4096) } }, logOuter := sk232LogOuterCertificate, logK := sk232LogKCertificate, logChi := chi281LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (456585563/456577024) } }, logDArg := sk232LogDArgCertificate }

private noncomputable def leaf5140InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf5140LocalValidity :
    LeafFacts leaf5140Box leaf5140Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5140Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (228297051/228288512) }) = true
      norm_num [leaf5140Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5140CertificateValid :
    WideCertificateValid leaf5140Box leaf5140Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk232ValidityFacts chi281ValidityFacts
    leaf5140LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5140CoverageChecked :
    coverageCheck (innerAD leaf5140Box) leaf5140InnerLog = true := by
  rfl'

private theorem leaf5140InnerLogValid :
    leaf5140InnerLog.Valid 8 (innerAD leaf5140Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf5140CoverageChecked

private noncomputable def leaf5140InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629395/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5140InputLogOnePlusV_eq :
    leaf5140InputLogOnePlusV = outerEnclosure 24
      (leaf5140Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5140RoundedFacts : LeafRoundedFacts 8
    leaf5140Certificate.logOnePlusV leaf5140InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5140InputLogOnePlusV_eq }

private noncomputable def leaf5140Inputs : Inputs :=
  inputsOfCaches globalInput sk232RoundedInputs
    chi281InputQChi innerPair242Input
    leaf5140InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5140LowerChecked :
    lowerCheck 24 leaf5140Box leaf5140Inputs = true := by
  rfl'

private theorem leaf5140CoversExact : CoversExact 8
    leaf5140Box leaf5140Certificate leaf5140InnerLog leaf5140Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk232RoundedFacts chi281RoundedFacts
    innerPair242RoundedFacts leaf5140RoundedFacts (by rfl)

private theorem leaf5140FlatSound : Sound leaf5140Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5140CertificateValid
    leaf5140InnerLogValid leaf5140CoversExact leaf5140LowerChecked

private noncomputable def leaf5141Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (247/64), chiLo := (73/256), chiHi := (37/128) }

private noncomputable def leaf5141Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742465/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714797568) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2250532073/2147483648) }, upper := { exponent := 1, mantissa := (17331/16384) } }, logOuter := sk231LogOuterCertificate, logK := sk231LogKCertificate, logChi := chi282LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432209919/137429595136) } }, logDArg := sk231LogDArgCertificate }

private noncomputable def leaf5141InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf5141LocalValidity :
    LeafFacts leaf5141Box leaf5141Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5141Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714797568) }) = true
      norm_num [leaf5141Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5141CertificateValid :
    WideCertificateValid leaf5141Box leaf5141Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk231ValidityFacts chi282ValidityFacts
    leaf5141LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5141CoverageChecked :
    coverageCheck (innerAD leaf5141Box) leaf5141InnerLog = true := by
  rfl'

private theorem leaf5141InnerLogValid :
    leaf5141InnerLog.Valid 8 (innerAD leaf5141Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf5141CoverageChecked

private noncomputable def leaf5141InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453675/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf5141InputLogOnePlusV_eq :
    leaf5141InputLogOnePlusV = outerEnclosure 24
      (leaf5141Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5141RoundedFacts : LeafRoundedFacts 8
    leaf5141Certificate.logOnePlusV leaf5141InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5141InputLogOnePlusV_eq }

private noncomputable def leaf5141Inputs : Inputs :=
  inputsOfCaches globalInput sk231RoundedInputs
    chi282InputQChi innerPair242Input
    leaf5141InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5141LowerChecked :
    lowerCheck 24 leaf5141Box leaf5141Inputs = true := by
  rfl'

private theorem leaf5141CoversExact : CoversExact 8
    leaf5141Box leaf5141Certificate leaf5141InnerLog leaf5141Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk231RoundedFacts chi282RoundedFacts
    innerPair242RoundedFacts leaf5141RoundedFacts (by rfl)

private theorem leaf5141FlatSound : Sound leaf5141Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5141CertificateValid
    leaf5141InnerLogValid leaf5141CoversExact leaf5141LowerChecked

private noncomputable def leaf5142Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (247/64), kHi := (31/8), chiLo := (73/256), chiHi := (37/128) }

private noncomputable def leaf5142Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742467/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22905804117/22904926208) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2255315907/2147483648) }, upper := { exponent := 1, mantissa := (2171/2048) } }, logOuter := sk232LogOuterCertificate, logK := sk232LogKCertificate, logChi := chi282LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45810730325/45809852416) } }, logDArg := sk232LogDArgCertificate }

private noncomputable def leaf5142InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf5142LocalValidity :
    LeafFacts leaf5142Box leaf5142Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5142Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22905804117/22904926208) }) = true
      norm_num [leaf5142Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5142CertificateValid :
    WideCertificateValid leaf5142Box leaf5142Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk232ValidityFacts chi282ValidityFacts
    leaf5142LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5142CoverageChecked :
    coverageCheck (innerAD leaf5142Box) leaf5142InnerLog = true := by
  rfl'

private theorem leaf5142InnerLogValid :
    leaf5142InnerLog.Valid 8 (innerAD leaf5142Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf5142CoverageChecked

private noncomputable def leaf5142InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814701/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5142InputLogOnePlusV_eq :
    leaf5142InputLogOnePlusV = outerEnclosure 24
      (leaf5142Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5142RoundedFacts : LeafRoundedFacts 8
    leaf5142Certificate.logOnePlusV leaf5142InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5142InputLogOnePlusV_eq }

private noncomputable def leaf5142Inputs : Inputs :=
  inputsOfCaches globalInput sk232RoundedInputs
    chi282InputQChi innerPair242Input
    leaf5142InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5142LowerChecked :
    lowerCheck 24 leaf5142Box leaf5142Inputs = true := by
  rfl'

private theorem leaf5142CoversExact : CoversExact 8
    leaf5142Box leaf5142Certificate leaf5142InnerLog leaf5142Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk232RoundedFacts chi282RoundedFacts
    innerPair242RoundedFacts leaf5142RoundedFacts (by rfl)

private theorem leaf5142FlatSound : Sound leaf5142Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5142CertificateValid
    leaf5142InnerLogValid leaf5142CoversExact leaf5142LowerChecked

private noncomputable def leaf5143Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (245/64), chiLo := (37/128), chiHi := (75/256) }

private noncomputable def leaf5143Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742463/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714772736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2256954211/2147483648) }, upper := { exponent := 1, mantissa := (34759/32768) } }, logOuter := sk229LogOuterCertificate, logK := sk229LogKCertificate, logChi := chi283LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432185087/137429545472) } }, logDArg := sk229LogDArgCertificate }

private noncomputable def leaf5143InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf5143LocalValidity :
    LeafFacts leaf5143Box leaf5143Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5143Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714772736) }) = true
      norm_num [leaf5143Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5143CertificateValid :
    WideCertificateValid leaf5143Box leaf5143Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk229ValidityFacts chi283ValidityFacts
    leaf5143LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5143CoverageChecked :
    coverageCheck (innerAD leaf5143Box) leaf5143InnerLog = true := by
  rfl'

private theorem leaf5143InnerLogValid :
    leaf5143InnerLog.Valid 8 (innerAD leaf5143Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf5143CoverageChecked

private noncomputable def leaf5143InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629403/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5143InputLogOnePlusV_eq :
    leaf5143InputLogOnePlusV = outerEnclosure 24
      (leaf5143Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5143RoundedFacts : LeafRoundedFacts 8
    leaf5143Certificate.logOnePlusV leaf5143InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5143InputLogOnePlusV_eq }

private noncomputable def leaf5143Inputs : Inputs :=
  inputsOfCaches globalInput sk229RoundedInputs
    chi283InputQChi innerPair242Input
    leaf5143InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5143LowerChecked :
    lowerCheck 24 leaf5143Box leaf5143Inputs = true := by
  rfl'

private theorem leaf5143CoversExact : CoversExact 8
    leaf5143Box leaf5143Certificate leaf5143InnerLog leaf5143Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk229RoundedFacts chi283RoundedFacts
    innerPair242RoundedFacts leaf5143RoundedFacts (by rfl)

private theorem leaf5143FlatSound : Sound leaf5143Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5143CertificateValid
    leaf5143InnerLogValid leaf5143CoversExact leaf5143LowerChecked

private noncomputable def leaf5144Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (245/64), kHi := (123/32), chiLo := (37/128), chiHi := (75/256) }

private noncomputable def leaf5144Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742465/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714753536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2261803577/2147483648) }, upper := { exponent := 1, mantissa := (17417/16384) } }, logOuter := sk230LogOuterCertificate, logK := sk230LogKCertificate, logChi := chi283LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432165887/137429507072) } }, logDArg := sk230LogDArgCertificate }

private noncomputable def leaf5144InnerLog : WideLogData :=
  innerPair551Data

set_option maxRecDepth 1000000 in
private theorem leaf5144LocalValidity :
    LeafFacts leaf5144Box leaf5144Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5144Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714753536) }) = true
      norm_num [leaf5144Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5144CertificateValid :
    WideCertificateValid leaf5144Box leaf5144Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk230ValidityFacts chi283ValidityFacts
    leaf5144LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5144CoverageChecked :
    coverageCheck (innerAD leaf5144Box) leaf5144InnerLog = true := by
  rfl'

private theorem leaf5144InnerLogValid :
    leaf5144InnerLog.Valid 8 (innerAD leaf5144Box) :=
  wideLogDataValid_of_cachedCheck endpoint284PositiveFacts
    endpoint289PositiveFacts.valid leaf5144CoverageChecked

private noncomputable def leaf5144InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629405/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5144InputLogOnePlusV_eq :
    leaf5144InputLogOnePlusV = outerEnclosure 24
      (leaf5144Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5144RoundedFacts : LeafRoundedFacts 8
    leaf5144Certificate.logOnePlusV leaf5144InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5144InputLogOnePlusV_eq }

private noncomputable def leaf5144Inputs : Inputs :=
  inputsOfCaches globalInput sk230RoundedInputs
    chi283InputQChi innerPair551Input
    leaf5144InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5144LowerChecked :
    lowerCheck 24 leaf5144Box leaf5144Inputs = true := by
  rfl'

private theorem leaf5144CoversExact : CoversExact 8
    leaf5144Box leaf5144Certificate leaf5144InnerLog leaf5144Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk230RoundedFacts chi283RoundedFacts
    innerPair551RoundedFacts leaf5144RoundedFacts (by rfl)

private theorem leaf5144FlatSound : Sound leaf5144Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5144CertificateValid
    leaf5144InnerLogValid leaf5144CoversExact leaf5144LowerChecked

private noncomputable def leaf5145Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (245/64), chiLo := (75/256), chiHi := (19/64) }

private noncomputable def leaf5145Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742465/1073741824) }, vSqrt := { lower := (8191/8192), upper := (1598079357/1598016512) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2272944017/2147483648) }, upper := { exponent := 1, mantissa := (8751/8192) } }, logOuter := sk229LogOuterCertificate, logK := sk229LogKCertificate, logChi := chi284LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (3196095869/3196033024) } }, logDArg := sk229LogDArgCertificate }

private noncomputable def leaf5145InnerLog : WideLogData :=
  innerPair336Data

set_option maxRecDepth 1000000 in
private theorem leaf5145LocalValidity :
    LeafFacts leaf5145Box leaf5145Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5145Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (1598079357/1598016512) }) = true
      norm_num [leaf5145Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5145CertificateValid :
    WideCertificateValid leaf5145Box leaf5145Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk229ValidityFacts chi284ValidityFacts
    leaf5145LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5145CoverageChecked :
    coverageCheck (innerAD leaf5145Box) leaf5145InnerLog = true := by
  rfl'

private theorem leaf5145InnerLogValid :
    leaf5145InnerLog.Valid 8 (innerAD leaf5145Box) :=
  wideLogDataValid_of_cachedCheck endpoint89PositiveFacts
    endpoint289PositiveFacts.valid leaf5145CoverageChecked

private noncomputable def leaf5145InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629411/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5145InputLogOnePlusV_eq :
    leaf5145InputLogOnePlusV = outerEnclosure 24
      (leaf5145Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5145RoundedFacts : LeafRoundedFacts 8
    leaf5145Certificate.logOnePlusV leaf5145InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5145InputLogOnePlusV_eq }

private noncomputable def leaf5145Inputs : Inputs :=
  inputsOfCaches globalInput sk229RoundedInputs
    chi284InputQChi innerPair336Input
    leaf5145InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5145LowerChecked :
    lowerCheck 24 leaf5145Box leaf5145Inputs = true := by
  rfl'

private theorem leaf5145CoversExact : CoversExact 8
    leaf5145Box leaf5145Certificate leaf5145InnerLog leaf5145Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk229RoundedFacts chi284RoundedFacts
    innerPair336RoundedFacts leaf5145RoundedFacts (by rfl)

private theorem leaf5145FlatSound : Sound leaf5145Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5145CertificateValid
    leaf5145InnerLogValid leaf5145CoversExact leaf5145LowerChecked

private noncomputable def leaf5146Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (245/64), kHi := (123/32), chiLo := (75/256), chiHi := (19/64) }

private noncomputable def leaf5146Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742467/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714690560) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2277858915/2147483648) }, upper := { exponent := 1, mantissa := (4385/4096) } }, logOuter := sk230LogOuterCertificate, logK := sk230LogKCertificate, logChi := chi284LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432102911/137429381120) } }, logDArg := sk230LogDArgCertificate }

private noncomputable def leaf5146InnerLog : WideLogData :=
  innerPair335Data

set_option maxRecDepth 1000000 in
private theorem leaf5146LocalValidity :
    LeafFacts leaf5146Box leaf5146Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5146Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714690560) }) = true
      norm_num [leaf5146Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5146CertificateValid :
    WideCertificateValid leaf5146Box leaf5146Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk230ValidityFacts chi284ValidityFacts
    leaf5146LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5146CoverageChecked :
    coverageCheck (innerAD leaf5146Box) leaf5146InnerLog = true := by
  rfl'

private theorem leaf5146InnerLogValid :
    leaf5146InnerLog.Valid 8 (innerAD leaf5146Box) :=
  wideLogDataValid_of_cachedCheck endpoint89PositiveFacts
    endpoint88PositiveFacts.valid leaf5146CoverageChecked

private noncomputable def leaf5146InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629413/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5146InputLogOnePlusV_eq :
    leaf5146InputLogOnePlusV = outerEnclosure 24
      (leaf5146Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5146RoundedFacts : LeafRoundedFacts 8
    leaf5146Certificate.logOnePlusV leaf5146InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5146InputLogOnePlusV_eq }

private noncomputable def leaf5146Inputs : Inputs :=
  inputsOfCaches globalInput sk230RoundedInputs
    chi284InputQChi innerPair335Input
    leaf5146InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5146LowerChecked :
    lowerCheck 24 leaf5146Box leaf5146Inputs = true := by
  rfl'

private theorem leaf5146CoversExact : CoversExact 8
    leaf5146Box leaf5146Certificate leaf5146InnerLog leaf5146Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk230RoundedFacts chi284RoundedFacts
    innerPair335RoundedFacts leaf5146RoundedFacts (by rfl)

private theorem leaf5146FlatSound : Sound leaf5146Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5146CertificateValid
    leaf5146InnerLogValid leaf5146CoversExact leaf5146LowerChecked

private noncomputable def leaf5147Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (247/64), chiLo := (37/128), chiHi := (75/256) }

private noncomputable def leaf5147Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742467/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714734336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2266652943/2147483648) }, upper := { exponent := 1, mantissa := (34909/32768) } }, logOuter := sk231LogOuterCertificate, logK := sk231LogKCertificate, logChi := chi283LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432146687/137429468672) } }, logDArg := sk231LogDArgCertificate }

private noncomputable def leaf5147InnerLog : WideLogData :=
  innerPair336Data

set_option maxRecDepth 1000000 in
private theorem leaf5147LocalValidity :
    LeafFacts leaf5147Box leaf5147Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5147Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714734336) }) = true
      norm_num [leaf5147Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5147CertificateValid :
    WideCertificateValid leaf5147Box leaf5147Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk231ValidityFacts chi283ValidityFacts
    leaf5147LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5147CoverageChecked :
    coverageCheck (innerAD leaf5147Box) leaf5147InnerLog = true := by
  rfl'

private theorem leaf5147InnerLogValid :
    leaf5147InnerLog.Valid 8 (innerAD leaf5147Box) :=
  wideLogDataValid_of_cachedCheck endpoint89PositiveFacts
    endpoint289PositiveFacts.valid leaf5147CoverageChecked

private noncomputable def leaf5147InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (363419/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf5147InputLogOnePlusV_eq :
    leaf5147InputLogOnePlusV = outerEnclosure 24
      (leaf5147Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5147RoundedFacts : LeafRoundedFacts 8
    leaf5147Certificate.logOnePlusV leaf5147InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5147InputLogOnePlusV_eq }

private noncomputable def leaf5147Inputs : Inputs :=
  inputsOfCaches globalInput sk231RoundedInputs
    chi283InputQChi innerPair336Input
    leaf5147InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5147LowerChecked :
    lowerCheck 24 leaf5147Box leaf5147Inputs = true := by
  rfl'

private theorem leaf5147CoversExact : CoversExact 8
    leaf5147Box leaf5147Certificate leaf5147InnerLog leaf5147Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk231RoundedFacts chi283RoundedFacts
    innerPair336RoundedFacts leaf5147RoundedFacts (by rfl)

private theorem leaf5147FlatSound : Sound leaf5147Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5147CertificateValid
    leaf5147InnerLogValid leaf5147CoversExact leaf5147LowerChecked

private noncomputable def leaf5148Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (247/64), kHi := (31/8), chiLo := (37/128), chiHi := (75/256) }

private noncomputable def leaf5148Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742469/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714715136) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2271502309/2147483648) }, upper := { exponent := 1, mantissa := (4373/4096) } }, logOuter := sk232LogOuterCertificate, logK := sk232LogKCertificate, logChi := chi283LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432127487/137429430272) } }, logDArg := sk232LogDArgCertificate }

private noncomputable def leaf5148InnerLog : WideLogData :=
  innerPair336Data

set_option maxRecDepth 1000000 in
private theorem leaf5148LocalValidity :
    LeafFacts leaf5148Box leaf5148Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5148Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714715136) }) = true
      norm_num [leaf5148Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5148CertificateValid :
    WideCertificateValid leaf5148Box leaf5148Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk232ValidityFacts chi283ValidityFacts
    leaf5148LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5148CoverageChecked :
    coverageCheck (innerAD leaf5148Box) leaf5148InnerLog = true := by
  rfl'

private theorem leaf5148InnerLogValid :
    leaf5148InnerLog.Valid 8 (innerAD leaf5148Box) :=
  wideLogDataValid_of_cachedCheck endpoint89PositiveFacts
    endpoint289PositiveFacts.valid leaf5148CoverageChecked

private noncomputable def leaf5148InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814705/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5148InputLogOnePlusV_eq :
    leaf5148InputLogOnePlusV = outerEnclosure 24
      (leaf5148Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5148RoundedFacts : LeafRoundedFacts 8
    leaf5148Certificate.logOnePlusV leaf5148InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5148InputLogOnePlusV_eq }

private noncomputable def leaf5148Inputs : Inputs :=
  inputsOfCaches globalInput sk232RoundedInputs
    chi283InputQChi innerPair336Input
    leaf5148InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5148LowerChecked :
    lowerCheck 24 leaf5148Box leaf5148Inputs = true := by
  rfl'

private theorem leaf5148CoversExact : CoversExact 8
    leaf5148Box leaf5148Certificate leaf5148InnerLog leaf5148Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk232RoundedFacts chi283RoundedFacts
    innerPair336RoundedFacts leaf5148RoundedFacts (by rfl)

private theorem leaf5148FlatSound : Sound leaf5148Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5148CertificateValid
    leaf5148InnerLogValid leaf5148CoversExact leaf5148LowerChecked

private noncomputable def leaf5149Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (247/64), chiLo := (75/256), chiHi := (19/64) }

private noncomputable def leaf5149Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742469/1073741824) }, vSqrt := { lower := (8191/8192), upper := (7635268039/7634963456) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2282773813/2147483648) }, upper := { exponent := 1, mantissa := (8789/8192) } }, logOuter := sk231LogOuterCertificate, logK := sk231LogKCertificate, logChi := chi284LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (15270231495/15269926912) } }, logDArg := sk231LogDArgCertificate }

private noncomputable def leaf5149InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf5149LocalValidity :
    LeafFacts leaf5149Box leaf5149Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5149Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (7635268039/7634963456) }) = true
      norm_num [leaf5149Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5149CertificateValid :
    WideCertificateValid leaf5149Box leaf5149Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk231ValidityFacts chi284ValidityFacts
    leaf5149LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5149CoverageChecked :
    coverageCheck (innerAD leaf5149Box) leaf5149InnerLog = true := by
  rfl'

private theorem leaf5149InnerLogValid :
    leaf5149InnerLog.Valid 8 (innerAD leaf5149Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf5149CoverageChecked

private noncomputable def leaf5149InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629415/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5149InputLogOnePlusV_eq :
    leaf5149InputLogOnePlusV = outerEnclosure 24
      (leaf5149Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5149RoundedFacts : LeafRoundedFacts 8
    leaf5149Certificate.logOnePlusV leaf5149InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5149InputLogOnePlusV_eq }

private noncomputable def leaf5149Inputs : Inputs :=
  inputsOfCaches globalInput sk231RoundedInputs
    chi284InputQChi innerPair249Input
    leaf5149InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5149LowerChecked :
    lowerCheck 24 leaf5149Box leaf5149Inputs = true := by
  rfl'

private theorem leaf5149CoversExact : CoversExact 8
    leaf5149Box leaf5149Certificate leaf5149InnerLog leaf5149Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk231RoundedFacts chi284RoundedFacts
    innerPair249RoundedFacts leaf5149RoundedFacts (by rfl)

private theorem leaf5149FlatSound : Sound leaf5149Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5149CertificateValid
    leaf5149InnerLogValid leaf5149CoversExact leaf5149LowerChecked

private noncomputable def leaf5150Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (247/64), kHi := (31/8), chiLo := (75/256), chiHi := (19/64) }

private noncomputable def leaf5150Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742471/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714651648) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2287688711/2147483648) }, upper := { exponent := 1, mantissa := (1101/1024) } }, logOuter := sk232LogOuterCertificate, logK := sk232LogKCertificate, logChi := chi284LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432063999/137429303296) } }, logDArg := sk232LogDArgCertificate }

private noncomputable def leaf5150InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf5150LocalValidity :
    LeafFacts leaf5150Box leaf5150Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5150Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714651648) }) = true
      norm_num [leaf5150Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5150CertificateValid :
    WideCertificateValid leaf5150Box leaf5150Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk232ValidityFacts chi284ValidityFacts
    leaf5150LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5150CoverageChecked :
    coverageCheck (innerAD leaf5150Box) leaf5150InnerLog = true := by
  rfl'

private theorem leaf5150InnerLogValid :
    leaf5150InnerLog.Valid 8 (innerAD leaf5150Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf5150CoverageChecked

private noncomputable def leaf5150InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814709/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5150InputLogOnePlusV_eq :
    leaf5150InputLogOnePlusV = outerEnclosure 24
      (leaf5150Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5150RoundedFacts : LeafRoundedFacts 8
    leaf5150Certificate.logOnePlusV leaf5150InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5150InputLogOnePlusV_eq }

private noncomputable def leaf5150Inputs : Inputs :=
  inputsOfCaches globalInput sk232RoundedInputs
    chi284InputQChi innerPair249Input
    leaf5150InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5150LowerChecked :
    lowerCheck 24 leaf5150Box leaf5150Inputs = true := by
  rfl'

private theorem leaf5150CoversExact : CoversExact 8
    leaf5150Box leaf5150Certificate leaf5150InnerLog leaf5150Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk232RoundedFacts chi284RoundedFacts
    innerPair249RoundedFacts leaf5150RoundedFacts (by rfl)

private theorem leaf5150FlatSound : Sound leaf5150Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5150CertificateValid
    leaf5150InnerLogValid leaf5150CoversExact leaf5150LowerChecked

private noncomputable def leaf5151Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (241/64), chiLo := (19/64), chiHi := (77/256) }

private noncomputable def leaf5151Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742459/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714726144) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2269012103/2147483648) }, upper := { exponent := 1, mantissa := (34941/32768) } }, logOuter := sk225LogOuterCertificate, logK := sk225LogKCertificate, logChi := chi285LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432138495/137429452288) } }, logDArg := sk225LogDArgCertificate }

private noncomputable def leaf5151InnerLog : WideLogData :=
  innerPair336Data

set_option maxRecDepth 1000000 in
private theorem leaf5151LocalValidity :
    LeafFacts leaf5151Box leaf5151Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5151Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714726144) }) = true
      norm_num [leaf5151Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5151CertificateValid :
    WideCertificateValid leaf5151Box leaf5151Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk225ValidityFacts chi285ValidityFacts
    leaf5151LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5151CoverageChecked :
    coverageCheck (innerAD leaf5151Box) leaf5151InnerLog = true := by
  rfl'

private theorem leaf5151InnerLogValid :
    leaf5151InnerLog.Valid 8 (innerAD leaf5151Box) :=
  wideLogDataValid_of_cachedCheck endpoint89PositiveFacts
    endpoint289PositiveFacts.valid leaf5151CoverageChecked

private noncomputable def leaf5151InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629409/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5151InputLogOnePlusV_eq :
    leaf5151InputLogOnePlusV = outerEnclosure 24
      (leaf5151Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5151RoundedFacts : LeafRoundedFacts 8
    leaf5151Certificate.logOnePlusV leaf5151InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5151InputLogOnePlusV_eq }

private noncomputable def leaf5151Inputs : Inputs :=
  inputsOfCaches globalInput sk225RoundedInputs
    chi285InputQChi innerPair336Input
    leaf5151InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5151LowerChecked :
    lowerCheck 24 leaf5151Box leaf5151Inputs = true := by
  rfl'

private theorem leaf5151CoversExact : CoversExact 8
    leaf5151Box leaf5151Certificate leaf5151InnerLog leaf5151Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk225RoundedFacts chi285RoundedFacts
    innerPair336RoundedFacts leaf5151RoundedFacts (by rfl)

private theorem leaf5151FlatSound : Sound leaf5151Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5151CertificateValid
    leaf5151InnerLogValid leaf5151CoversExact leaf5151LowerChecked

private noncomputable def leaf5152Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (241/64), kHi := (121/32), chiLo := (19/64), chiHi := (77/256) }

private noncomputable def leaf5152Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742461/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22905804117/22904902144) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2273992533/2147483648) }, upper := { exponent := 1, mantissa := (17509/16384) } }, logOuter := sk226LogOuterCertificate, logK := sk226LogKCertificate, logChi := chi285LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45810706261/45809804288) } }, logDArg := sk226LogDArgCertificate }

private noncomputable def leaf5152InnerLog : WideLogData :=
  innerPair243Data

set_option maxRecDepth 1000000 in
private theorem leaf5152LocalValidity :
    LeafFacts leaf5152Box leaf5152Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5152Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22905804117/22904902144) }) = true
      norm_num [leaf5152Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5152CertificateValid :
    WideCertificateValid leaf5152Box leaf5152Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk226ValidityFacts chi285ValidityFacts
    leaf5152LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5152CoverageChecked :
    coverageCheck (innerAD leaf5152Box) leaf5152InnerLog = true := by
  rfl'

private theorem leaf5152InnerLogValid :
    leaf5152InnerLog.Valid 8 (innerAD leaf5152Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint74PositiveFacts.valid leaf5152CoverageChecked

private noncomputable def leaf5152InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629411/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5152InputLogOnePlusV_eq :
    leaf5152InputLogOnePlusV = outerEnclosure 24
      (leaf5152Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5152RoundedFacts : LeafRoundedFacts 8
    leaf5152Certificate.logOnePlusV leaf5152InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5152InputLogOnePlusV_eq }

private noncomputable def leaf5152Inputs : Inputs :=
  inputsOfCaches globalInput sk226RoundedInputs
    chi285InputQChi innerPair243Input
    leaf5152InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5152LowerChecked :
    lowerCheck 24 leaf5152Box leaf5152Inputs = true := by
  rfl'

private theorem leaf5152CoversExact : CoversExact 8
    leaf5152Box leaf5152Certificate leaf5152InnerLog leaf5152Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk226RoundedFacts chi285RoundedFacts
    innerPair243RoundedFacts leaf5152RoundedFacts (by rfl)

private theorem leaf5152FlatSound : Sound leaf5152Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5152CertificateValid
    leaf5152InnerLogValid leaf5152CoversExact leaf5152LowerChecked

private noncomputable def leaf5153Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (241/64), chiLo := (77/256), chiHi := (39/128) }

private noncomputable def leaf5153Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742461/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714664448) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2284739781/2147483648) }, upper := { exponent := 1, mantissa := (17591/16384) } }, logOuter := sk225LogOuterCertificate, logK := sk225LogKCertificate, logChi := chi286LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432076799/137429328896) } }, logDArg := sk225LogDArgCertificate }

private noncomputable def leaf5153InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf5153LocalValidity :
    LeafFacts leaf5153Box leaf5153Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5153Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714664448) }) = true
      norm_num [leaf5153Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5153CertificateValid :
    WideCertificateValid leaf5153Box leaf5153Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk225ValidityFacts chi286ValidityFacts
    leaf5153LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5153CoverageChecked :
    coverageCheck (innerAD leaf5153Box) leaf5153InnerLog = true := by
  rfl'

private theorem leaf5153InnerLogValid :
    leaf5153InnerLog.Valid 8 (innerAD leaf5153Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf5153CoverageChecked

private noncomputable def leaf5153InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453677/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf5153InputLogOnePlusV_eq :
    leaf5153InputLogOnePlusV = outerEnclosure 24
      (leaf5153Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5153RoundedFacts : LeafRoundedFacts 8
    leaf5153Certificate.logOnePlusV leaf5153InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5153InputLogOnePlusV_eq }

private noncomputable def leaf5153Inputs : Inputs :=
  inputsOfCaches globalInput sk225RoundedInputs
    chi286InputQChi innerPair249Input
    leaf5153InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5153LowerChecked :
    lowerCheck 24 leaf5153Box leaf5153Inputs = true := by
  rfl'

private theorem leaf5153CoversExact : CoversExact 8
    leaf5153Box leaf5153Certificate leaf5153InnerLog leaf5153Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk225RoundedFacts chi286RoundedFacts
    innerPair249RoundedFacts leaf5153RoundedFacts (by rfl)

private theorem leaf5153FlatSound : Sound leaf5153Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5153CertificateValid
    leaf5153InnerLogValid leaf5153CoversExact leaf5153LowerChecked

private noncomputable def leaf5154Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (241/64), kHi := (121/32), chiLo := (77/256), chiHi := (39/128) }

private noncomputable def leaf5154Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742463/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714644480) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2289785743/2147483648) }, upper := { exponent := 1, mantissa := (8815/8192) } }, logOuter := sk226LogOuterCertificate, logK := sk226LogKCertificate, logChi := chi286LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432056831/137429288960) } }, logDArg := sk226LogDArgCertificate }

private noncomputable def leaf5154InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf5154LocalValidity :
    LeafFacts leaf5154Box leaf5154Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5154Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714644480) }) = true
      norm_num [leaf5154Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5154CertificateValid :
    WideCertificateValid leaf5154Box leaf5154Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk226ValidityFacts chi286ValidityFacts
    leaf5154LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5154CoverageChecked :
    coverageCheck (innerAD leaf5154Box) leaf5154InnerLog = true := by
  rfl'

private theorem leaf5154InnerLogValid :
    leaf5154InnerLog.Valid 8 (innerAD leaf5154Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf5154CoverageChecked

private noncomputable def leaf5154InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629419/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5154InputLogOnePlusV_eq :
    leaf5154InputLogOnePlusV = outerEnclosure 24
      (leaf5154Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5154RoundedFacts : LeafRoundedFacts 8
    leaf5154Certificate.logOnePlusV leaf5154InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5154InputLogOnePlusV_eq }

private noncomputable def leaf5154Inputs : Inputs :=
  inputsOfCaches globalInput sk226RoundedInputs
    chi286InputQChi innerPair249Input
    leaf5154InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5154LowerChecked :
    lowerCheck 24 leaf5154Box leaf5154Inputs = true := by
  rfl'

private theorem leaf5154CoversExact : CoversExact 8
    leaf5154Box leaf5154Certificate leaf5154InnerLog leaf5154Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk226RoundedFacts chi286RoundedFacts
    innerPair249RoundedFacts leaf5154RoundedFacts (by rfl)

private theorem leaf5154FlatSound : Sound leaf5154Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5154CertificateValid
    leaf5154InnerLogValid leaf5154CoversExact leaf5154LowerChecked

private noncomputable def leaf5155Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (243/64), chiLo := (19/64), chiHi := (77/256) }

private noncomputable def leaf5155Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742463/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714686720) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2278972963/2147483648) }, upper := { exponent := 1, mantissa := (35095/32768) } }, logOuter := sk227LogOuterCertificate, logK := sk227LogKCertificate, logChi := chi285LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432099071/137429373440) } }, logDArg := sk227LogDArgCertificate }

private noncomputable def leaf5155InnerLog : WideLogData :=
  innerPair243Data

set_option maxRecDepth 1000000 in
private theorem leaf5155LocalValidity :
    LeafFacts leaf5155Box leaf5155Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5155Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714686720) }) = true
      norm_num [leaf5155Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5155CertificateValid :
    WideCertificateValid leaf5155Box leaf5155Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk227ValidityFacts chi285ValidityFacts
    leaf5155LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5155CoverageChecked :
    coverageCheck (innerAD leaf5155Box) leaf5155InnerLog = true := by
  rfl'

private theorem leaf5155InnerLogValid :
    leaf5155InnerLog.Valid 8 (innerAD leaf5155Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint74PositiveFacts.valid leaf5155CoverageChecked

private noncomputable def leaf5155InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629413/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5155InputLogOnePlusV_eq :
    leaf5155InputLogOnePlusV = outerEnclosure 24
      (leaf5155Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5155RoundedFacts : LeafRoundedFacts 8
    leaf5155Certificate.logOnePlusV leaf5155InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5155InputLogOnePlusV_eq }

private noncomputable def leaf5155Inputs : Inputs :=
  inputsOfCaches globalInput sk227RoundedInputs
    chi285InputQChi innerPair243Input
    leaf5155InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5155LowerChecked :
    lowerCheck 24 leaf5155Box leaf5155Inputs = true := by
  rfl'

private theorem leaf5155CoversExact : CoversExact 8
    leaf5155Box leaf5155Certificate leaf5155InnerLog leaf5155Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk227RoundedFacts chi285RoundedFacts
    innerPair243RoundedFacts leaf5155RoundedFacts (by rfl)

private theorem leaf5155FlatSound : Sound leaf5155Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5155CertificateValid
    leaf5155InnerLogValid leaf5155CoversExact leaf5155LowerChecked

private noncomputable def leaf5156Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (243/64), kHi := (61/16), chiLo := (19/64), chiHi := (77/256) }

private noncomputable def leaf5156Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742465/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714667008) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2283953393/2147483648) }, upper := { exponent := 1, mantissa := (8793/8192) } }, logOuter := sk228LogOuterCertificate, logK := sk228LogKCertificate, logChi := chi285LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432079359/137429334016) } }, logDArg := sk228LogDArgCertificate }

private noncomputable def leaf5156InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf5156LocalValidity :
    LeafFacts leaf5156Box leaf5156Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5156Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714667008) }) = true
      norm_num [leaf5156Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5156CertificateValid :
    WideCertificateValid leaf5156Box leaf5156Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk228ValidityFacts chi285ValidityFacts
    leaf5156LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5156CoverageChecked :
    coverageCheck (innerAD leaf5156Box) leaf5156InnerLog = true := by
  rfl'

private theorem leaf5156InnerLogValid :
    leaf5156InnerLog.Valid 8 (innerAD leaf5156Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf5156CoverageChecked

private noncomputable def leaf5156InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453677/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf5156InputLogOnePlusV_eq :
    leaf5156InputLogOnePlusV = outerEnclosure 24
      (leaf5156Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5156RoundedFacts : LeafRoundedFacts 8
    leaf5156Certificate.logOnePlusV leaf5156InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5156InputLogOnePlusV_eq }

private noncomputable def leaf5156Inputs : Inputs :=
  inputsOfCaches globalInput sk228RoundedInputs
    chi285InputQChi innerPair249Input
    leaf5156InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5156LowerChecked :
    lowerCheck 24 leaf5156Box leaf5156Inputs = true := by
  rfl'

private theorem leaf5156CoversExact : CoversExact 8
    leaf5156Box leaf5156Certificate leaf5156InnerLog leaf5156Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk228RoundedFacts chi285RoundedFacts
    innerPair249RoundedFacts leaf5156RoundedFacts (by rfl)

private theorem leaf5156FlatSound : Sound leaf5156Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5156CertificateValid
    leaf5156InnerLogValid leaf5156CoversExact leaf5156LowerChecked

private noncomputable def leaf5157Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (243/64), chiLo := (77/256), chiHi := (39/128) }

private noncomputable def leaf5157Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742465/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714624512) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2294831705/2147483648) }, upper := { exponent := 1, mantissa := (17669/16384) } }, logOuter := sk227LogOuterCertificate, logK := sk227LogKCertificate, logChi := chi286LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432036863/137429249024) } }, logDArg := sk227LogDArgCertificate }

private noncomputable def leaf5157InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf5157LocalValidity :
    LeafFacts leaf5157Box leaf5157Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5157Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714624512) }) = true
      norm_num [leaf5157Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5157CertificateValid :
    WideCertificateValid leaf5157Box leaf5157Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk227ValidityFacts chi286ValidityFacts
    leaf5157LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5157CoverageChecked :
    coverageCheck (innerAD leaf5157Box) leaf5157InnerLog = true := by
  rfl'

private theorem leaf5157InnerLogValid :
    leaf5157InnerLog.Valid 8 (innerAD leaf5157Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf5157CoverageChecked

private noncomputable def leaf5157InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629421/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5157InputLogOnePlusV_eq :
    leaf5157InputLogOnePlusV = outerEnclosure 24
      (leaf5157Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5157RoundedFacts : LeafRoundedFacts 8
    leaf5157Certificate.logOnePlusV leaf5157InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5157InputLogOnePlusV_eq }

private noncomputable def leaf5157Inputs : Inputs :=
  inputsOfCaches globalInput sk227RoundedInputs
    chi286InputQChi innerPair249Input
    leaf5157InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5157LowerChecked :
    lowerCheck 24 leaf5157Box leaf5157Inputs = true := by
  rfl'

private theorem leaf5157CoversExact : CoversExact 8
    leaf5157Box leaf5157Certificate leaf5157InnerLog leaf5157Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk227RoundedFacts chi286RoundedFacts
    innerPair249RoundedFacts leaf5157RoundedFacts (by rfl)

private theorem leaf5157FlatSound : Sound leaf5157Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5157CertificateValid
    leaf5157InnerLogValid leaf5157CoversExact leaf5157LowerChecked

private noncomputable def leaf5158Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (243/64), kHi := (61/16), chiLo := (77/256), chiHi := (39/128) }

private noncomputable def leaf5158Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742467/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714604544) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2299877667/2147483648) }, upper := { exponent := 1, mantissa := (4427/4096) } }, logOuter := sk228LogOuterCertificate, logK := sk228LogKCertificate, logChi := chi286LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432016895/137429209088) } }, logDArg := sk228LogDArgCertificate }

private noncomputable def leaf5158InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf5158LocalValidity :
    LeafFacts leaf5158Box leaf5158Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5158Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714604544) }) = true
      norm_num [leaf5158Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5158CertificateValid :
    WideCertificateValid leaf5158Box leaf5158Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk228ValidityFacts chi286ValidityFacts
    leaf5158LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5158CoverageChecked :
    coverageCheck (innerAD leaf5158Box) leaf5158InnerLog = true := by
  rfl'

private theorem leaf5158InnerLogValid :
    leaf5158InnerLog.Valid 8 (innerAD leaf5158Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf5158CoverageChecked

private noncomputable def leaf5158InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726839/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf5158InputLogOnePlusV_eq :
    leaf5158InputLogOnePlusV = outerEnclosure 24
      (leaf5158Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5158RoundedFacts : LeafRoundedFacts 8
    leaf5158Certificate.logOnePlusV leaf5158InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5158InputLogOnePlusV_eq }

private noncomputable def leaf5158Inputs : Inputs :=
  inputsOfCaches globalInput sk228RoundedInputs
    chi286InputQChi innerPair249Input
    leaf5158InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5158LowerChecked :
    lowerCheck 24 leaf5158Box leaf5158Inputs = true := by
  rfl'

private theorem leaf5158CoversExact : CoversExact 8
    leaf5158Box leaf5158Certificate leaf5158InnerLog leaf5158Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk228RoundedFacts chi286RoundedFacts
    innerPair249RoundedFacts leaf5158RoundedFacts (by rfl)

private theorem leaf5158FlatSound : Sound leaf5158Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5158CertificateValid
    leaf5158InnerLogValid leaf5158CoversExact leaf5158LowerChecked

private noncomputable def leaf5159Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (241/64), chiLo := (39/128), chiHi := (79/256) }

private noncomputable def leaf5159Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742463/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22905804117/22904867584) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2300467459/2147483648) }, upper := { exponent := 1, mantissa := (35423/32768) } }, logOuter := sk225LogOuterCertificate, logK := sk225LogKCertificate, logChi := chi287LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45810671701/45809735168) } }, logDArg := sk225LogDArgCertificate }

private noncomputable def leaf5159InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf5159LocalValidity :
    LeafFacts leaf5159Box leaf5159Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5159Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22905804117/22904867584) }) = true
      norm_num [leaf5159Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5159CertificateValid :
    WideCertificateValid leaf5159Box leaf5159Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk225ValidityFacts chi287ValidityFacts
    leaf5159LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5159CoverageChecked :
    coverageCheck (innerAD leaf5159Box) leaf5159InnerLog = true := by
  rfl'

private theorem leaf5159InnerLogValid :
    leaf5159InnerLog.Valid 8 (innerAD leaf5159Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf5159CoverageChecked

private noncomputable def leaf5159InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726839/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf5159InputLogOnePlusV_eq :
    leaf5159InputLogOnePlusV = outerEnclosure 24
      (leaf5159Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5159RoundedFacts : LeafRoundedFacts 8
    leaf5159Certificate.logOnePlusV leaf5159InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5159InputLogOnePlusV_eq }

private noncomputable def leaf5159Inputs : Inputs :=
  inputsOfCaches globalInput sk225RoundedInputs
    chi287InputQChi innerPair249Input
    leaf5159InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5159LowerChecked :
    lowerCheck 24 leaf5159Box leaf5159Inputs = true := by
  rfl'

private theorem leaf5159CoversExact : CoversExact 8
    leaf5159Box leaf5159Certificate leaf5159InnerLog leaf5159Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk225RoundedFacts chi287RoundedFacts
    innerPair249RoundedFacts leaf5159RoundedFacts (by rfl)

private theorem leaf5159FlatSound : Sound leaf5159Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5159CertificateValid
    leaf5159InnerLogValid leaf5159CoversExact leaf5159LowerChecked

private noncomputable def leaf5160Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (241/64), kHi := (121/32), chiLo := (39/128), chiHi := (79/256) }

private noncomputable def leaf5160Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742465/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714582528) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2305578953/2147483648) }, upper := { exponent := 1, mantissa := (17751/16384) } }, logOuter := sk226LogOuterCertificate, logK := sk226LogKCertificate, logChi := chi287LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431994879/137429165056) } }, logDArg := sk226LogDArgCertificate }

private noncomputable def leaf5160InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf5160LocalValidity :
    LeafFacts leaf5160Box leaf5160Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5160Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714582528) }) = true
      norm_num [leaf5160Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5160CertificateValid :
    WideCertificateValid leaf5160Box leaf5160Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk226ValidityFacts chi287ValidityFacts
    leaf5160LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5160CoverageChecked :
    coverageCheck (innerAD leaf5160Box) leaf5160InnerLog = true := by
  rfl'

private theorem leaf5160InnerLogValid :
    leaf5160InnerLog.Valid 8 (innerAD leaf5160Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf5160CoverageChecked

private noncomputable def leaf5160InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814713/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5160InputLogOnePlusV_eq :
    leaf5160InputLogOnePlusV = outerEnclosure 24
      (leaf5160Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5160RoundedFacts : LeafRoundedFacts 8
    leaf5160Certificate.logOnePlusV leaf5160InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5160InputLogOnePlusV_eq }

private noncomputable def leaf5160Inputs : Inputs :=
  inputsOfCaches globalInput sk226RoundedInputs
    chi287InputQChi innerPair249Input
    leaf5160InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5160LowerChecked :
    lowerCheck 24 leaf5160Box leaf5160Inputs = true := by
  rfl'

private theorem leaf5160CoversExact : CoversExact 8
    leaf5160Box leaf5160Certificate leaf5160InnerLog leaf5160Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk226RoundedFacts chi287RoundedFacts
    innerPair249RoundedFacts leaf5160RoundedFacts (by rfl)

private theorem leaf5160FlatSound : Sound leaf5160Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5160CertificateValid
    leaf5160InnerLogValid leaf5160CoversExact leaf5160LowerChecked

private noncomputable def leaf5161Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (241/64), chiLo := (79/256), chiHi := (5/16) }

private noncomputable def leaf5161Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742465/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9816773193/9816363008) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2316195137/2147483648) }, upper := { exponent := 1, mantissa := (2229/2048) } }, logOuter := sk225LogOuterCertificate, logK := sk225LogKCertificate, logChi := chi288LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (19633136201/19632726016) } }, logDArg := sk225LogDArgCertificate }

private noncomputable def leaf5161InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf5161LocalValidity :
    LeafFacts leaf5161Box leaf5161Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5161Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9816773193/9816363008) }) = true
      norm_num [leaf5161Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5161CertificateValid :
    WideCertificateValid leaf5161Box leaf5161Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk225ValidityFacts chi288ValidityFacts
    leaf5161LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5161CoverageChecked :
    coverageCheck (innerAD leaf5161Box) leaf5161InnerLog = true := by
  rfl'

private theorem leaf5161InnerLogValid :
    leaf5161InnerLog.Valid 8 (innerAD leaf5161Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf5161CoverageChecked

private noncomputable def leaf5161InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629431/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5161InputLogOnePlusV_eq :
    leaf5161InputLogOnePlusV = outerEnclosure 24
      (leaf5161Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5161RoundedFacts : LeafRoundedFacts 8
    leaf5161Certificate.logOnePlusV leaf5161InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5161InputLogOnePlusV_eq }

private noncomputable def leaf5161Inputs : Inputs :=
  inputsOfCaches globalInput sk225RoundedInputs
    chi288InputQChi innerPair249Input
    leaf5161InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5161LowerChecked :
    lowerCheck 24 leaf5161Box leaf5161Inputs = true := by
  rfl'

private theorem leaf5161CoversExact : CoversExact 8
    leaf5161Box leaf5161Certificate leaf5161InnerLog leaf5161Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk225RoundedFacts chi288RoundedFacts
    innerPair249RoundedFacts leaf5161RoundedFacts (by rfl)

private theorem leaf5161FlatSound : Sound leaf5161Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5161CertificateValid
    leaf5161InnerLogValid leaf5161CoversExact leaf5161LowerChecked

private noncomputable def leaf5162Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (241/64), kHi := (121/32), chiLo := (79/256), chiHi := (5/16) }

private noncomputable def leaf5162Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742467/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22905804117/22904840192) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2321372163/2147483648) }, upper := { exponent := 1, mantissa := (1117/1024) } }, logOuter := sk226LogOuterCertificate, logK := sk226LogKCertificate, logChi := chi288LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45810644309/45809680384) } }, logDArg := sk226LogDArgCertificate }

private noncomputable def leaf5162InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf5162LocalValidity :
    LeafFacts leaf5162Box leaf5162Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5162Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22905804117/22904840192) }) = true
      norm_num [leaf5162Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5162CertificateValid :
    WideCertificateValid leaf5162Box leaf5162Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk226ValidityFacts chi288ValidityFacts
    leaf5162LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5162CoverageChecked :
    coverageCheck (innerAD leaf5162Box) leaf5162InnerLog = true := by
  rfl'

private theorem leaf5162InnerLogValid :
    leaf5162InnerLog.Valid 8 (innerAD leaf5162Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf5162CoverageChecked

private noncomputable def leaf5162InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814717/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5162InputLogOnePlusV_eq :
    leaf5162InputLogOnePlusV = outerEnclosure 24
      (leaf5162Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5162RoundedFacts : LeafRoundedFacts 8
    leaf5162Certificate.logOnePlusV leaf5162InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5162InputLogOnePlusV_eq }

private noncomputable def leaf5162Inputs : Inputs :=
  inputsOfCaches globalInput sk226RoundedInputs
    chi288InputQChi innerPair249Input
    leaf5162InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5162LowerChecked :
    lowerCheck 24 leaf5162Box leaf5162Inputs = true := by
  rfl'

private theorem leaf5162CoversExact : CoversExact 8
    leaf5162Box leaf5162Certificate leaf5162InnerLog leaf5162Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk226RoundedFacts chi288RoundedFacts
    innerPair249RoundedFacts leaf5162RoundedFacts (by rfl)

private theorem leaf5162FlatSound : Sound leaf5162Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5162CertificateValid
    leaf5162InnerLogValid leaf5162CoversExact leaf5162LowerChecked

private noncomputable def leaf5163Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (243/64), chiLo := (39/128), chiHi := (79/256) }

private noncomputable def leaf5163Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742467/1073741824) }, vSqrt := { lower := (8191/8192), upper := (2216690721/2216598784) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2310690447/2147483648) }, upper := { exponent := 1, mantissa := (35581/32768) } }, logOuter := sk227LogOuterCertificate, logK := sk227LogKCertificate, logChi := chi287LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (4433289505/4433197568) } }, logDArg := sk227LogDArgCertificate }

private noncomputable def leaf5163InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf5163LocalValidity :
    LeafFacts leaf5163Box leaf5163Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5163Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (2216690721/2216598784) }) = true
      norm_num [leaf5163Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5163CertificateValid :
    WideCertificateValid leaf5163Box leaf5163Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk227ValidityFacts chi287ValidityFacts
    leaf5163LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5163CoverageChecked :
    coverageCheck (innerAD leaf5163Box) leaf5163InnerLog = true := by
  rfl'

private theorem leaf5163InnerLogValid :
    leaf5163InnerLog.Valid 8 (innerAD leaf5163Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf5163CoverageChecked

private noncomputable def leaf5163InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629429/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5163InputLogOnePlusV_eq :
    leaf5163InputLogOnePlusV = outerEnclosure 24
      (leaf5163Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5163RoundedFacts : LeafRoundedFacts 8
    leaf5163Certificate.logOnePlusV leaf5163InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5163InputLogOnePlusV_eq }

private noncomputable def leaf5163Inputs : Inputs :=
  inputsOfCaches globalInput sk227RoundedInputs
    chi287InputQChi innerPair249Input
    leaf5163InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5163LowerChecked :
    lowerCheck 24 leaf5163Box leaf5163Inputs = true := by
  rfl'

private theorem leaf5163CoversExact : CoversExact 8
    leaf5163Box leaf5163Certificate leaf5163InnerLog leaf5163Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk227RoundedFacts chi287RoundedFacts
    innerPair249RoundedFacts leaf5163RoundedFacts (by rfl)

private theorem leaf5163FlatSound : Sound leaf5163Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5163CertificateValid
    leaf5163InnerLogValid leaf5163CoversExact leaf5163LowerChecked

private noncomputable def leaf5164Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (243/64), kHi := (61/16), chiLo := (39/128), chiHi := (79/256) }

private noncomputable def leaf5164Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742469/1073741824) }, vSqrt := { lower := (8191/8192), upper := (7635268039/7634949120) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2315801941/2147483648) }, upper := { exponent := 1, mantissa := (8915/8192) } }, logOuter := sk228LogOuterCertificate, logK := sk228LogKCertificate, logChi := chi287LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (15270217159/15269898240) } }, logDArg := sk228LogDArgCertificate }

private noncomputable def leaf5164InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf5164LocalValidity :
    LeafFacts leaf5164Box leaf5164Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5164Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (7635268039/7634949120) }) = true
      norm_num [leaf5164Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5164CertificateValid :
    WideCertificateValid leaf5164Box leaf5164Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk228ValidityFacts chi287ValidityFacts
    leaf5164LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5164CoverageChecked :
    coverageCheck (innerAD leaf5164Box) leaf5164InnerLog = true := by
  rfl'

private theorem leaf5164InnerLogValid :
    leaf5164InnerLog.Valid 8 (innerAD leaf5164Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf5164CoverageChecked

private noncomputable def leaf5164InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629431/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5164InputLogOnePlusV_eq :
    leaf5164InputLogOnePlusV = outerEnclosure 24
      (leaf5164Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5164RoundedFacts : LeafRoundedFacts 8
    leaf5164Certificate.logOnePlusV leaf5164InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5164InputLogOnePlusV_eq }

private noncomputable def leaf5164Inputs : Inputs :=
  inputsOfCaches globalInput sk228RoundedInputs
    chi287InputQChi innerPair249Input
    leaf5164InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5164LowerChecked :
    lowerCheck 24 leaf5164Box leaf5164Inputs = true := by
  rfl'

private theorem leaf5164CoversExact : CoversExact 8
    leaf5164Box leaf5164Certificate leaf5164InnerLog leaf5164Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk228RoundedFacts chi287RoundedFacts
    innerPair249RoundedFacts leaf5164RoundedFacts (by rfl)

private theorem leaf5164FlatSound : Sound leaf5164Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5164CertificateValid
    leaf5164InnerLogValid leaf5164CoversExact leaf5164LowerChecked

private noncomputable def leaf5165Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (243/64), chiLo := (79/256), chiHi := (5/16) }

private noncomputable def leaf5165Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742469/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714500096) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2326549189/2147483648) }, upper := { exponent := 1, mantissa := (2239/2048) } }, logOuter := sk227LogOuterCertificate, logK := sk227LogKCertificate, logChi := chi288LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431912447/137429000192) } }, logDArg := sk227LogDArgCertificate }

private noncomputable def leaf5165InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf5165LocalValidity :
    LeafFacts leaf5165Box leaf5165Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5165Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714500096) }) = true
      norm_num [leaf5165Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5165CertificateValid :
    WideCertificateValid leaf5165Box leaf5165Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk227ValidityFacts chi288ValidityFacts
    leaf5165LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5165CoverageChecked :
    coverageCheck (innerAD leaf5165Box) leaf5165InnerLog = true := by
  rfl'

private theorem leaf5165InnerLogValid :
    leaf5165InnerLog.Valid 8 (innerAD leaf5165Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf5165CoverageChecked

private noncomputable def leaf5165InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907359/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5165InputLogOnePlusV_eq :
    leaf5165InputLogOnePlusV = outerEnclosure 24
      (leaf5165Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5165RoundedFacts : LeafRoundedFacts 8
    leaf5165Certificate.logOnePlusV leaf5165InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5165InputLogOnePlusV_eq }

private noncomputable def leaf5165Inputs : Inputs :=
  inputsOfCaches globalInput sk227RoundedInputs
    chi288InputQChi innerPair249Input
    leaf5165InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5165LowerChecked :
    lowerCheck 24 leaf5165Box leaf5165Inputs = true := by
  rfl'

private theorem leaf5165CoversExact : CoversExact 8
    leaf5165Box leaf5165Certificate leaf5165InnerLog leaf5165Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk227RoundedFacts chi288RoundedFacts
    innerPair249RoundedFacts leaf5165RoundedFacts (by rfl)

private theorem leaf5165FlatSound : Sound leaf5165Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5165CertificateValid
    leaf5165InnerLogValid leaf5165CoversExact leaf5165LowerChecked

private noncomputable def leaf5166Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (243/64), kHi := (61/16), chiLo := (79/256), chiHi := (5/16) }

private noncomputable def leaf5166Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742471/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714479616) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2331726215/2147483648) }, upper := { exponent := 1, mantissa := (561/512) } }, logOuter := sk228LogOuterCertificate, logK := sk228LogKCertificate, logChi := chi288LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431891967/137428959232) } }, logDArg := sk228LogDArgCertificate }

private noncomputable def leaf5166InnerLog : WideLogData :=
  innerPair332Data

set_option maxRecDepth 1000000 in
private theorem leaf5166LocalValidity :
    LeafFacts leaf5166Box leaf5166Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5166Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714479616) }) = true
      norm_num [leaf5166Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5166CertificateValid :
    WideCertificateValid leaf5166Box leaf5166Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk228ValidityFacts chi288ValidityFacts
    leaf5166LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5166CoverageChecked :
    coverageCheck (innerAD leaf5166Box) leaf5166InnerLog = true := by
  rfl'

private theorem leaf5166InnerLogValid :
    leaf5166InnerLog.Valid 8 (innerAD leaf5166Box) :=
  wideLogDataValid_of_cachedCheck endpoint88PositiveFacts
    endpoint291PositiveFacts.valid leaf5166CoverageChecked

private noncomputable def leaf5166InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629439/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5166InputLogOnePlusV_eq :
    leaf5166InputLogOnePlusV = outerEnclosure 24
      (leaf5166Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5166RoundedFacts : LeafRoundedFacts 8
    leaf5166Certificate.logOnePlusV leaf5166InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5166InputLogOnePlusV_eq }

private noncomputable def leaf5166Inputs : Inputs :=
  inputsOfCaches globalInput sk228RoundedInputs
    chi288InputQChi innerPair332Input
    leaf5166InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5166LowerChecked :
    lowerCheck 24 leaf5166Box leaf5166Inputs = true := by
  rfl'

private theorem leaf5166CoversExact : CoversExact 8
    leaf5166Box leaf5166Certificate leaf5166InnerLog leaf5166Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk228RoundedFacts chi288RoundedFacts
    innerPair332RoundedFacts leaf5166RoundedFacts (by rfl)

private theorem leaf5166FlatSound : Sound leaf5166Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5166CertificateValid
    leaf5166InnerLogValid leaf5166CoversExact leaf5166LowerChecked

private noncomputable def leaf5167Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (245/64), chiLo := (19/64), chiHi := (77/256) }

private noncomputable def leaf5167Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742467/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22905804117/22904882432) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2288933823/2147483648) }, upper := { exponent := 1, mantissa := (35249/32768) } }, logOuter := sk229LogOuterCertificate, logK := sk229LogKCertificate, logChi := chi285LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45810686549/45809764864) } }, logDArg := sk229LogDArgCertificate }

private noncomputable def leaf5167InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf5167LocalValidity :
    LeafFacts leaf5167Box leaf5167Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5167Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22905804117/22904882432) }) = true
      norm_num [leaf5167Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5167CertificateValid :
    WideCertificateValid leaf5167Box leaf5167Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk229ValidityFacts chi285ValidityFacts
    leaf5167LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5167CoverageChecked :
    coverageCheck (innerAD leaf5167Box) leaf5167InnerLog = true := by
  rfl'

private theorem leaf5167InnerLogValid :
    leaf5167InnerLog.Valid 8 (innerAD leaf5167Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf5167CoverageChecked

private noncomputable def leaf5167InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814709/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5167InputLogOnePlusV_eq :
    leaf5167InputLogOnePlusV = outerEnclosure 24
      (leaf5167Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5167RoundedFacts : LeafRoundedFacts 8
    leaf5167Certificate.logOnePlusV leaf5167InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5167InputLogOnePlusV_eq }

private noncomputable def leaf5167Inputs : Inputs :=
  inputsOfCaches globalInput sk229RoundedInputs
    chi285InputQChi innerPair249Input
    leaf5167InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5167LowerChecked :
    lowerCheck 24 leaf5167Box leaf5167Inputs = true := by
  rfl'

private theorem leaf5167CoversExact : CoversExact 8
    leaf5167Box leaf5167Certificate leaf5167InnerLog leaf5167Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk229RoundedFacts chi285RoundedFacts
    innerPair249RoundedFacts leaf5167RoundedFacts (by rfl)

private theorem leaf5167FlatSound : Sound leaf5167Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5167CertificateValid
    leaf5167InnerLogValid leaf5167CoversExact leaf5167LowerChecked

private noncomputable def leaf5168Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (245/64), kHi := (123/32), chiLo := (19/64), chiHi := (77/256) }

private noncomputable def leaf5168Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742469/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714627584) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2293914253/2147483648) }, upper := { exponent := 1, mantissa := (17663/16384) } }, logOuter := sk230LogOuterCertificate, logK := sk230LogKCertificate, logChi := chi285LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432039935/137429255168) } }, logDArg := sk230LogDArgCertificate }

private noncomputable def leaf5168InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf5168LocalValidity :
    LeafFacts leaf5168Box leaf5168Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5168Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714627584) }) = true
      norm_num [leaf5168Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5168CertificateValid :
    WideCertificateValid leaf5168Box leaf5168Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk230ValidityFacts chi285ValidityFacts
    leaf5168LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5168CoverageChecked :
    coverageCheck (innerAD leaf5168Box) leaf5168InnerLog = true := by
  rfl'

private theorem leaf5168InnerLogValid :
    leaf5168InnerLog.Valid 8 (innerAD leaf5168Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf5168CoverageChecked

private noncomputable def leaf5168InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629421/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5168InputLogOnePlusV_eq :
    leaf5168InputLogOnePlusV = outerEnclosure 24
      (leaf5168Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5168RoundedFacts : LeafRoundedFacts 8
    leaf5168Certificate.logOnePlusV leaf5168InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5168InputLogOnePlusV_eq }

private noncomputable def leaf5168Inputs : Inputs :=
  inputsOfCaches globalInput sk230RoundedInputs
    chi285InputQChi innerPair249Input
    leaf5168InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5168LowerChecked :
    lowerCheck 24 leaf5168Box leaf5168Inputs = true := by
  rfl'

private theorem leaf5168CoversExact : CoversExact 8
    leaf5168Box leaf5168Certificate leaf5168InnerLog leaf5168Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk230RoundedFacts chi285RoundedFacts
    innerPair249RoundedFacts leaf5168RoundedFacts (by rfl)

private theorem leaf5168FlatSound : Sound leaf5168Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5168CertificateValid
    leaf5168InnerLogValid leaf5168CoversExact leaf5168LowerChecked

private noncomputable def leaf5169Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (245/64), chiLo := (77/256), chiHi := (39/128) }

private noncomputable def leaf5169Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742469/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714584576) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2304923629/2147483648) }, upper := { exponent := 1, mantissa := (17747/16384) } }, logOuter := sk229LogOuterCertificate, logK := sk229LogKCertificate, logChi := chi286LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431996927/137429169152) } }, logDArg := sk229LogDArgCertificate }

private noncomputable def leaf5169InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf5169LocalValidity :
    LeafFacts leaf5169Box leaf5169Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5169Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714584576) }) = true
      norm_num [leaf5169Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5169CertificateValid :
    WideCertificateValid leaf5169Box leaf5169Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk229ValidityFacts chi286ValidityFacts
    leaf5169LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5169CoverageChecked :
    coverageCheck (innerAD leaf5169Box) leaf5169InnerLog = true := by
  rfl'

private theorem leaf5169InnerLogValid :
    leaf5169InnerLog.Valid 8 (innerAD leaf5169Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf5169CoverageChecked

private noncomputable def leaf5169InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814713/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5169InputLogOnePlusV_eq :
    leaf5169InputLogOnePlusV = outerEnclosure 24
      (leaf5169Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5169RoundedFacts : LeafRoundedFacts 8
    leaf5169Certificate.logOnePlusV leaf5169InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5169InputLogOnePlusV_eq }

private noncomputable def leaf5169Inputs : Inputs :=
  inputsOfCaches globalInput sk229RoundedInputs
    chi286InputQChi innerPair249Input
    leaf5169InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5169LowerChecked :
    lowerCheck 24 leaf5169Box leaf5169Inputs = true := by
  rfl'

private theorem leaf5169CoversExact : CoversExact 8
    leaf5169Box leaf5169Certificate leaf5169InnerLog leaf5169Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk229RoundedFacts chi286RoundedFacts
    innerPair249RoundedFacts leaf5169RoundedFacts (by rfl)

private theorem leaf5169FlatSound : Sound leaf5169Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5169CertificateValid
    leaf5169InnerLogValid leaf5169CoversExact leaf5169LowerChecked

private noncomputable def leaf5170Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (245/64), kHi := (123/32), chiLo := (77/256), chiHi := (39/128) }

private noncomputable def leaf5170Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742471/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714564608) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2309969591/2147483648) }, upper := { exponent := 1, mantissa := (8893/8192) } }, logOuter := sk230LogOuterCertificate, logK := sk230LogKCertificate, logChi := chi286LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431976959/137429129216) } }, logDArg := sk230LogDArgCertificate }

private noncomputable def leaf5170InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf5170LocalValidity :
    LeafFacts leaf5170Box leaf5170Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5170Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714564608) }) = true
      norm_num [leaf5170Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5170CertificateValid :
    WideCertificateValid leaf5170Box leaf5170Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk230ValidityFacts chi286ValidityFacts
    leaf5170LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5170CoverageChecked :
    coverageCheck (innerAD leaf5170Box) leaf5170InnerLog = true := by
  rfl'

private theorem leaf5170InnerLogValid :
    leaf5170InnerLog.Valid 8 (innerAD leaf5170Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf5170CoverageChecked

private noncomputable def leaf5170InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907357/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5170InputLogOnePlusV_eq :
    leaf5170InputLogOnePlusV = outerEnclosure 24
      (leaf5170Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5170RoundedFacts : LeafRoundedFacts 8
    leaf5170Certificate.logOnePlusV leaf5170InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5170InputLogOnePlusV_eq }

private noncomputable def leaf5170Inputs : Inputs :=
  inputsOfCaches globalInput sk230RoundedInputs
    chi286InputQChi innerPair249Input
    leaf5170InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5170LowerChecked :
    lowerCheck 24 leaf5170Box leaf5170Inputs = true := by
  rfl'

private theorem leaf5170CoversExact : CoversExact 8
    leaf5170Box leaf5170Certificate leaf5170InnerLog leaf5170Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk230RoundedFacts chi286RoundedFacts
    innerPair249RoundedFacts leaf5170RoundedFacts (by rfl)

private theorem leaf5170FlatSound : Sound leaf5170Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5170CertificateValid
    leaf5170InnerLogValid leaf5170CoversExact leaf5170LowerChecked

private noncomputable def leaf5171Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (247/64), chiLo := (19/64), chiHi := (77/256) }

private noncomputable def leaf5171Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742471/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714607872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2298894683/2147483648) }, upper := { exponent := 1, mantissa := (35403/32768) } }, logOuter := sk231LogOuterCertificate, logK := sk231LogKCertificate, logChi := chi285LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432020223/137429215744) } }, logDArg := sk231LogDArgCertificate }

private noncomputable def leaf5171InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf5171LocalValidity :
    LeafFacts leaf5171Box leaf5171Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5171Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714607872) }) = true
      norm_num [leaf5171Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5171CertificateValid :
    WideCertificateValid leaf5171Box leaf5171Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk231ValidityFacts chi285ValidityFacts
    leaf5171LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5171CoverageChecked :
    coverageCheck (innerAD leaf5171Box) leaf5171InnerLog = true := by
  rfl'

private theorem leaf5171InnerLogValid :
    leaf5171InnerLog.Valid 8 (innerAD leaf5171Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf5171CoverageChecked

private noncomputable def leaf5171InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629423/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5171InputLogOnePlusV_eq :
    leaf5171InputLogOnePlusV = outerEnclosure 24
      (leaf5171Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5171RoundedFacts : LeafRoundedFacts 8
    leaf5171Certificate.logOnePlusV leaf5171InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5171InputLogOnePlusV_eq }

private noncomputable def leaf5171Inputs : Inputs :=
  inputsOfCaches globalInput sk231RoundedInputs
    chi285InputQChi innerPair249Input
    leaf5171InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5171LowerChecked :
    lowerCheck 24 leaf5171Box leaf5171Inputs = true := by
  rfl'

private theorem leaf5171CoversExact : CoversExact 8
    leaf5171Box leaf5171Certificate leaf5171InnerLog leaf5171Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk231RoundedFacts chi285RoundedFacts
    innerPair249RoundedFacts leaf5171RoundedFacts (by rfl)

private theorem leaf5171FlatSound : Sound leaf5171Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5171CertificateValid
    leaf5171InnerLogValid leaf5171CoversExact leaf5171LowerChecked

private noncomputable def leaf5172Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (247/64), kHi := (31/8), chiLo := (19/64), chiHi := (77/256) }

private noncomputable def leaf5172Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742473/1073741824) }, vSqrt := { lower := (8191/8192), upper := (7635268039/7634954240) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2303875113/2147483648) }, upper := { exponent := 1, mantissa := (4435/4096) } }, logOuter := sk232LogOuterCertificate, logK := sk232LogKCertificate, logChi := chi285LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (15270222279/15269908480) } }, logDArg := sk232LogDArgCertificate }

private noncomputable def leaf5172InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf5172LocalValidity :
    LeafFacts leaf5172Box leaf5172Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5172Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (7635268039/7634954240) }) = true
      norm_num [leaf5172Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5172CertificateValid :
    WideCertificateValid leaf5172Box leaf5172Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk232ValidityFacts chi285ValidityFacts
    leaf5172LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5172CoverageChecked :
    coverageCheck (innerAD leaf5172Box) leaf5172InnerLog = true := by
  rfl'

private theorem leaf5172InnerLogValid :
    leaf5172InnerLog.Valid 8 (innerAD leaf5172Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf5172CoverageChecked

private noncomputable def leaf5172InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814713/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5172InputLogOnePlusV_eq :
    leaf5172InputLogOnePlusV = outerEnclosure 24
      (leaf5172Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5172RoundedFacts : LeafRoundedFacts 8
    leaf5172Certificate.logOnePlusV leaf5172InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5172InputLogOnePlusV_eq }

private noncomputable def leaf5172Inputs : Inputs :=
  inputsOfCaches globalInput sk232RoundedInputs
    chi285InputQChi innerPair249Input
    leaf5172InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5172LowerChecked :
    lowerCheck 24 leaf5172Box leaf5172Inputs = true := by
  rfl'

private theorem leaf5172CoversExact : CoversExact 8
    leaf5172Box leaf5172Certificate leaf5172InnerLog leaf5172Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk232RoundedFacts chi285RoundedFacts
    innerPair249RoundedFacts leaf5172RoundedFacts (by rfl)

private theorem leaf5172FlatSound : Sound leaf5172Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5172CertificateValid
    leaf5172InnerLogValid leaf5172CoversExact leaf5172LowerChecked

private noncomputable def leaf5173Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (247/64), chiLo := (77/256), chiHi := (39/128) }

private noncomputable def leaf5173Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742473/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9816773193/9816363520) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2315015553/2147483648) }, upper := { exponent := 1, mantissa := (17825/16384) } }, logOuter := sk231LogOuterCertificate, logK := sk231LogKCertificate, logChi := chi286LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (19633136713/19632727040) } }, logDArg := sk231LogDArgCertificate }

private noncomputable def leaf5173InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf5173LocalValidity :
    LeafFacts leaf5173Box leaf5173Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5173Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9816773193/9816363520) }) = true
      norm_num [leaf5173Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5173CertificateValid :
    WideCertificateValid leaf5173Box leaf5173Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk231ValidityFacts chi286ValidityFacts
    leaf5173LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5173CoverageChecked :
    coverageCheck (innerAD leaf5173Box) leaf5173InnerLog = true := by
  rfl'

private theorem leaf5173InnerLogValid :
    leaf5173InnerLog.Valid 8 (innerAD leaf5173Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf5173CoverageChecked

private noncomputable def leaf5173InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629431/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5173InputLogOnePlusV_eq :
    leaf5173InputLogOnePlusV = outerEnclosure 24
      (leaf5173Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5173RoundedFacts : LeafRoundedFacts 8
    leaf5173Certificate.logOnePlusV leaf5173InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5173InputLogOnePlusV_eq }

private noncomputable def leaf5173Inputs : Inputs :=
  inputsOfCaches globalInput sk231RoundedInputs
    chi286InputQChi innerPair249Input
    leaf5173InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5173LowerChecked :
    lowerCheck 24 leaf5173Box leaf5173Inputs = true := by
  rfl'

private theorem leaf5173CoversExact : CoversExact 8
    leaf5173Box leaf5173Certificate leaf5173InnerLog leaf5173Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk231RoundedFacts chi286RoundedFacts
    innerPair249RoundedFacts leaf5173RoundedFacts (by rfl)

private theorem leaf5173FlatSound : Sound leaf5173Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5173CertificateValid
    leaf5173InnerLogValid leaf5173CoversExact leaf5173LowerChecked

private noncomputable def leaf5174Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (247/64), kHi := (31/8), chiLo := (77/256), chiHi := (39/128) }

private noncomputable def leaf5174Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742475/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714524672) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2320061515/2147483648) }, upper := { exponent := 1, mantissa := (2233/2048) } }, logOuter := sk232LogOuterCertificate, logK := sk232LogKCertificate, logChi := chi286LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431937023/137429049344) } }, logDArg := sk232LogDArgCertificate }

private noncomputable def leaf5174InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf5174LocalValidity :
    LeafFacts leaf5174Box leaf5174Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5174Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714524672) }) = true
      norm_num [leaf5174Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5174CertificateValid :
    WideCertificateValid leaf5174Box leaf5174Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk232ValidityFacts chi286ValidityFacts
    leaf5174LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5174CoverageChecked :
    coverageCheck (innerAD leaf5174Box) leaf5174InnerLog = true := by
  rfl'

private theorem leaf5174InnerLogValid :
    leaf5174InnerLog.Valid 8 (innerAD leaf5174Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf5174CoverageChecked

private noncomputable def leaf5174InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629433/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5174InputLogOnePlusV_eq :
    leaf5174InputLogOnePlusV = outerEnclosure 24
      (leaf5174Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5174RoundedFacts : LeafRoundedFacts 8
    leaf5174Certificate.logOnePlusV leaf5174InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5174InputLogOnePlusV_eq }

private noncomputable def leaf5174Inputs : Inputs :=
  inputsOfCaches globalInput sk232RoundedInputs
    chi286InputQChi innerPair249Input
    leaf5174InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5174LowerChecked :
    lowerCheck 24 leaf5174Box leaf5174Inputs = true := by
  rfl'

private theorem leaf5174CoversExact : CoversExact 8
    leaf5174Box leaf5174Certificate leaf5174InnerLog leaf5174Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk232RoundedFacts chi286RoundedFacts
    innerPair249RoundedFacts leaf5174RoundedFacts (by rfl)

private theorem leaf5174FlatSound : Sound leaf5174Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5174CertificateValid
    leaf5174InnerLogValid leaf5174CoversExact leaf5174LowerChecked

private noncomputable def leaf5175Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (245/64), chiLo := (39/128), chiHi := (79/256) }

private noncomputable def leaf5175Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742471/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714521856) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2320913435/2147483648) }, upper := { exponent := 1, mantissa := (35739/32768) } }, logOuter := sk229LogOuterCertificate, logK := sk229LogKCertificate, logChi := chi287LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431934207/137429043712) } }, logDArg := sk229LogDArgCertificate }

private noncomputable def leaf5175InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf5175LocalValidity :
    LeafFacts leaf5175Box leaf5175Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5175Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714521856) }) = true
      norm_num [leaf5175Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5175CertificateValid :
    WideCertificateValid leaf5175Box leaf5175Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk229ValidityFacts chi287ValidityFacts
    leaf5175LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5175CoverageChecked :
    coverageCheck (innerAD leaf5175Box) leaf5175InnerLog = true := by
  rfl'

private theorem leaf5175InnerLogValid :
    leaf5175InnerLog.Valid 8 (innerAD leaf5175Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf5175CoverageChecked

private noncomputable def leaf5175InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814717/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5175InputLogOnePlusV_eq :
    leaf5175InputLogOnePlusV = outerEnclosure 24
      (leaf5175Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5175RoundedFacts : LeafRoundedFacts 8
    leaf5175Certificate.logOnePlusV leaf5175InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5175InputLogOnePlusV_eq }

private noncomputable def leaf5175Inputs : Inputs :=
  inputsOfCaches globalInput sk229RoundedInputs
    chi287InputQChi innerPair249Input
    leaf5175InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5175LowerChecked :
    lowerCheck 24 leaf5175Box leaf5175Inputs = true := by
  rfl'

private theorem leaf5175CoversExact : CoversExact 8
    leaf5175Box leaf5175Certificate leaf5175InnerLog leaf5175Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk229RoundedFacts chi287RoundedFacts
    innerPair249RoundedFacts leaf5175RoundedFacts (by rfl)

private theorem leaf5175FlatSound : Sound leaf5175Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5175CertificateValid
    leaf5175InnerLogValid leaf5175CoversExact leaf5175LowerChecked

private noncomputable def leaf5176Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (245/64), kHi := (123/32), chiLo := (39/128), chiHi := (79/256) }

private noncomputable def leaf5176Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742473/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9816773193/9816357376) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2326024929/2147483648) }, upper := { exponent := 1, mantissa := (17909/16384) } }, logOuter := sk230LogOuterCertificate, logK := sk230LogKCertificate, logChi := chi287LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (19633130569/19632714752) } }, logDArg := sk230LogDArgCertificate }

private noncomputable def leaf5176InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf5176LocalValidity :
    LeafFacts leaf5176Box leaf5176Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5176Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9816773193/9816357376) }) = true
      norm_num [leaf5176Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5176CertificateValid :
    WideCertificateValid leaf5176Box leaf5176Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk230ValidityFacts chi287ValidityFacts
    leaf5176LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5176CoverageChecked :
    coverageCheck (innerAD leaf5176Box) leaf5176InnerLog = true := by
  rfl'

private theorem leaf5176InnerLogValid :
    leaf5176InnerLog.Valid 8 (innerAD leaf5176Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf5176CoverageChecked

private noncomputable def leaf5176InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907359/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5176InputLogOnePlusV_eq :
    leaf5176InputLogOnePlusV = outerEnclosure 24
      (leaf5176Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5176RoundedFacts : LeafRoundedFacts 8
    leaf5176Certificate.logOnePlusV leaf5176InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5176InputLogOnePlusV_eq }

private noncomputable def leaf5176Inputs : Inputs :=
  inputsOfCaches globalInput sk230RoundedInputs
    chi287InputQChi innerPair249Input
    leaf5176InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5176LowerChecked :
    lowerCheck 24 leaf5176Box leaf5176Inputs = true := by
  rfl'

private theorem leaf5176CoversExact : CoversExact 8
    leaf5176Box leaf5176Certificate leaf5176InnerLog leaf5176Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk230RoundedFacts chi287RoundedFacts
    innerPair249RoundedFacts leaf5176RoundedFacts (by rfl)

private theorem leaf5176FlatSound : Sound leaf5176Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5176CertificateValid
    leaf5176InnerLogValid leaf5176CoversExact leaf5176LowerChecked

private noncomputable def leaf5177Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (245/64), chiLo := (79/256), chiHi := (5/16) }

private noncomputable def leaf5177Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742473/1073741824) }, vSqrt := { lower := (8191/8192), upper := (246298969/246288384) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2336903241/2147483648) }, upper := { exponent := 1, mantissa := (2249/2048) } }, logOuter := sk229LogOuterCertificate, logK := sk229LogKCertificate, logChi := chi288LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (492587353/492576768) } }, logDArg := sk229LogDArgCertificate }

private noncomputable def leaf5177InnerLog : WideLogData :=
  innerPair250Data

set_option maxRecDepth 1000000 in
private theorem leaf5177LocalValidity :
    LeafFacts leaf5177Box leaf5177Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5177Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (246298969/246288384) }) = true
      norm_num [leaf5177Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5177CertificateValid :
    WideCertificateValid leaf5177Box leaf5177Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk229ValidityFacts chi288ValidityFacts
    leaf5177LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5177CoverageChecked :
    coverageCheck (innerAD leaf5177Box) leaf5177InnerLog = true := by
  rfl'

private theorem leaf5177InnerLogValid :
    leaf5177InnerLog.Valid 8 (innerAD leaf5177Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint75PositiveFacts.valid leaf5177CoverageChecked

private noncomputable def leaf5177InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629441/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5177InputLogOnePlusV_eq :
    leaf5177InputLogOnePlusV = outerEnclosure 24
      (leaf5177Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5177RoundedFacts : LeafRoundedFacts 8
    leaf5177Certificate.logOnePlusV leaf5177InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5177InputLogOnePlusV_eq }

private noncomputable def leaf5177Inputs : Inputs :=
  inputsOfCaches globalInput sk229RoundedInputs
    chi288InputQChi innerPair250Input
    leaf5177InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5177LowerChecked :
    lowerCheck 24 leaf5177Box leaf5177Inputs = true := by
  rfl'

private theorem leaf5177CoversExact : CoversExact 8
    leaf5177Box leaf5177Certificate leaf5177InnerLog leaf5177Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk229RoundedFacts chi288RoundedFacts
    innerPair250RoundedFacts leaf5177RoundedFacts (by rfl)

private theorem leaf5177FlatSound : Sound leaf5177Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5177CertificateValid
    leaf5177InnerLogValid leaf5177CoversExact leaf5177LowerChecked

private noncomputable def leaf5178Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (245/64), kHi := (123/32), chiLo := (79/256), chiHi := (5/16) }

private noncomputable def leaf5178Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742475/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714438656) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2342080267/2147483648) }, upper := { exponent := 1, mantissa := (1127/1024) } }, logOuter := sk230LogOuterCertificate, logK := sk230LogKCertificate, logChi := chi288LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431851007/137428877312) } }, logDArg := sk230LogDArgCertificate }

private noncomputable def leaf5178InnerLog : WideLogData :=
  innerPair250Data

set_option maxRecDepth 1000000 in
private theorem leaf5178LocalValidity :
    LeafFacts leaf5178Box leaf5178Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5178Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714438656) }) = true
      norm_num [leaf5178Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5178CertificateValid :
    WideCertificateValid leaf5178Box leaf5178Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk230ValidityFacts chi288ValidityFacts
    leaf5178LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5178CoverageChecked :
    coverageCheck (innerAD leaf5178Box) leaf5178InnerLog = true := by
  rfl'

private theorem leaf5178InnerLogValid :
    leaf5178InnerLog.Valid 8 (innerAD leaf5178Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint75PositiveFacts.valid leaf5178CoverageChecked

private noncomputable def leaf5178InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907361/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5178InputLogOnePlusV_eq :
    leaf5178InputLogOnePlusV = outerEnclosure 24
      (leaf5178Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5178RoundedFacts : LeafRoundedFacts 8
    leaf5178Certificate.logOnePlusV leaf5178InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5178InputLogOnePlusV_eq }

private noncomputable def leaf5178Inputs : Inputs :=
  inputsOfCaches globalInput sk230RoundedInputs
    chi288InputQChi innerPair250Input
    leaf5178InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5178LowerChecked :
    lowerCheck 24 leaf5178Box leaf5178Inputs = true := by
  rfl'

private theorem leaf5178CoversExact : CoversExact 8
    leaf5178Box leaf5178Certificate leaf5178InnerLog leaf5178Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk230RoundedFacts chi288RoundedFacts
    innerPair250RoundedFacts leaf5178RoundedFacts (by rfl)

private theorem leaf5178FlatSound : Sound leaf5178Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5178CertificateValid
    leaf5178InnerLogValid leaf5178CoversExact leaf5178LowerChecked

private noncomputable def leaf5179Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (247/64), chiLo := (39/128), chiHi := (79/256) }

private noncomputable def leaf5179Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742475/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22905804117/22904827136) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2331136423/2147483648) }, upper := { exponent := 1, mantissa := (35897/32768) } }, logOuter := sk231LogOuterCertificate, logK := sk231LogKCertificate, logChi := chi287LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45810631253/45809654272) } }, logDArg := sk231LogDArgCertificate }

private noncomputable def leaf5179InnerLog : WideLogData :=
  innerPair332Data

set_option maxRecDepth 1000000 in
private theorem leaf5179LocalValidity :
    LeafFacts leaf5179Box leaf5179Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5179Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22905804117/22904827136) }) = true
      norm_num [leaf5179Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5179CertificateValid :
    WideCertificateValid leaf5179Box leaf5179Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk231ValidityFacts chi287ValidityFacts
    leaf5179LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5179CoverageChecked :
    coverageCheck (innerAD leaf5179Box) leaf5179InnerLog = true := by
  rfl'

private theorem leaf5179InnerLogValid :
    leaf5179InnerLog.Valid 8 (innerAD leaf5179Box) :=
  wideLogDataValid_of_cachedCheck endpoint88PositiveFacts
    endpoint291PositiveFacts.valid leaf5179CoverageChecked

private noncomputable def leaf5179InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629439/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5179InputLogOnePlusV_eq :
    leaf5179InputLogOnePlusV = outerEnclosure 24
      (leaf5179Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5179RoundedFacts : LeafRoundedFacts 8
    leaf5179Certificate.logOnePlusV leaf5179InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5179InputLogOnePlusV_eq }

private noncomputable def leaf5179Inputs : Inputs :=
  inputsOfCaches globalInput sk231RoundedInputs
    chi287InputQChi innerPair332Input
    leaf5179InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5179LowerChecked :
    lowerCheck 24 leaf5179Box leaf5179Inputs = true := by
  rfl'

private theorem leaf5179CoversExact : CoversExact 8
    leaf5179Box leaf5179Certificate leaf5179InnerLog leaf5179Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk231RoundedFacts chi287RoundedFacts
    innerPair332RoundedFacts leaf5179RoundedFacts (by rfl)

private theorem leaf5179FlatSound : Sound leaf5179Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5179CertificateValid
    leaf5179InnerLogValid leaf5179CoversExact leaf5179LowerChecked

private noncomputable def leaf5180Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (247/64), kHi := (31/8), chiLo := (39/128), chiHi := (79/256) }

private noncomputable def leaf5180Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742477/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714461184) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2336247917/2147483648) }, upper := { exponent := 1, mantissa := (4497/4096) } }, logOuter := sk232LogOuterCertificate, logK := sk232LogKCertificate, logChi := chi287LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431873535/137428922368) } }, logDArg := sk232LogDArgCertificate }

private noncomputable def leaf5180InnerLog : WideLogData :=
  innerPair612Data

set_option maxRecDepth 1000000 in
private theorem leaf5180LocalValidity :
    LeafFacts leaf5180Box leaf5180Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5180Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714461184) }) = true
      norm_num [leaf5180Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5180CertificateValid :
    WideCertificateValid leaf5180Box leaf5180Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk232ValidityFacts chi287ValidityFacts
    leaf5180LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5180CoverageChecked :
    coverageCheck (innerAD leaf5180Box) leaf5180InnerLog = true := by
  rfl'

private theorem leaf5180InnerLogValid :
    leaf5180InnerLog.Valid 8 (innerAD leaf5180Box) :=
  wideLogDataValid_of_cachedCheck endpoint337PositiveFacts
    endpoint291PositiveFacts.valid leaf5180CoverageChecked

private noncomputable def leaf5180InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629441/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5180InputLogOnePlusV_eq :
    leaf5180InputLogOnePlusV = outerEnclosure 24
      (leaf5180Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5180RoundedFacts : LeafRoundedFacts 8
    leaf5180Certificate.logOnePlusV leaf5180InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5180InputLogOnePlusV_eq }

private noncomputable def leaf5180Inputs : Inputs :=
  inputsOfCaches globalInput sk232RoundedInputs
    chi287InputQChi innerPair612Input
    leaf5180InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5180LowerChecked :
    lowerCheck 24 leaf5180Box leaf5180Inputs = true := by
  rfl'

private theorem leaf5180CoversExact : CoversExact 8
    leaf5180Box leaf5180Certificate leaf5180InnerLog leaf5180Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk232RoundedFacts chi287RoundedFacts
    innerPair612RoundedFacts leaf5180RoundedFacts (by rfl)

private theorem leaf5180FlatSound : Sound leaf5180Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5180CertificateValid
    leaf5180InnerLogValid leaf5180CoversExact leaf5180LowerChecked

private noncomputable def leaf5181Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (247/64), chiLo := (79/256), chiHi := (5/16) }

private noncomputable def leaf5181Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742477/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714418176) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2347257293/2147483648) }, upper := { exponent := 1, mantissa := (2259/2048) } }, logOuter := sk231LogOuterCertificate, logK := sk231LogKCertificate, logChi := chi288LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431830527/137428836352) } }, logDArg := sk231LogDArgCertificate }

private noncomputable def leaf5181InnerLog : WideLogData :=
  innerPair250Data

set_option maxRecDepth 1000000 in
private theorem leaf5181LocalValidity :
    LeafFacts leaf5181Box leaf5181Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5181Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714418176) }) = true
      norm_num [leaf5181Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5181CertificateValid :
    WideCertificateValid leaf5181Box leaf5181Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk231ValidityFacts chi288ValidityFacts
    leaf5181LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5181CoverageChecked :
    coverageCheck (innerAD leaf5181Box) leaf5181InnerLog = true := by
  rfl'

private theorem leaf5181InnerLogValid :
    leaf5181InnerLog.Valid 8 (innerAD leaf5181Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint75PositiveFacts.valid leaf5181CoverageChecked

private noncomputable def leaf5181InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814723/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5181InputLogOnePlusV_eq :
    leaf5181InputLogOnePlusV = outerEnclosure 24
      (leaf5181Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5181RoundedFacts : LeafRoundedFacts 8
    leaf5181Certificate.logOnePlusV leaf5181InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5181InputLogOnePlusV_eq }

private noncomputable def leaf5181Inputs : Inputs :=
  inputsOfCaches globalInput sk231RoundedInputs
    chi288InputQChi innerPair250Input
    leaf5181InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5181LowerChecked :
    lowerCheck 24 leaf5181Box leaf5181Inputs = true := by
  rfl'

private theorem leaf5181CoversExact : CoversExact 8
    leaf5181Box leaf5181Certificate leaf5181InnerLog leaf5181Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk231RoundedFacts chi288RoundedFacts
    innerPair250RoundedFacts leaf5181RoundedFacts (by rfl)

private theorem leaf5181FlatSound : Sound leaf5181Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5181CertificateValid
    leaf5181InnerLogValid leaf5181CoversExact leaf5181LowerChecked

private noncomputable def leaf5182Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (247/64), kHi := (31/8), chiLo := (79/256), chiHi := (5/16) }

private noncomputable def leaf5182Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742479/1073741824) }, vSqrt := { lower := (8191/8192), upper := (3272257731/3272114176) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2352434319/2147483648) }, upper := { exponent := 1, mantissa := (283/256) } }, logOuter := sk232LogOuterCertificate, logK := sk232LogKCertificate, logChi := chi288LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (6544371907/6544228352) } }, logDArg := sk232LogDArgCertificate }

private noncomputable def leaf5182InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf5182LocalValidity :
    LeafFacts leaf5182Box leaf5182Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5182Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (3272257731/3272114176) }) = true
      norm_num [leaf5182Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5182CertificateValid :
    WideCertificateValid leaf5182Box leaf5182Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk232ValidityFacts chi288ValidityFacts
    leaf5182LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5182CoverageChecked :
    coverageCheck (innerAD leaf5182Box) leaf5182InnerLog = true := by
  rfl'

private theorem leaf5182InnerLogValid :
    leaf5182InnerLog.Valid 8 (innerAD leaf5182Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf5182CoverageChecked

private noncomputable def leaf5182InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629449/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5182InputLogOnePlusV_eq :
    leaf5182InputLogOnePlusV = outerEnclosure 24
      (leaf5182Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5182RoundedFacts : LeafRoundedFacts 8
    leaf5182Certificate.logOnePlusV leaf5182InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5182InputLogOnePlusV_eq }

private noncomputable def leaf5182Inputs : Inputs :=
  inputsOfCaches globalInput sk232RoundedInputs
    chi288InputQChi innerPair256Input
    leaf5182InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5182LowerChecked :
    lowerCheck 24 leaf5182Box leaf5182Inputs = true := by
  rfl'

private theorem leaf5182CoversExact : CoversExact 8
    leaf5182Box leaf5182Certificate leaf5182InnerLog leaf5182Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk232RoundedFacts chi288RoundedFacts
    innerPair256RoundedFacts leaf5182RoundedFacts (by rfl)

private theorem leaf5182FlatSound : Sound leaf5182Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5182CertificateValid
    leaf5182InnerLogValid leaf5182CoversExact leaf5182LowerChecked

private noncomputable def component104Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (9/32), chiHi := (73/256) }

set_option maxRecDepth 1000000 in
private theorem component104Node0_sound : Sound component104Node0Box :=
  sound_of_literal_split component104Node0Box leaf5119Box leaf5120Box
    .k (241/64) (by rfl) (by rfl)
    leaf5119FlatSound leaf5120FlatSound

private noncomputable def component104Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (73/256), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component104Node1_sound : Sound component104Node1Box :=
  sound_of_literal_split component104Node1Box leaf5121Box leaf5122Box
    .k (241/64) (by rfl) (by rfl)
    leaf5121FlatSound leaf5122FlatSound

private noncomputable def component104Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (9/32), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component104Node2_sound : Sound component104Node2Box :=
  sound_of_literal_split component104Node2Box component104Node0Box component104Node1Box
    .chi (73/256) (by rfl) (by rfl)
    component104Node0_sound component104Node1_sound

private noncomputable def component104Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (9/32), chiHi := (73/256) }

set_option maxRecDepth 1000000 in
private theorem component104Node3_sound : Sound component104Node3Box :=
  sound_of_literal_split component104Node3Box leaf5123Box leaf5124Box
    .k (243/64) (by rfl) (by rfl)
    leaf5123FlatSound leaf5124FlatSound

private noncomputable def component104Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (73/256), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component104Node4_sound : Sound component104Node4Box :=
  sound_of_literal_split component104Node4Box leaf5125Box leaf5126Box
    .k (243/64) (by rfl) (by rfl)
    leaf5125FlatSound leaf5126FlatSound

private noncomputable def component104Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (9/32), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component104Node5_sound : Sound component104Node5Box :=
  sound_of_literal_split component104Node5Box component104Node3Box component104Node4Box
    .chi (73/256) (by rfl) (by rfl)
    component104Node3_sound component104Node4_sound

private noncomputable def component104Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (9/32), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component104Node6_sound : Sound component104Node6Box :=
  sound_of_literal_split component104Node6Box component104Node2Box component104Node5Box
    .k (121/32) (by rfl) (by rfl)
    component104Node2_sound component104Node5_sound

private noncomputable def component104Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (37/128), chiHi := (75/256) }

set_option maxRecDepth 1000000 in
private theorem component104Node7_sound : Sound component104Node7Box :=
  sound_of_literal_split component104Node7Box leaf5127Box leaf5128Box
    .k (241/64) (by rfl) (by rfl)
    leaf5127FlatSound leaf5128FlatSound

private noncomputable def component104Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (75/256), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component104Node8_sound : Sound component104Node8Box :=
  sound_of_literal_split component104Node8Box leaf5129Box leaf5130Box
    .k (241/64) (by rfl) (by rfl)
    leaf5129FlatSound leaf5130FlatSound

private noncomputable def component104Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (37/128), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component104Node9_sound : Sound component104Node9Box :=
  sound_of_literal_split component104Node9Box component104Node7Box component104Node8Box
    .chi (75/256) (by rfl) (by rfl)
    component104Node7_sound component104Node8_sound

private noncomputable def component104Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (37/128), chiHi := (75/256) }

set_option maxRecDepth 1000000 in
private theorem component104Node10_sound : Sound component104Node10Box :=
  sound_of_literal_split component104Node10Box leaf5131Box leaf5132Box
    .k (243/64) (by rfl) (by rfl)
    leaf5131FlatSound leaf5132FlatSound

private noncomputable def component104Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (75/256), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component104Node11_sound : Sound component104Node11Box :=
  sound_of_literal_split component104Node11Box leaf5133Box leaf5134Box
    .k (243/64) (by rfl) (by rfl)
    leaf5133FlatSound leaf5134FlatSound

private noncomputable def component104Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (37/128), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component104Node12_sound : Sound component104Node12Box :=
  sound_of_literal_split component104Node12Box component104Node10Box component104Node11Box
    .chi (75/256) (by rfl) (by rfl)
    component104Node10_sound component104Node11_sound

private noncomputable def component104Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (37/128), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component104Node13_sound : Sound component104Node13Box :=
  sound_of_literal_split component104Node13Box component104Node9Box component104Node12Box
    .k (121/32) (by rfl) (by rfl)
    component104Node9_sound component104Node12_sound

private noncomputable def component104Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (9/32), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component104Node14_sound : Sound component104Node14Box :=
  sound_of_literal_split component104Node14Box component104Node6Box component104Node13Box
    .chi (37/128) (by rfl) (by rfl)
    component104Node6_sound component104Node13_sound

private noncomputable def component104Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (9/32), chiHi := (73/256) }

set_option maxRecDepth 1000000 in
private theorem component104Node15_sound : Sound component104Node15Box :=
  sound_of_literal_split component104Node15Box leaf5135Box leaf5136Box
    .k (245/64) (by rfl) (by rfl)
    leaf5135FlatSound leaf5136FlatSound

private noncomputable def component104Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (73/256), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component104Node16_sound : Sound component104Node16Box :=
  sound_of_literal_split component104Node16Box leaf5137Box leaf5138Box
    .k (245/64) (by rfl) (by rfl)
    leaf5137FlatSound leaf5138FlatSound

private noncomputable def component104Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (9/32), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component104Node17_sound : Sound component104Node17Box :=
  sound_of_literal_split component104Node17Box component104Node15Box component104Node16Box
    .chi (73/256) (by rfl) (by rfl)
    component104Node15_sound component104Node16_sound

private noncomputable def component104Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (9/32), chiHi := (73/256) }

set_option maxRecDepth 1000000 in
private theorem component104Node18_sound : Sound component104Node18Box :=
  sound_of_literal_split component104Node18Box leaf5139Box leaf5140Box
    .k (247/64) (by rfl) (by rfl)
    leaf5139FlatSound leaf5140FlatSound

private noncomputable def component104Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (73/256), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component104Node19_sound : Sound component104Node19Box :=
  sound_of_literal_split component104Node19Box leaf5141Box leaf5142Box
    .k (247/64) (by rfl) (by rfl)
    leaf5141FlatSound leaf5142FlatSound

private noncomputable def component104Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (9/32), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component104Node20_sound : Sound component104Node20Box :=
  sound_of_literal_split component104Node20Box component104Node18Box component104Node19Box
    .chi (73/256) (by rfl) (by rfl)
    component104Node18_sound component104Node19_sound

private noncomputable def component104Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (9/32), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component104Node21_sound : Sound component104Node21Box :=
  sound_of_literal_split component104Node21Box component104Node17Box component104Node20Box
    .k (123/32) (by rfl) (by rfl)
    component104Node17_sound component104Node20_sound

private noncomputable def component104Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (37/128), chiHi := (75/256) }

set_option maxRecDepth 1000000 in
private theorem component104Node22_sound : Sound component104Node22Box :=
  sound_of_literal_split component104Node22Box leaf5143Box leaf5144Box
    .k (245/64) (by rfl) (by rfl)
    leaf5143FlatSound leaf5144FlatSound

private noncomputable def component104Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (75/256), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component104Node23_sound : Sound component104Node23Box :=
  sound_of_literal_split component104Node23Box leaf5145Box leaf5146Box
    .k (245/64) (by rfl) (by rfl)
    leaf5145FlatSound leaf5146FlatSound

private noncomputable def component104Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (37/128), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component104Node24_sound : Sound component104Node24Box :=
  sound_of_literal_split component104Node24Box component104Node22Box component104Node23Box
    .chi (75/256) (by rfl) (by rfl)
    component104Node22_sound component104Node23_sound

private noncomputable def component104Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (37/128), chiHi := (75/256) }

set_option maxRecDepth 1000000 in
private theorem component104Node25_sound : Sound component104Node25Box :=
  sound_of_literal_split component104Node25Box leaf5147Box leaf5148Box
    .k (247/64) (by rfl) (by rfl)
    leaf5147FlatSound leaf5148FlatSound

private noncomputable def component104Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (75/256), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component104Node26_sound : Sound component104Node26Box :=
  sound_of_literal_split component104Node26Box leaf5149Box leaf5150Box
    .k (247/64) (by rfl) (by rfl)
    leaf5149FlatSound leaf5150FlatSound

private noncomputable def component104Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (37/128), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component104Node27_sound : Sound component104Node27Box :=
  sound_of_literal_split component104Node27Box component104Node25Box component104Node26Box
    .chi (75/256) (by rfl) (by rfl)
    component104Node25_sound component104Node26_sound

private noncomputable def component104Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (37/128), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component104Node28_sound : Sound component104Node28Box :=
  sound_of_literal_split component104Node28Box component104Node24Box component104Node27Box
    .k (123/32) (by rfl) (by rfl)
    component104Node24_sound component104Node27_sound

private noncomputable def component104Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (9/32), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component104Node29_sound : Sound component104Node29Box :=
  sound_of_literal_split component104Node29Box component104Node21Box component104Node28Box
    .chi (37/128) (by rfl) (by rfl)
    component104Node21_sound component104Node28_sound

private noncomputable def component104Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (9/32), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component104Node30_sound : Sound component104Node30Box :=
  sound_of_literal_split component104Node30Box component104Node14Box component104Node29Box
    .k (61/16) (by rfl) (by rfl)
    component104Node14_sound component104Node29_sound

private noncomputable def component104Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (19/64), chiHi := (77/256) }

set_option maxRecDepth 1000000 in
private theorem component104Node31_sound : Sound component104Node31Box :=
  sound_of_literal_split component104Node31Box leaf5151Box leaf5152Box
    .k (241/64) (by rfl) (by rfl)
    leaf5151FlatSound leaf5152FlatSound

private noncomputable def component104Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (77/256), chiHi := (39/128) }

set_option maxRecDepth 1000000 in
private theorem component104Node32_sound : Sound component104Node32Box :=
  sound_of_literal_split component104Node32Box leaf5153Box leaf5154Box
    .k (241/64) (by rfl) (by rfl)
    leaf5153FlatSound leaf5154FlatSound

private noncomputable def component104Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (19/64), chiHi := (39/128) }

set_option maxRecDepth 1000000 in
private theorem component104Node33_sound : Sound component104Node33Box :=
  sound_of_literal_split component104Node33Box component104Node31Box component104Node32Box
    .chi (77/256) (by rfl) (by rfl)
    component104Node31_sound component104Node32_sound

private noncomputable def component104Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (19/64), chiHi := (77/256) }

set_option maxRecDepth 1000000 in
private theorem component104Node34_sound : Sound component104Node34Box :=
  sound_of_literal_split component104Node34Box leaf5155Box leaf5156Box
    .k (243/64) (by rfl) (by rfl)
    leaf5155FlatSound leaf5156FlatSound

private noncomputable def component104Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (77/256), chiHi := (39/128) }

set_option maxRecDepth 1000000 in
private theorem component104Node35_sound : Sound component104Node35Box :=
  sound_of_literal_split component104Node35Box leaf5157Box leaf5158Box
    .k (243/64) (by rfl) (by rfl)
    leaf5157FlatSound leaf5158FlatSound

private noncomputable def component104Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (19/64), chiHi := (39/128) }

set_option maxRecDepth 1000000 in
private theorem component104Node36_sound : Sound component104Node36Box :=
  sound_of_literal_split component104Node36Box component104Node34Box component104Node35Box
    .chi (77/256) (by rfl) (by rfl)
    component104Node34_sound component104Node35_sound

private noncomputable def component104Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (19/64), chiHi := (39/128) }

set_option maxRecDepth 1000000 in
private theorem component104Node37_sound : Sound component104Node37Box :=
  sound_of_literal_split component104Node37Box component104Node33Box component104Node36Box
    .k (121/32) (by rfl) (by rfl)
    component104Node33_sound component104Node36_sound

private noncomputable def component104Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (39/128), chiHi := (79/256) }

set_option maxRecDepth 1000000 in
private theorem component104Node38_sound : Sound component104Node38Box :=
  sound_of_literal_split component104Node38Box leaf5159Box leaf5160Box
    .k (241/64) (by rfl) (by rfl)
    leaf5159FlatSound leaf5160FlatSound

private noncomputable def component104Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (79/256), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component104Node39_sound : Sound component104Node39Box :=
  sound_of_literal_split component104Node39Box leaf5161Box leaf5162Box
    .k (241/64) (by rfl) (by rfl)
    leaf5161FlatSound leaf5162FlatSound

private noncomputable def component104Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (39/128), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component104Node40_sound : Sound component104Node40Box :=
  sound_of_literal_split component104Node40Box component104Node38Box component104Node39Box
    .chi (79/256) (by rfl) (by rfl)
    component104Node38_sound component104Node39_sound

private noncomputable def component104Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (39/128), chiHi := (79/256) }

set_option maxRecDepth 1000000 in
private theorem component104Node41_sound : Sound component104Node41Box :=
  sound_of_literal_split component104Node41Box leaf5163Box leaf5164Box
    .k (243/64) (by rfl) (by rfl)
    leaf5163FlatSound leaf5164FlatSound

private noncomputable def component104Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (79/256), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component104Node42_sound : Sound component104Node42Box :=
  sound_of_literal_split component104Node42Box leaf5165Box leaf5166Box
    .k (243/64) (by rfl) (by rfl)
    leaf5165FlatSound leaf5166FlatSound

private noncomputable def component104Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (39/128), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component104Node43_sound : Sound component104Node43Box :=
  sound_of_literal_split component104Node43Box component104Node41Box component104Node42Box
    .chi (79/256) (by rfl) (by rfl)
    component104Node41_sound component104Node42_sound

private noncomputable def component104Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (39/128), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component104Node44_sound : Sound component104Node44Box :=
  sound_of_literal_split component104Node44Box component104Node40Box component104Node43Box
    .k (121/32) (by rfl) (by rfl)
    component104Node40_sound component104Node43_sound

private noncomputable def component104Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (19/64), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component104Node45_sound : Sound component104Node45Box :=
  sound_of_literal_split component104Node45Box component104Node37Box component104Node44Box
    .chi (39/128) (by rfl) (by rfl)
    component104Node37_sound component104Node44_sound

private noncomputable def component104Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (19/64), chiHi := (77/256) }

set_option maxRecDepth 1000000 in
private theorem component104Node46_sound : Sound component104Node46Box :=
  sound_of_literal_split component104Node46Box leaf5167Box leaf5168Box
    .k (245/64) (by rfl) (by rfl)
    leaf5167FlatSound leaf5168FlatSound

private noncomputable def component104Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (77/256), chiHi := (39/128) }

set_option maxRecDepth 1000000 in
private theorem component104Node47_sound : Sound component104Node47Box :=
  sound_of_literal_split component104Node47Box leaf5169Box leaf5170Box
    .k (245/64) (by rfl) (by rfl)
    leaf5169FlatSound leaf5170FlatSound

private noncomputable def component104Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (19/64), chiHi := (39/128) }

set_option maxRecDepth 1000000 in
private theorem component104Node48_sound : Sound component104Node48Box :=
  sound_of_literal_split component104Node48Box component104Node46Box component104Node47Box
    .chi (77/256) (by rfl) (by rfl)
    component104Node46_sound component104Node47_sound

private noncomputable def component104Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (19/64), chiHi := (77/256) }

set_option maxRecDepth 1000000 in
private theorem component104Node49_sound : Sound component104Node49Box :=
  sound_of_literal_split component104Node49Box leaf5171Box leaf5172Box
    .k (247/64) (by rfl) (by rfl)
    leaf5171FlatSound leaf5172FlatSound

private noncomputable def component104Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (77/256), chiHi := (39/128) }

set_option maxRecDepth 1000000 in
private theorem component104Node50_sound : Sound component104Node50Box :=
  sound_of_literal_split component104Node50Box leaf5173Box leaf5174Box
    .k (247/64) (by rfl) (by rfl)
    leaf5173FlatSound leaf5174FlatSound

private noncomputable def component104Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (19/64), chiHi := (39/128) }

set_option maxRecDepth 1000000 in
private theorem component104Node51_sound : Sound component104Node51Box :=
  sound_of_literal_split component104Node51Box component104Node49Box component104Node50Box
    .chi (77/256) (by rfl) (by rfl)
    component104Node49_sound component104Node50_sound

private noncomputable def component104Node52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (19/64), chiHi := (39/128) }

set_option maxRecDepth 1000000 in
private theorem component104Node52_sound : Sound component104Node52Box :=
  sound_of_literal_split component104Node52Box component104Node48Box component104Node51Box
    .k (123/32) (by rfl) (by rfl)
    component104Node48_sound component104Node51_sound

private noncomputable def component104Node53Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (39/128), chiHi := (79/256) }

set_option maxRecDepth 1000000 in
private theorem component104Node53_sound : Sound component104Node53Box :=
  sound_of_literal_split component104Node53Box leaf5175Box leaf5176Box
    .k (245/64) (by rfl) (by rfl)
    leaf5175FlatSound leaf5176FlatSound

private noncomputable def component104Node54Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (79/256), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component104Node54_sound : Sound component104Node54Box :=
  sound_of_literal_split component104Node54Box leaf5177Box leaf5178Box
    .k (245/64) (by rfl) (by rfl)
    leaf5177FlatSound leaf5178FlatSound

private noncomputable def component104Node55Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (39/128), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component104Node55_sound : Sound component104Node55Box :=
  sound_of_literal_split component104Node55Box component104Node53Box component104Node54Box
    .chi (79/256) (by rfl) (by rfl)
    component104Node53_sound component104Node54_sound

private noncomputable def component104Node56Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (39/128), chiHi := (79/256) }

set_option maxRecDepth 1000000 in
private theorem component104Node56_sound : Sound component104Node56Box :=
  sound_of_literal_split component104Node56Box leaf5179Box leaf5180Box
    .k (247/64) (by rfl) (by rfl)
    leaf5179FlatSound leaf5180FlatSound

private noncomputable def component104Node57Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (79/256), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component104Node57_sound : Sound component104Node57Box :=
  sound_of_literal_split component104Node57Box leaf5181Box leaf5182Box
    .k (247/64) (by rfl) (by rfl)
    leaf5181FlatSound leaf5182FlatSound

private noncomputable def component104Node58Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (39/128), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component104Node58_sound : Sound component104Node58Box :=
  sound_of_literal_split component104Node58Box component104Node56Box component104Node57Box
    .chi (79/256) (by rfl) (by rfl)
    component104Node56_sound component104Node57_sound

private noncomputable def component104Node59Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (39/128), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component104Node59_sound : Sound component104Node59Box :=
  sound_of_literal_split component104Node59Box component104Node55Box component104Node58Box
    .k (123/32) (by rfl) (by rfl)
    component104Node55_sound component104Node58_sound

private noncomputable def component104Node60Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (19/64), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component104Node60_sound : Sound component104Node60Box :=
  sound_of_literal_split component104Node60Box component104Node52Box component104Node59Box
    .chi (39/128) (by rfl) (by rfl)
    component104Node52_sound component104Node59_sound

private noncomputable def component104Node61Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (19/64), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component104Node61_sound : Sound component104Node61Box :=
  sound_of_literal_split component104Node61Box component104Node45Box component104Node60Box
    .k (61/16) (by rfl) (by rfl)
    component104Node45_sound component104Node60_sound

noncomputable def component104Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (9/32), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
theorem component104_sound : Sound component104Box :=
  sound_of_literal_split component104Box component104Node30Box component104Node61Box
    .chi (19/64) (by rfl) (by rfl)
    component104Node30_sound component104Node61_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
