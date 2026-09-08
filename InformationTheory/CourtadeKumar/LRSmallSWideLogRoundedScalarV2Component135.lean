import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch5
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch7
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch8
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch11
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch5
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch6
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

private noncomputable def leaf6670Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (9/16), chiHi := (73/128) }

private noncomputable def leaf6670Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217979/134217728) }, vSqrt := { lower := (65529/65536), upper := (11452743679/11451925504) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (379536519/268435456) }, upper := { exponent := 1, mantissa := (5917/4096) } }, logOuter := sk131LogOuterCertificate, logK := sk131LogKCertificate, logChi := chi335LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (22904669183/22903851008) } }, logDArg := sk131LogDArgCertificate }

private noncomputable def leaf6670InnerLog : WideLogData :=
  innerPair370Data

set_option maxRecDepth 1000000 in
private theorem leaf6670LocalValidity :
    LeafFacts leaf6670Box leaf6670Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6670Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (11452743679/11451925504) }) = true
      norm_num [leaf6670Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6670CertificateValid :
    WideCertificateValid leaf6670Box leaf6670Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk131ValidityFacts chi335ValidityFacts
    leaf6670LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6670CoverageChecked :
    coverageCheck (innerAD leaf6670Box) leaf6670InnerLog = true := by
  rfl'

private theorem leaf6670InnerLogValid :
    leaf6670InnerLog.Valid 8 (innerAD leaf6670Box) :=
  wideLogDataValid_of_cachedCheck endpoint96PositiveFacts
    endpoint470PositiveFacts.valid leaf6670CoverageChecked

private noncomputable def leaf6670InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (726855/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf6670InputLogOnePlusV_eq :
    leaf6670InputLogOnePlusV = outerEnclosure 24
      (leaf6670Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6670RoundedFacts : LeafRoundedFacts 8
    leaf6670Certificate.logOnePlusV leaf6670InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6670InputLogOnePlusV_eq }

private noncomputable def leaf6670Inputs : Inputs :=
  inputsOfCaches globalInput sk131RoundedInputs
    chi335InputQChi innerPair370Input
    leaf6670InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6670LowerChecked :
    lowerCheck 24 leaf6670Box leaf6670Inputs = true := by
  rfl'

private theorem leaf6670CoversExact : CoversExact 8
    leaf6670Box leaf6670Certificate leaf6670InnerLog leaf6670Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk131RoundedFacts chi335RoundedFacts
    innerPair370RoundedFacts leaf6670RoundedFacts (by rfl)

private theorem leaf6670FlatSound : Sound leaf6670Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6670CertificateValid
    leaf6670InnerLogValid leaf6670CoversExact leaf6670LowerChecked

private noncomputable def leaf6671Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (73/128), chiHi := (37/64) }

private noncomputable def leaf6671Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217981/134217728) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34355722240) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (382944181/268435456) }, upper := { exponent := 1, mantissa := (2985/2048) } }, logOuter := sk131LogOuterCertificate, logK := sk131LogKCertificate, logChi := chi336LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68713953277/68711444480) } }, logDArg := sk131LogDArgCertificate }

private noncomputable def leaf6671InnerLog : WideLogData :=
  innerPair368Data

set_option maxRecDepth 1000000 in
private theorem leaf6671LocalValidity :
    LeafFacts leaf6671Box leaf6671Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6671Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34355722240) }) = true
      norm_num [leaf6671Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6671CertificateValid :
    WideCertificateValid leaf6671Box leaf6671Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk131ValidityFacts chi336ValidityFacts
    leaf6671LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6671CoverageChecked :
    coverageCheck (innerAD leaf6671Box) leaf6671InnerLog = true := by
  rfl'

private theorem leaf6671InnerLogValid :
    leaf6671InnerLog.Valid 8 (innerAD leaf6671Box) :=
  wideLogDataValid_of_cachedCheck endpoint96PositiveFacts
    endpoint98PositiveFacts.valid leaf6671CoverageChecked

private noncomputable def leaf6671InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629693/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6671InputLogOnePlusV_eq :
    leaf6671InputLogOnePlusV = outerEnclosure 24
      (leaf6671Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6671RoundedFacts : LeafRoundedFacts 8
    leaf6671Certificate.logOnePlusV leaf6671InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6671InputLogOnePlusV_eq }

private noncomputable def leaf6671Inputs : Inputs :=
  inputsOfCaches globalInput sk131RoundedInputs
    chi336InputQChi innerPair368Input
    leaf6671InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6671LowerChecked :
    lowerCheck 24 leaf6671Box leaf6671Inputs = true := by
  rfl'

private theorem leaf6671CoversExact : CoversExact 8
    leaf6671Box leaf6671Certificate leaf6671InnerLog leaf6671Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk131RoundedFacts chi336RoundedFacts
    innerPair368RoundedFacts leaf6671RoundedFacts (by rfl)

private theorem leaf6671FlatSound : Sound leaf6671Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6671CertificateValid
    leaf6671InnerLogValid leaf6671CoversExact leaf6671LowerChecked

private noncomputable def leaf6672Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (9/16), chiHi := (73/128) }

private noncomputable def leaf6672Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217981/134217728) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34355701760) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (384254821/268435456) }, upper := { exponent := 1, mantissa := (2995/2048) } }, logOuter := sk132LogOuterCertificate, logK := sk132LogKCertificate, logChi := chi335LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68713932797/68711403520) } }, logDArg := sk132LogDArgCertificate }

private noncomputable def leaf6672InnerLog : WideLogData :=
  innerPair368Data

set_option maxRecDepth 1000000 in
private theorem leaf6672LocalValidity :
    LeafFacts leaf6672Box leaf6672Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6672Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34355701760) }) = true
      norm_num [leaf6672Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6672CertificateValid :
    WideCertificateValid leaf6672Box leaf6672Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk132ValidityFacts chi335ValidityFacts
    leaf6672LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6672CoverageChecked :
    coverageCheck (innerAD leaf6672Box) leaf6672InnerLog = true := by
  rfl'

private theorem leaf6672InnerLogValid :
    leaf6672InnerLog.Valid 8 (innerAD leaf6672Box) :=
  wideLogDataValid_of_cachedCheck endpoint96PositiveFacts
    endpoint98PositiveFacts.valid leaf6672CoverageChecked

private noncomputable def leaf6672InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814849/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6672InputLogOnePlusV_eq :
    leaf6672InputLogOnePlusV = outerEnclosure 24
      (leaf6672Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6672RoundedFacts : LeafRoundedFacts 8
    leaf6672Certificate.logOnePlusV leaf6672InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6672InputLogOnePlusV_eq }

private noncomputable def leaf6672Inputs : Inputs :=
  inputsOfCaches globalInput sk132RoundedInputs
    chi335InputQChi innerPair368Input
    leaf6672InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6672LowerChecked :
    lowerCheck 24 leaf6672Box leaf6672Inputs = true := by
  rfl'

private theorem leaf6672CoversExact : CoversExact 8
    leaf6672Box leaf6672Certificate leaf6672InnerLog leaf6672Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk132RoundedFacts chi335RoundedFacts
    innerPair368RoundedFacts leaf6672RoundedFacts (by rfl)

private theorem leaf6672FlatSound : Sound leaf6672Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6672CertificateValid
    leaf6672InnerLogValid leaf6672CoversExact leaf6672LowerChecked

private noncomputable def leaf6673Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (73/128), chiHi := (37/64) }

private noncomputable def leaf6673Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217983/134217728) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34355646464) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (387728015/268435456) }, upper := { exponent := 1, mantissa := (1511/1024) } }, logOuter := sk132LogOuterCertificate, logK := sk132LogKCertificate, logChi := chi336LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68713877501/68711292928) } }, logDArg := sk132LogDArgCertificate }

private noncomputable def leaf6673InnerLog : WideLogData :=
  innerPair373Data

set_option maxRecDepth 1000000 in
private theorem leaf6673LocalValidity :
    LeafFacts leaf6673Box leaf6673Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6673Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34355646464) }) = true
      norm_num [leaf6673Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6673CertificateValid :
    WideCertificateValid leaf6673Box leaf6673Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk132ValidityFacts chi336ValidityFacts
    leaf6673LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6673CoverageChecked :
    coverageCheck (innerAD leaf6673Box) leaf6673InnerLog = true := by
  rfl'

private theorem leaf6673InnerLogValid :
    leaf6673InnerLog.Valid 8 (innerAD leaf6673Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint472PositiveFacts.valid leaf6673CoverageChecked

private noncomputable def leaf6673InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (726857/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf6673InputLogOnePlusV_eq :
    leaf6673InputLogOnePlusV = outerEnclosure 24
      (leaf6673Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6673RoundedFacts : LeafRoundedFacts 8
    leaf6673Certificate.logOnePlusV leaf6673InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6673InputLogOnePlusV_eq }

private noncomputable def leaf6673Inputs : Inputs :=
  inputsOfCaches globalInput sk132RoundedInputs
    chi336InputQChi innerPair373Input
    leaf6673InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6673LowerChecked :
    lowerCheck 24 leaf6673Box leaf6673Inputs = true := by
  rfl'

private theorem leaf6673CoversExact : CoversExact 8
    leaf6673Box leaf6673Certificate leaf6673InnerLog leaf6673Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk132RoundedFacts chi336RoundedFacts
    innerPair373RoundedFacts leaf6673RoundedFacts (by rfl)

private theorem leaf6673FlatSound : Sound leaf6673Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6673CertificateValid
    leaf6673InnerLogValid leaf6673CoversExact leaf6673LowerChecked

private noncomputable def leaf6674Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (37/64), chiHi := (75/128) }

private noncomputable def leaf6674Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217983/134217728) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34355667968) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (386351843/268435456) }, upper := { exponent := 1, mantissa := (6023/4096) } }, logOuter := sk131LogOuterCertificate, logK := sk131LogKCertificate, logChi := chi337LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68713899005/68711335936) } }, logDArg := sk131LogDArgCertificate }

private noncomputable def leaf6674InnerLog : WideLogData :=
  innerPair373Data

set_option maxRecDepth 1000000 in
private theorem leaf6674LocalValidity :
    LeafFacts leaf6674Box leaf6674Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6674Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34355667968) }) = true
      norm_num [leaf6674Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6674CertificateValid :
    WideCertificateValid leaf6674Box leaf6674Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk131ValidityFacts chi337ValidityFacts
    leaf6674LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6674CoverageChecked :
    coverageCheck (innerAD leaf6674Box) leaf6674InnerLog = true := by
  rfl'

private theorem leaf6674InnerLogValid :
    leaf6674InnerLog.Valid 8 (innerAD leaf6674Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint472PositiveFacts.valid leaf6674CoverageChecked

private noncomputable def leaf6674InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629707/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6674InputLogOnePlusV_eq :
    leaf6674InputLogOnePlusV = outerEnclosure 24
      (leaf6674Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6674RoundedFacts : LeafRoundedFacts 8
    leaf6674Certificate.logOnePlusV leaf6674InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6674InputLogOnePlusV_eq }

private noncomputable def leaf6674Inputs : Inputs :=
  inputsOfCaches globalInput sk131RoundedInputs
    chi337InputQChi innerPair373Input
    leaf6674InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6674LowerChecked :
    lowerCheck 24 leaf6674Box leaf6674Inputs = true := by
  rfl'

private theorem leaf6674CoversExact : CoversExact 8
    leaf6674Box leaf6674Certificate leaf6674InnerLog leaf6674Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk131RoundedFacts chi337RoundedFacts
    innerPair373RoundedFacts leaf6674RoundedFacts (by rfl)

private theorem leaf6674FlatSound : Sound leaf6674Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6674CertificateValid
    leaf6674InnerLogValid leaf6674CoversExact leaf6674LowerChecked

private noncomputable def leaf6675Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (75/128), chiHi := (19/32) }

private noncomputable def leaf6675Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217985/134217728) }, vSqrt := { lower := (65529/65536), upper := (11452743679/11451871232) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (389759505/268435456) }, upper := { exponent := 1, mantissa := (1519/1024) } }, logOuter := sk131LogOuterCertificate, logK := sk131LogKCertificate, logChi := chi338LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (22904614911/22903742464) } }, logDArg := sk131LogDArgCertificate }

private noncomputable def leaf6675InnerLog : WideLogData :=
  innerPair372Data

set_option maxRecDepth 1000000 in
private theorem leaf6675LocalValidity :
    LeafFacts leaf6675Box leaf6675Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6675Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (11452743679/11451871232) }) = true
      norm_num [leaf6675Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6675CertificateValid :
    WideCertificateValid leaf6675Box leaf6675Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk131ValidityFacts chi338ValidityFacts
    leaf6675LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6675CoverageChecked :
    coverageCheck (innerAD leaf6675Box) leaf6675InnerLog = true := by
  rfl'

private theorem leaf6675InnerLogValid :
    leaf6675InnerLog.Valid 8 (innerAD leaf6675Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint99PositiveFacts.valid leaf6675CoverageChecked

private noncomputable def leaf6675InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453715/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf6675InputLogOnePlusV_eq :
    leaf6675InputLogOnePlusV = outerEnclosure 24
      (leaf6675Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6675RoundedFacts : LeafRoundedFacts 8
    leaf6675Certificate.logOnePlusV leaf6675InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6675InputLogOnePlusV_eq }

private noncomputable def leaf6675Inputs : Inputs :=
  inputsOfCaches globalInput sk131RoundedInputs
    chi338InputQChi innerPair372Input
    leaf6675InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6675LowerChecked :
    lowerCheck 24 leaf6675Box leaf6675Inputs = true := by
  rfl'

private theorem leaf6675CoversExact : CoversExact 8
    leaf6675Box leaf6675Certificate leaf6675InnerLog leaf6675Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk131RoundedFacts chi338RoundedFacts
    innerPair372RoundedFacts leaf6675RoundedFacts (by rfl)

private theorem leaf6675FlatSound : Sound leaf6675Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6675CertificateValid
    leaf6675InnerLogValid leaf6675CoversExact leaf6675LowerChecked

private noncomputable def leaf6676Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (37/64), chiHi := (75/128) }

private noncomputable def leaf6676Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217985/134217728) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588897792) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (391201209/268435456) }, upper := { exponent := 1, mantissa := (3049/2048) } }, logOuter := sk132LogOuterCertificate, logK := sk132LogKCertificate, logChi := chi337LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178324479/17177795584) } }, logDArg := sk132LogDArgCertificate }

private noncomputable def leaf6676InnerLog : WideLogData :=
  innerPair372Data

set_option maxRecDepth 1000000 in
private theorem leaf6676LocalValidity :
    LeafFacts leaf6676Box leaf6676Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6676Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588897792) }) = true
      norm_num [leaf6676Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6676CertificateValid :
    WideCertificateValid leaf6676Box leaf6676Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk132ValidityFacts chi337ValidityFacts
    leaf6676LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6676CoverageChecked :
    coverageCheck (innerAD leaf6676Box) leaf6676InnerLog = true := by
  rfl'

private theorem leaf6676InnerLogValid :
    leaf6676InnerLog.Valid 8 (innerAD leaf6676Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint99PositiveFacts.valid leaf6676CoverageChecked

private noncomputable def leaf6676InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629597/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6676InputLogOnePlusV_eq :
    leaf6676InputLogOnePlusV = outerEnclosure 24
      (leaf6676Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6676RoundedFacts : LeafRoundedFacts 8
    leaf6676Certificate.logOnePlusV leaf6676InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6676InputLogOnePlusV_eq }

private noncomputable def leaf6676Inputs : Inputs :=
  inputsOfCaches globalInput sk132RoundedInputs
    chi337InputQChi innerPair372Input
    leaf6676InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6676LowerChecked :
    lowerCheck 24 leaf6676Box leaf6676Inputs = true := by
  rfl'

private theorem leaf6676CoversExact : CoversExact 8
    leaf6676Box leaf6676Certificate leaf6676InnerLog leaf6676Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk132RoundedFacts chi337RoundedFacts
    innerPair372RoundedFacts leaf6676RoundedFacts (by rfl)

private theorem leaf6676FlatSound : Sound leaf6676Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6676CertificateValid
    leaf6676InnerLogValid leaf6676CoversExact leaf6676LowerChecked

private noncomputable def leaf6677Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (75/128), chiHi := (19/32) }

private noncomputable def leaf6677Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134217987/134217728) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588883968) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (394674403/268435456) }, upper := { exponent := 1, mantissa := (769/512) } }, logOuter := sk132LogOuterCertificate, logK := sk132LogKCertificate, logChi := chi338LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178310655/17177767936) } }, logDArg := sk132LogDArgCertificate }

private noncomputable def leaf6677InnerLog : WideLogData :=
  innerPair378Data

set_option maxRecDepth 1000000 in
private theorem leaf6677LocalValidity :
    LeafFacts leaf6677Box leaf6677Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6677Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588883968) }) = true
      norm_num [leaf6677Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6677CertificateValid :
    WideCertificateValid leaf6677Box leaf6677Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk132ValidityFacts chi338ValidityFacts
    leaf6677LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6677CoverageChecked :
    coverageCheck (innerAD leaf6677Box) leaf6677InnerLog = true := by
  rfl'

private theorem leaf6677InnerLogValid :
    leaf6677InnerLog.Valid 8 (innerAD leaf6677Box) :=
  wideLogDataValid_of_cachedCheck endpoint98PositiveFacts
    endpoint491PositiveFacts.valid leaf6677CoverageChecked

private noncomputable def leaf6677InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629611/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6677InputLogOnePlusV_eq :
    leaf6677InputLogOnePlusV = outerEnclosure 24
      (leaf6677Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6677RoundedFacts : LeafRoundedFacts 8
    leaf6677Certificate.logOnePlusV leaf6677InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6677InputLogOnePlusV_eq }

private noncomputable def leaf6677Inputs : Inputs :=
  inputsOfCaches globalInput sk132RoundedInputs
    chi338InputQChi innerPair378Input
    leaf6677InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6677LowerChecked :
    lowerCheck 24 leaf6677Box leaf6677Inputs = true := by
  rfl'

private theorem leaf6677CoversExact : CoversExact 8
    leaf6677Box leaf6677Certificate leaf6677InnerLog leaf6677Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk132RoundedFacts chi338RoundedFacts
    innerPair378RoundedFacts leaf6677RoundedFacts (by rfl)

private theorem leaf6677FlatSound : Sound leaf6677Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6677CertificateValid
    leaf6677InnerLogValid leaf6677CoversExact leaf6677LowerChecked

private noncomputable def leaf6678Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (19/32), chiHi := (77/128) }

private noncomputable def leaf6678Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217987/134217728) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588889856) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (393167167/268435456) }, upper := { exponent := 1, mantissa := (6129/4096) } }, logOuter := sk131LogOuterCertificate, logK := sk131LogKCertificate, logChi := chi339LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178316543/17177779712) } }, logDArg := sk131LogDArgCertificate }

private noncomputable def leaf6678InnerLog : WideLogData :=
  innerPair372Data

set_option maxRecDepth 1000000 in
private theorem leaf6678LocalValidity :
    LeafFacts leaf6678Box leaf6678Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6678Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588889856) }) = true
      norm_num [leaf6678Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6678CertificateValid :
    WideCertificateValid leaf6678Box leaf6678Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk131ValidityFacts chi339ValidityFacts
    leaf6678LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6678CoverageChecked :
    coverageCheck (innerAD leaf6678Box) leaf6678InnerLog = true := by
  rfl'

private theorem leaf6678InnerLogValid :
    leaf6678InnerLog.Valid 8 (innerAD leaf6678Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint99PositiveFacts.valid leaf6678CoverageChecked

private noncomputable def leaf6678InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629605/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6678InputLogOnePlusV_eq :
    leaf6678InputLogOnePlusV = outerEnclosure 24
      (leaf6678Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6678RoundedFacts : LeafRoundedFacts 8
    leaf6678Certificate.logOnePlusV leaf6678InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6678InputLogOnePlusV_eq }

private noncomputable def leaf6678Inputs : Inputs :=
  inputsOfCaches globalInput sk131RoundedInputs
    chi339InputQChi innerPair372Input
    leaf6678InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6678LowerChecked :
    lowerCheck 24 leaf6678Box leaf6678Inputs = true := by
  rfl'

private theorem leaf6678CoversExact : CoversExact 8
    leaf6678Box leaf6678Certificate leaf6678InnerLog leaf6678Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk131RoundedFacts chi339RoundedFacts
    innerPair372RoundedFacts leaf6678RoundedFacts (by rfl)

private theorem leaf6678FlatSound : Sound leaf6678Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6678CertificateValid
    leaf6678InnerLogValid leaf6678CoversExact leaf6678LowerChecked

private noncomputable def leaf6679Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (77/128), chiHi := (39/64) }

private noncomputable def leaf6679Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134217989/134217728) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588876288) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (396574829/268435456) }, upper := { exponent := 1, mantissa := (3091/2048) } }, logOuter := sk131LogOuterCertificate, logK := sk131LogKCertificate, logChi := chi340LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178302975/17177752576) } }, logDArg := sk131LogDArgCertificate }

private noncomputable def leaf6679InnerLog : WideLogData :=
  innerPair376Data

set_option maxRecDepth 1000000 in
private theorem leaf6679LocalValidity :
    LeafFacts leaf6679Box leaf6679Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6679Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588876288) }) = true
      norm_num [leaf6679Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6679CertificateValid :
    WideCertificateValid leaf6679Box leaf6679Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk131ValidityFacts chi340ValidityFacts
    leaf6679LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6679CoverageChecked :
    coverageCheck (innerAD leaf6679Box) leaf6679InnerLog = true := by
  rfl'

private theorem leaf6679InnerLogValid :
    leaf6679InnerLog.Valid 8 (innerAD leaf6679Box) :=
  wideLogDataValid_of_cachedCheck endpoint98PositiveFacts
    endpoint482PositiveFacts.valid leaf6679CoverageChecked

private noncomputable def leaf6679InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814809/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6679InputLogOnePlusV_eq :
    leaf6679InputLogOnePlusV = outerEnclosure 24
      (leaf6679Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6679RoundedFacts : LeafRoundedFacts 8
    leaf6679Certificate.logOnePlusV leaf6679InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6679InputLogOnePlusV_eq }

private noncomputable def leaf6679Inputs : Inputs :=
  inputsOfCaches globalInput sk131RoundedInputs
    chi340InputQChi innerPair376Input
    leaf6679InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6679LowerChecked :
    lowerCheck 24 leaf6679Box leaf6679Inputs = true := by
  rfl'

private theorem leaf6679CoversExact : CoversExact 8
    leaf6679Box leaf6679Certificate leaf6679InnerLog leaf6679Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk131RoundedFacts chi340RoundedFacts
    innerPair376RoundedFacts leaf6679RoundedFacts (by rfl)

private theorem leaf6679FlatSound : Sound leaf6679Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6679CertificateValid
    leaf6679InnerLogValid leaf6679CoversExact leaf6679LowerChecked

private noncomputable def leaf6680Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (19/32), chiHi := (77/128) }

private noncomputable def leaf6680Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134217989/134217728) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588870144) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (398147597/268435456) }, upper := { exponent := 1, mantissa := (3103/2048) } }, logOuter := sk132LogOuterCertificate, logK := sk132LogKCertificate, logChi := chi339LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178296831/17177740288) } }, logDArg := sk132LogDArgCertificate }

private noncomputable def leaf6680InnerLog : WideLogData :=
  innerPair376Data

set_option maxRecDepth 1000000 in
private theorem leaf6680LocalValidity :
    LeafFacts leaf6680Box leaf6680Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6680Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588870144) }) = true
      norm_num [leaf6680Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6680CertificateValid :
    WideCertificateValid leaf6680Box leaf6680Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk132ValidityFacts chi339ValidityFacts
    leaf6680LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6680CoverageChecked :
    coverageCheck (innerAD leaf6680Box) leaf6680InnerLog = true := by
  rfl'

private theorem leaf6680InnerLogValid :
    leaf6680InnerLog.Valid 8 (innerAD leaf6680Box) :=
  wideLogDataValid_of_cachedCheck endpoint98PositiveFacts
    endpoint482PositiveFacts.valid leaf6680CoverageChecked

private noncomputable def leaf6680InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453703/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf6680InputLogOnePlusV_eq :
    leaf6680InputLogOnePlusV = outerEnclosure 24
      (leaf6680Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6680RoundedFacts : LeafRoundedFacts 8
    leaf6680Certificate.logOnePlusV leaf6680InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6680InputLogOnePlusV_eq }

private noncomputable def leaf6680Inputs : Inputs :=
  inputsOfCaches globalInput sk132RoundedInputs
    chi339InputQChi innerPair376Input
    leaf6680InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6680LowerChecked :
    lowerCheck 24 leaf6680Box leaf6680Inputs = true := by
  rfl'

private theorem leaf6680CoversExact : CoversExact 8
    leaf6680Box leaf6680Certificate leaf6680InnerLog leaf6680Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk132RoundedFacts chi339RoundedFacts
    innerPair376RoundedFacts leaf6680RoundedFacts (by rfl)

private theorem leaf6680FlatSound : Sound leaf6680Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6680CertificateValid
    leaf6680InnerLogValid leaf6680CoversExact leaf6680LowerChecked

private noncomputable def leaf6681Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (77/128), chiHi := (39/64) }

private noncomputable def leaf6681Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134217991/134217728) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588856320) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (401620791/268435456) }, upper := { exponent := 1, mantissa := (1565/1024) } }, logOuter := sk132LogOuterCertificate, logK := sk132LogKCertificate, logChi := chi340LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178283007/17177712640) } }, logDArg := sk132LogDArgCertificate }

private noncomputable def leaf6681InnerLog : WideLogData :=
  innerPair376Data

set_option maxRecDepth 1000000 in
private theorem leaf6681LocalValidity :
    LeafFacts leaf6681Box leaf6681Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6681Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588856320) }) = true
      norm_num [leaf6681Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6681CertificateValid :
    WideCertificateValid leaf6681Box leaf6681Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk132ValidityFacts chi340ValidityFacts
    leaf6681LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6681CoverageChecked :
    coverageCheck (innerAD leaf6681Box) leaf6681InnerLog = true := by
  rfl'

private theorem leaf6681InnerLogValid :
    leaf6681InnerLog.Valid 8 (innerAD leaf6681Box) :=
  wideLogDataValid_of_cachedCheck endpoint98PositiveFacts
    endpoint482PositiveFacts.valid leaf6681CoverageChecked

private noncomputable def leaf6681InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814819/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6681InputLogOnePlusV_eq :
    leaf6681InputLogOnePlusV = outerEnclosure 24
      (leaf6681Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6681RoundedFacts : LeafRoundedFacts 8
    leaf6681Certificate.logOnePlusV leaf6681InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6681InputLogOnePlusV_eq }

private noncomputable def leaf6681Inputs : Inputs :=
  inputsOfCaches globalInput sk132RoundedInputs
    chi340InputQChi innerPair376Input
    leaf6681InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6681LowerChecked :
    lowerCheck 24 leaf6681Box leaf6681Inputs = true := by
  rfl'

private theorem leaf6681CoversExact : CoversExact 8
    leaf6681Box leaf6681Certificate leaf6681InnerLog leaf6681Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk132RoundedFacts chi340RoundedFacts
    innerPair376RoundedFacts leaf6681RoundedFacts (by rfl)

private theorem leaf6681FlatSound : Sound leaf6681Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6681CertificateValid
    leaf6681InnerLogValid leaf6681CoversExact leaf6681LowerChecked

private noncomputable def leaf6682Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (39/64), chiHi := (79/128) }

private noncomputable def leaf6682Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134217991/134217728) }, vSqrt := { lower := (65529/65536), upper := (954380743/954318080) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (399982491/268435456) }, upper := { exponent := 1, mantissa := (6235/4096) } }, logOuter := sk131LogOuterCertificate, logK := sk131LogKCertificate, logChi := chi347LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (1908698823/1908636160) } }, logDArg := sk131LogDArgCertificate }

private noncomputable def leaf6682InnerLog : WideLogData :=
  innerPair376Data

set_option maxRecDepth 1000000 in
private theorem leaf6682LocalValidity :
    LeafFacts leaf6682Box leaf6682Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6682Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (954380743/954318080) }) = true
      norm_num [leaf6682Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6682CertificateValid :
    WideCertificateValid leaf6682Box leaf6682Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk131ValidityFacts chi347ValidityFacts
    leaf6682LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6682CoverageChecked :
    coverageCheck (innerAD leaf6682Box) leaf6682InnerLog = true := by
  rfl'

private theorem leaf6682InnerLogValid :
    leaf6682InnerLog.Valid 8 (innerAD leaf6682Box) :=
  wideLogDataValid_of_cachedCheck endpoint98PositiveFacts
    endpoint482PositiveFacts.valid leaf6682CoverageChecked

private noncomputable def leaf6682InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (181713/262144) }

set_option maxRecDepth 1000000 in
private theorem leaf6682InputLogOnePlusV_eq :
    leaf6682InputLogOnePlusV = outerEnclosure 24
      (leaf6682Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6682RoundedFacts : LeafRoundedFacts 8
    leaf6682Certificate.logOnePlusV leaf6682InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6682InputLogOnePlusV_eq }

private noncomputable def leaf6682Inputs : Inputs :=
  inputsOfCaches globalInput sk131RoundedInputs
    chi347InputQChi innerPair376Input
    leaf6682InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6682LowerChecked :
    lowerCheck 24 leaf6682Box leaf6682Inputs = true := by
  rfl'

private theorem leaf6682CoversExact : CoversExact 8
    leaf6682Box leaf6682Certificate leaf6682InnerLog leaf6682Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk131RoundedFacts chi347RoundedFacts
    innerPair376RoundedFacts leaf6682RoundedFacts (by rfl)

private theorem leaf6682FlatSound : Sound leaf6682Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6682CertificateValid
    leaf6682InnerLogValid leaf6682CoversExact leaf6682LowerChecked

private noncomputable def leaf6683Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (79/128), chiHi := (5/8) }

private noncomputable def leaf6683Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134217993/134217728) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588849152) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (403390153/268435456) }, upper := { exponent := 1, mantissa := (393/256) } }, logOuter := sk131LogOuterCertificate, logK := sk131LogKCertificate, logChi := chi348LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178275839/17177698304) } }, logDArg := sk131LogDArgCertificate }

private noncomputable def leaf6683InnerLog : WideLogData :=
  innerPair382Data

set_option maxRecDepth 1000000 in
private theorem leaf6683LocalValidity :
    LeafFacts leaf6683Box leaf6683Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6683Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588849152) }) = true
      norm_num [leaf6683Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6683CertificateValid :
    WideCertificateValid leaf6683Box leaf6683Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk131ValidityFacts chi348ValidityFacts
    leaf6683LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6683CoverageChecked :
    coverageCheck (innerAD leaf6683Box) leaf6683InnerLog = true := by
  rfl'

private theorem leaf6683InnerLogValid :
    leaf6683InnerLog.Valid 8 (innerAD leaf6683Box) :=
  wideLogDataValid_of_cachedCheck endpoint99PositiveFacts
    endpoint483PositiveFacts.valid leaf6683CoverageChecked

private noncomputable def leaf6683InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629645/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6683InputLogOnePlusV_eq :
    leaf6683InputLogOnePlusV = outerEnclosure 24
      (leaf6683Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6683RoundedFacts : LeafRoundedFacts 8
    leaf6683Certificate.logOnePlusV leaf6683InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6683InputLogOnePlusV_eq }

private noncomputable def leaf6683Inputs : Inputs :=
  inputsOfCaches globalInput sk131RoundedInputs
    chi348InputQChi innerPair382Input
    leaf6683InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6683LowerChecked :
    lowerCheck 24 leaf6683Box leaf6683Inputs = true := by
  rfl'

private theorem leaf6683CoversExact : CoversExact 8
    leaf6683Box leaf6683Certificate leaf6683InnerLog leaf6683Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk131RoundedFacts chi348RoundedFacts
    innerPair382RoundedFacts leaf6683RoundedFacts (by rfl)

private theorem leaf6683FlatSound : Sound leaf6683Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6683CertificateValid
    leaf6683InnerLogValid leaf6683CoversExact leaf6683LowerChecked

private noncomputable def leaf6684Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (39/64), chiHi := (79/128) }

private noncomputable def leaf6684Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134217993/134217728) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588842496) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (405093985/268435456) }, upper := { exponent := 1, mantissa := (3157/2048) } }, logOuter := sk132LogOuterCertificate, logK := sk132LogKCertificate, logChi := chi347LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178269183/17177684992) } }, logDArg := sk132LogDArgCertificate }

private noncomputable def leaf6684InnerLog : WideLogData :=
  innerPair382Data

set_option maxRecDepth 1000000 in
private theorem leaf6684LocalValidity :
    LeafFacts leaf6684Box leaf6684Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6684Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588842496) }) = true
      norm_num [leaf6684Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6684CertificateValid :
    WideCertificateValid leaf6684Box leaf6684Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk132ValidityFacts chi347ValidityFacts
    leaf6684LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6684CoverageChecked :
    coverageCheck (innerAD leaf6684Box) leaf6684InnerLog = true := by
  rfl'

private theorem leaf6684InnerLogValid :
    leaf6684InnerLog.Valid 8 (innerAD leaf6684Box) :=
  wideLogDataValid_of_cachedCheck endpoint99PositiveFacts
    endpoint483PositiveFacts.valid leaf6684CoverageChecked

private noncomputable def leaf6684InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629651/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6684InputLogOnePlusV_eq :
    leaf6684InputLogOnePlusV = outerEnclosure 24
      (leaf6684Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6684RoundedFacts : LeafRoundedFacts 8
    leaf6684Certificate.logOnePlusV leaf6684InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6684InputLogOnePlusV_eq }

private noncomputable def leaf6684Inputs : Inputs :=
  inputsOfCaches globalInput sk132RoundedInputs
    chi347InputQChi innerPair382Input
    leaf6684InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6684LowerChecked :
    lowerCheck 24 leaf6684Box leaf6684Inputs = true := by
  rfl'

private theorem leaf6684CoversExact : CoversExact 8
    leaf6684Box leaf6684Certificate leaf6684InnerLog leaf6684Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk132RoundedFacts chi347RoundedFacts
    innerPair382RoundedFacts leaf6684RoundedFacts (by rfl)

private theorem leaf6684FlatSound : Sound leaf6684Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6684CertificateValid
    leaf6684InnerLogValid leaf6684CoversExact leaf6684LowerChecked

private noncomputable def leaf6685Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (79/128), chiHi := (5/8) }

private noncomputable def leaf6685Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134217995/134217728) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588828672) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (408567179/268435456) }, upper := { exponent := 1, mantissa := (199/128) } }, logOuter := sk132LogOuterCertificate, logK := sk132LogKCertificate, logChi := chi348LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178255359/17177657344) } }, logDArg := sk132LogDArgCertificate }

private noncomputable def leaf6685InnerLog : WideLogData :=
  innerPair382Data

set_option maxRecDepth 1000000 in
private theorem leaf6685LocalValidity :
    LeafFacts leaf6685Box leaf6685Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6685Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588828672) }) = true
      norm_num [leaf6685Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6685CertificateValid :
    WideCertificateValid leaf6685Box leaf6685Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk132ValidityFacts chi348ValidityFacts
    leaf6685LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6685CoverageChecked :
    coverageCheck (innerAD leaf6685Box) leaf6685InnerLog = true := by
  rfl'

private theorem leaf6685InnerLogValid :
    leaf6685InnerLog.Valid 8 (innerAD leaf6685Box) :=
  wideLogDataValid_of_cachedCheck endpoint99PositiveFacts
    endpoint483PositiveFacts.valid leaf6685CoverageChecked

private noncomputable def leaf6685InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629665/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6685InputLogOnePlusV_eq :
    leaf6685InputLogOnePlusV = outerEnclosure 24
      (leaf6685Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6685RoundedFacts : LeafRoundedFacts 8
    leaf6685Certificate.logOnePlusV leaf6685InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6685InputLogOnePlusV_eq }

private noncomputable def leaf6685Inputs : Inputs :=
  inputsOfCaches globalInput sk132RoundedInputs
    chi348InputQChi innerPair382Input
    leaf6685InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6685LowerChecked :
    lowerCheck 24 leaf6685Box leaf6685Inputs = true := by
  rfl'

private theorem leaf6685CoversExact : CoversExact 8
    leaf6685Box leaf6685Certificate leaf6685InnerLog leaf6685Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk132RoundedFacts chi348RoundedFacts
    innerPair382RoundedFacts leaf6685RoundedFacts (by rfl)

private theorem leaf6685FlatSound : Sound leaf6685Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6685CertificateValid
    leaf6685InnerLogValid leaf6685CoversExact leaf6685LowerChecked

private noncomputable def leaf6686Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (9/16), chiHi := (73/128) }

private noncomputable def leaf6686Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217983/134217728) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34355627008) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (388973123/268435456) }, upper := { exponent := 1, mantissa := (6063/4096) } }, logOuter := sk129LogOuterCertificate, logK := sk129LogKCertificate, logChi := chi335LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68713858045/68711254016) } }, logDArg := sk129LogDArgCertificate }

private noncomputable def leaf6686InnerLog : WideLogData :=
  innerPair734Data

set_option maxRecDepth 1000000 in
private theorem leaf6686LocalValidity :
    LeafFacts leaf6686Box leaf6686Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6686Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34355627008) }) = true
      norm_num [leaf6686Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6686CertificateValid :
    WideCertificateValid leaf6686Box leaf6686Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk129ValidityFacts chi335ValidityFacts
    leaf6686LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6686CoverageChecked :
    coverageCheck (innerAD leaf6686Box) leaf6686InnerLog = true := by
  rfl'

private theorem leaf6686InnerLogValid :
    leaf6686InnerLog.Valid 8 (innerAD leaf6686Box) :=
  wideLogDataValid_of_cachedCheck endpoint470PositiveFacts
    endpoint481PositiveFacts.valid leaf6686CoverageChecked

private noncomputable def leaf6686InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629717/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6686InputLogOnePlusV_eq :
    leaf6686InputLogOnePlusV = outerEnclosure 24
      (leaf6686Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6686RoundedFacts : LeafRoundedFacts 8
    leaf6686Certificate.logOnePlusV leaf6686InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6686InputLogOnePlusV_eq }

private noncomputable def leaf6686Inputs : Inputs :=
  inputsOfCaches globalInput sk129RoundedInputs
    chi335InputQChi innerPair734Input
    leaf6686InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6686LowerChecked :
    lowerCheck 24 leaf6686Box leaf6686Inputs = true := by
  rfl'

private theorem leaf6686CoversExact : CoversExact 8
    leaf6686Box leaf6686Certificate leaf6686InnerLog leaf6686Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk129RoundedFacts chi335RoundedFacts
    innerPair734RoundedFacts leaf6686RoundedFacts (by rfl)

private theorem leaf6686FlatSound : Sound leaf6686Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6686CertificateValid
    leaf6686InnerLogValid leaf6686CoversExact leaf6686LowerChecked

private noncomputable def leaf6687Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (73/128), chiHi := (37/64) }

private noncomputable def leaf6687Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217985/134217728) }, vSqrt := { lower := (65529/65536), upper := (954380743/954321408) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (392511849/268435456) }, upper := { exponent := 1, mantissa := (3059/2048) } }, logOuter := sk129LogOuterCertificate, logK := sk129LogKCertificate, logChi := chi336LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (1908702151/1908642816) } }, logDArg := sk129LogDArgCertificate }

private noncomputable def leaf6687InnerLog : WideLogData :=
  innerPair372Data

set_option maxRecDepth 1000000 in
private theorem leaf6687LocalValidity :
    LeafFacts leaf6687Box leaf6687Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6687Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (954380743/954321408) }) = true
      norm_num [leaf6687Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6687CertificateValid :
    WideCertificateValid leaf6687Box leaf6687Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk129ValidityFacts chi336ValidityFacts
    leaf6687LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6687CoverageChecked :
    coverageCheck (innerAD leaf6687Box) leaf6687InnerLog = true := by
  rfl'

private theorem leaf6687InnerLogValid :
    leaf6687InnerLog.Valid 8 (innerAD leaf6687Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint99PositiveFacts.valid leaf6687CoverageChecked

private noncomputable def leaf6687InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814801/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6687InputLogOnePlusV_eq :
    leaf6687InputLogOnePlusV = outerEnclosure 24
      (leaf6687Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6687RoundedFacts : LeafRoundedFacts 8
    leaf6687Certificate.logOnePlusV leaf6687InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6687InputLogOnePlusV_eq }

private noncomputable def leaf6687Inputs : Inputs :=
  inputsOfCaches globalInput sk129RoundedInputs
    chi336InputQChi innerPair372Input
    leaf6687InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6687LowerChecked :
    lowerCheck 24 leaf6687Box leaf6687Inputs = true := by
  rfl'

private theorem leaf6687CoversExact : CoversExact 8
    leaf6687Box leaf6687Certificate leaf6687InnerLog leaf6687Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk129RoundedFacts chi336RoundedFacts
    innerPair372RoundedFacts leaf6687RoundedFacts (by rfl)

private theorem leaf6687FlatSound : Sound leaf6687Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6687CertificateValid
    leaf6687InnerLogValid leaf6687CoversExact leaf6687LowerChecked

private noncomputable def leaf6688Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (9/16), chiHi := (73/128) }

private noncomputable def leaf6688Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217985/134217728) }, vSqrt := { lower := (8191/8192), upper := (954380743/954320896) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (393691425/268435456) }, upper := { exponent := 1, mantissa := (767/512) } }, logOuter := sk130LogOuterCertificate, logK := sk130LogKCertificate, logChi := chi335LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (1908701639/1908641792) } }, logDArg := sk130LogDArgCertificate }

private noncomputable def leaf6688InnerLog : WideLogData :=
  innerPair372Data

set_option maxRecDepth 1000000 in
private theorem leaf6688LocalValidity :
    LeafFacts leaf6688Box leaf6688Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6688Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (954380743/954320896) }) = true
      norm_num [leaf6688Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6688CertificateValid :
    WideCertificateValid leaf6688Box leaf6688Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk130ValidityFacts chi335ValidityFacts
    leaf6688LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6688CoverageChecked :
    coverageCheck (innerAD leaf6688Box) leaf6688InnerLog = true := by
  rfl'

private theorem leaf6688InnerLogValid :
    leaf6688InnerLog.Valid 8 (innerAD leaf6688Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint99PositiveFacts.valid leaf6688CoverageChecked

private noncomputable def leaf6688InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629607/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6688InputLogOnePlusV_eq :
    leaf6688InputLogOnePlusV = outerEnclosure 24
      (leaf6688Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6688RoundedFacts : LeafRoundedFacts 8
    leaf6688Certificate.logOnePlusV leaf6688InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6688InputLogOnePlusV_eq }

private noncomputable def leaf6688Inputs : Inputs :=
  inputsOfCaches globalInput sk130RoundedInputs
    chi335InputQChi innerPair372Input
    leaf6688InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6688LowerChecked :
    lowerCheck 24 leaf6688Box leaf6688Inputs = true := by
  rfl'

private theorem leaf6688CoversExact : CoversExact 8
    leaf6688Box leaf6688Certificate leaf6688InnerLog leaf6688Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk130RoundedFacts chi335RoundedFacts
    innerPair372RoundedFacts leaf6688RoundedFacts (by rfl)

private theorem leaf6688FlatSound : Sound leaf6688Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6688CertificateValid
    leaf6688InnerLogValid leaf6688CoversExact leaf6688LowerChecked

private noncomputable def leaf6689Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (73/128), chiHi := (37/64) }

private noncomputable def leaf6689Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134217987/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588873728) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (397295683/268435456) }, upper := { exponent := 1, mantissa := (387/256) } }, logOuter := sk130LogOuterCertificate, logK := sk130LogKCertificate, logChi := chi336LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178300415/17177747456) } }, logDArg := sk130LogDArgCertificate }

private noncomputable def leaf6689InnerLog : WideLogData :=
  innerPair737Data

set_option maxRecDepth 1000000 in
private theorem leaf6689LocalValidity :
    LeafFacts leaf6689Box leaf6689Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6689Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588873728) }) = true
      norm_num [leaf6689Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6689CertificateValid :
    WideCertificateValid leaf6689Box leaf6689Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk130ValidityFacts chi336ValidityFacts
    leaf6689LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6689CoverageChecked :
    coverageCheck (innerAD leaf6689Box) leaf6689InnerLog = true := by
  rfl'

private theorem leaf6689InnerLogValid :
    leaf6689InnerLog.Valid 8 (innerAD leaf6689Box) :=
  wideLogDataValid_of_cachedCheck endpoint472PositiveFacts
    endpoint526PositiveFacts.valid leaf6689CoverageChecked

private noncomputable def leaf6689InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629621/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6689InputLogOnePlusV_eq :
    leaf6689InputLogOnePlusV = outerEnclosure 24
      (leaf6689Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6689RoundedFacts : LeafRoundedFacts 8
    leaf6689Certificate.logOnePlusV leaf6689InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6689InputLogOnePlusV_eq }

private noncomputable def leaf6689Inputs : Inputs :=
  inputsOfCaches globalInput sk130RoundedInputs
    chi336InputQChi innerPair737Input
    leaf6689InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6689LowerChecked :
    lowerCheck 24 leaf6689Box leaf6689Inputs = true := by
  rfl'

private theorem leaf6689CoversExact : CoversExact 8
    leaf6689Box leaf6689Certificate leaf6689InnerLog leaf6689Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk130RoundedFacts chi336RoundedFacts
    innerPair737RoundedFacts leaf6689RoundedFacts (by rfl)

private theorem leaf6689FlatSound : Sound leaf6689Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6689CertificateValid
    leaf6689InnerLogValid leaf6689CoversExact leaf6689LowerChecked

private noncomputable def leaf6690Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (37/64), chiHi := (75/128) }

private noncomputable def leaf6690Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134217987/134217728) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588878592) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (396050575/268435456) }, upper := { exponent := 1, mantissa := (6173/4096) } }, logOuter := sk129LogOuterCertificate, logK := sk129LogKCertificate, logChi := chi337LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178305279/17177757184) } }, logDArg := sk129LogDArgCertificate }

private noncomputable def leaf6690InnerLog : WideLogData :=
  innerPair378Data

set_option maxRecDepth 1000000 in
private theorem leaf6690LocalValidity :
    LeafFacts leaf6690Box leaf6690Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6690Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588878592) }) = true
      norm_num [leaf6690Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6690CertificateValid :
    WideCertificateValid leaf6690Box leaf6690Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk129ValidityFacts chi337ValidityFacts
    leaf6690LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6690CoverageChecked :
    coverageCheck (innerAD leaf6690Box) leaf6690InnerLog = true := by
  rfl'

private theorem leaf6690InnerLogValid :
    leaf6690InnerLog.Valid 8 (innerAD leaf6690Box) :=
  wideLogDataValid_of_cachedCheck endpoint98PositiveFacts
    endpoint491PositiveFacts.valid leaf6690CoverageChecked

private noncomputable def leaf6690InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (726851/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf6690InputLogOnePlusV_eq :
    leaf6690InputLogOnePlusV = outerEnclosure 24
      (leaf6690Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6690RoundedFacts : LeafRoundedFacts 8
    leaf6690Certificate.logOnePlusV leaf6690InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6690InputLogOnePlusV_eq }

private noncomputable def leaf6690Inputs : Inputs :=
  inputsOfCaches globalInput sk129RoundedInputs
    chi337InputQChi innerPair378Input
    leaf6690InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6690LowerChecked :
    lowerCheck 24 leaf6690Box leaf6690Inputs = true := by
  rfl'

private theorem leaf6690CoversExact : CoversExact 8
    leaf6690Box leaf6690Certificate leaf6690InnerLog leaf6690Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk129RoundedFacts chi337RoundedFacts
    innerPair378RoundedFacts leaf6690RoundedFacts (by rfl)

private theorem leaf6690FlatSound : Sound leaf6690Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6690CertificateValid
    leaf6690InnerLogValid leaf6690CoversExact leaf6690LowerChecked

private noncomputable def leaf6691Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (75/128), chiHi := (19/32) }

private noncomputable def leaf6691Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134217989/134217728) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588864512) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (399589301/268435456) }, upper := { exponent := 1, mantissa := (1557/1024) } }, logOuter := sk129LogOuterCertificate, logK := sk129LogKCertificate, logChi := chi338LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178291199/17177729024) } }, logDArg := sk129LogDArgCertificate }

private noncomputable def leaf6691InnerLog : WideLogData :=
  innerPair376Data

set_option maxRecDepth 1000000 in
private theorem leaf6691LocalValidity :
    LeafFacts leaf6691Box leaf6691Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6691Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588864512) }) = true
      norm_num [leaf6691Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6691CertificateValid :
    WideCertificateValid leaf6691Box leaf6691Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk129ValidityFacts chi338ValidityFacts
    leaf6691LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6691CoverageChecked :
    coverageCheck (innerAD leaf6691Box) leaf6691InnerLog = true := by
  rfl'

private theorem leaf6691InnerLogValid :
    leaf6691InnerLog.Valid 8 (innerAD leaf6691Box) :=
  wideLogDataValid_of_cachedCheck endpoint98PositiveFacts
    endpoint482PositiveFacts.valid leaf6691CoverageChecked

private noncomputable def leaf6691InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814815/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6691InputLogOnePlusV_eq :
    leaf6691InputLogOnePlusV = outerEnclosure 24
      (leaf6691Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6691RoundedFacts : LeafRoundedFacts 8
    leaf6691Certificate.logOnePlusV leaf6691InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6691InputLogOnePlusV_eq }

private noncomputable def leaf6691Inputs : Inputs :=
  inputsOfCaches globalInput sk129RoundedInputs
    chi338InputQChi innerPair376Input
    leaf6691InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6691LowerChecked :
    lowerCheck 24 leaf6691Box leaf6691Inputs = true := by
  rfl'

private theorem leaf6691CoversExact : CoversExact 8
    leaf6691Box leaf6691Certificate leaf6691InnerLog leaf6691Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk129RoundedFacts chi338RoundedFacts
    innerPair376RoundedFacts leaf6691RoundedFacts (by rfl)

private theorem leaf6691FlatSound : Sound leaf6691Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6691CertificateValid
    leaf6691InnerLogValid leaf6691CoversExact leaf6691LowerChecked

private noncomputable def leaf6692Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (37/64), chiHi := (75/128) }

private noncomputable def leaf6692Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134217989/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588859392) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (400899941/268435456) }, upper := { exponent := 1, mantissa := (781/512) } }, logOuter := sk130LogOuterCertificate, logK := sk130LogKCertificate, logChi := chi337LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178286079/17177718784) } }, logDArg := sk130LogDArgCertificate }

private noncomputable def leaf6692InnerLog : WideLogData :=
  innerPair376Data

set_option maxRecDepth 1000000 in
private theorem leaf6692LocalValidity :
    LeafFacts leaf6692Box leaf6692Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6692Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588859392) }) = true
      norm_num [leaf6692Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6692CertificateValid :
    WideCertificateValid leaf6692Box leaf6692Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk130ValidityFacts chi337ValidityFacts
    leaf6692LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6692CoverageChecked :
    coverageCheck (innerAD leaf6692Box) leaf6692InnerLog = true := by
  rfl'

private theorem leaf6692InnerLogValid :
    leaf6692InnerLog.Valid 8 (innerAD leaf6692Box) :=
  wideLogDataValid_of_cachedCheck endpoint98PositiveFacts
    endpoint482PositiveFacts.valid leaf6692CoverageChecked

private noncomputable def leaf6692InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629635/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6692InputLogOnePlusV_eq :
    leaf6692InputLogOnePlusV = outerEnclosure 24
      (leaf6692Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6692RoundedFacts : LeafRoundedFacts 8
    leaf6692Certificate.logOnePlusV leaf6692InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6692InputLogOnePlusV_eq }

private noncomputable def leaf6692Inputs : Inputs :=
  inputsOfCaches globalInput sk130RoundedInputs
    chi337InputQChi innerPair376Input
    leaf6692InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6692LowerChecked :
    lowerCheck 24 leaf6692Box leaf6692Inputs = true := by
  rfl'

private theorem leaf6692CoversExact : CoversExact 8
    leaf6692Box leaf6692Certificate leaf6692InnerLog leaf6692Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk130RoundedFacts chi337RoundedFacts
    innerPair376RoundedFacts leaf6692RoundedFacts (by rfl)

private theorem leaf6692FlatSound : Sound leaf6692Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6692CertificateValid
    leaf6692InnerLogValid leaf6692CoversExact leaf6692LowerChecked

private noncomputable def leaf6693Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (75/128), chiHi := (19/32) }

private noncomputable def leaf6693Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134217991/134217728) }, vSqrt := { lower := (8191/8192), upper := (2863142229/2862948352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (404504199/268435456) }, upper := { exponent := 1, mantissa := (197/128) } }, logOuter := sk130LogOuterCertificate, logK := sk130LogKCertificate, logChi := chi338LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (5726090581/5725896704) } }, logDArg := sk130LogDArgCertificate }

private noncomputable def leaf6693InnerLog : WideLogData :=
  innerPair385Data

set_option maxRecDepth 1000000 in
private theorem leaf6693LocalValidity :
    LeafFacts leaf6693Box leaf6693Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6693Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (2863142229/2862948352) }) = true
      norm_num [leaf6693Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6693CertificateValid :
    WideCertificateValid leaf6693Box leaf6693Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk130ValidityFacts chi338ValidityFacts
    leaf6693LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6693CoverageChecked :
    coverageCheck (innerAD leaf6693Box) leaf6693InnerLog = true := by
  rfl'

private theorem leaf6693InnerLogValid :
    leaf6693InnerLog.Valid 8 (innerAD leaf6693Box) :=
  wideLogDataValid_of_cachedCheck endpoint99PositiveFacts
    endpoint527PositiveFacts.valid leaf6693CoverageChecked

private noncomputable def leaf6693InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629649/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6693InputLogOnePlusV_eq :
    leaf6693InputLogOnePlusV = outerEnclosure 24
      (leaf6693Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6693RoundedFacts : LeafRoundedFacts 8
    leaf6693Certificate.logOnePlusV leaf6693InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6693InputLogOnePlusV_eq }

private noncomputable def leaf6693Inputs : Inputs :=
  inputsOfCaches globalInput sk130RoundedInputs
    chi338InputQChi innerPair385Input
    leaf6693InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6693LowerChecked :
    lowerCheck 24 leaf6693Box leaf6693Inputs = true := by
  rfl'

private theorem leaf6693CoversExact : CoversExact 8
    leaf6693Box leaf6693Certificate leaf6693InnerLog leaf6693Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk130RoundedFacts chi338RoundedFacts
    innerPair385RoundedFacts leaf6693RoundedFacts (by rfl)

private theorem leaf6693FlatSound : Sound leaf6693Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6693CertificateValid
    leaf6693InnerLogValid leaf6693CoversExact leaf6693LowerChecked

private noncomputable def leaf6694Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (19/32), chiHi := (77/128) }

private noncomputable def leaf6694Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134217991/134217728) }, vSqrt := { lower := (65529/65536), upper := (2863142229/2862950144) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (403128027/268435456) }, upper := { exponent := 1, mantissa := (6283/4096) } }, logOuter := sk129LogOuterCertificate, logK := sk129LogKCertificate, logChi := chi339LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (5726092373/5725900288) } }, logDArg := sk129LogDArgCertificate }

private noncomputable def leaf6694InnerLog : WideLogData :=
  innerPair385Data

set_option maxRecDepth 1000000 in
private theorem leaf6694LocalValidity :
    LeafFacts leaf6694Box leaf6694Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6694Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (2863142229/2862950144) }) = true
      norm_num [leaf6694Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6694CertificateValid :
    WideCertificateValid leaf6694Box leaf6694Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk129ValidityFacts chi339ValidityFacts
    leaf6694LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6694CoverageChecked :
    coverageCheck (innerAD leaf6694Box) leaf6694InnerLog = true := by
  rfl'

private theorem leaf6694InnerLogValid :
    leaf6694InnerLog.Valid 8 (innerAD leaf6694Box) :=
  wideLogDataValid_of_cachedCheck endpoint99PositiveFacts
    endpoint527PositiveFacts.valid leaf6694CoverageChecked

private noncomputable def leaf6694InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907411/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6694InputLogOnePlusV_eq :
    leaf6694InputLogOnePlusV = outerEnclosure 24
      (leaf6694Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6694RoundedFacts : LeafRoundedFacts 8
    leaf6694Certificate.logOnePlusV leaf6694InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6694InputLogOnePlusV_eq }

private noncomputable def leaf6694Inputs : Inputs :=
  inputsOfCaches globalInput sk129RoundedInputs
    chi339InputQChi innerPair385Input
    leaf6694InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6694LowerChecked :
    lowerCheck 24 leaf6694Box leaf6694Inputs = true := by
  rfl'

private theorem leaf6694CoversExact : CoversExact 8
    leaf6694Box leaf6694Certificate leaf6694InnerLog leaf6694Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk129RoundedFacts chi339RoundedFacts
    innerPair385RoundedFacts leaf6694RoundedFacts (by rfl)

private theorem leaf6694FlatSound : Sound leaf6694Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6694CertificateValid
    leaf6694InnerLogValid leaf6694CoversExact leaf6694LowerChecked

private noncomputable def leaf6695Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (77/128), chiHi := (39/64) }

private noncomputable def leaf6695Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134217993/134217728) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588836352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (406666753/268435456) }, upper := { exponent := 1, mantissa := (3169/2048) } }, logOuter := sk129LogOuterCertificate, logK := sk129LogKCertificate, logChi := chi340LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178263039/17177672704) } }, logDArg := sk129LogDArgCertificate }

private noncomputable def leaf6695InnerLog : WideLogData :=
  innerPair382Data

set_option maxRecDepth 1000000 in
private theorem leaf6695LocalValidity :
    LeafFacts leaf6695Box leaf6695Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6695Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588836352) }) = true
      norm_num [leaf6695Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6695CertificateValid :
    WideCertificateValid leaf6695Box leaf6695Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk129ValidityFacts chi340ValidityFacts
    leaf6695LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6695CoverageChecked :
    coverageCheck (innerAD leaf6695Box) leaf6695InnerLog = true := by
  rfl'

private theorem leaf6695InnerLogValid :
    leaf6695InnerLog.Valid 8 (innerAD leaf6695Box) :=
  wideLogDataValid_of_cachedCheck endpoint99PositiveFacts
    endpoint483PositiveFacts.valid leaf6695CoverageChecked

private noncomputable def leaf6695InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629657/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6695InputLogOnePlusV_eq :
    leaf6695InputLogOnePlusV = outerEnclosure 24
      (leaf6695Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6695RoundedFacts : LeafRoundedFacts 8
    leaf6695Certificate.logOnePlusV leaf6695InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6695InputLogOnePlusV_eq }

private noncomputable def leaf6695Inputs : Inputs :=
  inputsOfCaches globalInput sk129RoundedInputs
    chi340InputQChi innerPair382Input
    leaf6695InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6695LowerChecked :
    lowerCheck 24 leaf6695Box leaf6695Inputs = true := by
  rfl'

private theorem leaf6695CoversExact : CoversExact 8
    leaf6695Box leaf6695Certificate leaf6695InnerLog leaf6695Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk129RoundedFacts chi340RoundedFacts
    innerPair382RoundedFacts leaf6695RoundedFacts (by rfl)

private theorem leaf6695FlatSound : Sound leaf6695Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6695CertificateValid
    leaf6695InnerLogValid leaf6695CoversExact leaf6695LowerChecked

private noncomputable def leaf6696Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (19/32), chiHi := (77/128) }

private noncomputable def leaf6696Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134217993/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588830720) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (408108457/268435456) }, upper := { exponent := 1, mantissa := (795/512) } }, logOuter := sk130LogOuterCertificate, logK := sk130LogKCertificate, logChi := chi339LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178257407/17177661440) } }, logDArg := sk130LogDArgCertificate }

private noncomputable def leaf6696InnerLog : WideLogData :=
  innerPair382Data

set_option maxRecDepth 1000000 in
private theorem leaf6696LocalValidity :
    LeafFacts leaf6696Box leaf6696Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6696Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588830720) }) = true
      norm_num [leaf6696Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6696CertificateValid :
    WideCertificateValid leaf6696Box leaf6696Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk130ValidityFacts chi339ValidityFacts
    leaf6696LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6696CoverageChecked :
    coverageCheck (innerAD leaf6696Box) leaf6696InnerLog = true := by
  rfl'

private theorem leaf6696InnerLogValid :
    leaf6696InnerLog.Valid 8 (innerAD leaf6696Box) :=
  wideLogDataValid_of_cachedCheck endpoint99PositiveFacts
    endpoint483PositiveFacts.valid leaf6696CoverageChecked

private noncomputable def leaf6696InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629663/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6696InputLogOnePlusV_eq :
    leaf6696InputLogOnePlusV = outerEnclosure 24
      (leaf6696Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6696RoundedFacts : LeafRoundedFacts 8
    leaf6696Certificate.logOnePlusV leaf6696InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6696InputLogOnePlusV_eq }

private noncomputable def leaf6696Inputs : Inputs :=
  inputsOfCaches globalInput sk130RoundedInputs
    chi339InputQChi innerPair382Input
    leaf6696InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6696LowerChecked :
    lowerCheck 24 leaf6696Box leaf6696Inputs = true := by
  rfl'

private theorem leaf6696CoversExact : CoversExact 8
    leaf6696Box leaf6696Certificate leaf6696InnerLog leaf6696Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk130RoundedFacts chi339RoundedFacts
    innerPair382RoundedFacts leaf6696RoundedFacts (by rfl)

private theorem leaf6696FlatSound : Sound leaf6696Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6696CertificateValid
    leaf6696InnerLogValid leaf6696CoversExact leaf6696LowerChecked

private noncomputable def leaf6697Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (77/128), chiHi := (39/64) }

private noncomputable def leaf6697Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134217995/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588816384) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (411712715/268435456) }, upper := { exponent := 1, mantissa := (401/256) } }, logOuter := sk130LogOuterCertificate, logK := sk130LogKCertificate, logChi := chi340LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178243071/17177632768) } }, logDArg := sk130LogDArgCertificate }

private noncomputable def leaf6697InnerLog : WideLogData :=
  innerPair747Data

set_option maxRecDepth 1000000 in
private theorem leaf6697LocalValidity :
    LeafFacts leaf6697Box leaf6697Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6697Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588816384) }) = true
      norm_num [leaf6697Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6697CertificateValid :
    WideCertificateValid leaf6697Box leaf6697Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk130ValidityFacts chi340ValidityFacts
    leaf6697LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6697CoverageChecked :
    coverageCheck (innerAD leaf6697Box) leaf6697InnerLog = true := by
  rfl'

private theorem leaf6697InnerLogValid :
    leaf6697InnerLog.Valid 8 (innerAD leaf6697Box) :=
  wideLogDataValid_of_cachedCheck endpoint482PositiveFacts
    endpoint528PositiveFacts.valid leaf6697CoverageChecked

private noncomputable def leaf6697InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629677/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6697InputLogOnePlusV_eq :
    leaf6697InputLogOnePlusV = outerEnclosure 24
      (leaf6697Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6697RoundedFacts : LeafRoundedFacts 8
    leaf6697Certificate.logOnePlusV leaf6697InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6697InputLogOnePlusV_eq }

private noncomputable def leaf6697Inputs : Inputs :=
  inputsOfCaches globalInput sk130RoundedInputs
    chi340InputQChi innerPair747Input
    leaf6697InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6697LowerChecked :
    lowerCheck 24 leaf6697Box leaf6697Inputs = true := by
  rfl'

private theorem leaf6697CoversExact : CoversExact 8
    leaf6697Box leaf6697Certificate leaf6697InnerLog leaf6697Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk130RoundedFacts chi340RoundedFacts
    innerPair747RoundedFacts leaf6697RoundedFacts (by rfl)

private theorem leaf6697FlatSound : Sound leaf6697Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6697CertificateValid
    leaf6697InnerLogValid leaf6697CoversExact leaf6697LowerChecked

private noncomputable def leaf6698Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (39/64), chiHi := (79/128) }

private noncomputable def leaf6698Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134217995/134217728) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588822272) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (410205479/268435456) }, upper := { exponent := 1, mantissa := (6393/4096) } }, logOuter := sk129LogOuterCertificate, logK := sk129LogKCertificate, logChi := chi347LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178248959/17177644544) } }, logDArg := sk129LogDArgCertificate }

private noncomputable def leaf6698InnerLog : WideLogData :=
  innerPair382Data

set_option maxRecDepth 1000000 in
private theorem leaf6698LocalValidity :
    LeafFacts leaf6698Box leaf6698Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6698Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588822272) }) = true
      norm_num [leaf6698Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6698CertificateValid :
    WideCertificateValid leaf6698Box leaf6698Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk129ValidityFacts chi347ValidityFacts
    leaf6698LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6698CoverageChecked :
    coverageCheck (innerAD leaf6698Box) leaf6698InnerLog = true := by
  rfl'

private theorem leaf6698InnerLogValid :
    leaf6698InnerLog.Valid 8 (innerAD leaf6698Box) :=
  wideLogDataValid_of_cachedCheck endpoint99PositiveFacts
    endpoint483PositiveFacts.valid leaf6698CoverageChecked

private noncomputable def leaf6698InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629671/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6698InputLogOnePlusV_eq :
    leaf6698InputLogOnePlusV = outerEnclosure 24
      (leaf6698Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6698RoundedFacts : LeafRoundedFacts 8
    leaf6698Certificate.logOnePlusV leaf6698InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6698InputLogOnePlusV_eq }

private noncomputable def leaf6698Inputs : Inputs :=
  inputsOfCaches globalInput sk129RoundedInputs
    chi347InputQChi innerPair382Input
    leaf6698InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6698LowerChecked :
    lowerCheck 24 leaf6698Box leaf6698Inputs = true := by
  rfl'

private theorem leaf6698CoversExact : CoversExact 8
    leaf6698Box leaf6698Certificate leaf6698InnerLog leaf6698Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk129RoundedFacts chi347RoundedFacts
    innerPair382RoundedFacts leaf6698RoundedFacts (by rfl)

private theorem leaf6698FlatSound : Sound leaf6698Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6698CertificateValid
    leaf6698InnerLogValid leaf6698CoversExact leaf6698LowerChecked

private noncomputable def leaf6699Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (79/128), chiHi := (5/8) }

private noncomputable def leaf6699Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134217997/134217728) }, vSqrt := { lower := (65529/65536), upper := (2863142229/2862936064) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (413744205/268435456) }, upper := { exponent := 1, mantissa := (403/256) } }, logOuter := sk129LogOuterCertificate, logK := sk129LogKCertificate, logChi := chi348LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (5726078293/5725872128) } }, logDArg := sk129LogDArgCertificate }

private noncomputable def leaf6699InnerLog : WideLogData :=
  innerPair744Data

set_option maxRecDepth 1000000 in
private theorem leaf6699LocalValidity :
    LeafFacts leaf6699Box leaf6699Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6699Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (2863142229/2862936064) }) = true
      norm_num [leaf6699Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6699CertificateValid :
    WideCertificateValid leaf6699Box leaf6699Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk129ValidityFacts chi348ValidityFacts
    leaf6699LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6699CoverageChecked :
    coverageCheck (innerAD leaf6699Box) leaf6699InnerLog = true := by
  rfl'

private theorem leaf6699InnerLogValid :
    leaf6699InnerLog.Valid 8 (innerAD leaf6699Box) :=
  wideLogDataValid_of_cachedCheck endpoint482PositiveFacts
    endpoint484PositiveFacts.valid leaf6699CoverageChecked

private noncomputable def leaf6699InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629685/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6699InputLogOnePlusV_eq :
    leaf6699InputLogOnePlusV = outerEnclosure 24
      (leaf6699Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6699RoundedFacts : LeafRoundedFacts 8
    leaf6699Certificate.logOnePlusV leaf6699InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6699InputLogOnePlusV_eq }

private noncomputable def leaf6699Inputs : Inputs :=
  inputsOfCaches globalInput sk129RoundedInputs
    chi348InputQChi innerPair744Input
    leaf6699InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6699LowerChecked :
    lowerCheck 24 leaf6699Box leaf6699Inputs = true := by
  rfl'

private theorem leaf6699CoversExact : CoversExact 8
    leaf6699Box leaf6699Certificate leaf6699InnerLog leaf6699Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk129RoundedFacts chi348RoundedFacts
    innerPair744RoundedFacts leaf6699RoundedFacts (by rfl)

private theorem leaf6699FlatSound : Sound leaf6699Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6699CertificateValid
    leaf6699InnerLogValid leaf6699CoversExact leaf6699LowerChecked

private noncomputable def leaf6700Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (39/64), chiHi := (79/128) }

private noncomputable def leaf6700Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134217997/134217728) }, vSqrt := { lower := (8191/8192), upper := (2863142229/2862934016) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (415316973/268435456) }, upper := { exponent := 1, mantissa := (809/512) } }, logOuter := sk130LogOuterCertificate, logK := sk130LogKCertificate, logChi := chi347LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (5726076245/5725868032) } }, logDArg := sk130LogDArgCertificate }

private noncomputable def leaf6700InnerLog : WideLogData :=
  innerPair744Data

set_option maxRecDepth 1000000 in
private theorem leaf6700LocalValidity :
    LeafFacts leaf6700Box leaf6700Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6700Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (2863142229/2862934016) }) = true
      norm_num [leaf6700Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6700CertificateValid :
    WideCertificateValid leaf6700Box leaf6700Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk130ValidityFacts chi347ValidityFacts
    leaf6700LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6700CoverageChecked :
    coverageCheck (innerAD leaf6700Box) leaf6700InnerLog = true := by
  rfl'

private theorem leaf6700InnerLogValid :
    leaf6700InnerLog.Valid 8 (innerAD leaf6700Box) :=
  wideLogDataValid_of_cachedCheck endpoint482PositiveFacts
    endpoint484PositiveFacts.valid leaf6700CoverageChecked

private noncomputable def leaf6700InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629691/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6700InputLogOnePlusV_eq :
    leaf6700InputLogOnePlusV = outerEnclosure 24
      (leaf6700Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6700RoundedFacts : LeafRoundedFacts 8
    leaf6700Certificate.logOnePlusV leaf6700InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6700InputLogOnePlusV_eq }

private noncomputable def leaf6700Inputs : Inputs :=
  inputsOfCaches globalInput sk130RoundedInputs
    chi347InputQChi innerPair744Input
    leaf6700InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6700LowerChecked :
    lowerCheck 24 leaf6700Box leaf6700Inputs = true := by
  rfl'

private theorem leaf6700CoversExact : CoversExact 8
    leaf6700Box leaf6700Certificate leaf6700InnerLog leaf6700Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk130RoundedFacts chi347RoundedFacts
    innerPair744RoundedFacts leaf6700RoundedFacts (by rfl)

private theorem leaf6700FlatSound : Sound leaf6700Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6700CertificateValid
    leaf6700InnerLogValid leaf6700CoversExact leaf6700LowerChecked

private noncomputable def leaf6701Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (79/128), chiHi := (5/8) }

private noncomputable def leaf6701Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134217999/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588787712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (418921231/268435456) }, upper := { exponent := 1, mantissa := (51/32) } }, logOuter := sk130LogOuterCertificate, logK := sk130LogKCertificate, logChi := chi348LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178214399/17177575424) } }, logDArg := sk130LogDArgCertificate }

private noncomputable def leaf6701InnerLog : WideLogData :=
  innerPair744Data

set_option maxRecDepth 1000000 in
private theorem leaf6701LocalValidity :
    LeafFacts leaf6701Box leaf6701Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6701Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588787712) }) = true
      norm_num [leaf6701Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6701CertificateValid :
    WideCertificateValid leaf6701Box leaf6701Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk130ValidityFacts chi348ValidityFacts
    leaf6701LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6701CoverageChecked :
    coverageCheck (innerAD leaf6701Box) leaf6701InnerLog = true := by
  rfl'

private theorem leaf6701InnerLogValid :
    leaf6701InnerLog.Valid 8 (innerAD leaf6701Box) :=
  wideLogDataValid_of_cachedCheck endpoint482PositiveFacts
    endpoint484PositiveFacts.valid leaf6701CoverageChecked

private noncomputable def leaf6701InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629705/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6701InputLogOnePlusV_eq :
    leaf6701InputLogOnePlusV = outerEnclosure 24
      (leaf6701Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6701RoundedFacts : LeafRoundedFacts 8
    leaf6701Certificate.logOnePlusV leaf6701InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6701InputLogOnePlusV_eq }

private noncomputable def leaf6701Inputs : Inputs :=
  inputsOfCaches globalInput sk130RoundedInputs
    chi348InputQChi innerPair744Input
    leaf6701InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6701LowerChecked :
    lowerCheck 24 leaf6701Box leaf6701Inputs = true := by
  rfl'

private theorem leaf6701CoversExact : CoversExact 8
    leaf6701Box leaf6701Certificate leaf6701InnerLog leaf6701Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk130RoundedFacts chi348RoundedFacts
    innerPair744RoundedFacts leaf6701RoundedFacts (by rfl)

private theorem leaf6701FlatSound : Sound leaf6701Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6701CertificateValid
    leaf6701InnerLogValid leaf6701CoversExact leaf6701LowerChecked

private noncomputable def component135Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (9/16), chiHi := (37/64) }

set_option maxRecDepth 1000000 in
private theorem component135Node0_sound : Sound component135Node0Box :=
  sound_of_literal_split component135Node0Box leaf6670Box leaf6671Box
    .chi (73/128) (by rfl) (by rfl)
    leaf6670FlatSound leaf6671FlatSound

private noncomputable def component135Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (9/16), chiHi := (37/64) }

set_option maxRecDepth 1000000 in
private theorem component135Node1_sound : Sound component135Node1Box :=
  sound_of_literal_split component135Node1Box leaf6672Box leaf6673Box
    .chi (73/128) (by rfl) (by rfl)
    leaf6672FlatSound leaf6673FlatSound

private noncomputable def component135Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (9/16), chiHi := (37/64) }

set_option maxRecDepth 1000000 in
private theorem component135Node2_sound : Sound component135Node2Box :=
  sound_of_literal_split component135Node2Box component135Node0Box component135Node1Box
    .k (53/16) (by rfl) (by rfl)
    component135Node0_sound component135Node1_sound

private noncomputable def component135Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (37/64), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component135Node3_sound : Sound component135Node3Box :=
  sound_of_literal_split component135Node3Box leaf6674Box leaf6675Box
    .chi (75/128) (by rfl) (by rfl)
    leaf6674FlatSound leaf6675FlatSound

private noncomputable def component135Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (37/64), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component135Node4_sound : Sound component135Node4Box :=
  sound_of_literal_split component135Node4Box leaf6676Box leaf6677Box
    .chi (75/128) (by rfl) (by rfl)
    leaf6676FlatSound leaf6677FlatSound

private noncomputable def component135Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (37/64), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component135Node5_sound : Sound component135Node5Box :=
  sound_of_literal_split component135Node5Box component135Node3Box component135Node4Box
    .k (53/16) (by rfl) (by rfl)
    component135Node3_sound component135Node4_sound

private noncomputable def component135Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (9/16), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component135Node6_sound : Sound component135Node6Box :=
  sound_of_literal_split component135Node6Box component135Node2Box component135Node5Box
    .chi (37/64) (by rfl) (by rfl)
    component135Node2_sound component135Node5_sound

private noncomputable def component135Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (19/32), chiHi := (39/64) }

set_option maxRecDepth 1000000 in
private theorem component135Node7_sound : Sound component135Node7Box :=
  sound_of_literal_split component135Node7Box leaf6678Box leaf6679Box
    .chi (77/128) (by rfl) (by rfl)
    leaf6678FlatSound leaf6679FlatSound

private noncomputable def component135Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (19/32), chiHi := (39/64) }

set_option maxRecDepth 1000000 in
private theorem component135Node8_sound : Sound component135Node8Box :=
  sound_of_literal_split component135Node8Box leaf6680Box leaf6681Box
    .chi (77/128) (by rfl) (by rfl)
    leaf6680FlatSound leaf6681FlatSound

private noncomputable def component135Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (19/32), chiHi := (39/64) }

set_option maxRecDepth 1000000 in
private theorem component135Node9_sound : Sound component135Node9Box :=
  sound_of_literal_split component135Node9Box component135Node7Box component135Node8Box
    .k (53/16) (by rfl) (by rfl)
    component135Node7_sound component135Node8_sound

private noncomputable def component135Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (39/64), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component135Node10_sound : Sound component135Node10Box :=
  sound_of_literal_split component135Node10Box leaf6682Box leaf6683Box
    .chi (79/128) (by rfl) (by rfl)
    leaf6682FlatSound leaf6683FlatSound

private noncomputable def component135Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (39/64), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component135Node11_sound : Sound component135Node11Box :=
  sound_of_literal_split component135Node11Box leaf6684Box leaf6685Box
    .chi (79/128) (by rfl) (by rfl)
    leaf6684FlatSound leaf6685FlatSound

private noncomputable def component135Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (39/64), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component135Node12_sound : Sound component135Node12Box :=
  sound_of_literal_split component135Node12Box component135Node10Box component135Node11Box
    .k (53/16) (by rfl) (by rfl)
    component135Node10_sound component135Node11_sound

private noncomputable def component135Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (19/32), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component135Node13_sound : Sound component135Node13Box :=
  sound_of_literal_split component135Node13Box component135Node9Box component135Node12Box
    .chi (39/64) (by rfl) (by rfl)
    component135Node9_sound component135Node12_sound

private noncomputable def component135Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (9/16), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component135Node14_sound : Sound component135Node14Box :=
  sound_of_literal_split component135Node14Box component135Node6Box component135Node13Box
    .chi (19/32) (by rfl) (by rfl)
    component135Node6_sound component135Node13_sound

private noncomputable def component135Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (9/16), chiHi := (37/64) }

set_option maxRecDepth 1000000 in
private theorem component135Node15_sound : Sound component135Node15Box :=
  sound_of_literal_split component135Node15Box leaf6686Box leaf6687Box
    .chi (73/128) (by rfl) (by rfl)
    leaf6686FlatSound leaf6687FlatSound

private noncomputable def component135Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (9/16), chiHi := (37/64) }

set_option maxRecDepth 1000000 in
private theorem component135Node16_sound : Sound component135Node16Box :=
  sound_of_literal_split component135Node16Box leaf6688Box leaf6689Box
    .chi (73/128) (by rfl) (by rfl)
    leaf6688FlatSound leaf6689FlatSound

private noncomputable def component135Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (9/16), chiHi := (37/64) }

set_option maxRecDepth 1000000 in
private theorem component135Node17_sound : Sound component135Node17Box :=
  sound_of_literal_split component135Node17Box component135Node15Box component135Node16Box
    .k (55/16) (by rfl) (by rfl)
    component135Node15_sound component135Node16_sound

private noncomputable def component135Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (37/64), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component135Node18_sound : Sound component135Node18Box :=
  sound_of_literal_split component135Node18Box leaf6690Box leaf6691Box
    .chi (75/128) (by rfl) (by rfl)
    leaf6690FlatSound leaf6691FlatSound

private noncomputable def component135Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (37/64), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component135Node19_sound : Sound component135Node19Box :=
  sound_of_literal_split component135Node19Box leaf6692Box leaf6693Box
    .chi (75/128) (by rfl) (by rfl)
    leaf6692FlatSound leaf6693FlatSound

private noncomputable def component135Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (37/64), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component135Node20_sound : Sound component135Node20Box :=
  sound_of_literal_split component135Node20Box component135Node18Box component135Node19Box
    .k (55/16) (by rfl) (by rfl)
    component135Node18_sound component135Node19_sound

private noncomputable def component135Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (9/16), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component135Node21_sound : Sound component135Node21Box :=
  sound_of_literal_split component135Node21Box component135Node17Box component135Node20Box
    .chi (37/64) (by rfl) (by rfl)
    component135Node17_sound component135Node20_sound

private noncomputable def component135Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (19/32), chiHi := (39/64) }

set_option maxRecDepth 1000000 in
private theorem component135Node22_sound : Sound component135Node22Box :=
  sound_of_literal_split component135Node22Box leaf6694Box leaf6695Box
    .chi (77/128) (by rfl) (by rfl)
    leaf6694FlatSound leaf6695FlatSound

private noncomputable def component135Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (19/32), chiHi := (39/64) }

set_option maxRecDepth 1000000 in
private theorem component135Node23_sound : Sound component135Node23Box :=
  sound_of_literal_split component135Node23Box leaf6696Box leaf6697Box
    .chi (77/128) (by rfl) (by rfl)
    leaf6696FlatSound leaf6697FlatSound

private noncomputable def component135Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (19/32), chiHi := (39/64) }

set_option maxRecDepth 1000000 in
private theorem component135Node24_sound : Sound component135Node24Box :=
  sound_of_literal_split component135Node24Box component135Node22Box component135Node23Box
    .k (55/16) (by rfl) (by rfl)
    component135Node22_sound component135Node23_sound

private noncomputable def component135Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (39/64), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component135Node25_sound : Sound component135Node25Box :=
  sound_of_literal_split component135Node25Box leaf6698Box leaf6699Box
    .chi (79/128) (by rfl) (by rfl)
    leaf6698FlatSound leaf6699FlatSound

private noncomputable def component135Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (39/64), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component135Node26_sound : Sound component135Node26Box :=
  sound_of_literal_split component135Node26Box leaf6700Box leaf6701Box
    .chi (79/128) (by rfl) (by rfl)
    leaf6700FlatSound leaf6701FlatSound

private noncomputable def component135Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (39/64), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component135Node27_sound : Sound component135Node27Box :=
  sound_of_literal_split component135Node27Box component135Node25Box component135Node26Box
    .k (55/16) (by rfl) (by rfl)
    component135Node25_sound component135Node26_sound

private noncomputable def component135Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (19/32), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component135Node28_sound : Sound component135Node28Box :=
  sound_of_literal_split component135Node28Box component135Node24Box component135Node27Box
    .chi (39/64) (by rfl) (by rfl)
    component135Node24_sound component135Node27_sound

private noncomputable def component135Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (9/16), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component135Node29_sound : Sound component135Node29Box :=
  sound_of_literal_split component135Node29Box component135Node21Box component135Node28Box
    .chi (19/32) (by rfl) (by rfl)
    component135Node21_sound component135Node28_sound

noncomputable def component135Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (7/2), chiLo := (9/16), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
theorem component135_sound : Sound component135Box :=
  sound_of_literal_split component135Box component135Node14Box component135Node29Box
    .k (27/8) (by rfl) (by rfl)
    component135Node14_sound component135Node29_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
