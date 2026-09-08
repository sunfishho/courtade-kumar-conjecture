import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch6
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch10
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch5
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch9
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

private noncomputable def leaf5877Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (13/32), chiHi := (53/128) }

private noncomputable def leaf5877Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435787/268435456) }, vSqrt := { lower := (8191/8192), upper := (4908388937/4908096000) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (650060727/536870912) }, upper := { exponent := 1, mantissa := (10085/8192) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi263LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (9816484937/9816192000) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf5877InnerLog : WideLogData :=
  innerPair589Data

set_option maxRecDepth 1000000 in
private theorem leaf5877LocalValidity :
    LeafFacts leaf5877Box leaf5877Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5877Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4908388937/4908096000) }) = true
      norm_num [leaf5877Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5877CertificateValid :
    WideCertificateValid leaf5877Box leaf5877Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi263ValidityFacts
    leaf5877LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5877CoverageChecked :
    coverageCheck (innerAD leaf5877Box) leaf5877InnerLog = true := by
  rfl'

private theorem leaf5877InnerLogValid :
    leaf5877InnerLog.Valid 8 (innerAD leaf5877Box) :=
  wideLogDataValid_of_cachedCheck endpoint305PositiveFacts
    endpoint94PositiveFacts.valid leaf5877CoverageChecked

private noncomputable def leaf5877InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629581/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5877InputLogOnePlusV_eq :
    leaf5877InputLogOnePlusV = outerEnclosure 24
      (leaf5877Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5877RoundedFacts : LeafRoundedFacts 8
    leaf5877Certificate.logOnePlusV leaf5877InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5877InputLogOnePlusV_eq }

private noncomputable def leaf5877Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi263InputQChi innerPair589Input
    leaf5877InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5877LowerChecked :
    lowerCheck 24 leaf5877Box leaf5877Inputs = true := by
  rfl'

private theorem leaf5877CoversExact : CoversExact 8
    leaf5877Box leaf5877Certificate leaf5877InnerLog leaf5877Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi263RoundedFacts
    innerPair589RoundedFacts leaf5877RoundedFacts (by rfl)

private theorem leaf5877FlatSound : Sound leaf5877Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5877CertificateValid
    leaf5877InnerLogValid leaf5877CoversExact leaf5877LowerChecked

private noncomputable def leaf5878Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (13/32), chiHi := (53/128) }

private noncomputable def leaf5878Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435789/268435456) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356644864) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (653468389/536870912) }, upper := { exponent := 1, mantissa := (5069/4096) } }, logOuter := sk168LogOuterCertificate, logK := sk168LogKCertificate, logChi := chi263LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715367423/68713289728) } }, logDArg := sk168LogDArgCertificate }

private noncomputable def leaf5878InnerLog : WideLogData :=
  innerPair594Data

set_option maxRecDepth 1000000 in
private theorem leaf5878LocalValidity :
    LeafFacts leaf5878Box leaf5878Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5878Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356644864) }) = true
      norm_num [leaf5878Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5878CertificateValid :
    WideCertificateValid leaf5878Box leaf5878Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk168ValidityFacts chi263ValidityFacts
    leaf5878LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5878CoverageChecked :
    coverageCheck (innerAD leaf5878Box) leaf5878InnerLog = true := by
  rfl'

private theorem leaf5878InnerLogValid :
    leaf5878InnerLog.Valid 8 (innerAD leaf5878Box) :=
  wideLogDataValid_of_cachedCheck endpoint308PositiveFacts
    endpoint414PositiveFacts.valid leaf5878CoverageChecked

private noncomputable def leaf5878InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907397/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5878InputLogOnePlusV_eq :
    leaf5878InputLogOnePlusV = outerEnclosure 24
      (leaf5878Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5878RoundedFacts : LeafRoundedFacts 8
    leaf5878Certificate.logOnePlusV leaf5878InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5878InputLogOnePlusV_eq }

private noncomputable def leaf5878Inputs : Inputs :=
  inputsOfCaches globalInput sk168RoundedInputs
    chi263InputQChi innerPair594Input
    leaf5878InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5878LowerChecked :
    lowerCheck 24 leaf5878Box leaf5878Inputs = true := by
  rfl'

private theorem leaf5878CoversExact : CoversExact 8
    leaf5878Box leaf5878Certificate leaf5878InnerLog leaf5878Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk168RoundedFacts chi263RoundedFacts
    innerPair594RoundedFacts leaf5878RoundedFacts (by rfl)

private theorem leaf5878FlatSound : Sound leaf5878Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5878CertificateValid
    leaf5878InnerLogValid leaf5878CoversExact leaf5878LowerChecked

private noncomputable def leaf5879Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (53/128), chiHi := (27/64) }

private noncomputable def leaf5879Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435789/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68713228288) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (657400309/536870912) }, upper := { exponent := 1, mantissa := (5099/4096) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi264LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429624829/137426456576) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf5879InnerLog : WideLogData :=
  innerPair285Data

set_option maxRecDepth 1000000 in
private theorem leaf5879LocalValidity :
    LeafFacts leaf5879Box leaf5879Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5879Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68713228288) }) = true
      norm_num [leaf5879Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5879CertificateValid :
    WideCertificateValid leaf5879Box leaf5879Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi264ValidityFacts
    leaf5879LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5879CoverageChecked :
    coverageCheck (innerAD leaf5879Box) leaf5879InnerLog = true := by
  rfl'

private theorem leaf5879InnerLogValid :
    leaf5879InnerLog.Valid 8 (innerAD leaf5879Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint79PositiveFacts.valid leaf5879CoverageChecked

private noncomputable def leaf5879InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907367/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5879InputLogOnePlusV_eq :
    leaf5879InputLogOnePlusV = outerEnclosure 24
      (leaf5879Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5879RoundedFacts : LeafRoundedFacts 8
    leaf5879Certificate.logOnePlusV leaf5879InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5879InputLogOnePlusV_eq }

private noncomputable def leaf5879Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi264InputQChi innerPair285Input
    leaf5879InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5879LowerChecked :
    lowerCheck 24 leaf5879Box leaf5879Inputs = true := by
  rfl'

private theorem leaf5879CoversExact : CoversExact 8
    leaf5879Box leaf5879Certificate leaf5879InnerLog leaf5879Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi264RoundedFacts
    innerPair285RoundedFacts leaf5879RoundedFacts (by rfl)

private theorem leaf5879FlatSound : Sound leaf5879Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5879CertificateValid
    leaf5879InnerLogValid leaf5879CoversExact leaf5879LowerChecked

private noncomputable def leaf5880Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (53/128), chiHi := (27/64) }

private noncomputable def leaf5880Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435791/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68713172992) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (660873503/536870912) }, upper := { exponent := 1, mantissa := (2563/2048) } }, logOuter := sk168LogOuterCertificate, logK := sk168LogKCertificate, logChi := chi264LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429569533/137426345984) } }, logDArg := sk168LogDArgCertificate }

private noncomputable def leaf5880InnerLog : WideLogData :=
  innerPair658Data

set_option maxRecDepth 1000000 in
private theorem leaf5880LocalValidity :
    LeafFacts leaf5880Box leaf5880Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5880Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68713172992) }) = true
      norm_num [leaf5880Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5880CertificateValid :
    WideCertificateValid leaf5880Box leaf5880Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk168ValidityFacts chi264ValidityFacts
    leaf5880LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5880CoverageChecked :
    coverageCheck (innerAD leaf5880Box) leaf5880InnerLog = true := by
  rfl'

private theorem leaf5880InnerLogValid :
    leaf5880InnerLog.Valid 8 (innerAD leaf5880Box) :=
  wideLogDataValid_of_cachedCheck endpoint403PositiveFacts
    endpoint419PositiveFacts.valid leaf5880CoverageChecked

private noncomputable def leaf5880InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814737/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5880InputLogOnePlusV_eq :
    leaf5880InputLogOnePlusV = outerEnclosure 24
      (leaf5880Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5880RoundedFacts : LeafRoundedFacts 8
    leaf5880Certificate.logOnePlusV leaf5880InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5880InputLogOnePlusV_eq }

private noncomputable def leaf5880Inputs : Inputs :=
  inputsOfCaches globalInput sk168RoundedInputs
    chi264InputQChi innerPair658Input
    leaf5880InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5880LowerChecked :
    lowerCheck 24 leaf5880Box leaf5880Inputs = true := by
  rfl'

private theorem leaf5880CoversExact : CoversExact 8
    leaf5880Box leaf5880Certificate leaf5880InnerLog leaf5880Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk168RoundedFacts chi264RoundedFacts
    innerPair658RoundedFacts leaf5880RoundedFacts (by rfl)

private theorem leaf5880FlatSound : Sound leaf5880Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5880CertificateValid
    leaf5880InnerLogValid leaf5880CoversExact leaf5880LowerChecked

private noncomputable def leaf5881Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (13/32), chiHi := (53/128) }

private noncomputable def leaf5881Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435791/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68713235456) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (656876051/536870912) }, upper := { exponent := 1, mantissa := (10191/8192) } }, logOuter := sk161LogOuterCertificate, logK := sk161LogKCertificate, logChi := chi263LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429631997/137426470912) } }, logDArg := sk161LogDArgCertificate }

private noncomputable def leaf5881InnerLog : WideLogData :=
  innerPair285Data

set_option maxRecDepth 1000000 in
private theorem leaf5881LocalValidity :
    LeafFacts leaf5881Box leaf5881Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5881Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68713235456) }) = true
      norm_num [leaf5881Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5881CertificateValid :
    WideCertificateValid leaf5881Box leaf5881Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk161ValidityFacts chi263ValidityFacts
    leaf5881LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5881CoverageChecked :
    coverageCheck (innerAD leaf5881Box) leaf5881InnerLog = true := by
  rfl'

private theorem leaf5881InnerLogValid :
    leaf5881InnerLog.Valid 8 (innerAD leaf5881Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint79PositiveFacts.valid leaf5881CoverageChecked

private noncomputable def leaf5881InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629467/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5881InputLogOnePlusV_eq :
    leaf5881InputLogOnePlusV = outerEnclosure 24
      (leaf5881Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5881RoundedFacts : LeafRoundedFacts 8
    leaf5881Certificate.logOnePlusV leaf5881InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5881InputLogOnePlusV_eq }

private noncomputable def leaf5881Inputs : Inputs :=
  inputsOfCaches globalInput sk161RoundedInputs
    chi263InputQChi innerPair285Input
    leaf5881InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5881LowerChecked :
    lowerCheck 24 leaf5881Box leaf5881Inputs = true := by
  rfl'

private theorem leaf5881CoversExact : CoversExact 8
    leaf5881Box leaf5881Certificate leaf5881InnerLog leaf5881Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk161RoundedFacts chi263RoundedFacts
    innerPair285RoundedFacts leaf5881RoundedFacts (by rfl)

private theorem leaf5881FlatSound : Sound leaf5881Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5881CertificateValid
    leaf5881InnerLogValid leaf5881CoversExact leaf5881LowerChecked

private noncomputable def leaf5882Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (13/32), chiHi := (53/128) }

private noncomputable def leaf5882Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435793/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68713181184) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (660283713/536870912) }, upper := { exponent := 1, mantissa := (2561/2048) } }, logOuter := sk162LogOuterCertificate, logK := sk162LogKCertificate, logChi := chi263LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429577725/137426362368) } }, logDArg := sk162LogDArgCertificate }

private noncomputable def leaf5882InnerLog : WideLogData :=
  innerPair680Data

set_option maxRecDepth 1000000 in
private theorem leaf5882LocalValidity :
    LeafFacts leaf5882Box leaf5882Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5882Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68713181184) }) = true
      norm_num [leaf5882Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5882CertificateValid :
    WideCertificateValid leaf5882Box leaf5882Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk162ValidityFacts chi263ValidityFacts
    leaf5882LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5882CoverageChecked :
    coverageCheck (innerAD leaf5882Box) leaf5882InnerLog = true := by
  rfl'

private theorem leaf5882InnerLogValid :
    leaf5882InnerLog.Valid 8 (innerAD leaf5882Box) :=
  wideLogDataValid_of_cachedCheck endpoint432PositiveFacts
    endpoint433PositiveFacts.valid leaf5882CoverageChecked

private noncomputable def leaf5882InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629473/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5882InputLogOnePlusV_eq :
    leaf5882InputLogOnePlusV = outerEnclosure 24
      (leaf5882Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5882RoundedFacts : LeafRoundedFacts 8
    leaf5882Certificate.logOnePlusV leaf5882InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5882InputLogOnePlusV_eq }

private noncomputable def leaf5882Inputs : Inputs :=
  inputsOfCaches globalInput sk162RoundedInputs
    chi263InputQChi innerPair680Input
    leaf5882InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5882LowerChecked :
    lowerCheck 24 leaf5882Box leaf5882Inputs = true := by
  rfl'

private theorem leaf5882CoversExact : CoversExact 8
    leaf5882Box leaf5882Certificate leaf5882InnerLog leaf5882Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk162RoundedFacts chi263RoundedFacts
    innerPair680RoundedFacts leaf5882RoundedFacts (by rfl)

private theorem leaf5882FlatSound : Sound leaf5882Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5882CertificateValid
    leaf5882InnerLogValid leaf5882CoversExact leaf5882LowerChecked

private noncomputable def leaf5883Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (53/128), chiHi := (27/64) }

private noncomputable def leaf5883Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435793/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68713117696) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (664346697/536870912) }, upper := { exponent := 1, mantissa := (5153/4096) } }, logOuter := sk161LogOuterCertificate, logK := sk161LogKCertificate, logChi := chi264LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429514237/137426235392) } }, logDArg := sk161LogDArgCertificate }

private noncomputable def leaf5883InnerLog : WideLogData :=
  innerPair363Data

set_option maxRecDepth 1000000 in
private theorem leaf5883LocalValidity :
    LeafFacts leaf5883Box leaf5883Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5883Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68713117696) }) = true
      norm_num [leaf5883Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5883CertificateValid :
    WideCertificateValid leaf5883Box leaf5883Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk161ValidityFacts chi264ValidityFacts
    leaf5883LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5883CoverageChecked :
    coverageCheck (innerAD leaf5883Box) leaf5883InnerLog = true := by
  rfl'

private theorem leaf5883InnerLogValid :
    leaf5883InnerLog.Valid 8 (innerAD leaf5883Box) :=
  wideLogDataValid_of_cachedCheck endpoint94PositiveFacts
    endpoint434PositiveFacts.valid leaf5883CoverageChecked

private noncomputable def leaf5883InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629481/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5883InputLogOnePlusV_eq :
    leaf5883InputLogOnePlusV = outerEnclosure 24
      (leaf5883Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5883RoundedFacts : LeafRoundedFacts 8
    leaf5883Certificate.logOnePlusV leaf5883InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5883InputLogOnePlusV_eq }

private noncomputable def leaf5883Inputs : Inputs :=
  inputsOfCaches globalInput sk161RoundedInputs
    chi264InputQChi innerPair363Input
    leaf5883InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5883LowerChecked :
    lowerCheck 24 leaf5883Box leaf5883Inputs = true := by
  rfl'

private theorem leaf5883CoversExact : CoversExact 8
    leaf5883Box leaf5883Certificate leaf5883InnerLog leaf5883Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk161RoundedFacts chi264RoundedFacts
    innerPair363RoundedFacts leaf5883RoundedFacts (by rfl)

private theorem leaf5883FlatSound : Sound leaf5883Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5883CertificateValid
    leaf5883InnerLogValid leaf5883CoversExact leaf5883LowerChecked

private noncomputable def leaf5884Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (53/128), chiHi := (27/64) }

private noncomputable def leaf5884Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435795/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68713062400) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (667819891/536870912) }, upper := { exponent := 1, mantissa := (1295/1024) } }, logOuter := sk162LogOuterCertificate, logK := sk162LogKCertificate, logChi := chi264LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429458941/137426124800) } }, logDArg := sk162LogDArgCertificate }

private noncomputable def leaf5884InnerLog : WideLogData :=
  innerPair668Data

set_option maxRecDepth 1000000 in
private theorem leaf5884LocalValidity :
    LeafFacts leaf5884Box leaf5884Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5884Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68713062400) }) = true
      norm_num [leaf5884Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5884CertificateValid :
    WideCertificateValid leaf5884Box leaf5884Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk162ValidityFacts chi264ValidityFacts
    leaf5884LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5884CoverageChecked :
    coverageCheck (innerAD leaf5884Box) leaf5884InnerLog = true := by
  rfl'

private theorem leaf5884InnerLogValid :
    leaf5884InnerLog.Valid 8 (innerAD leaf5884Box) :=
  wideLogDataValid_of_cachedCheck endpoint414PositiveFacts
    endpoint434PositiveFacts.valid leaf5884CoverageChecked

private noncomputable def leaf5884InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726843/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf5884InputLogOnePlusV_eq :
    leaf5884InputLogOnePlusV = outerEnclosure 24
      (leaf5884Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5884RoundedFacts : LeafRoundedFacts 8
    leaf5884Certificate.logOnePlusV leaf5884InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5884InputLogOnePlusV_eq }

private noncomputable def leaf5884Inputs : Inputs :=
  inputsOfCaches globalInput sk162RoundedInputs
    chi264InputQChi innerPair668Input
    leaf5884InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5884LowerChecked :
    lowerCheck 24 leaf5884Box leaf5884Inputs = true := by
  rfl'

private theorem leaf5884CoversExact : CoversExact 8
    leaf5884Box leaf5884Certificate leaf5884InnerLog leaf5884Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk162RoundedFacts chi264RoundedFacts
    innerPair668RoundedFacts leaf5884RoundedFacts (by rfl)

private theorem leaf5884FlatSound : Sound leaf5884Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5884CertificateValid
    leaf5884InnerLogValid leaf5884CoversExact leaf5884LowerChecked

private noncomputable def leaf5885Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (27/64), chiHi := (55/128) }

private noncomputable def leaf5885Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435791/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68713112576) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (664739891/536870912) }, upper := { exponent := 1, mantissa := (10311/8192) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi265LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429509117/137426225152) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf5885InnerLog : WideLogData :=
  innerPair363Data

set_option maxRecDepth 1000000 in
private theorem leaf5885LocalValidity :
    LeafFacts leaf5885Box leaf5885Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5885Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68713112576) }) = true
      norm_num [leaf5885Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5885CertificateValid :
    WideCertificateValid leaf5885Box leaf5885Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi265ValidityFacts
    leaf5885LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5885CoverageChecked :
    coverageCheck (innerAD leaf5885Box) leaf5885InnerLog = true := by
  rfl'

private theorem leaf5885InnerLogValid :
    leaf5885InnerLog.Valid 8 (innerAD leaf5885Box) :=
  wideLogDataValid_of_cachedCheck endpoint94PositiveFacts
    endpoint434PositiveFacts.valid leaf5885CoverageChecked

private noncomputable def leaf5885InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814741/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5885InputLogOnePlusV_eq :
    leaf5885InputLogOnePlusV = outerEnclosure 24
      (leaf5885Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5885RoundedFacts : LeafRoundedFacts 8
    leaf5885Certificate.logOnePlusV leaf5885InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5885InputLogOnePlusV_eq }

private noncomputable def leaf5885Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi265InputQChi innerPair363Input
    leaf5885InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5885LowerChecked :
    lowerCheck 24 leaf5885Box leaf5885Inputs = true := by
  rfl'

private theorem leaf5885CoversExact : CoversExact 8
    leaf5885Box leaf5885Certificate leaf5885InnerLog leaf5885Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi265RoundedFacts
    innerPair363RoundedFacts leaf5885RoundedFacts (by rfl)

private theorem leaf5885FlatSound : Sound leaf5885Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5885CertificateValid
    leaf5885InnerLogValid leaf5885CoversExact leaf5885LowerChecked

private noncomputable def leaf5886Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (27/64), chiHi := (55/128) }

private noncomputable def leaf5886Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435793/268435456) }, vSqrt := { lower := (8191/8192), upper := (5285876657/5285619712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (668278617/536870912) }, upper := { exponent := 1, mantissa := (5183/4096) } }, logOuter := sk168LogOuterCertificate, logK := sk168LogKCertificate, logChi := chi265LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (10571496369/10571239424) } }, logDArg := sk168LogDArgCertificate }

private noncomputable def leaf5886InnerLog : WideLogData :=
  innerPair286Data

set_option maxRecDepth 1000000 in
private theorem leaf5886LocalValidity :
    LeafFacts leaf5886Box leaf5886Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5886Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5285876657/5285619712) }) = true
      norm_num [leaf5886Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5886CertificateValid :
    WideCertificateValid leaf5886Box leaf5886Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk168ValidityFacts chi265ValidityFacts
    leaf5886LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5886CoverageChecked :
    coverageCheck (innerAD leaf5886Box) leaf5886InnerLog = true := by
  rfl'

private theorem leaf5886InnerLogValid :
    leaf5886InnerLog.Valid 8 (innerAD leaf5886Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint90PositiveFacts.valid leaf5886CoverageChecked

private noncomputable def leaf5886InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629489/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5886InputLogOnePlusV_eq :
    leaf5886InputLogOnePlusV = outerEnclosure 24
      (leaf5886Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5886RoundedFacts : LeafRoundedFacts 8
    leaf5886Certificate.logOnePlusV leaf5886InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5886InputLogOnePlusV_eq }

private noncomputable def leaf5886Inputs : Inputs :=
  inputsOfCaches globalInput sk168RoundedInputs
    chi265InputQChi innerPair286Input
    leaf5886InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5886LowerChecked :
    lowerCheck 24 leaf5886Box leaf5886Inputs = true := by
  rfl'

private theorem leaf5886CoversExact : CoversExact 8
    leaf5886Box leaf5886Certificate leaf5886InnerLog leaf5886Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk168RoundedFacts chi265RoundedFacts
    innerPair286RoundedFacts leaf5886RoundedFacts (by rfl)

private theorem leaf5886FlatSound : Sound leaf5886Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5886CertificateValid
    leaf5886InnerLogValid leaf5886CoversExact leaf5886LowerChecked

private noncomputable def leaf5887Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (55/128), chiHi := (7/16) }

private noncomputable def leaf5887Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435793/268435456) }, vSqrt := { lower := (8191/8192), upper := (4042140973/4041940992) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (672079473/536870912) }, upper := { exponent := 1, mantissa := (1303/1024) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi266LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (8084081965/8083881984) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf5887InnerLog : WideLogData :=
  innerPair293Data

set_option maxRecDepth 1000000 in
private theorem leaf5887LocalValidity :
    LeafFacts leaf5887Box leaf5887Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5887Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4042140973/4041940992) }) = true
      norm_num [leaf5887Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5887CertificateValid :
    WideCertificateValid leaf5887Box leaf5887Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi266ValidityFacts
    leaf5887LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5887CoverageChecked :
    coverageCheck (innerAD leaf5887Box) leaf5887InnerLog = true := by
  rfl'

private theorem leaf5887InnerLogValid :
    leaf5887InnerLog.Valid 8 (innerAD leaf5887Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint90PositiveFacts.valid leaf5887CoverageChecked

private noncomputable def leaf5887InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453687/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf5887InputLogOnePlusV_eq :
    leaf5887InputLogOnePlusV = outerEnclosure 24
      (leaf5887Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5887RoundedFacts : LeafRoundedFacts 8
    leaf5887Certificate.logOnePlusV leaf5887InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5887InputLogOnePlusV_eq }

private noncomputable def leaf5887Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi266InputQChi innerPair293Input
    leaf5887InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5887LowerChecked :
    lowerCheck 24 leaf5887Box leaf5887Inputs = true := by
  rfl'

private theorem leaf5887CoversExact : CoversExact 8
    leaf5887Box leaf5887Certificate leaf5887InnerLog leaf5887Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi266RoundedFacts
    innerPair293RoundedFacts leaf5887RoundedFacts (by rfl)

private theorem leaf5887FlatSound : Sound leaf5887Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5887CertificateValid
    leaf5887InnerLogValid leaf5887CoversExact leaf5887LowerChecked

private noncomputable def leaf5888Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (55/128), chiHi := (7/16) }

private noncomputable def leaf5888Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435795/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712939520) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (675683731/536870912) }, upper := { exponent := 1, mantissa := (655/512) } }, logOuter := sk168LogOuterCertificate, logK := sk168LogKCertificate, logChi := chi266LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429336061/137425879040) } }, logDArg := sk168LogDArgCertificate }

private noncomputable def leaf5888InnerLog : WideLogData :=
  innerPair293Data

set_option maxRecDepth 1000000 in
private theorem leaf5888LocalValidity :
    LeafFacts leaf5888Box leaf5888Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5888Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712939520) }) = true
      norm_num [leaf5888Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5888CertificateValid :
    WideCertificateValid leaf5888Box leaf5888Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk168ValidityFacts chi266ValidityFacts
    leaf5888LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5888CoverageChecked :
    coverageCheck (innerAD leaf5888Box) leaf5888InnerLog = true := by
  rfl'

private theorem leaf5888InnerLogValid :
    leaf5888InnerLog.Valid 8 (innerAD leaf5888Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint90PositiveFacts.valid leaf5888CoverageChecked

private noncomputable def leaf5888InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629503/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5888InputLogOnePlusV_eq :
    leaf5888InputLogOnePlusV = outerEnclosure 24
      (leaf5888Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5888RoundedFacts : LeafRoundedFacts 8
    leaf5888Certificate.logOnePlusV leaf5888InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5888InputLogOnePlusV_eq }

private noncomputable def leaf5888Inputs : Inputs :=
  inputsOfCaches globalInput sk168RoundedInputs
    chi266InputQChi innerPair293Input
    leaf5888InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5888LowerChecked :
    lowerCheck 24 leaf5888Box leaf5888Inputs = true := by
  rfl'

private theorem leaf5888CoversExact : CoversExact 8
    leaf5888Box leaf5888Certificate leaf5888InnerLog leaf5888Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk168RoundedFacts chi266RoundedFacts
    innerPair293RoundedFacts leaf5888RoundedFacts (by rfl)

private theorem leaf5888FlatSound : Sound leaf5888Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5888CertificateValid
    leaf5888InnerLogValid leaf5888CoversExact leaf5888LowerChecked

private noncomputable def leaf5889Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (27/64), chiHi := (55/128) }

private noncomputable def leaf5889Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435795/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712999936) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (671817343/536870912) }, upper := { exponent := 1, mantissa := (10421/8192) } }, logOuter := sk161LogOuterCertificate, logK := sk161LogKCertificate, logChi := chi265LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429396477/137425999872) } }, logDArg := sk161LogDArgCertificate }

private noncomputable def leaf5889InnerLog : WideLogData :=
  innerPair293Data

set_option maxRecDepth 1000000 in
private theorem leaf5889LocalValidity :
    LeafFacts leaf5889Box leaf5889Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5889Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712999936) }) = true
      norm_num [leaf5889Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5889CertificateValid :
    WideCertificateValid leaf5889Box leaf5889Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk161ValidityFacts chi265ValidityFacts
    leaf5889LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5889CoverageChecked :
    coverageCheck (innerAD leaf5889Box) leaf5889InnerLog = true := by
  rfl'

private theorem leaf5889InnerLogValid :
    leaf5889InnerLog.Valid 8 (innerAD leaf5889Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint90PositiveFacts.valid leaf5889CoverageChecked

private noncomputable def leaf5889InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629495/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5889InputLogOnePlusV_eq :
    leaf5889InputLogOnePlusV = outerEnclosure 24
      (leaf5889Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5889RoundedFacts : LeafRoundedFacts 8
    leaf5889Certificate.logOnePlusV leaf5889InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5889InputLogOnePlusV_eq }

private noncomputable def leaf5889Inputs : Inputs :=
  inputsOfCaches globalInput sk161RoundedInputs
    chi265InputQChi innerPair293Input
    leaf5889InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5889LowerChecked :
    lowerCheck 24 leaf5889Box leaf5889Inputs = true := by
  rfl'

private theorem leaf5889CoversExact : CoversExact 8
    leaf5889Box leaf5889Certificate leaf5889InnerLog leaf5889Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk161RoundedFacts chi265RoundedFacts
    innerPair293RoundedFacts leaf5889RoundedFacts (by rfl)

private theorem leaf5889FlatSound : Sound leaf5889Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5889CertificateValid
    leaf5889InnerLogValid leaf5889CoversExact leaf5889LowerChecked

private noncomputable def leaf5890Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (27/64), chiHi := (55/128) }

private noncomputable def leaf5890Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435797/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712943616) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (675356069/536870912) }, upper := { exponent := 1, mantissa := (2619/2048) } }, logOuter := sk162LogOuterCertificate, logK := sk162LogKCertificate, logChi := chi265LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429340157/137425887232) } }, logDArg := sk162LogDArgCertificate }

private noncomputable def leaf5890InnerLog : WideLogData :=
  innerPair293Data

set_option maxRecDepth 1000000 in
private theorem leaf5890LocalValidity :
    LeafFacts leaf5890Box leaf5890Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5890Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712943616) }) = true
      norm_num [leaf5890Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5890CertificateValid :
    WideCertificateValid leaf5890Box leaf5890Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk162ValidityFacts chi265ValidityFacts
    leaf5890LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5890CoverageChecked :
    coverageCheck (innerAD leaf5890Box) leaf5890InnerLog = true := by
  rfl'

private theorem leaf5890InnerLogValid :
    leaf5890InnerLog.Valid 8 (innerAD leaf5890Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint90PositiveFacts.valid leaf5890CoverageChecked

private noncomputable def leaf5890InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814751/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5890InputLogOnePlusV_eq :
    leaf5890InputLogOnePlusV = outerEnclosure 24
      (leaf5890Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5890RoundedFacts : LeafRoundedFacts 8
    leaf5890Certificate.logOnePlusV leaf5890InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5890InputLogOnePlusV_eq }

private noncomputable def leaf5890Inputs : Inputs :=
  inputsOfCaches globalInput sk162RoundedInputs
    chi265InputQChi innerPair293Input
    leaf5890InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5890LowerChecked :
    lowerCheck 24 leaf5890Box leaf5890Inputs = true := by
  rfl'

private theorem leaf5890CoversExact : CoversExact 8
    leaf5890Box leaf5890Certificate leaf5890InnerLog leaf5890Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk162RoundedFacts chi265RoundedFacts
    innerPair293RoundedFacts leaf5890RoundedFacts (by rfl)

private theorem leaf5890FlatSound : Sound leaf5890Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5890CertificateValid
    leaf5890InnerLogValid leaf5890CoversExact leaf5890LowerChecked

private noncomputable def leaf5891Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (55/128), chiHi := (7/16) }

private noncomputable def leaf5891Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435797/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712882176) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (679287989/536870912) }, upper := { exponent := 1, mantissa := (1317/1024) } }, logOuter := sk161LogOuterCertificate, logK := sk161LogKCertificate, logChi := chi266LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429278717/137425764352) } }, logDArg := sk161LogDArgCertificate }

private noncomputable def leaf5891InnerLog : WideLogData :=
  innerPair671Data

set_option maxRecDepth 1000000 in
private theorem leaf5891LocalValidity :
    LeafFacts leaf5891Box leaf5891Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5891Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712882176) }) = true
      norm_num [leaf5891Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5891CertificateValid :
    WideCertificateValid leaf5891Box leaf5891Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk161ValidityFacts chi266ValidityFacts
    leaf5891LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5891CoverageChecked :
    coverageCheck (innerAD leaf5891Box) leaf5891InnerLog = true := by
  rfl'

private theorem leaf5891InnerLogValid :
    leaf5891InnerLog.Valid 8 (innerAD leaf5891Box) :=
  wideLogDataValid_of_cachedCheck endpoint419PositiveFacts
    endpoint435PositiveFacts.valid leaf5891CoverageChecked

private noncomputable def leaf5891InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814755/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5891InputLogOnePlusV_eq :
    leaf5891InputLogOnePlusV = outerEnclosure 24
      (leaf5891Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5891RoundedFacts : LeafRoundedFacts 8
    leaf5891Certificate.logOnePlusV leaf5891InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5891InputLogOnePlusV_eq }

private noncomputable def leaf5891Inputs : Inputs :=
  inputsOfCaches globalInput sk161RoundedInputs
    chi266InputQChi innerPair671Input
    leaf5891InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5891LowerChecked :
    lowerCheck 24 leaf5891Box leaf5891Inputs = true := by
  rfl'

private theorem leaf5891CoversExact : CoversExact 8
    leaf5891Box leaf5891Certificate leaf5891InnerLog leaf5891Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk161RoundedFacts chi266RoundedFacts
    innerPair671RoundedFacts leaf5891RoundedFacts (by rfl)

private theorem leaf5891FlatSound : Sound leaf5891Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5891CertificateValid
    leaf5891InnerLogValid leaf5891CoversExact leaf5891LowerChecked

private noncomputable def leaf5892Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (55/128), chiHi := (7/16) }

private noncomputable def leaf5892Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435799/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712824832) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (682892247/536870912) }, upper := { exponent := 1, mantissa := (331/256) } }, logOuter := sk162LogOuterCertificate, logK := sk162LogKCertificate, logChi := chi266LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429221373/137425649664) } }, logDArg := sk162LogDArgCertificate }

private noncomputable def leaf5892InnerLog : WideLogData :=
  innerPair682Data

set_option maxRecDepth 1000000 in
private theorem leaf5892LocalValidity :
    LeafFacts leaf5892Box leaf5892Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5892Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712824832) }) = true
      norm_num [leaf5892Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5892CertificateValid :
    WideCertificateValid leaf5892Box leaf5892Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk162ValidityFacts chi266ValidityFacts
    leaf5892LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5892CoverageChecked :
    coverageCheck (innerAD leaf5892Box) leaf5892InnerLog = true := by
  rfl'

private theorem leaf5892InnerLogValid :
    leaf5892InnerLog.Valid 8 (innerAD leaf5892Box) :=
  wideLogDataValid_of_cachedCheck endpoint434PositiveFacts
    endpoint436PositiveFacts.valid leaf5892CoverageChecked

private noncomputable def leaf5892InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629517/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5892InputLogOnePlusV_eq :
    leaf5892InputLogOnePlusV = outerEnclosure 24
      (leaf5892Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5892RoundedFacts : LeafRoundedFacts 8
    leaf5892Certificate.logOnePlusV leaf5892InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5892InputLogOnePlusV_eq }

private noncomputable def leaf5892Inputs : Inputs :=
  inputsOfCaches globalInput sk162RoundedInputs
    chi266InputQChi innerPair682Input
    leaf5892InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5892LowerChecked :
    lowerCheck 24 leaf5892Box leaf5892Inputs = true := by
  rfl'

private theorem leaf5892CoversExact : CoversExact 8
    leaf5892Box leaf5892Certificate leaf5892InnerLog leaf5892Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk162RoundedFacts chi266RoundedFacts
    innerPair682RoundedFacts leaf5892RoundedFacts (by rfl)

private theorem leaf5892FlatSound : Sound leaf5892Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5892CertificateValid
    leaf5892InnerLogValid leaf5892CoversExact leaf5892LowerChecked

private noncomputable def leaf5893Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (13/32), chiHi := (53/128) }

private noncomputable def leaf5893Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435795/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68713126912) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (663691375/536870912) }, upper := { exponent := 1, mantissa := (10297/8192) } }, logOuter := sk163LogOuterCertificate, logK := sk163LogKCertificate, logChi := chi263LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429523453/137426253824) } }, logDArg := sk163LogDArgCertificate }

private noncomputable def leaf5893InnerLog : WideLogData :=
  innerPair362Data

set_option maxRecDepth 1000000 in
private theorem leaf5893LocalValidity :
    LeafFacts leaf5893Box leaf5893Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5893Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68713126912) }) = true
      norm_num [leaf5893Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5893CertificateValid :
    WideCertificateValid leaf5893Box leaf5893Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk163ValidityFacts chi263ValidityFacts
    leaf5893LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5893CoverageChecked :
    coverageCheck (innerAD leaf5893Box) leaf5893InnerLog = true := by
  rfl'

private theorem leaf5893InnerLogValid :
    leaf5893InnerLog.Valid 8 (innerAD leaf5893Box) :=
  wideLogDataValid_of_cachedCheck endpoint94PositiveFacts
    endpoint419PositiveFacts.valid leaf5893CoverageChecked

private noncomputable def leaf5893InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453685/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf5893InputLogOnePlusV_eq :
    leaf5893InputLogOnePlusV = outerEnclosure 24
      (leaf5893Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5893RoundedFacts : LeafRoundedFacts 8
    leaf5893Certificate.logOnePlusV leaf5893InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5893InputLogOnePlusV_eq }

private noncomputable def leaf5893Inputs : Inputs :=
  inputsOfCaches globalInput sk163RoundedInputs
    chi263InputQChi innerPair362Input
    leaf5893InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5893LowerChecked :
    lowerCheck 24 leaf5893Box leaf5893Inputs = true := by
  rfl'

private theorem leaf5893CoversExact : CoversExact 8
    leaf5893Box leaf5893Certificate leaf5893InnerLog leaf5893Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk163RoundedFacts chi263RoundedFacts
    innerPair362RoundedFacts leaf5893RoundedFacts (by rfl)

private theorem leaf5893FlatSound : Sound leaf5893Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5893CertificateValid
    leaf5893InnerLogValid leaf5893CoversExact leaf5893LowerChecked

private noncomputable def leaf5894Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (13/32), chiHi := (53/128) }

private noncomputable def leaf5894Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435797/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68713072640) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (667099037/536870912) }, upper := { exponent := 1, mantissa := (5175/4096) } }, logOuter := sk164LogOuterCertificate, logK := sk164LogKCertificate, logChi := chi263LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429469181/137426145280) } }, logDArg := sk164LogDArgCertificate }

private noncomputable def leaf5894InnerLog : WideLogData :=
  innerPair668Data

set_option maxRecDepth 1000000 in
private theorem leaf5894LocalValidity :
    LeafFacts leaf5894Box leaf5894Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5894Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68713072640) }) = true
      norm_num [leaf5894Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5894CertificateValid :
    WideCertificateValid leaf5894Box leaf5894Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk164ValidityFacts chi263ValidityFacts
    leaf5894LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5894CoverageChecked :
    coverageCheck (innerAD leaf5894Box) leaf5894InnerLog = true := by
  rfl'

private theorem leaf5894InnerLogValid :
    leaf5894InnerLog.Valid 8 (innerAD leaf5894Box) :=
  wideLogDataValid_of_cachedCheck endpoint414PositiveFacts
    endpoint434PositiveFacts.valid leaf5894CoverageChecked

private noncomputable def leaf5894InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629487/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5894InputLogOnePlusV_eq :
    leaf5894InputLogOnePlusV = outerEnclosure 24
      (leaf5894Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5894RoundedFacts : LeafRoundedFacts 8
    leaf5894Certificate.logOnePlusV leaf5894InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5894InputLogOnePlusV_eq }

private noncomputable def leaf5894Inputs : Inputs :=
  inputsOfCaches globalInput sk164RoundedInputs
    chi263InputQChi innerPair668Input
    leaf5894InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5894LowerChecked :
    lowerCheck 24 leaf5894Box leaf5894Inputs = true := by
  rfl'

private theorem leaf5894CoversExact : CoversExact 8
    leaf5894Box leaf5894Certificate leaf5894InnerLog leaf5894Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk164RoundedFacts chi263RoundedFacts
    innerPair668RoundedFacts leaf5894RoundedFacts (by rfl)

private theorem leaf5894FlatSound : Sound leaf5894Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5894CertificateValid
    leaf5894InnerLogValid leaf5894CoversExact leaf5894LowerChecked

private noncomputable def leaf5895Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (53/128), chiHi := (27/64) }

private noncomputable def leaf5895Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435797/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68713007104) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (671293085/536870912) }, upper := { exponent := 1, mantissa := (5207/4096) } }, logOuter := sk163LogOuterCertificate, logK := sk163LogKCertificate, logChi := chi264LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429403645/137426014208) } }, logDArg := sk163LogDArgCertificate }

private noncomputable def leaf5895InnerLog : WideLogData :=
  innerPair299Data

set_option maxRecDepth 1000000 in
private theorem leaf5895LocalValidity :
    LeafFacts leaf5895Box leaf5895Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5895Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68713007104) }) = true
      norm_num [leaf5895Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5895CertificateValid :
    WideCertificateValid leaf5895Box leaf5895Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk163ValidityFacts chi264ValidityFacts
    leaf5895LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5895CoverageChecked :
    coverageCheck (innerAD leaf5895Box) leaf5895InnerLog = true := by
  rfl'

private theorem leaf5895InnerLogValid :
    leaf5895InnerLog.Valid 8 (innerAD leaf5895Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint437PositiveFacts.valid leaf5895CoverageChecked

private noncomputable def leaf5895InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629495/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5895InputLogOnePlusV_eq :
    leaf5895InputLogOnePlusV = outerEnclosure 24
      (leaf5895Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5895RoundedFacts : LeafRoundedFacts 8
    leaf5895Certificate.logOnePlusV leaf5895InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5895InputLogOnePlusV_eq }

private noncomputable def leaf5895Inputs : Inputs :=
  inputsOfCaches globalInput sk163RoundedInputs
    chi264InputQChi innerPair299Input
    leaf5895InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5895LowerChecked :
    lowerCheck 24 leaf5895Box leaf5895Inputs = true := by
  rfl'

private theorem leaf5895CoversExact : CoversExact 8
    leaf5895Box leaf5895Certificate leaf5895InnerLog leaf5895Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk163RoundedFacts chi264RoundedFacts
    innerPair299RoundedFacts leaf5895RoundedFacts (by rfl)

private theorem leaf5895FlatSound : Sound leaf5895Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5895CertificateValid
    leaf5895InnerLogValid leaf5895CoversExact leaf5895LowerChecked

private noncomputable def leaf5896Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (53/128), chiHi := (27/64) }

private noncomputable def leaf5896Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435799/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712951808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (674766279/536870912) }, upper := { exponent := 1, mantissa := (2617/2048) } }, logOuter := sk164LogOuterCertificate, logK := sk164LogKCertificate, logChi := chi264LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429348349/137425903616) } }, logDArg := sk164LogDArgCertificate }

private noncomputable def leaf5896InnerLog : WideLogData :=
  innerPair293Data

set_option maxRecDepth 1000000 in
private theorem leaf5896LocalValidity :
    LeafFacts leaf5896Box leaf5896Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5896Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712951808) }) = true
      norm_num [leaf5896Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5896CertificateValid :
    WideCertificateValid leaf5896Box leaf5896Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk164ValidityFacts chi264ValidityFacts
    leaf5896LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5896CoverageChecked :
    coverageCheck (innerAD leaf5896Box) leaf5896InnerLog = true := by
  rfl'

private theorem leaf5896InnerLogValid :
    leaf5896InnerLog.Valid 8 (innerAD leaf5896Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint90PositiveFacts.valid leaf5896CoverageChecked

private noncomputable def leaf5896InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629501/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5896InputLogOnePlusV_eq :
    leaf5896InputLogOnePlusV = outerEnclosure 24
      (leaf5896Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5896RoundedFacts : LeafRoundedFacts 8
    leaf5896Certificate.logOnePlusV leaf5896InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5896InputLogOnePlusV_eq }

private noncomputable def leaf5896Inputs : Inputs :=
  inputsOfCaches globalInput sk164RoundedInputs
    chi264InputQChi innerPair293Input
    leaf5896InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5896LowerChecked :
    lowerCheck 24 leaf5896Box leaf5896Inputs = true := by
  rfl'

private theorem leaf5896CoversExact : CoversExact 8
    leaf5896Box leaf5896Certificate leaf5896InnerLog leaf5896Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk164RoundedFacts chi264RoundedFacts
    innerPair293RoundedFacts leaf5896RoundedFacts (by rfl)

private theorem leaf5896FlatSound : Sound leaf5896Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5896CertificateValid
    leaf5896InnerLogValid leaf5896CoversExact leaf5896LowerChecked

private noncomputable def leaf5897Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (13/32), chiHi := (53/128) }

private noncomputable def leaf5897Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435799/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68713018368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (670506699/536870912) }, upper := { exponent := 1, mantissa := (10403/8192) } }, logOuter := sk165LogOuterCertificate, logK := sk165LogKCertificate, logChi := chi263LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429414909/137426036736) } }, logDArg := sk165LogDArgCertificate }

private noncomputable def leaf5897InnerLog : WideLogData :=
  innerPair695Data

set_option maxRecDepth 1000000 in
private theorem leaf5897LocalValidity :
    LeafFacts leaf5897Box leaf5897Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5897Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68713018368) }) = true
      norm_num [leaf5897Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5897CertificateValid :
    WideCertificateValid leaf5897Box leaf5897Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk165ValidityFacts chi263ValidityFacts
    leaf5897LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5897CoverageChecked :
    coverageCheck (innerAD leaf5897Box) leaf5897InnerLog = true := by
  rfl'

private theorem leaf5897InnerLogValid :
    leaf5897InnerLog.Valid 8 (innerAD leaf5897Box) :=
  wideLogDataValid_of_cachedCheck endpoint438PositiveFacts
    endpoint439PositiveFacts.valid leaf5897CoverageChecked

private noncomputable def leaf5897InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629493/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5897InputLogOnePlusV_eq :
    leaf5897InputLogOnePlusV = outerEnclosure 24
      (leaf5897Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5897RoundedFacts : LeafRoundedFacts 8
    leaf5897Certificate.logOnePlusV leaf5897InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5897InputLogOnePlusV_eq }

private noncomputable def leaf5897Inputs : Inputs :=
  inputsOfCaches globalInput sk165RoundedInputs
    chi263InputQChi innerPair695Input
    leaf5897InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5897LowerChecked :
    lowerCheck 24 leaf5897Box leaf5897Inputs = true := by
  rfl'

private theorem leaf5897CoversExact : CoversExact 8
    leaf5897Box leaf5897Certificate leaf5897InnerLog leaf5897Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk165RoundedFacts chi263RoundedFacts
    innerPair695RoundedFacts leaf5897RoundedFacts (by rfl)

private theorem leaf5897FlatSound : Sound leaf5897Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5897CertificateValid
    leaf5897InnerLogValid leaf5897CoversExact leaf5897LowerChecked

private noncomputable def leaf5898Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (13/32), chiHi := (53/128) }

private noncomputable def leaf5898Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435801/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712964096) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (673914361/536870912) }, upper := { exponent := 1, mantissa := (1307/1024) } }, logOuter := sk166LogOuterCertificate, logK := sk166LogKCertificate, logChi := chi263LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429360637/137425928192) } }, logDArg := sk166LogDArgCertificate }

private noncomputable def leaf5898InnerLog : WideLogData :=
  innerPair696Data

set_option maxRecDepth 1000000 in
private theorem leaf5898LocalValidity :
    LeafFacts leaf5898Box leaf5898Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5898Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712964096) }) = true
      norm_num [leaf5898Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5898CertificateValid :
    WideCertificateValid leaf5898Box leaf5898Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk166ValidityFacts chi263ValidityFacts
    leaf5898LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5898CoverageChecked :
    coverageCheck (innerAD leaf5898Box) leaf5898InnerLog = true := by
  rfl'

private theorem leaf5898InnerLogValid :
    leaf5898InnerLog.Valid 8 (innerAD leaf5898Box) :=
  wideLogDataValid_of_cachedCheck endpoint440PositiveFacts
    endpoint441PositiveFacts.valid leaf5898CoverageChecked

private noncomputable def leaf5898InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907375/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5898InputLogOnePlusV_eq :
    leaf5898InputLogOnePlusV = outerEnclosure 24
      (leaf5898Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5898RoundedFacts : LeafRoundedFacts 8
    leaf5898Certificate.logOnePlusV leaf5898InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5898InputLogOnePlusV_eq }

private noncomputable def leaf5898Inputs : Inputs :=
  inputsOfCaches globalInput sk166RoundedInputs
    chi263InputQChi innerPair696Input
    leaf5898InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5898LowerChecked :
    lowerCheck 24 leaf5898Box leaf5898Inputs = true := by
  rfl'

private theorem leaf5898CoversExact : CoversExact 8
    leaf5898Box leaf5898Certificate leaf5898InnerLog leaf5898Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk166RoundedFacts chi263RoundedFacts
    innerPair696RoundedFacts leaf5898RoundedFacts (by rfl)

private theorem leaf5898FlatSound : Sound leaf5898Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5898CertificateValid
    leaf5898InnerLogValid leaf5898CoversExact leaf5898LowerChecked

private noncomputable def leaf5899Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (53/128), chiHi := (27/64) }

private noncomputable def leaf5899Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435801/268435456) }, vSqrt := { lower := (8191/8192), upper := (5285876657/5285607424) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (678239473/536870912) }, upper := { exponent := 1, mantissa := (5261/4096) } }, logOuter := sk165LogOuterCertificate, logK := sk165LogKCertificate, logChi := chi264LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (10571484081/10571214848) } }, logDArg := sk165LogDArgCertificate }

private noncomputable def leaf5899InnerLog : WideLogData :=
  innerPair671Data

set_option maxRecDepth 1000000 in
private theorem leaf5899LocalValidity :
    LeafFacts leaf5899Box leaf5899Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5899Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5285876657/5285607424) }) = true
      norm_num [leaf5899Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5899CertificateValid :
    WideCertificateValid leaf5899Box leaf5899Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk165ValidityFacts chi264ValidityFacts
    leaf5899LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5899CoverageChecked :
    coverageCheck (innerAD leaf5899Box) leaf5899InnerLog = true := by
  rfl'

private theorem leaf5899InnerLogValid :
    leaf5899InnerLog.Valid 8 (innerAD leaf5899Box) :=
  wideLogDataValid_of_cachedCheck endpoint419PositiveFacts
    endpoint435PositiveFacts.valid leaf5899CoverageChecked

private noncomputable def leaf5899InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907377/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5899InputLogOnePlusV_eq :
    leaf5899InputLogOnePlusV = outerEnclosure 24
      (leaf5899Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5899RoundedFacts : LeafRoundedFacts 8
    leaf5899Certificate.logOnePlusV leaf5899InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5899InputLogOnePlusV_eq }

private noncomputable def leaf5899Inputs : Inputs :=
  inputsOfCaches globalInput sk165RoundedInputs
    chi264InputQChi innerPair671Input
    leaf5899InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5899LowerChecked :
    lowerCheck 24 leaf5899Box leaf5899Inputs = true := by
  rfl'

private theorem leaf5899CoversExact : CoversExact 8
    leaf5899Box leaf5899Certificate leaf5899InnerLog leaf5899Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk165RoundedFacts chi264RoundedFacts
    innerPair671RoundedFacts leaf5899RoundedFacts (by rfl)

private theorem leaf5899FlatSound : Sound leaf5899Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5899CertificateValid
    leaf5899InnerLogValid leaf5899CoversExact leaf5899LowerChecked

private noncomputable def leaf5900Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (53/128), chiHi := (27/64) }

private noncomputable def leaf5900Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435803/268435456) }, vSqrt := { lower := (8191/8192), upper := (967836571/967786496) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (681712667/536870912) }, upper := { exponent := 1, mantissa := (661/512) } }, logOuter := sk166LogOuterCertificate, logK := sk166LogKCertificate, logChi := chi264LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (1935623067/1935572992) } }, logDArg := sk166LogDArgCertificate }

private noncomputable def leaf5900InnerLog : WideLogData :=
  innerPair697Data

set_option maxRecDepth 1000000 in
private theorem leaf5900LocalValidity :
    LeafFacts leaf5900Box leaf5900Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5900Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (967836571/967786496) }) = true
      norm_num [leaf5900Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5900CertificateValid :
    WideCertificateValid leaf5900Box leaf5900Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk166ValidityFacts chi264ValidityFacts
    leaf5900LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5900CoverageChecked :
    coverageCheck (innerAD leaf5900Box) leaf5900InnerLog = true := by
  rfl'

private theorem leaf5900InnerLogValid :
    leaf5900InnerLog.Valid 8 (innerAD leaf5900Box) :=
  wideLogDataValid_of_cachedCheck endpoint442PositiveFacts
    endpoint443PositiveFacts.valid leaf5900CoverageChecked

private noncomputable def leaf5900InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629515/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5900InputLogOnePlusV_eq :
    leaf5900InputLogOnePlusV = outerEnclosure 24
      (leaf5900Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5900RoundedFacts : LeafRoundedFacts 8
    leaf5900Certificate.logOnePlusV leaf5900InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5900InputLogOnePlusV_eq }

private noncomputable def leaf5900Inputs : Inputs :=
  inputsOfCaches globalInput sk166RoundedInputs
    chi264InputQChi innerPair697Input
    leaf5900InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5900LowerChecked :
    lowerCheck 24 leaf5900Box leaf5900Inputs = true := by
  rfl'

private theorem leaf5900CoversExact : CoversExact 8
    leaf5900Box leaf5900Certificate leaf5900InnerLog leaf5900Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk166RoundedFacts chi264RoundedFacts
    innerPair697RoundedFacts leaf5900RoundedFacts (by rfl)

private theorem leaf5900FlatSound : Sound leaf5900Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5900CertificateValid
    leaf5900InnerLogValid leaf5900CoversExact leaf5900LowerChecked

private noncomputable def leaf5901Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (27/64), chiHi := (55/128) }

private noncomputable def leaf5901Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435799/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712887296) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (678894795/536870912) }, upper := { exponent := 1, mantissa := (10531/8192) } }, logOuter := sk163LogOuterCertificate, logK := sk163LogKCertificate, logChi := chi265LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429283837/137425774592) } }, logDArg := sk163LogDArgCertificate }

private noncomputable def leaf5901InnerLog : WideLogData :=
  innerPair671Data

set_option maxRecDepth 1000000 in
private theorem leaf5901LocalValidity :
    LeafFacts leaf5901Box leaf5901Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5901Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712887296) }) = true
      norm_num [leaf5901Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5901CertificateValid :
    WideCertificateValid leaf5901Box leaf5901Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk163ValidityFacts chi265ValidityFacts
    leaf5901LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5901CoverageChecked :
    coverageCheck (innerAD leaf5901Box) leaf5901InnerLog = true := by
  rfl'

private theorem leaf5901InnerLogValid :
    leaf5901InnerLog.Valid 8 (innerAD leaf5901Box) :=
  wideLogDataValid_of_cachedCheck endpoint419PositiveFacts
    endpoint435PositiveFacts.valid leaf5901CoverageChecked

private noncomputable def leaf5901InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629509/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5901InputLogOnePlusV_eq :
    leaf5901InputLogOnePlusV = outerEnclosure 24
      (leaf5901Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5901RoundedFacts : LeafRoundedFacts 8
    leaf5901Certificate.logOnePlusV leaf5901InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5901InputLogOnePlusV_eq }

private noncomputable def leaf5901Inputs : Inputs :=
  inputsOfCaches globalInput sk163RoundedInputs
    chi265InputQChi innerPair671Input
    leaf5901InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5901LowerChecked :
    lowerCheck 24 leaf5901Box leaf5901Inputs = true := by
  rfl'

private theorem leaf5901CoversExact : CoversExact 8
    leaf5901Box leaf5901Certificate leaf5901InnerLog leaf5901Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk163RoundedFacts chi265RoundedFacts
    innerPair671RoundedFacts leaf5901RoundedFacts (by rfl)

private theorem leaf5901FlatSound : Sound leaf5901Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5901CertificateValid
    leaf5901InnerLogValid leaf5901CoversExact leaf5901LowerChecked

private noncomputable def leaf5902Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (27/64), chiHi := (55/128) }

private noncomputable def leaf5902Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435801/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712830976) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (682433521/536870912) }, upper := { exponent := 1, mantissa := (5293/4096) } }, logOuter := sk164LogOuterCertificate, logK := sk164LogKCertificate, logChi := chi265LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429227517/137425661952) } }, logDArg := sk164LogDArgCertificate }

private noncomputable def leaf5902InnerLog : WideLogData :=
  innerPair682Data

set_option maxRecDepth 1000000 in
private theorem leaf5902LocalValidity :
    LeafFacts leaf5902Box leaf5902Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5902Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712830976) }) = true
      norm_num [leaf5902Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5902CertificateValid :
    WideCertificateValid leaf5902Box leaf5902Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk164ValidityFacts chi265ValidityFacts
    leaf5902LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5902CoverageChecked :
    coverageCheck (innerAD leaf5902Box) leaf5902InnerLog = true := by
  rfl'

private theorem leaf5902InnerLogValid :
    leaf5902InnerLog.Valid 8 (innerAD leaf5902Box) :=
  wideLogDataValid_of_cachedCheck endpoint434PositiveFacts
    endpoint436PositiveFacts.valid leaf5902CoverageChecked

private noncomputable def leaf5902InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907379/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5902InputLogOnePlusV_eq :
    leaf5902InputLogOnePlusV = outerEnclosure 24
      (leaf5902Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5902RoundedFacts : LeafRoundedFacts 8
    leaf5902Certificate.logOnePlusV leaf5902InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5902InputLogOnePlusV_eq }

private noncomputable def leaf5902Inputs : Inputs :=
  inputsOfCaches globalInput sk164RoundedInputs
    chi265InputQChi innerPair682Input
    leaf5902InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5902LowerChecked :
    lowerCheck 24 leaf5902Box leaf5902Inputs = true := by
  rfl'

private theorem leaf5902CoversExact : CoversExact 8
    leaf5902Box leaf5902Certificate leaf5902InnerLog leaf5902Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk164RoundedFacts chi265RoundedFacts
    innerPair682RoundedFacts leaf5902RoundedFacts (by rfl)

private theorem leaf5902FlatSound : Sound leaf5902Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5902CertificateValid
    leaf5902InnerLogValid leaf5902CoversExact leaf5902LowerChecked

private noncomputable def leaf5903Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (55/128), chiHi := (7/16) }

private noncomputable def leaf5903Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435801/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712767488) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (686496505/536870912) }, upper := { exponent := 1, mantissa := (1331/1024) } }, logOuter := sk163LogOuterCertificate, logK := sk163LogKCertificate, logChi := chi266LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429164029/137425534976) } }, logDArg := sk163LogDArgCertificate }

private noncomputable def leaf5903InnerLog : WideLogData :=
  innerPair294Data

set_option maxRecDepth 1000000 in
private theorem leaf5903LocalValidity :
    LeafFacts leaf5903Box leaf5903Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5903Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712767488) }) = true
      norm_num [leaf5903Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5903CertificateValid :
    WideCertificateValid leaf5903Box leaf5903Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk163ValidityFacts chi266ValidityFacts
    leaf5903LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5903CoverageChecked :
    coverageCheck (innerAD leaf5903Box) leaf5903InnerLog = true := by
  rfl'

private theorem leaf5903InnerLogValid :
    leaf5903InnerLog.Valid 8 (innerAD leaf5903Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint91PositiveFacts.valid leaf5903CoverageChecked

private noncomputable def leaf5903InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907381/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5903InputLogOnePlusV_eq :
    leaf5903InputLogOnePlusV = outerEnclosure 24
      (leaf5903Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5903RoundedFacts : LeafRoundedFacts 8
    leaf5903Certificate.logOnePlusV leaf5903InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5903InputLogOnePlusV_eq }

private noncomputable def leaf5903Inputs : Inputs :=
  inputsOfCaches globalInput sk163RoundedInputs
    chi266InputQChi innerPair294Input
    leaf5903InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5903LowerChecked :
    lowerCheck 24 leaf5903Box leaf5903Inputs = true := by
  rfl'

private theorem leaf5903CoversExact : CoversExact 8
    leaf5903Box leaf5903Certificate leaf5903InnerLog leaf5903Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk163RoundedFacts chi266RoundedFacts
    innerPair294RoundedFacts leaf5903RoundedFacts (by rfl)

private theorem leaf5903FlatSound : Sound leaf5903Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5903CertificateValid
    leaf5903InnerLogValid leaf5903CoversExact leaf5903LowerChecked

private noncomputable def leaf5904Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (55/128), chiHi := (7/16) }

private noncomputable def leaf5904Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435803/268435456) }, vSqrt := { lower := (8191/8192), upper := (5285876657/5285593088) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (690100763/536870912) }, upper := { exponent := 1, mantissa := (669/512) } }, logOuter := sk164LogOuterCertificate, logK := sk164LogKCertificate, logChi := chi266LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (10571469745/10571186176) } }, logDArg := sk164LogDArgCertificate }

private noncomputable def leaf5904InnerLog : WideLogData :=
  innerPair339Data

set_option maxRecDepth 1000000 in
private theorem leaf5904LocalValidity :
    LeafFacts leaf5904Box leaf5904Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5904Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5285876657/5285593088) }) = true
      norm_num [leaf5904Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5904CertificateValid :
    WideCertificateValid leaf5904Box leaf5904Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk164ValidityFacts chi266ValidityFacts
    leaf5904LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5904CoverageChecked :
    coverageCheck (innerAD leaf5904Box) leaf5904InnerLog = true := by
  rfl'

private theorem leaf5904InnerLogValid :
    leaf5904InnerLog.Valid 8 (innerAD leaf5904Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint91PositiveFacts.valid leaf5904CoverageChecked

private noncomputable def leaf5904InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629531/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5904InputLogOnePlusV_eq :
    leaf5904InputLogOnePlusV = outerEnclosure 24
      (leaf5904Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5904RoundedFacts : LeafRoundedFacts 8
    leaf5904Certificate.logOnePlusV leaf5904InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5904InputLogOnePlusV_eq }

private noncomputable def leaf5904Inputs : Inputs :=
  inputsOfCaches globalInput sk164RoundedInputs
    chi266InputQChi innerPair339Input
    leaf5904InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5904LowerChecked :
    lowerCheck 24 leaf5904Box leaf5904Inputs = true := by
  rfl'

private theorem leaf5904CoversExact : CoversExact 8
    leaf5904Box leaf5904Certificate leaf5904InnerLog leaf5904Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk164RoundedFacts chi266RoundedFacts
    innerPair339RoundedFacts leaf5904RoundedFacts (by rfl)

private theorem leaf5904FlatSound : Sound leaf5904Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5904CertificateValid
    leaf5904InnerLogValid leaf5904CoversExact leaf5904LowerChecked

private noncomputable def leaf5905Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (27/64), chiHi := (55/128) }

private noncomputable def leaf5905Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435803/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712774656) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (685972247/536870912) }, upper := { exponent := 1, mantissa := (10641/8192) } }, logOuter := sk165LogOuterCertificate, logK := sk165LogKCertificate, logChi := chi265LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429171197/137425549312) } }, logDArg := sk165LogDArgCertificate }

private noncomputable def leaf5905InnerLog : WideLogData :=
  innerPair694Data

set_option maxRecDepth 1000000 in
private theorem leaf5905LocalValidity :
    LeafFacts leaf5905Box leaf5905Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5905Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712774656) }) = true
      norm_num [leaf5905Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5905CertificateValid :
    WideCertificateValid leaf5905Box leaf5905Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk165ValidityFacts chi265ValidityFacts
    leaf5905LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5905CoverageChecked :
    coverageCheck (innerAD leaf5905Box) leaf5905InnerLog = true := by
  rfl'

private theorem leaf5905InnerLogValid :
    leaf5905InnerLog.Valid 8 (innerAD leaf5905Box) :=
  wideLogDataValid_of_cachedCheck endpoint437PositiveFacts
    endpoint444PositiveFacts.valid leaf5905CoverageChecked

private noncomputable def leaf5905InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629523/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5905InputLogOnePlusV_eq :
    leaf5905InputLogOnePlusV = outerEnclosure 24
      (leaf5905Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5905RoundedFacts : LeafRoundedFacts 8
    leaf5905Certificate.logOnePlusV leaf5905InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5905InputLogOnePlusV_eq }

private noncomputable def leaf5905Inputs : Inputs :=
  inputsOfCaches globalInput sk165RoundedInputs
    chi265InputQChi innerPair694Input
    leaf5905InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5905LowerChecked :
    lowerCheck 24 leaf5905Box leaf5905Inputs = true := by
  rfl'

private theorem leaf5905CoversExact : CoversExact 8
    leaf5905Box leaf5905Certificate leaf5905InnerLog leaf5905Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk165RoundedFacts chi265RoundedFacts
    innerPair694RoundedFacts leaf5905RoundedFacts (by rfl)

private theorem leaf5905FlatSound : Sound leaf5905Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5905CertificateValid
    leaf5905InnerLogValid leaf5905CoversExact leaf5905LowerChecked

private noncomputable def leaf5906Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (27/64), chiHi := (55/128) }

private noncomputable def leaf5906Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435805/268435456) }, vSqrt := { lower := (8191/8192), upper := (4042140973/4041924608) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (689510973/536870912) }, upper := { exponent := 1, mantissa := (1337/1024) } }, logOuter := sk166LogOuterCertificate, logK := sk166LogKCertificate, logChi := chi265LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (8084065581/8083849216) } }, logDArg := sk166LogDArgCertificate }

private noncomputable def leaf5906InnerLog : WideLogData :=
  innerPair339Data

set_option maxRecDepth 1000000 in
private theorem leaf5906LocalValidity :
    LeafFacts leaf5906Box leaf5906Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5906Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4042140973/4041924608) }) = true
      norm_num [leaf5906Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5906CertificateValid :
    WideCertificateValid leaf5906Box leaf5906Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk166ValidityFacts chi265ValidityFacts
    leaf5906LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5906CoverageChecked :
    coverageCheck (innerAD leaf5906Box) leaf5906InnerLog = true := by
  rfl'

private theorem leaf5906InnerLogValid :
    leaf5906InnerLog.Valid 8 (innerAD leaf5906Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint91PositiveFacts.valid leaf5906CoverageChecked

private noncomputable def leaf5906InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814765/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5906InputLogOnePlusV_eq :
    leaf5906InputLogOnePlusV = outerEnclosure 24
      (leaf5906Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5906RoundedFacts : LeafRoundedFacts 8
    leaf5906Certificate.logOnePlusV leaf5906InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5906InputLogOnePlusV_eq }

private noncomputable def leaf5906Inputs : Inputs :=
  inputsOfCaches globalInput sk166RoundedInputs
    chi265InputQChi innerPair339Input
    leaf5906InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5906LowerChecked :
    lowerCheck 24 leaf5906Box leaf5906Inputs = true := by
  rfl'

private theorem leaf5906CoversExact : CoversExact 8
    leaf5906Box leaf5906Certificate leaf5906InnerLog leaf5906Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk166RoundedFacts chi265RoundedFacts
    innerPair339RoundedFacts leaf5906RoundedFacts (by rfl)

private theorem leaf5906FlatSound : Sound leaf5906Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5906CertificateValid
    leaf5906InnerLogValid leaf5906CoversExact leaf5906LowerChecked

private noncomputable def leaf5907Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (55/128), chiHi := (7/16) }

private noncomputable def leaf5907Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435805/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712652800) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (693705021/536870912) }, upper := { exponent := 1, mantissa := (1345/1024) } }, logOuter := sk165LogOuterCertificate, logK := sk165LogKCertificate, logChi := chi266LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429049341/137425305600) } }, logDArg := sk165LogDArgCertificate }

private noncomputable def leaf5907InnerLog : WideLogData :=
  innerPair684Data

set_option maxRecDepth 1000000 in
private theorem leaf5907LocalValidity :
    LeafFacts leaf5907Box leaf5907Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5907Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712652800) }) = true
      norm_num [leaf5907Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5907CertificateValid :
    WideCertificateValid leaf5907Box leaf5907Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk165ValidityFacts chi266ValidityFacts
    leaf5907LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5907CoverageChecked :
    coverageCheck (innerAD leaf5907Box) leaf5907InnerLog = true := by
  rfl'

private theorem leaf5907InnerLogValid :
    leaf5907InnerLog.Valid 8 (innerAD leaf5907Box) :=
  wideLogDataValid_of_cachedCheck endpoint435PositiveFacts
    endpoint95PositiveFacts.valid leaf5907CoverageChecked

private noncomputable def leaf5907InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814769/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5907InputLogOnePlusV_eq :
    leaf5907InputLogOnePlusV = outerEnclosure 24
      (leaf5907Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5907RoundedFacts : LeafRoundedFacts 8
    leaf5907Certificate.logOnePlusV leaf5907InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5907InputLogOnePlusV_eq }

private noncomputable def leaf5907Inputs : Inputs :=
  inputsOfCaches globalInput sk165RoundedInputs
    chi266InputQChi innerPair684Input
    leaf5907InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5907LowerChecked :
    lowerCheck 24 leaf5907Box leaf5907Inputs = true := by
  rfl'

private theorem leaf5907CoversExact : CoversExact 8
    leaf5907Box leaf5907Certificate leaf5907InnerLog leaf5907Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk165RoundedFacts chi266RoundedFacts
    innerPair684RoundedFacts leaf5907RoundedFacts (by rfl)

private theorem leaf5907FlatSound : Sound leaf5907Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5907CertificateValid
    leaf5907InnerLogValid leaf5907CoversExact leaf5907LowerChecked

private noncomputable def leaf5908Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (55/128), chiHi := (7/16) }

private noncomputable def leaf5908Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435807/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712595456) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (697309279/536870912) }, upper := { exponent := 1, mantissa := (169/128) } }, logOuter := sk166LogOuterCertificate, logK := sk166LogKCertificate, logChi := chi266LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428991997/137425190912) } }, logDArg := sk166LogDArgCertificate }

private noncomputable def leaf5908InnerLog : WideLogData :=
  innerPair688Data

set_option maxRecDepth 1000000 in
private theorem leaf5908LocalValidity :
    LeafFacts leaf5908Box leaf5908Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5908Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712595456) }) = true
      norm_num [leaf5908Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5908CertificateValid :
    WideCertificateValid leaf5908Box leaf5908Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk166ValidityFacts chi266ValidityFacts
    leaf5908LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5908CoverageChecked :
    coverageCheck (innerAD leaf5908Box) leaf5908InnerLog = true := by
  rfl'

private theorem leaf5908InnerLogValid :
    leaf5908InnerLog.Valid 8 (innerAD leaf5908Box) :=
  wideLogDataValid_of_cachedCheck endpoint436PositiveFacts
    endpoint95PositiveFacts.valid leaf5908CoverageChecked

private noncomputable def leaf5908InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629545/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5908InputLogOnePlusV_eq :
    leaf5908InputLogOnePlusV = outerEnclosure 24
      (leaf5908Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5908RoundedFacts : LeafRoundedFacts 8
    leaf5908Certificate.logOnePlusV leaf5908InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5908InputLogOnePlusV_eq }

private noncomputable def leaf5908Inputs : Inputs :=
  inputsOfCaches globalInput sk166RoundedInputs
    chi266InputQChi innerPair688Input
    leaf5908InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5908LowerChecked :
    lowerCheck 24 leaf5908Box leaf5908Inputs = true := by
  rfl'

private theorem leaf5908CoversExact : CoversExact 8
    leaf5908Box leaf5908Certificate leaf5908InnerLog leaf5908Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk166RoundedFacts chi266RoundedFacts
    innerPair688RoundedFacts leaf5908RoundedFacts (by rfl)

private theorem leaf5908FlatSound : Sound leaf5908Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5908CertificateValid
    leaf5908InnerLogValid leaf5908CoversExact leaf5908LowerChecked

private noncomputable def component118Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (13/32), chiHi := (53/128) }

set_option maxRecDepth 1000000 in
private theorem component118Node0_sound : Sound component118Node0Box :=
  sound_of_literal_split component118Node0Box leaf5877Box leaf5878Box
    .k (113/32) (by rfl) (by rfl)
    leaf5877FlatSound leaf5878FlatSound

private noncomputable def component118Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (53/128), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component118Node1_sound : Sound component118Node1Box :=
  sound_of_literal_split component118Node1Box leaf5879Box leaf5880Box
    .k (113/32) (by rfl) (by rfl)
    leaf5879FlatSound leaf5880FlatSound

private noncomputable def component118Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (13/32), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component118Node2_sound : Sound component118Node2Box :=
  sound_of_literal_split component118Node2Box component118Node0Box component118Node1Box
    .chi (53/128) (by rfl) (by rfl)
    component118Node0_sound component118Node1_sound

private noncomputable def component118Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (13/32), chiHi := (53/128) }

set_option maxRecDepth 1000000 in
private theorem component118Node3_sound : Sound component118Node3Box :=
  sound_of_literal_split component118Node3Box leaf5881Box leaf5882Box
    .k (115/32) (by rfl) (by rfl)
    leaf5881FlatSound leaf5882FlatSound

private noncomputable def component118Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (53/128), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component118Node4_sound : Sound component118Node4Box :=
  sound_of_literal_split component118Node4Box leaf5883Box leaf5884Box
    .k (115/32) (by rfl) (by rfl)
    leaf5883FlatSound leaf5884FlatSound

private noncomputable def component118Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (13/32), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component118Node5_sound : Sound component118Node5Box :=
  sound_of_literal_split component118Node5Box component118Node3Box component118Node4Box
    .chi (53/128) (by rfl) (by rfl)
    component118Node3_sound component118Node4_sound

private noncomputable def component118Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (13/32), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component118Node6_sound : Sound component118Node6Box :=
  sound_of_literal_split component118Node6Box component118Node2Box component118Node5Box
    .k (57/16) (by rfl) (by rfl)
    component118Node2_sound component118Node5_sound

private noncomputable def component118Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (27/64), chiHi := (55/128) }

set_option maxRecDepth 1000000 in
private theorem component118Node7_sound : Sound component118Node7Box :=
  sound_of_literal_split component118Node7Box leaf5885Box leaf5886Box
    .k (113/32) (by rfl) (by rfl)
    leaf5885FlatSound leaf5886FlatSound

private noncomputable def component118Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (55/128), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component118Node8_sound : Sound component118Node8Box :=
  sound_of_literal_split component118Node8Box leaf5887Box leaf5888Box
    .k (113/32) (by rfl) (by rfl)
    leaf5887FlatSound leaf5888FlatSound

private noncomputable def component118Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (27/64), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component118Node9_sound : Sound component118Node9Box :=
  sound_of_literal_split component118Node9Box component118Node7Box component118Node8Box
    .chi (55/128) (by rfl) (by rfl)
    component118Node7_sound component118Node8_sound

private noncomputable def component118Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (27/64), chiHi := (55/128) }

set_option maxRecDepth 1000000 in
private theorem component118Node10_sound : Sound component118Node10Box :=
  sound_of_literal_split component118Node10Box leaf5889Box leaf5890Box
    .k (115/32) (by rfl) (by rfl)
    leaf5889FlatSound leaf5890FlatSound

private noncomputable def component118Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (55/128), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component118Node11_sound : Sound component118Node11Box :=
  sound_of_literal_split component118Node11Box leaf5891Box leaf5892Box
    .k (115/32) (by rfl) (by rfl)
    leaf5891FlatSound leaf5892FlatSound

private noncomputable def component118Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (27/64), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component118Node12_sound : Sound component118Node12Box :=
  sound_of_literal_split component118Node12Box component118Node10Box component118Node11Box
    .chi (55/128) (by rfl) (by rfl)
    component118Node10_sound component118Node11_sound

private noncomputable def component118Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (27/64), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component118Node13_sound : Sound component118Node13Box :=
  sound_of_literal_split component118Node13Box component118Node9Box component118Node12Box
    .k (57/16) (by rfl) (by rfl)
    component118Node9_sound component118Node12_sound

private noncomputable def component118Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (13/32), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component118Node14_sound : Sound component118Node14Box :=
  sound_of_literal_split component118Node14Box component118Node6Box component118Node13Box
    .chi (27/64) (by rfl) (by rfl)
    component118Node6_sound component118Node13_sound

private noncomputable def component118Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (13/32), chiHi := (53/128) }

set_option maxRecDepth 1000000 in
private theorem component118Node15_sound : Sound component118Node15Box :=
  sound_of_literal_split component118Node15Box leaf5893Box leaf5894Box
    .k (117/32) (by rfl) (by rfl)
    leaf5893FlatSound leaf5894FlatSound

private noncomputable def component118Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (53/128), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component118Node16_sound : Sound component118Node16Box :=
  sound_of_literal_split component118Node16Box leaf5895Box leaf5896Box
    .k (117/32) (by rfl) (by rfl)
    leaf5895FlatSound leaf5896FlatSound

private noncomputable def component118Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (13/32), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component118Node17_sound : Sound component118Node17Box :=
  sound_of_literal_split component118Node17Box component118Node15Box component118Node16Box
    .chi (53/128) (by rfl) (by rfl)
    component118Node15_sound component118Node16_sound

private noncomputable def component118Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (13/32), chiHi := (53/128) }

set_option maxRecDepth 1000000 in
private theorem component118Node18_sound : Sound component118Node18Box :=
  sound_of_literal_split component118Node18Box leaf5897Box leaf5898Box
    .k (119/32) (by rfl) (by rfl)
    leaf5897FlatSound leaf5898FlatSound

private noncomputable def component118Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (53/128), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component118Node19_sound : Sound component118Node19Box :=
  sound_of_literal_split component118Node19Box leaf5899Box leaf5900Box
    .k (119/32) (by rfl) (by rfl)
    leaf5899FlatSound leaf5900FlatSound

private noncomputable def component118Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (13/32), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component118Node20_sound : Sound component118Node20Box :=
  sound_of_literal_split component118Node20Box component118Node18Box component118Node19Box
    .chi (53/128) (by rfl) (by rfl)
    component118Node18_sound component118Node19_sound

private noncomputable def component118Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (13/32), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component118Node21_sound : Sound component118Node21Box :=
  sound_of_literal_split component118Node21Box component118Node17Box component118Node20Box
    .k (59/16) (by rfl) (by rfl)
    component118Node17_sound component118Node20_sound

private noncomputable def component118Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (27/64), chiHi := (55/128) }

set_option maxRecDepth 1000000 in
private theorem component118Node22_sound : Sound component118Node22Box :=
  sound_of_literal_split component118Node22Box leaf5901Box leaf5902Box
    .k (117/32) (by rfl) (by rfl)
    leaf5901FlatSound leaf5902FlatSound

private noncomputable def component118Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (55/128), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component118Node23_sound : Sound component118Node23Box :=
  sound_of_literal_split component118Node23Box leaf5903Box leaf5904Box
    .k (117/32) (by rfl) (by rfl)
    leaf5903FlatSound leaf5904FlatSound

private noncomputable def component118Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (27/64), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component118Node24_sound : Sound component118Node24Box :=
  sound_of_literal_split component118Node24Box component118Node22Box component118Node23Box
    .chi (55/128) (by rfl) (by rfl)
    component118Node22_sound component118Node23_sound

private noncomputable def component118Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (27/64), chiHi := (55/128) }

set_option maxRecDepth 1000000 in
private theorem component118Node25_sound : Sound component118Node25Box :=
  sound_of_literal_split component118Node25Box leaf5905Box leaf5906Box
    .k (119/32) (by rfl) (by rfl)
    leaf5905FlatSound leaf5906FlatSound

private noncomputable def component118Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (55/128), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component118Node26_sound : Sound component118Node26Box :=
  sound_of_literal_split component118Node26Box leaf5907Box leaf5908Box
    .k (119/32) (by rfl) (by rfl)
    leaf5907FlatSound leaf5908FlatSound

private noncomputable def component118Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (27/64), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component118Node27_sound : Sound component118Node27Box :=
  sound_of_literal_split component118Node27Box component118Node25Box component118Node26Box
    .chi (55/128) (by rfl) (by rfl)
    component118Node25_sound component118Node26_sound

private noncomputable def component118Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (27/64), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component118Node28_sound : Sound component118Node28Box :=
  sound_of_literal_split component118Node28Box component118Node24Box component118Node27Box
    .k (59/16) (by rfl) (by rfl)
    component118Node24_sound component118Node27_sound

private noncomputable def component118Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (13/32), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component118Node29_sound : Sound component118Node29Box :=
  sound_of_literal_split component118Node29Box component118Node21Box component118Node28Box
    .chi (27/64) (by rfl) (by rfl)
    component118Node21_sound component118Node28_sound

noncomputable def component118Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (15/4), chiLo := (13/32), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
theorem component118_sound : Sound component118Box :=
  sound_of_literal_split component118Box component118Node14Box component118Node29Box
    .k (29/8) (by rfl) (by rfl)
    component118Node14_sound component118Node29_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
