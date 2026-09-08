import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch5
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch8
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

private noncomputable def leaf5317Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (11/32), chiHi := (89/256) }

private noncomputable def leaf5317Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871315/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357163776) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1182721135/1073741824) }, upper := { exponent := 1, mantissa := (18249/16384) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi297LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715886335/68714327552) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf5317InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf5317LocalValidity :
    LeafFacts leaf5317Box leaf5317Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5317Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357163776) }) = true
      norm_num [leaf5317Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5317CertificateValid :
    WideCertificateValid leaf5317Box leaf5317Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi297ValidityFacts
    leaf5317LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5317CoverageChecked :
    coverageCheck (innerAD leaf5317Box) leaf5317InnerLog = true := by
  rfl'

private theorem leaf5317InnerLogValid :
    leaf5317InnerLog.Valid 8 (innerAD leaf5317Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf5317CoverageChecked

private noncomputable def leaf5317InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629461/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5317InputLogOnePlusV_eq :
    leaf5317InputLogOnePlusV = outerEnclosure 24
      (leaf5317Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5317RoundedFacts : LeafRoundedFacts 8
    leaf5317Certificate.logOnePlusV leaf5317InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5317InputLogOnePlusV_eq }

private noncomputable def leaf5317Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi297InputQChi innerPair256Input
    leaf5317InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5317LowerChecked :
    lowerCheck 24 leaf5317Box leaf5317Inputs = true := by
  rfl'

private theorem leaf5317CoversExact : CoversExact 8
    leaf5317Box leaf5317Certificate leaf5317InnerLog leaf5317Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi297RoundedFacts
    innerPair256RoundedFacts leaf5317RoundedFacts (by rfl)

private theorem leaf5317FlatSound : Sound leaf5317Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5317CertificateValid
    leaf5317InnerLogValid leaf5317CoversExact leaf5317LowerChecked

private noncomputable def leaf5318Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (89/256), chiHi := (45/128) }

private noncomputable def leaf5318Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871317/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357134848) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1190060717/1073741824) }, upper := { exponent := 1, mantissa := (9181/8192) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi298LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715857407/68714269696) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf5318InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf5318LocalValidity :
    LeafFacts leaf5318Box leaf5318Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5318Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357134848) }) = true
      norm_num [leaf5318Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5318CertificateValid :
    WideCertificateValid leaf5318Box leaf5318Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi298ValidityFacts
    leaf5318LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5318CoverageChecked :
    coverageCheck (innerAD leaf5318Box) leaf5318InnerLog = true := by
  rfl'

private theorem leaf5318InnerLogValid :
    leaf5318InnerLog.Valid 8 (innerAD leaf5318Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf5318CoverageChecked

private noncomputable def leaf5318InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907367/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5318InputLogOnePlusV_eq :
    leaf5318InputLogOnePlusV = outerEnclosure 24
      (leaf5318Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5318RoundedFacts : LeafRoundedFacts 8
    leaf5318Certificate.logOnePlusV leaf5318InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5318InputLogOnePlusV_eq }

private noncomputable def leaf5318Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi298InputQChi innerPair256Input
    leaf5318InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5318LowerChecked :
    lowerCheck 24 leaf5318Box leaf5318Inputs = true := by
  rfl'

private theorem leaf5318CoversExact : CoversExact 8
    leaf5318Box leaf5318Certificate leaf5318InnerLog leaf5318Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi298RoundedFacts
    innerPair256RoundedFacts leaf5318RoundedFacts (by rfl)

private theorem leaf5318FlatSound : Sound leaf5318Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5318CertificateValid
    leaf5318InnerLogValid leaf5318CoversExact leaf5318LowerChecked

private noncomputable def leaf5319Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (11/32), chiHi := (89/256) }

private noncomputable def leaf5319Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871317/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357140992) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1188487949/1073741824) }, upper := { exponent := 1, mantissa := (9169/8192) } }, logOuter := sk168LogOuterCertificate, logK := sk168LogKCertificate, logChi := chi297LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715863551/68714281984) } }, logDArg := sk168LogDArgCertificate }

private noncomputable def leaf5319InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf5319LocalValidity :
    LeafFacts leaf5319Box leaf5319Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5319Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357140992) }) = true
      norm_num [leaf5319Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5319CertificateValid :
    WideCertificateValid leaf5319Box leaf5319Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk168ValidityFacts chi297ValidityFacts
    leaf5319LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5319CoverageChecked :
    coverageCheck (innerAD leaf5319Box) leaf5319InnerLog = true := by
  rfl'

private theorem leaf5319InnerLogValid :
    leaf5319InnerLog.Valid 8 (innerAD leaf5319Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf5319CoverageChecked

private noncomputable def leaf5319InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629467/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5319InputLogOnePlusV_eq :
    leaf5319InputLogOnePlusV = outerEnclosure 24
      (leaf5319Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5319RoundedFacts : LeafRoundedFacts 8
    leaf5319Certificate.logOnePlusV leaf5319InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5319InputLogOnePlusV_eq }

private noncomputable def leaf5319Inputs : Inputs :=
  inputsOfCaches globalInput sk168RoundedInputs
    chi297InputQChi innerPair256Input
    leaf5319InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5319LowerChecked :
    lowerCheck 24 leaf5319Box leaf5319Inputs = true := by
  rfl'

private theorem leaf5319CoversExact : CoversExact 8
    leaf5319Box leaf5319Certificate leaf5319InnerLog leaf5319Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk168RoundedFacts chi297RoundedFacts
    innerPair256RoundedFacts leaf5319RoundedFacts (by rfl)

private theorem leaf5319FlatSound : Sound leaf5319Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5319CertificateValid
    leaf5319InnerLogValid leaf5319CoversExact leaf5319LowerChecked

private noncomputable def leaf5320Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (89/256), chiHi := (45/128) }

private noncomputable def leaf5320Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871319/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357111808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1195893063/1073741824) }, upper := { exponent := 1, mantissa := (4613/4096) } }, logOuter := sk168LogOuterCertificate, logK := sk168LogKCertificate, logChi := chi298LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715834367/68714223616) } }, logDArg := sk168LogDArgCertificate }

private noncomputable def leaf5320InnerLog : WideLogData :=
  innerPair300Data

set_option maxRecDepth 1000000 in
private theorem leaf5320LocalValidity :
    LeafFacts leaf5320Box leaf5320Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5320Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357111808) }) = true
      norm_num [leaf5320Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5320CertificateValid :
    WideCertificateValid leaf5320Box leaf5320Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk168ValidityFacts chi298ValidityFacts
    leaf5320LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5320CoverageChecked :
    coverageCheck (innerAD leaf5320Box) leaf5320InnerLog = true := by
  rfl'

private theorem leaf5320InnerLogValid :
    leaf5320InnerLog.Valid 8 (innerAD leaf5320Box) :=
  wideLogDataValid_of_cachedCheck endpoint80PositiveFacts
    endpoint292PositiveFacts.valid leaf5320CoverageChecked

private noncomputable def leaf5320InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814737/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5320InputLogOnePlusV_eq :
    leaf5320InputLogOnePlusV = outerEnclosure 24
      (leaf5320Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5320RoundedFacts : LeafRoundedFacts 8
    leaf5320Certificate.logOnePlusV leaf5320InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5320InputLogOnePlusV_eq }

private noncomputable def leaf5320Inputs : Inputs :=
  inputsOfCaches globalInput sk168RoundedInputs
    chi298InputQChi innerPair300Input
    leaf5320InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5320LowerChecked :
    lowerCheck 24 leaf5320Box leaf5320Inputs = true := by
  rfl'

private theorem leaf5320CoversExact : CoversExact 8
    leaf5320Box leaf5320Certificate leaf5320InnerLog leaf5320Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk168RoundedFacts chi298RoundedFacts
    innerPair300RoundedFacts leaf5320RoundedFacts (by rfl)

private theorem leaf5320FlatSound : Sound leaf5320Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5320CertificateValid
    leaf5320InnerLogValid leaf5320CoversExact leaf5320LowerChecked

private noncomputable def leaf5321Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (45/128), chiHi := (91/256) }

private noncomputable def leaf5321Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871319/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357105920) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1197400299/1073741824) }, upper := { exponent := 1, mantissa := (18475/16384) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi299LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715828479/68714211840) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf5321InnerLog : WideLogData :=
  innerPair300Data

set_option maxRecDepth 1000000 in
private theorem leaf5321LocalValidity :
    LeafFacts leaf5321Box leaf5321Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5321Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357105920) }) = true
      norm_num [leaf5321Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5321CertificateValid :
    WideCertificateValid leaf5321Box leaf5321Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi299ValidityFacts
    leaf5321LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5321CoverageChecked :
    coverageCheck (innerAD leaf5321Box) leaf5321InnerLog = true := by
  rfl'

private theorem leaf5321InnerLogValid :
    leaf5321InnerLog.Valid 8 (innerAD leaf5321Box) :=
  wideLogDataValid_of_cachedCheck endpoint80PositiveFacts
    endpoint292PositiveFacts.valid leaf5321CoverageChecked

private noncomputable def leaf5321InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629475/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5321InputLogOnePlusV_eq :
    leaf5321InputLogOnePlusV = outerEnclosure 24
      (leaf5321Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5321RoundedFacts : LeafRoundedFacts 8
    leaf5321Certificate.logOnePlusV leaf5321InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5321InputLogOnePlusV_eq }

private noncomputable def leaf5321Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi299InputQChi innerPair300Input
    leaf5321InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5321LowerChecked :
    lowerCheck 24 leaf5321Box leaf5321Inputs = true := by
  rfl'

private theorem leaf5321CoversExact : CoversExact 8
    leaf5321Box leaf5321Certificate leaf5321InnerLog leaf5321Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi299RoundedFacts
    innerPair300RoundedFacts leaf5321RoundedFacts (by rfl)

private theorem leaf5321FlatSound : Sound leaf5321Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5321CertificateValid
    leaf5321InnerLogValid leaf5321CoversExact leaf5321LowerChecked

private noncomputable def leaf5322Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (91/256), chiHi := (23/64) }

private noncomputable def leaf5322Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871321/536870912) }, vSqrt := { lower := (8191/8192), upper := (4908388937/4908153856) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1204739881/1073741824) }, upper := { exponent := 1, mantissa := (4647/4096) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi300LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (9816542793/9816307712) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf5322InnerLog : WideLogData :=
  innerPair622Data

set_option maxRecDepth 1000000 in
private theorem leaf5322LocalValidity :
    LeafFacts leaf5322Box leaf5322Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5322Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4908388937/4908153856) }) = true
      norm_num [leaf5322Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5322CertificateValid :
    WideCertificateValid leaf5322Box leaf5322Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi300ValidityFacts
    leaf5322LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5322CoverageChecked :
    coverageCheck (innerAD leaf5322Box) leaf5322InnerLog = true := by
  rfl'

private theorem leaf5322InnerLogValid :
    leaf5322InnerLog.Valid 8 (innerAD leaf5322Box) :=
  wideLogDataValid_of_cachedCheck endpoint347PositiveFacts
    endpoint295PositiveFacts.valid leaf5322CoverageChecked

private noncomputable def leaf5322InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629483/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5322InputLogOnePlusV_eq :
    leaf5322InputLogOnePlusV = outerEnclosure 24
      (leaf5322Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5322RoundedFacts : LeafRoundedFacts 8
    leaf5322Certificate.logOnePlusV leaf5322InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5322InputLogOnePlusV_eq }

private noncomputable def leaf5322Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi300InputQChi innerPair622Input
    leaf5322InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5322LowerChecked :
    lowerCheck 24 leaf5322Box leaf5322Inputs = true := by
  rfl'

private theorem leaf5322CoversExact : CoversExact 8
    leaf5322Box leaf5322Certificate leaf5322InnerLog leaf5322Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi300RoundedFacts
    innerPair622RoundedFacts leaf5322RoundedFacts (by rfl)

private theorem leaf5322FlatSound : Sound leaf5322Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5322CertificateValid
    leaf5322InnerLogValid leaf5322CoversExact leaf5322LowerChecked

private noncomputable def leaf5323Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (45/128), chiHi := (91/256) }

private noncomputable def leaf5323Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871321/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357082624) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1203298177/1073741824) }, upper := { exponent := 1, mantissa := (9283/8192) } }, logOuter := sk168LogOuterCertificate, logK := sk168LogKCertificate, logChi := chi299LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715805183/68714165248) } }, logDArg := sk168LogDArgCertificate }

private noncomputable def leaf5323InnerLog : WideLogData :=
  innerPair622Data

set_option maxRecDepth 1000000 in
private theorem leaf5323LocalValidity :
    LeafFacts leaf5323Box leaf5323Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5323Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357082624) }) = true
      norm_num [leaf5323Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5323CertificateValid :
    WideCertificateValid leaf5323Box leaf5323Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk168ValidityFacts chi299ValidityFacts
    leaf5323LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5323CoverageChecked :
    coverageCheck (innerAD leaf5323Box) leaf5323InnerLog = true := by
  rfl'

private theorem leaf5323InnerLogValid :
    leaf5323InnerLog.Valid 8 (innerAD leaf5323Box) :=
  wideLogDataValid_of_cachedCheck endpoint347PositiveFacts
    endpoint295PositiveFacts.valid leaf5323CoverageChecked

private noncomputable def leaf5323InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629481/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5323InputLogOnePlusV_eq :
    leaf5323InputLogOnePlusV = outerEnclosure 24
      (leaf5323Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5323RoundedFacts : LeafRoundedFacts 8
    leaf5323Certificate.logOnePlusV leaf5323InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5323InputLogOnePlusV_eq }

private noncomputable def leaf5323Inputs : Inputs :=
  inputsOfCaches globalInput sk168RoundedInputs
    chi299InputQChi innerPair622Input
    leaf5323InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5323LowerChecked :
    lowerCheck 24 leaf5323Box leaf5323Inputs = true := by
  rfl'

private theorem leaf5323CoversExact : CoversExact 8
    leaf5323Box leaf5323Certificate leaf5323InnerLog leaf5323Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk168RoundedFacts chi299RoundedFacts
    innerPair622RoundedFacts leaf5323RoundedFacts (by rfl)

private theorem leaf5323FlatSound : Sound leaf5323Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5323CertificateValid
    leaf5323InnerLogValid leaf5323CoversExact leaf5323LowerChecked

private noncomputable def leaf5324Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (91/256), chiHi := (23/64) }

private noncomputable def leaf5324Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871323/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357053440) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1210703291/1073741824) }, upper := { exponent := 1, mantissa := (2335/2048) } }, logOuter := sk168LogOuterCertificate, logK := sk168LogKCertificate, logChi := chi300LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715775999/68714106880) } }, logDArg := sk168LogDArgCertificate }

private noncomputable def leaf5324InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf5324LocalValidity :
    LeafFacts leaf5324Box leaf5324Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5324Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357053440) }) = true
      norm_num [leaf5324Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5324CertificateValid :
    WideCertificateValid leaf5324Box leaf5324Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk168ValidityFacts chi300ValidityFacts
    leaf5324LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5324CoverageChecked :
    coverageCheck (innerAD leaf5324Box) leaf5324InnerLog = true := by
  rfl'

private theorem leaf5324InnerLogValid :
    leaf5324InnerLog.Valid 8 (innerAD leaf5324Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf5324CoverageChecked

private noncomputable def leaf5324InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726843/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf5324InputLogOnePlusV_eq :
    leaf5324InputLogOnePlusV = outerEnclosure 24
      (leaf5324Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5324RoundedFacts : LeafRoundedFacts 8
    leaf5324Certificate.logOnePlusV leaf5324InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5324InputLogOnePlusV_eq }

private noncomputable def leaf5324Inputs : Inputs :=
  inputsOfCaches globalInput sk168RoundedInputs
    chi300InputQChi innerPair264Input
    leaf5324InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5324LowerChecked :
    lowerCheck 24 leaf5324Box leaf5324Inputs = true := by
  rfl'

private theorem leaf5324CoversExact : CoversExact 8
    leaf5324Box leaf5324Certificate leaf5324InnerLog leaf5324Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk168RoundedFacts chi300RoundedFacts
    innerPair264RoundedFacts leaf5324RoundedFacts (by rfl)

private theorem leaf5324FlatSound : Sound leaf5324Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5324CertificateValid
    leaf5324InnerLogValid leaf5324CoversExact leaf5324LowerChecked

private noncomputable def leaf5325Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (11/32), chiHi := (89/256) }

private noncomputable def leaf5325Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871319/536870912) }, vSqrt := { lower := (8191/8192), upper := (4908388937/4908159744) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1194254763/1073741824) }, upper := { exponent := 1, mantissa := (18427/16384) } }, logOuter := sk161LogOuterCertificate, logK := sk161LogKCertificate, logChi := chi297LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (9816548681/9816319488) } }, logDArg := sk161LogDArgCertificate }

private noncomputable def leaf5325InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf5325LocalValidity :
    LeafFacts leaf5325Box leaf5325Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5325Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4908388937/4908159744) }) = true
      norm_num [leaf5325Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5325CertificateValid :
    WideCertificateValid leaf5325Box leaf5325Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk161ValidityFacts chi297ValidityFacts
    leaf5325LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5325CoverageChecked :
    coverageCheck (innerAD leaf5325Box) leaf5325InnerLog = true := by
  rfl'

private theorem leaf5325InnerLogValid :
    leaf5325InnerLog.Valid 8 (innerAD leaf5325Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf5325CoverageChecked

private noncomputable def leaf5325InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (363421/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf5325InputLogOnePlusV_eq :
    leaf5325InputLogOnePlusV = outerEnclosure 24
      (leaf5325Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5325RoundedFacts : LeafRoundedFacts 8
    leaf5325Certificate.logOnePlusV leaf5325InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5325InputLogOnePlusV_eq }

private noncomputable def leaf5325Inputs : Inputs :=
  inputsOfCaches globalInput sk161RoundedInputs
    chi297InputQChi innerPair256Input
    leaf5325InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5325LowerChecked :
    lowerCheck 24 leaf5325Box leaf5325Inputs = true := by
  rfl'

private theorem leaf5325CoversExact : CoversExact 8
    leaf5325Box leaf5325Certificate leaf5325InnerLog leaf5325Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk161RoundedFacts chi297RoundedFacts
    innerPair256RoundedFacts leaf5325RoundedFacts (by rfl)

private theorem leaf5325FlatSound : Sound leaf5325Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5325CertificateValid
    leaf5325InnerLogValid leaf5325CoversExact leaf5325LowerChecked

private noncomputable def leaf5326Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (89/256), chiHi := (45/128) }

private noncomputable def leaf5326Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871321/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357088768) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1201725409/1073741824) }, upper := { exponent := 1, mantissa := (9271/8192) } }, logOuter := sk161LogOuterCertificate, logK := sk161LogKCertificate, logChi := chi298LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715811327/68714177536) } }, logDArg := sk161LogDArgCertificate }

private noncomputable def leaf5326InnerLog : WideLogData :=
  innerPair621Data

set_option maxRecDepth 1000000 in
private theorem leaf5326LocalValidity :
    LeafFacts leaf5326Box leaf5326Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5326Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357088768) }) = true
      norm_num [leaf5326Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5326CertificateValid :
    WideCertificateValid leaf5326Box leaf5326Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk161ValidityFacts chi298ValidityFacts
    leaf5326LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5326CoverageChecked :
    coverageCheck (innerAD leaf5326Box) leaf5326InnerLog = true := by
  rfl'

private theorem leaf5326InnerLogValid :
    leaf5326InnerLog.Valid 8 (innerAD leaf5326Box) :=
  wideLogDataValid_of_cachedCheck endpoint347PositiveFacts
    endpoint292PositiveFacts.valid leaf5326CoverageChecked

private noncomputable def leaf5326InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453685/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf5326InputLogOnePlusV_eq :
    leaf5326InputLogOnePlusV = outerEnclosure 24
      (leaf5326Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5326RoundedFacts : LeafRoundedFacts 8
    leaf5326Certificate.logOnePlusV leaf5326InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5326InputLogOnePlusV_eq }

private noncomputable def leaf5326Inputs : Inputs :=
  inputsOfCaches globalInput sk161RoundedInputs
    chi298InputQChi innerPair621Input
    leaf5326InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5326LowerChecked :
    lowerCheck 24 leaf5326Box leaf5326Inputs = true := by
  rfl'

private theorem leaf5326CoversExact : CoversExact 8
    leaf5326Box leaf5326Certificate leaf5326InnerLog leaf5326Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk161RoundedFacts chi298RoundedFacts
    innerPair621RoundedFacts leaf5326RoundedFacts (by rfl)

private theorem leaf5326FlatSound : Sound leaf5326Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5326CertificateValid
    leaf5326InnerLogValid leaf5326CoversExact leaf5326LowerChecked

private noncomputable def leaf5327Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (11/32), chiHi := (89/256) }

private noncomputable def leaf5327Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871321/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357095424) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1200021577/1073741824) }, upper := { exponent := 1, mantissa := (4629/4096) } }, logOuter := sk162LogOuterCertificate, logK := sk162LogKCertificate, logChi := chi297LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715817983/68714190848) } }, logDArg := sk162LogDArgCertificate }

private noncomputable def leaf5327InnerLog : WideLogData :=
  innerPair621Data

set_option maxRecDepth 1000000 in
private theorem leaf5327LocalValidity :
    LeafFacts leaf5327Box leaf5327Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5327Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357095424) }) = true
      norm_num [leaf5327Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5327CertificateValid :
    WideCertificateValid leaf5327Box leaf5327Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk162ValidityFacts chi297ValidityFacts
    leaf5327LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5327CoverageChecked :
    coverageCheck (innerAD leaf5327Box) leaf5327InnerLog = true := by
  rfl'

private theorem leaf5327InnerLogValid :
    leaf5327InnerLog.Valid 8 (innerAD leaf5327Box) :=
  wideLogDataValid_of_cachedCheck endpoint347PositiveFacts
    endpoint292PositiveFacts.valid leaf5327CoverageChecked

private noncomputable def leaf5327InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814739/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5327InputLogOnePlusV_eq :
    leaf5327InputLogOnePlusV = outerEnclosure 24
      (leaf5327Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5327RoundedFacts : LeafRoundedFacts 8
    leaf5327Certificate.logOnePlusV leaf5327InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5327InputLogOnePlusV_eq }

private noncomputable def leaf5327Inputs : Inputs :=
  inputsOfCaches globalInput sk162RoundedInputs
    chi297InputQChi innerPair621Input
    leaf5327InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5327LowerChecked :
    lowerCheck 24 leaf5327Box leaf5327Inputs = true := by
  rfl'

private theorem leaf5327CoversExact : CoversExact 8
    leaf5327Box leaf5327Certificate leaf5327InnerLog leaf5327Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk162RoundedFacts chi297RoundedFacts
    innerPair621RoundedFacts leaf5327RoundedFacts (by rfl)

private theorem leaf5327FlatSound : Sound leaf5327Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5327CertificateValid
    leaf5327InnerLogValid leaf5327CoversExact leaf5327LowerChecked

private noncomputable def leaf5328Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (89/256), chiHi := (45/128) }

private noncomputable def leaf5328Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871323/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357065728) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1207557755/1073741824) }, upper := { exponent := 1, mantissa := (2329/2048) } }, logOuter := sk162LogOuterCertificate, logK := sk162LogKCertificate, logChi := chi298LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715788287/68714131456) } }, logDArg := sk162LogDArgCertificate }

private noncomputable def leaf5328InnerLog : WideLogData :=
  innerPair622Data

set_option maxRecDepth 1000000 in
private theorem leaf5328LocalValidity :
    LeafFacts leaf5328Box leaf5328Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5328Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357065728) }) = true
      norm_num [leaf5328Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5328CertificateValid :
    WideCertificateValid leaf5328Box leaf5328Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk162ValidityFacts chi298ValidityFacts
    leaf5328LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5328CoverageChecked :
    coverageCheck (innerAD leaf5328Box) leaf5328InnerLog = true := by
  rfl'

private theorem leaf5328InnerLogValid :
    leaf5328InnerLog.Valid 8 (innerAD leaf5328Box) :=
  wideLogDataValid_of_cachedCheck endpoint347PositiveFacts
    endpoint295PositiveFacts.valid leaf5328CoverageChecked

private noncomputable def leaf5328InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629485/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5328InputLogOnePlusV_eq :
    leaf5328InputLogOnePlusV = outerEnclosure 24
      (leaf5328Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5328RoundedFacts : LeafRoundedFacts 8
    leaf5328Certificate.logOnePlusV leaf5328InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5328InputLogOnePlusV_eq }

private noncomputable def leaf5328Inputs : Inputs :=
  inputsOfCaches globalInput sk162RoundedInputs
    chi298InputQChi innerPair622Input
    leaf5328InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5328LowerChecked :
    lowerCheck 24 leaf5328Box leaf5328Inputs = true := by
  rfl'

private theorem leaf5328CoversExact : CoversExact 8
    leaf5328Box leaf5328Certificate leaf5328InnerLog leaf5328Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk162RoundedFacts chi298RoundedFacts
    innerPair622RoundedFacts leaf5328RoundedFacts (by rfl)

private theorem leaf5328FlatSound : Sound leaf5328Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5328CertificateValid
    leaf5328InnerLogValid leaf5328CoversExact leaf5328LowerChecked

private noncomputable def leaf5329Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (45/128), chiHi := (91/256) }

private noncomputable def leaf5329Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871323/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357059328) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1209196055/1073741824) }, upper := { exponent := 1, mantissa := (18657/16384) } }, logOuter := sk161LogOuterCertificate, logK := sk161LogKCertificate, logChi := chi299LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715781887/68714118656) } }, logDArg := sk161LogDArgCertificate }

private noncomputable def leaf5329InnerLog : WideLogData :=
  innerPair269Data

set_option maxRecDepth 1000000 in
private theorem leaf5329LocalValidity :
    LeafFacts leaf5329Box leaf5329Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5329Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357059328) }) = true
      norm_num [leaf5329Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5329CertificateValid :
    WideCertificateValid leaf5329Box leaf5329Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk161ValidityFacts chi299ValidityFacts
    leaf5329LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5329CoverageChecked :
    coverageCheck (innerAD leaf5329Box) leaf5329InnerLog = true := by
  rfl'

private theorem leaf5329InnerLogValid :
    leaf5329InnerLog.Valid 8 (innerAD leaf5329Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint295PositiveFacts.valid leaf5329CoverageChecked

private noncomputable def leaf5329InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629487/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5329InputLogOnePlusV_eq :
    leaf5329InputLogOnePlusV = outerEnclosure 24
      (leaf5329Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5329RoundedFacts : LeafRoundedFacts 8
    leaf5329Certificate.logOnePlusV leaf5329InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5329InputLogOnePlusV_eq }

private noncomputable def leaf5329Inputs : Inputs :=
  inputsOfCaches globalInput sk161RoundedInputs
    chi299InputQChi innerPair269Input
    leaf5329InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5329LowerChecked :
    lowerCheck 24 leaf5329Box leaf5329Inputs = true := by
  rfl'

private theorem leaf5329CoversExact : CoversExact 8
    leaf5329Box leaf5329Certificate leaf5329InnerLog leaf5329Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk161RoundedFacts chi299RoundedFacts
    innerPair269RoundedFacts leaf5329RoundedFacts (by rfl)

private theorem leaf5329FlatSound : Sound leaf5329Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5329CertificateValid
    leaf5329InnerLogValid leaf5329CoversExact leaf5329LowerChecked

private noncomputable def leaf5330Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (91/256), chiHi := (23/64) }

private noncomputable def leaf5330Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871325/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357029888) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1216666701/1073741824) }, upper := { exponent := 1, mantissa := (4693/4096) } }, logOuter := sk161LogOuterCertificate, logK := sk161LogKCertificate, logChi := chi300LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715752447/68714059776) } }, logDArg := sk161LogDArgCertificate }

private noncomputable def leaf5330InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf5330LocalValidity :
    LeafFacts leaf5330Box leaf5330Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5330Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357029888) }) = true
      norm_num [leaf5330Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5330CertificateValid :
    WideCertificateValid leaf5330Box leaf5330Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk161ValidityFacts chi300ValidityFacts
    leaf5330LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5330CoverageChecked :
    coverageCheck (innerAD leaf5330Box) leaf5330InnerLog = true := by
  rfl'

private theorem leaf5330InnerLogValid :
    leaf5330InnerLog.Valid 8 (innerAD leaf5330Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf5330CoverageChecked

private noncomputable def leaf5330InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814747/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5330InputLogOnePlusV_eq :
    leaf5330InputLogOnePlusV = outerEnclosure 24
      (leaf5330Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5330RoundedFacts : LeafRoundedFacts 8
    leaf5330Certificate.logOnePlusV leaf5330InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5330InputLogOnePlusV_eq }

private noncomputable def leaf5330Inputs : Inputs :=
  inputsOfCaches globalInput sk161RoundedInputs
    chi300InputQChi innerPair264Input
    leaf5330InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5330LowerChecked :
    lowerCheck 24 leaf5330Box leaf5330Inputs = true := by
  rfl'

private theorem leaf5330CoversExact : CoversExact 8
    leaf5330Box leaf5330Certificate leaf5330InnerLog leaf5330Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk161RoundedFacts chi300RoundedFacts
    innerPair264RoundedFacts leaf5330RoundedFacts (by rfl)

private theorem leaf5330FlatSound : Sound leaf5330Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5330CertificateValid
    leaf5330InnerLogValid leaf5330CoversExact leaf5330LowerChecked

private noncomputable def leaf5331Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (45/128), chiHi := (91/256) }

private noncomputable def leaf5331Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871325/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357036032) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1215093933/1073741824) }, upper := { exponent := 1, mantissa := (4687/4096) } }, logOuter := sk162LogOuterCertificate, logK := sk162LogKCertificate, logChi := chi299LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715758591/68714072064) } }, logDArg := sk162LogDArgCertificate }

private noncomputable def leaf5331InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf5331LocalValidity :
    LeafFacts leaf5331Box leaf5331Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5331Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357036032) }) = true
      norm_num [leaf5331Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5331CertificateValid :
    WideCertificateValid leaf5331Box leaf5331Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk162ValidityFacts chi299ValidityFacts
    leaf5331LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5331CoverageChecked :
    coverageCheck (innerAD leaf5331Box) leaf5331InnerLog = true := by
  rfl'

private theorem leaf5331InnerLogValid :
    leaf5331InnerLog.Valid 8 (innerAD leaf5331Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf5331CoverageChecked

private noncomputable def leaf5331InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629493/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5331InputLogOnePlusV_eq :
    leaf5331InputLogOnePlusV = outerEnclosure 24
      (leaf5331Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5331RoundedFacts : LeafRoundedFacts 8
    leaf5331Certificate.logOnePlusV leaf5331InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5331InputLogOnePlusV_eq }

private noncomputable def leaf5331Inputs : Inputs :=
  inputsOfCaches globalInput sk162RoundedInputs
    chi299InputQChi innerPair264Input
    leaf5331InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5331LowerChecked :
    lowerCheck 24 leaf5331Box leaf5331Inputs = true := by
  rfl'

private theorem leaf5331CoversExact : CoversExact 8
    leaf5331Box leaf5331Certificate leaf5331InnerLog leaf5331Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk162RoundedFacts chi299RoundedFacts
    innerPair264RoundedFacts leaf5331RoundedFacts (by rfl)

private theorem leaf5331FlatSound : Sound leaf5331Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5331CertificateValid
    leaf5331InnerLogValid leaf5331CoversExact leaf5331LowerChecked

private noncomputable def leaf5332Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (91/256), chiHi := (23/64) }

private noncomputable def leaf5332Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871327/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357006336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1222630111/1073741824) }, upper := { exponent := 1, mantissa := (1179/1024) } }, logOuter := sk162LogOuterCertificate, logK := sk162LogKCertificate, logChi := chi300LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715728895/68714012672) } }, logDArg := sk162LogDArgCertificate }

private noncomputable def leaf5332InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf5332LocalValidity :
    LeafFacts leaf5332Box leaf5332Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5332Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357006336) }) = true
      norm_num [leaf5332Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5332CertificateValid :
    WideCertificateValid leaf5332Box leaf5332Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk162ValidityFacts chi300ValidityFacts
    leaf5332LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5332CoverageChecked :
    coverageCheck (innerAD leaf5332Box) leaf5332InnerLog = true := by
  rfl'

private theorem leaf5332InnerLogValid :
    leaf5332InnerLog.Valid 8 (innerAD leaf5332Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf5332CoverageChecked

private noncomputable def leaf5332InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907375/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5332InputLogOnePlusV_eq :
    leaf5332InputLogOnePlusV = outerEnclosure 24
      (leaf5332Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5332RoundedFacts : LeafRoundedFacts 8
    leaf5332Certificate.logOnePlusV leaf5332InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5332InputLogOnePlusV_eq }

private noncomputable def leaf5332Inputs : Inputs :=
  inputsOfCaches globalInput sk162RoundedInputs
    chi300InputQChi innerPair264Input
    leaf5332InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5332LowerChecked :
    lowerCheck 24 leaf5332Box leaf5332Inputs = true := by
  rfl'

private theorem leaf5332CoversExact : CoversExact 8
    leaf5332Box leaf5332Certificate leaf5332InnerLog leaf5332Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk162RoundedFacts chi300RoundedFacts
    innerPair264RoundedFacts leaf5332RoundedFacts (by rfl)

private theorem leaf5332FlatSound : Sound leaf5332Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5332CertificateValid
    leaf5332InnerLogValid leaf5332CoversExact leaf5332LowerChecked

private noncomputable def leaf5333Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (23/64), chiHi := (93/256) }

private noncomputable def leaf5333Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871323/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357048064) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1212079463/1073741824) }, upper := { exponent := 1, mantissa := (18701/16384) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi301LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715770623/68714096128) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf5333InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf5333LocalValidity :
    LeafFacts leaf5333Box leaf5333Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5333Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357048064) }) = true
      norm_num [leaf5333Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5333CertificateValid :
    WideCertificateValid leaf5333Box leaf5333Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi301ValidityFacts
    leaf5333LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5333CoverageChecked :
    coverageCheck (innerAD leaf5333Box) leaf5333InnerLog = true := by
  rfl'

private theorem leaf5333InnerLogValid :
    leaf5333InnerLog.Valid 8 (innerAD leaf5333Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf5333CoverageChecked

private noncomputable def leaf5333InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814745/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5333InputLogOnePlusV_eq :
    leaf5333InputLogOnePlusV = outerEnclosure 24
      (leaf5333Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5333RoundedFacts : LeafRoundedFacts 8
    leaf5333Certificate.logOnePlusV leaf5333InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5333InputLogOnePlusV_eq }

private noncomputable def leaf5333Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi301InputQChi innerPair264Input
    leaf5333InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5333LowerChecked :
    lowerCheck 24 leaf5333Box leaf5333Inputs = true := by
  rfl'

private theorem leaf5333CoversExact : CoversExact 8
    leaf5333Box leaf5333Certificate leaf5333InnerLog leaf5333Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi301RoundedFacts
    innerPair264RoundedFacts leaf5333RoundedFacts (by rfl)

private theorem leaf5333FlatSound : Sound leaf5333Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5333CertificateValid
    leaf5333InnerLogValid leaf5333CoversExact leaf5333LowerChecked

private noncomputable def leaf5334Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (93/256), chiHi := (47/128) }

private noncomputable def leaf5334Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871325/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357019136) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1219419045/1073741824) }, upper := { exponent := 1, mantissa := (9407/8192) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi302LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715741695/68714038272) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf5334InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf5334LocalValidity :
    LeafFacts leaf5334Box leaf5334Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5334Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357019136) }) = true
      norm_num [leaf5334Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5334CertificateValid :
    WideCertificateValid leaf5334Box leaf5334Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi302ValidityFacts
    leaf5334LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5334CoverageChecked :
    coverageCheck (innerAD leaf5334Box) leaf5334InnerLog = true := by
  rfl'

private theorem leaf5334InnerLogValid :
    leaf5334InnerLog.Valid 8 (innerAD leaf5334Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf5334CoverageChecked

private noncomputable def leaf5334InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629497/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5334InputLogOnePlusV_eq :
    leaf5334InputLogOnePlusV = outerEnclosure 24
      (leaf5334Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5334RoundedFacts : LeafRoundedFacts 8
    leaf5334Certificate.logOnePlusV leaf5334InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5334InputLogOnePlusV_eq }

private noncomputable def leaf5334Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi302InputQChi innerPair264Input
    leaf5334InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5334LowerChecked :
    lowerCheck 24 leaf5334Box leaf5334Inputs = true := by
  rfl'

private theorem leaf5334CoversExact : CoversExact 8
    leaf5334Box leaf5334Certificate leaf5334InnerLog leaf5334Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi302RoundedFacts
    innerPair264RoundedFacts leaf5334RoundedFacts (by rfl)

private theorem leaf5334FlatSound : Sound leaf5334Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5334CertificateValid
    leaf5334InnerLogValid leaf5334CoversExact leaf5334LowerChecked

private noncomputable def leaf5335Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (23/64), chiHi := (93/256) }

private noncomputable def leaf5335Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871325/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357024256) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1218108405/1073741824) }, upper := { exponent := 1, mantissa := (9397/8192) } }, logOuter := sk168LogOuterCertificate, logK := sk168LogKCertificate, logChi := chi301LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715746815/68714048512) } }, logDArg := sk168LogDArgCertificate }

private noncomputable def leaf5335InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf5335LocalValidity :
    LeafFacts leaf5335Box leaf5335Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5335Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357024256) }) = true
      norm_num [leaf5335Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5335CertificateValid :
    WideCertificateValid leaf5335Box leaf5335Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk168ValidityFacts chi301ValidityFacts
    leaf5335LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5335CoverageChecked :
    coverageCheck (innerAD leaf5335Box) leaf5335InnerLog = true := by
  rfl'

private theorem leaf5335InnerLogValid :
    leaf5335InnerLog.Valid 8 (innerAD leaf5335Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf5335CoverageChecked

private noncomputable def leaf5335InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629495/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5335InputLogOnePlusV_eq :
    leaf5335InputLogOnePlusV = outerEnclosure 24
      (leaf5335Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5335RoundedFacts : LeafRoundedFacts 8
    leaf5335Certificate.logOnePlusV leaf5335InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5335InputLogOnePlusV_eq }

private noncomputable def leaf5335Inputs : Inputs :=
  inputsOfCaches globalInput sk168RoundedInputs
    chi301InputQChi innerPair264Input
    leaf5335InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5335LowerChecked :
    lowerCheck 24 leaf5335Box leaf5335Inputs = true := by
  rfl'

private theorem leaf5335CoversExact : CoversExact 8
    leaf5335Box leaf5335Certificate leaf5335InnerLog leaf5335Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk168RoundedFacts chi301RoundedFacts
    innerPair264RoundedFacts leaf5335RoundedFacts (by rfl)

private theorem leaf5335FlatSound : Sound leaf5335Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5335CertificateValid
    leaf5335InnerLogValid leaf5335CoversExact leaf5335LowerChecked

private noncomputable def leaf5336Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (93/256), chiHi := (47/128) }

private noncomputable def leaf5336Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871327/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356995072) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1225513519/1073741824) }, upper := { exponent := 1, mantissa := (4727/4096) } }, logOuter := sk168LogOuterCertificate, logK := sk168LogKCertificate, logChi := chi302LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715717631/68713990144) } }, logDArg := sk168LogDArgCertificate }

private noncomputable def leaf5336InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf5336LocalValidity :
    LeafFacts leaf5336Box leaf5336Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5336Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356995072) }) = true
      norm_num [leaf5336Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5336CertificateValid :
    WideCertificateValid leaf5336Box leaf5336Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk168ValidityFacts chi302ValidityFacts
    leaf5336LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5336CoverageChecked :
    coverageCheck (innerAD leaf5336Box) leaf5336InnerLog = true := by
  rfl'

private theorem leaf5336InnerLogValid :
    leaf5336InnerLog.Valid 8 (innerAD leaf5336Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf5336CoverageChecked

private noncomputable def leaf5336InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629503/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5336InputLogOnePlusV_eq :
    leaf5336InputLogOnePlusV = outerEnclosure 24
      (leaf5336Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5336RoundedFacts : LeafRoundedFacts 8
    leaf5336Certificate.logOnePlusV leaf5336InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5336InputLogOnePlusV_eq }

private noncomputable def leaf5336Inputs : Inputs :=
  inputsOfCaches globalInput sk168RoundedInputs
    chi302InputQChi innerPair264Input
    leaf5336InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5336LowerChecked :
    lowerCheck 24 leaf5336Box leaf5336Inputs = true := by
  rfl'

private theorem leaf5336CoversExact : CoversExact 8
    leaf5336Box leaf5336Certificate leaf5336InnerLog leaf5336Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk168RoundedFacts chi302RoundedFacts
    innerPair264RoundedFacts leaf5336RoundedFacts (by rfl)

private theorem leaf5336FlatSound : Sound leaf5336Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5336CertificateValid
    leaf5336InnerLogValid leaf5336CoversExact leaf5336LowerChecked

private noncomputable def leaf5337Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (47/128), chiHi := (95/256) }

private noncomputable def leaf5337Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871327/536870912) }, vSqrt := { lower := (8191/8192), upper := (2021101327/2020999424) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1226758627/1073741824) }, upper := { exponent := 1, mantissa := (18927/16384) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi303LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (4042100751/4041998848) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf5337InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf5337LocalValidity :
    LeafFacts leaf5337Box leaf5337Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5337Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (2021101327/2020999424) }) = true
      norm_num [leaf5337Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5337CertificateValid :
    WideCertificateValid leaf5337Box leaf5337Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi303ValidityFacts
    leaf5337LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5337CoverageChecked :
    coverageCheck (innerAD leaf5337Box) leaf5337InnerLog = true := by
  rfl'

private theorem leaf5337InnerLogValid :
    leaf5337InnerLog.Valid 8 (innerAD leaf5337Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf5337CoverageChecked

private noncomputable def leaf5337InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (181711/262144) }

set_option maxRecDepth 1000000 in
private theorem leaf5337InputLogOnePlusV_eq :
    leaf5337InputLogOnePlusV = outerEnclosure 24
      (leaf5337Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5337RoundedFacts : LeafRoundedFacts 8
    leaf5337Certificate.logOnePlusV leaf5337InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5337InputLogOnePlusV_eq }

private noncomputable def leaf5337Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi303InputQChi innerPair264Input
    leaf5337InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5337LowerChecked :
    lowerCheck 24 leaf5337Box leaf5337Inputs = true := by
  rfl'

private theorem leaf5337CoversExact : CoversExact 8
    leaf5337Box leaf5337Certificate leaf5337InnerLog leaf5337Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi303RoundedFacts
    innerPair264RoundedFacts leaf5337RoundedFacts (by rfl)

private theorem leaf5337FlatSound : Sound leaf5337Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5337CertificateValid
    leaf5337InnerLogValid leaf5337CoversExact leaf5337LowerChecked

private noncomputable def leaf5338Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (95/256), chiHi := (3/8) }

private noncomputable def leaf5338Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871329/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356961280) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1234098209/1073741824) }, upper := { exponent := 1, mantissa := (595/512) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi304LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715683839/68713922560) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf5338InnerLog : WideLogData :=
  innerPair265Data

set_option maxRecDepth 1000000 in
private theorem leaf5338LocalValidity :
    LeafFacts leaf5338Box leaf5338Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5338Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356961280) }) = true
      norm_num [leaf5338Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5338CertificateValid :
    WideCertificateValid leaf5338Box leaf5338Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi304ValidityFacts
    leaf5338LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5338CoverageChecked :
    coverageCheck (innerAD leaf5338Box) leaf5338InnerLog = true := by
  rfl'

private theorem leaf5338InnerLogValid :
    leaf5338InnerLog.Valid 8 (innerAD leaf5338Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint77PositiveFacts.valid leaf5338CoverageChecked

private noncomputable def leaf5338InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629511/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5338InputLogOnePlusV_eq :
    leaf5338InputLogOnePlusV = outerEnclosure 24
      (leaf5338Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5338RoundedFacts : LeafRoundedFacts 8
    leaf5338Certificate.logOnePlusV leaf5338InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5338InputLogOnePlusV_eq }

private noncomputable def leaf5338Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi304InputQChi innerPair265Input
    leaf5338InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5338LowerChecked :
    lowerCheck 24 leaf5338Box leaf5338Inputs = true := by
  rfl'

private theorem leaf5338CoversExact : CoversExact 8
    leaf5338Box leaf5338Certificate leaf5338InnerLog leaf5338Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi304RoundedFacts
    innerPair265RoundedFacts leaf5338RoundedFacts (by rfl)

private theorem leaf5338FlatSound : Sound leaf5338Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5338CertificateValid
    leaf5338InnerLogValid leaf5338CoversExact leaf5338LowerChecked

private noncomputable def leaf5339Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (47/128), chiHi := (95/256) }

private noncomputable def leaf5339Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871329/536870912) }, vSqrt := { lower := (8191/8192), upper := (4908388937/4908137984) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1232918633/1073741824) }, upper := { exponent := 1, mantissa := (9511/8192) } }, logOuter := sk168LogOuterCertificate, logK := sk168LogKCertificate, logChi := chi303LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (9816526921/9816275968) } }, logDArg := sk168LogDArgCertificate }

private noncomputable def leaf5339InnerLog : WideLogData :=
  innerPair563Data

set_option maxRecDepth 1000000 in
private theorem leaf5339LocalValidity :
    LeafFacts leaf5339Box leaf5339Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5339Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4908388937/4908137984) }) = true
      norm_num [leaf5339Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5339CertificateValid :
    WideCertificateValid leaf5339Box leaf5339Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk168ValidityFacts chi303ValidityFacts
    leaf5339LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5339CoverageChecked :
    coverageCheck (innerAD leaf5339Box) leaf5339InnerLog = true := by
  rfl'

private theorem leaf5339InnerLogValid :
    leaf5339InnerLog.Valid 8 (innerAD leaf5339Box) :=
  wideLogDataValid_of_cachedCheck endpoint295PositiveFacts
    endpoint296PositiveFacts.valid leaf5339CoverageChecked

private noncomputable def leaf5339InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814755/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5339InputLogOnePlusV_eq :
    leaf5339InputLogOnePlusV = outerEnclosure 24
      (leaf5339Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5339RoundedFacts : LeafRoundedFacts 8
    leaf5339Certificate.logOnePlusV leaf5339InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5339InputLogOnePlusV_eq }

private noncomputable def leaf5339Inputs : Inputs :=
  inputsOfCaches globalInput sk168RoundedInputs
    chi303InputQChi innerPair563Input
    leaf5339InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5339LowerChecked :
    lowerCheck 24 leaf5339Box leaf5339Inputs = true := by
  rfl'

private theorem leaf5339CoversExact : CoversExact 8
    leaf5339Box leaf5339Certificate leaf5339InnerLog leaf5339Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk168RoundedFacts chi303RoundedFacts
    innerPair563RoundedFacts leaf5339RoundedFacts (by rfl)

private theorem leaf5339FlatSound : Sound leaf5339Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5339CertificateValid
    leaf5339InnerLogValid leaf5339CoversExact leaf5339LowerChecked

private noncomputable def leaf5340Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (95/256), chiHi := (3/8) }

private noncomputable def leaf5340Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871331/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356936704) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1240323747/1073741824) }, upper := { exponent := 1, mantissa := (299/256) } }, logOuter := sk168LogOuterCertificate, logK := sk168LogKCertificate, logChi := chi304LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715659263/68713873408) } }, logDArg := sk168LogDArgCertificate }

private noncomputable def leaf5340InnerLog : WideLogData :=
  innerPair265Data

set_option maxRecDepth 1000000 in
private theorem leaf5340LocalValidity :
    LeafFacts leaf5340Box leaf5340Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5340Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356936704) }) = true
      norm_num [leaf5340Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5340CertificateValid :
    WideCertificateValid leaf5340Box leaf5340Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk168ValidityFacts chi304ValidityFacts
    leaf5340LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5340CoverageChecked :
    coverageCheck (innerAD leaf5340Box) leaf5340InnerLog = true := by
  rfl'

private theorem leaf5340InnerLogValid :
    leaf5340InnerLog.Valid 8 (innerAD leaf5340Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint77PositiveFacts.valid leaf5340CoverageChecked

private noncomputable def leaf5340InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629517/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5340InputLogOnePlusV_eq :
    leaf5340InputLogOnePlusV = outerEnclosure 24
      (leaf5340Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5340RoundedFacts : LeafRoundedFacts 8
    leaf5340Certificate.logOnePlusV leaf5340InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5340InputLogOnePlusV_eq }

private noncomputable def leaf5340Inputs : Inputs :=
  inputsOfCaches globalInput sk168RoundedInputs
    chi304InputQChi innerPair265Input
    leaf5340InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5340LowerChecked :
    lowerCheck 24 leaf5340Box leaf5340Inputs = true := by
  rfl'

private theorem leaf5340CoversExact : CoversExact 8
    leaf5340Box leaf5340Certificate leaf5340InnerLog leaf5340Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk168RoundedFacts chi304RoundedFacts
    innerPair265RoundedFacts leaf5340RoundedFacts (by rfl)

private theorem leaf5340FlatSound : Sound leaf5340Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5340CertificateValid
    leaf5340InnerLogValid leaf5340CoversExact leaf5340LowerChecked

private noncomputable def leaf5341Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (23/64), chiHi := (93/256) }

private noncomputable def leaf5341Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871327/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357000448) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1224137347/1073741824) }, upper := { exponent := 1, mantissa := (18887/16384) } }, logOuter := sk161LogOuterCertificate, logK := sk161LogKCertificate, logChi := chi301LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715723007/68714000896) } }, logDArg := sk161LogDArgCertificate }

private noncomputable def leaf5341InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf5341LocalValidity :
    LeafFacts leaf5341Box leaf5341Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5341Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357000448) }) = true
      norm_num [leaf5341Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5341CertificateValid :
    WideCertificateValid leaf5341Box leaf5341Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk161ValidityFacts chi301ValidityFacts
    leaf5341LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5341CoverageChecked :
    coverageCheck (innerAD leaf5341Box) leaf5341InnerLog = true := by
  rfl'

private theorem leaf5341InnerLogValid :
    leaf5341InnerLog.Valid 8 (innerAD leaf5341Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf5341CoverageChecked

private noncomputable def leaf5341InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629501/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5341InputLogOnePlusV_eq :
    leaf5341InputLogOnePlusV = outerEnclosure 24
      (leaf5341Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5341RoundedFacts : LeafRoundedFacts 8
    leaf5341Certificate.logOnePlusV leaf5341InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5341InputLogOnePlusV_eq }

private noncomputable def leaf5341Inputs : Inputs :=
  inputsOfCaches globalInput sk161RoundedInputs
    chi301InputQChi innerPair264Input
    leaf5341InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5341LowerChecked :
    lowerCheck 24 leaf5341Box leaf5341Inputs = true := by
  rfl'

private theorem leaf5341CoversExact : CoversExact 8
    leaf5341Box leaf5341Certificate leaf5341InnerLog leaf5341Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk161RoundedFacts chi301RoundedFacts
    innerPair264RoundedFacts leaf5341RoundedFacts (by rfl)

private theorem leaf5341FlatSound : Sound leaf5341Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5341CertificateValid
    leaf5341InnerLogValid leaf5341CoversExact leaf5341LowerChecked

private noncomputable def leaf5342Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (93/256), chiHi := (47/128) }

private noncomputable def leaf5342Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871329/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356971008) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1231607993/1073741824) }, upper := { exponent := 1, mantissa := (9501/8192) } }, logOuter := sk161LogOuterCertificate, logK := sk161LogKCertificate, logChi := chi302LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715693567/68713942016) } }, logDArg := sk161LogDArgCertificate }

private noncomputable def leaf5342InnerLog : WideLogData :=
  innerPair563Data

set_option maxRecDepth 1000000 in
private theorem leaf5342LocalValidity :
    LeafFacts leaf5342Box leaf5342Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5342Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356971008) }) = true
      norm_num [leaf5342Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5342CertificateValid :
    WideCertificateValid leaf5342Box leaf5342Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk161ValidityFacts chi302ValidityFacts
    leaf5342LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5342CoverageChecked :
    coverageCheck (innerAD leaf5342Box) leaf5342InnerLog = true := by
  rfl'

private theorem leaf5342InnerLogValid :
    leaf5342InnerLog.Valid 8 (innerAD leaf5342Box) :=
  wideLogDataValid_of_cachedCheck endpoint295PositiveFacts
    endpoint296PositiveFacts.valid leaf5342CoverageChecked

private noncomputable def leaf5342InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907377/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5342InputLogOnePlusV_eq :
    leaf5342InputLogOnePlusV = outerEnclosure 24
      (leaf5342Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5342RoundedFacts : LeafRoundedFacts 8
    leaf5342Certificate.logOnePlusV leaf5342InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5342InputLogOnePlusV_eq }

private noncomputable def leaf5342Inputs : Inputs :=
  inputsOfCaches globalInput sk161RoundedInputs
    chi302InputQChi innerPair563Input
    leaf5342InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5342LowerChecked :
    lowerCheck 24 leaf5342Box leaf5342Inputs = true := by
  rfl'

private theorem leaf5342CoversExact : CoversExact 8
    leaf5342Box leaf5342Certificate leaf5342InnerLog leaf5342Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk161RoundedFacts chi302RoundedFacts
    innerPair563RoundedFacts leaf5342RoundedFacts (by rfl)

private theorem leaf5342FlatSound : Sound leaf5342Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5342CertificateValid
    leaf5342InnerLogValid leaf5342CoversExact leaf5342LowerChecked

private noncomputable def leaf5343Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (23/64), chiHi := (93/256) }

private noncomputable def leaf5343Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871329/536870912) }, vSqrt := { lower := (8191/8192), upper := (4908388937/4908139520) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1230166289/1073741824) }, upper := { exponent := 1, mantissa := (4745/4096) } }, logOuter := sk162LogOuterCertificate, logK := sk162LogKCertificate, logChi := chi301LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (9816528457/9816279040) } }, logDArg := sk162LogDArgCertificate }

private noncomputable def leaf5343InnerLog : WideLogData :=
  innerPair563Data

set_option maxRecDepth 1000000 in
private theorem leaf5343LocalValidity :
    LeafFacts leaf5343Box leaf5343Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5343Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4908388937/4908139520) }) = true
      norm_num [leaf5343Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5343CertificateValid :
    WideCertificateValid leaf5343Box leaf5343Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk162ValidityFacts chi301ValidityFacts
    leaf5343LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5343CoverageChecked :
    coverageCheck (innerAD leaf5343Box) leaf5343InnerLog = true := by
  rfl'

private theorem leaf5343InnerLogValid :
    leaf5343InnerLog.Valid 8 (innerAD leaf5343Box) :=
  wideLogDataValid_of_cachedCheck endpoint295PositiveFacts
    endpoint296PositiveFacts.valid leaf5343CoverageChecked

private noncomputable def leaf5343InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629507/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5343InputLogOnePlusV_eq :
    leaf5343InputLogOnePlusV = outerEnclosure 24
      (leaf5343Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5343RoundedFacts : LeafRoundedFacts 8
    leaf5343Certificate.logOnePlusV leaf5343InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5343InputLogOnePlusV_eq }

private noncomputable def leaf5343Inputs : Inputs :=
  inputsOfCaches globalInput sk162RoundedInputs
    chi301InputQChi innerPair563Input
    leaf5343InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5343LowerChecked :
    lowerCheck 24 leaf5343Box leaf5343Inputs = true := by
  rfl'

private theorem leaf5343CoversExact : CoversExact 8
    leaf5343Box leaf5343Certificate leaf5343InnerLog leaf5343Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk162RoundedFacts chi301RoundedFacts
    innerPair563RoundedFacts leaf5343RoundedFacts (by rfl)

private theorem leaf5343FlatSound : Sound leaf5343Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5343CertificateValid
    leaf5343InnerLogValid leaf5343CoversExact leaf5343LowerChecked

private noncomputable def leaf5344Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (93/256), chiHi := (47/128) }

private noncomputable def leaf5344Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871331/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356946944) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1237702467/1073741824) }, upper := { exponent := 1, mantissa := (2387/2048) } }, logOuter := sk162LogOuterCertificate, logK := sk162LogKCertificate, logChi := chi302LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715669503/68713893888) } }, logDArg := sk162LogDArgCertificate }

private noncomputable def leaf5344InnerLog : WideLogData :=
  innerPair572Data

set_option maxRecDepth 1000000 in
private theorem leaf5344LocalValidity :
    LeafFacts leaf5344Box leaf5344Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5344Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356946944) }) = true
      norm_num [leaf5344Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5344CertificateValid :
    WideCertificateValid leaf5344Box leaf5344Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk162ValidityFacts chi302ValidityFacts
    leaf5344LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5344CoverageChecked :
    coverageCheck (innerAD leaf5344Box) leaf5344InnerLog = true := by
  rfl'

private theorem leaf5344InnerLogValid :
    leaf5344InnerLog.Valid 8 (innerAD leaf5344Box) :=
  wideLogDataValid_of_cachedCheck endpoint298PositiveFacts
    endpoint297PositiveFacts.valid leaf5344CoverageChecked

private noncomputable def leaf5344InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814757/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5344InputLogOnePlusV_eq :
    leaf5344InputLogOnePlusV = outerEnclosure 24
      (leaf5344Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5344RoundedFacts : LeafRoundedFacts 8
    leaf5344Certificate.logOnePlusV leaf5344InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5344InputLogOnePlusV_eq }

private noncomputable def leaf5344Inputs : Inputs :=
  inputsOfCaches globalInput sk162RoundedInputs
    chi302InputQChi innerPair572Input
    leaf5344InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5344LowerChecked :
    lowerCheck 24 leaf5344Box leaf5344Inputs = true := by
  rfl'

private theorem leaf5344CoversExact : CoversExact 8
    leaf5344Box leaf5344Certificate leaf5344InnerLog leaf5344Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk162RoundedFacts chi302RoundedFacts
    innerPair572RoundedFacts leaf5344RoundedFacts (by rfl)

private theorem leaf5344FlatSound : Sound leaf5344Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5344CertificateValid
    leaf5344InnerLogValid leaf5344CoversExact leaf5344LowerChecked

private noncomputable def leaf5345Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (47/128), chiHi := (95/256) }

private noncomputable def leaf5345Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871331/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356941568) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1239078639/1073741824) }, upper := { exponent := 1, mantissa := (19117/16384) } }, logOuter := sk161LogOuterCertificate, logK := sk161LogKCertificate, logChi := chi303LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715664127/68713883136) } }, logDArg := sk161LogDArgCertificate }

private noncomputable def leaf5345InnerLog : WideLogData :=
  innerPair265Data

set_option maxRecDepth 1000000 in
private theorem leaf5345LocalValidity :
    LeafFacts leaf5345Box leaf5345Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5345Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356941568) }) = true
      norm_num [leaf5345Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5345CertificateValid :
    WideCertificateValid leaf5345Box leaf5345Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk161ValidityFacts chi303ValidityFacts
    leaf5345LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5345CoverageChecked :
    coverageCheck (innerAD leaf5345Box) leaf5345InnerLog = true := by
  rfl'

private theorem leaf5345InnerLogValid :
    leaf5345InnerLog.Valid 8 (innerAD leaf5345Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint77PositiveFacts.valid leaf5345CoverageChecked

private noncomputable def leaf5345InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907379/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5345InputLogOnePlusV_eq :
    leaf5345InputLogOnePlusV = outerEnclosure 24
      (leaf5345Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5345RoundedFacts : LeafRoundedFacts 8
    leaf5345Certificate.logOnePlusV leaf5345InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5345InputLogOnePlusV_eq }

private noncomputable def leaf5345Inputs : Inputs :=
  inputsOfCaches globalInput sk161RoundedInputs
    chi303InputQChi innerPair265Input
    leaf5345InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5345LowerChecked :
    lowerCheck 24 leaf5345Box leaf5345Inputs = true := by
  rfl'

private theorem leaf5345CoversExact : CoversExact 8
    leaf5345Box leaf5345Certificate leaf5345InnerLog leaf5345Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk161RoundedFacts chi303RoundedFacts
    innerPair265RoundedFacts leaf5345RoundedFacts (by rfl)

private theorem leaf5345FlatSound : Sound leaf5345Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5345CertificateValid
    leaf5345InnerLogValid leaf5345CoversExact leaf5345LowerChecked

private noncomputable def leaf5346Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (95/256), chiHi := (3/8) }

private noncomputable def leaf5346Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871333/536870912) }, vSqrt := { lower := (8191/8192), upper := (158335127/158326784) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1246549285/1073741824) }, upper := { exponent := 1, mantissa := (601/512) } }, logOuter := sk161LogOuterCertificate, logK := sk161LogKCertificate, logChi := chi304LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (316661911/316653568) } }, logDArg := sk161LogDArgCertificate }

private noncomputable def leaf5346InnerLog : WideLogData :=
  innerPair272Data

set_option maxRecDepth 1000000 in
private theorem leaf5346LocalValidity :
    LeafFacts leaf5346Box leaf5346Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5346Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (158335127/158326784) }) = true
      norm_num [leaf5346Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5346CertificateValid :
    WideCertificateValid leaf5346Box leaf5346Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk161ValidityFacts chi304ValidityFacts
    leaf5346LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5346CoverageChecked :
    coverageCheck (innerAD leaf5346Box) leaf5346InnerLog = true := by
  rfl'

private theorem leaf5346InnerLogValid :
    leaf5346InnerLog.Valid 8 (innerAD leaf5346Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint77PositiveFacts.valid leaf5346CoverageChecked

private noncomputable def leaf5346InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629523/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5346InputLogOnePlusV_eq :
    leaf5346InputLogOnePlusV = outerEnclosure 24
      (leaf5346Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5346RoundedFacts : LeafRoundedFacts 8
    leaf5346Certificate.logOnePlusV leaf5346InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5346InputLogOnePlusV_eq }

private noncomputable def leaf5346Inputs : Inputs :=
  inputsOfCaches globalInput sk161RoundedInputs
    chi304InputQChi innerPair272Input
    leaf5346InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5346LowerChecked :
    lowerCheck 24 leaf5346Box leaf5346Inputs = true := by
  rfl'

private theorem leaf5346CoversExact : CoversExact 8
    leaf5346Box leaf5346Certificate leaf5346InnerLog leaf5346Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk161RoundedFacts chi304RoundedFacts
    innerPair272RoundedFacts leaf5346RoundedFacts (by rfl)

private theorem leaf5346FlatSound : Sound leaf5346Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5346CertificateValid
    leaf5346InnerLogValid leaf5346CoversExact leaf5346LowerChecked

private noncomputable def leaf5347Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (47/128), chiHi := (95/256) }

private noncomputable def leaf5347Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871333/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356917248) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1245238645/1073741824) }, upper := { exponent := 1, mantissa := (4803/4096) } }, logOuter := sk162LogOuterCertificate, logK := sk162LogKCertificate, logChi := chi303LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715639807/68713834496) } }, logDArg := sk162LogDArgCertificate }

private noncomputable def leaf5347InnerLog : WideLogData :=
  innerPair272Data

set_option maxRecDepth 1000000 in
private theorem leaf5347LocalValidity :
    LeafFacts leaf5347Box leaf5347Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5347Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356917248) }) = true
      norm_num [leaf5347Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5347CertificateValid :
    WideCertificateValid leaf5347Box leaf5347Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk162ValidityFacts chi303ValidityFacts
    leaf5347LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5347CoverageChecked :
    coverageCheck (innerAD leaf5347Box) leaf5347InnerLog = true := by
  rfl'

private theorem leaf5347InnerLogValid :
    leaf5347InnerLog.Valid 8 (innerAD leaf5347Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint77PositiveFacts.valid leaf5347CoverageChecked

private noncomputable def leaf5347InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814761/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5347InputLogOnePlusV_eq :
    leaf5347InputLogOnePlusV = outerEnclosure 24
      (leaf5347Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5347RoundedFacts : LeafRoundedFacts 8
    leaf5347Certificate.logOnePlusV leaf5347InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5347InputLogOnePlusV_eq }

private noncomputable def leaf5347Inputs : Inputs :=
  inputsOfCaches globalInput sk162RoundedInputs
    chi303InputQChi innerPair272Input
    leaf5347InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5347LowerChecked :
    lowerCheck 24 leaf5347Box leaf5347Inputs = true := by
  rfl'

private theorem leaf5347CoversExact : CoversExact 8
    leaf5347Box leaf5347Certificate leaf5347InnerLog leaf5347Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk162RoundedFacts chi303RoundedFacts
    innerPair272RoundedFacts leaf5347RoundedFacts (by rfl)

private theorem leaf5347FlatSound : Sound leaf5347Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5347CertificateValid
    leaf5347InnerLogValid leaf5347CoversExact leaf5347LowerChecked

private noncomputable def leaf5348Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (95/256), chiHi := (3/8) }

private noncomputable def leaf5348Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871335/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356887552) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1252774823/1073741824) }, upper := { exponent := 1, mantissa := (151/128) } }, logOuter := sk162LogOuterCertificate, logK := sk162LogKCertificate, logChi := chi304LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715610111/68713775104) } }, logDArg := sk162LogDArgCertificate }

private noncomputable def leaf5348InnerLog : WideLogData :=
  innerPair272Data

set_option maxRecDepth 1000000 in
private theorem leaf5348LocalValidity :
    LeafFacts leaf5348Box leaf5348Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5348Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356887552) }) = true
      norm_num [leaf5348Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5348CertificateValid :
    WideCertificateValid leaf5348Box leaf5348Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk162ValidityFacts chi304ValidityFacts
    leaf5348LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5348CoverageChecked :
    coverageCheck (innerAD leaf5348Box) leaf5348InnerLog = true := by
  rfl'

private theorem leaf5348InnerLogValid :
    leaf5348InnerLog.Valid 8 (innerAD leaf5348Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint77PositiveFacts.valid leaf5348CoverageChecked

private noncomputable def leaf5348InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629529/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5348InputLogOnePlusV_eq :
    leaf5348InputLogOnePlusV = outerEnclosure 24
      (leaf5348Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5348RoundedFacts : LeafRoundedFacts 8
    leaf5348Certificate.logOnePlusV leaf5348InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5348InputLogOnePlusV_eq }

private noncomputable def leaf5348Inputs : Inputs :=
  inputsOfCaches globalInput sk162RoundedInputs
    chi304InputQChi innerPair272Input
    leaf5348InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5348LowerChecked :
    lowerCheck 24 leaf5348Box leaf5348Inputs = true := by
  rfl'

private theorem leaf5348CoversExact : CoversExact 8
    leaf5348Box leaf5348Certificate leaf5348InnerLog leaf5348Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk162RoundedFacts chi304RoundedFacts
    innerPair272RoundedFacts leaf5348RoundedFacts (by rfl)

private theorem leaf5348FlatSound : Sound leaf5348Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5348CertificateValid
    leaf5348InnerLogValid leaf5348CoversExact leaf5348LowerChecked

private noncomputable def leaf5349Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (11/32), chiHi := (89/256) }

private noncomputable def leaf5349Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871323/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357072640) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1205788391/1073741824) }, upper := { exponent := 1, mantissa := (18605/16384) } }, logOuter := sk163LogOuterCertificate, logK := sk163LogKCertificate, logChi := chi297LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715795199/68714145280) } }, logDArg := sk163LogDArgCertificate }

private noncomputable def leaf5349InnerLog : WideLogData :=
  innerPair622Data

set_option maxRecDepth 1000000 in
private theorem leaf5349LocalValidity :
    LeafFacts leaf5349Box leaf5349Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5349Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357072640) }) = true
      norm_num [leaf5349Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5349CertificateValid :
    WideCertificateValid leaf5349Box leaf5349Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk163ValidityFacts chi297ValidityFacts
    leaf5349LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5349CoverageChecked :
    coverageCheck (innerAD leaf5349Box) leaf5349InnerLog = true := by
  rfl'

private theorem leaf5349InnerLogValid :
    leaf5349InnerLog.Valid 8 (innerAD leaf5349Box) :=
  wideLogDataValid_of_cachedCheck endpoint347PositiveFacts
    endpoint295PositiveFacts.valid leaf5349CoverageChecked

private noncomputable def leaf5349InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907371/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5349InputLogOnePlusV_eq :
    leaf5349InputLogOnePlusV = outerEnclosure 24
      (leaf5349Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5349RoundedFacts : LeafRoundedFacts 8
    leaf5349Certificate.logOnePlusV leaf5349InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5349InputLogOnePlusV_eq }

private noncomputable def leaf5349Inputs : Inputs :=
  inputsOfCaches globalInput sk163RoundedInputs
    chi297InputQChi innerPair622Input
    leaf5349InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5349LowerChecked :
    lowerCheck 24 leaf5349Box leaf5349Inputs = true := by
  rfl'

private theorem leaf5349CoversExact : CoversExact 8
    leaf5349Box leaf5349Certificate leaf5349InnerLog leaf5349Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk163RoundedFacts chi297RoundedFacts
    innerPair622RoundedFacts leaf5349RoundedFacts (by rfl)

private theorem leaf5349FlatSound : Sound leaf5349Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5349CertificateValid
    leaf5349InnerLogValid leaf5349CoversExact leaf5349LowerChecked

private noncomputable def leaf5350Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (89/256), chiHi := (45/128) }

private noncomputable def leaf5350Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871325/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357042688) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1213390101/1073741824) }, upper := { exponent := 1, mantissa := (9361/8192) } }, logOuter := sk163LogOuterCertificate, logK := sk163LogKCertificate, logChi := chi298LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715765247/68714085376) } }, logDArg := sk163LogDArgCertificate }

private noncomputable def leaf5350InnerLog : WideLogData :=
  innerPair271Data

set_option maxRecDepth 1000000 in
private theorem leaf5350LocalValidity :
    LeafFacts leaf5350Box leaf5350Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5350Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357042688) }) = true
      norm_num [leaf5350Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5350CertificateValid :
    WideCertificateValid leaf5350Box leaf5350Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk163ValidityFacts chi298ValidityFacts
    leaf5350LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5350CoverageChecked :
    coverageCheck (innerAD leaf5350Box) leaf5350InnerLog = true := by
  rfl'

private theorem leaf5350InnerLogValid :
    leaf5350InnerLog.Valid 8 (innerAD leaf5350Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint298PositiveFacts.valid leaf5350CoverageChecked

private noncomputable def leaf5350InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629491/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5350InputLogOnePlusV_eq :
    leaf5350InputLogOnePlusV = outerEnclosure 24
      (leaf5350Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5350RoundedFacts : LeafRoundedFacts 8
    leaf5350Certificate.logOnePlusV leaf5350InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5350InputLogOnePlusV_eq }

private noncomputable def leaf5350Inputs : Inputs :=
  inputsOfCaches globalInput sk163RoundedInputs
    chi298InputQChi innerPair271Input
    leaf5350InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5350LowerChecked :
    lowerCheck 24 leaf5350Box leaf5350Inputs = true := by
  rfl'

private theorem leaf5350CoversExact : CoversExact 8
    leaf5350Box leaf5350Certificate leaf5350InnerLog leaf5350Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk163RoundedFacts chi298RoundedFacts
    innerPair271RoundedFacts leaf5350RoundedFacts (by rfl)

private theorem leaf5350FlatSound : Sound leaf5350Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5350CertificateValid
    leaf5350InnerLogValid leaf5350CoversExact leaf5350LowerChecked

private noncomputable def leaf5351Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (11/32), chiHi := (89/256) }

private noncomputable def leaf5351Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871325/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357049856) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1211555205/1073741824) }, upper := { exponent := 1, mantissa := (9347/8192) } }, logOuter := sk164LogOuterCertificate, logK := sk164LogKCertificate, logChi := chi297LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715772415/68714099712) } }, logDArg := sk164LogDArgCertificate }

private noncomputable def leaf5351InnerLog : WideLogData :=
  innerPair271Data

set_option maxRecDepth 1000000 in
private theorem leaf5351LocalValidity :
    LeafFacts leaf5351Box leaf5351Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5351Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357049856) }) = true
      norm_num [leaf5351Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5351CertificateValid :
    WideCertificateValid leaf5351Box leaf5351Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk164ValidityFacts chi297ValidityFacts
    leaf5351LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5351CoverageChecked :
    coverageCheck (innerAD leaf5351Box) leaf5351InnerLog = true := by
  rfl'

private theorem leaf5351InnerLogValid :
    leaf5351InnerLog.Valid 8 (innerAD leaf5351Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint298PositiveFacts.valid leaf5351CoverageChecked

private noncomputable def leaf5351InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629489/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5351InputLogOnePlusV_eq :
    leaf5351InputLogOnePlusV = outerEnclosure 24
      (leaf5351Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5351RoundedFacts : LeafRoundedFacts 8
    leaf5351Certificate.logOnePlusV leaf5351InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5351InputLogOnePlusV_eq }

private noncomputable def leaf5351Inputs : Inputs :=
  inputsOfCaches globalInput sk164RoundedInputs
    chi297InputQChi innerPair271Input
    leaf5351InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5351LowerChecked :
    lowerCheck 24 leaf5351Box leaf5351Inputs = true := by
  rfl'

private theorem leaf5351CoversExact : CoversExact 8
    leaf5351Box leaf5351Certificate leaf5351InnerLog leaf5351Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk164RoundedFacts chi297RoundedFacts
    innerPair271RoundedFacts leaf5351RoundedFacts (by rfl)

private theorem leaf5351FlatSound : Sound leaf5351Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5351CertificateValid
    leaf5351InnerLogValid leaf5351CoversExact leaf5351LowerChecked

private noncomputable def leaf5352Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (89/256), chiHi := (45/128) }

private noncomputable def leaf5352Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871327/536870912) }, vSqrt := { lower := (8191/8192), upper := (4908388937/4908145664) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1219222447/1073741824) }, upper := { exponent := 1, mantissa := (4703/4096) } }, logOuter := sk164LogOuterCertificate, logK := sk164LogKCertificate, logChi := chi298LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (9816534601/9816291328) } }, logDArg := sk164LogDArgCertificate }

private noncomputable def leaf5352InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf5352LocalValidity :
    LeafFacts leaf5352Box leaf5352Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5352Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4908388937/4908145664) }) = true
      norm_num [leaf5352Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5352CertificateValid :
    WideCertificateValid leaf5352Box leaf5352Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk164ValidityFacts chi298ValidityFacts
    leaf5352LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5352CoverageChecked :
    coverageCheck (innerAD leaf5352Box) leaf5352InnerLog = true := by
  rfl'

private theorem leaf5352InnerLogValid :
    leaf5352InnerLog.Valid 8 (innerAD leaf5352Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf5352CoverageChecked

private noncomputable def leaf5352InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629497/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5352InputLogOnePlusV_eq :
    leaf5352InputLogOnePlusV = outerEnclosure 24
      (leaf5352Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5352RoundedFacts : LeafRoundedFacts 8
    leaf5352Certificate.logOnePlusV leaf5352InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5352InputLogOnePlusV_eq }

private noncomputable def leaf5352Inputs : Inputs :=
  inputsOfCaches globalInput sk164RoundedInputs
    chi298InputQChi innerPair264Input
    leaf5352InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5352LowerChecked :
    lowerCheck 24 leaf5352Box leaf5352Inputs = true := by
  rfl'

private theorem leaf5352CoversExact : CoversExact 8
    leaf5352Box leaf5352Certificate leaf5352InnerLog leaf5352Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk164RoundedFacts chi298RoundedFacts
    innerPair264RoundedFacts leaf5352RoundedFacts (by rfl)

private theorem leaf5352FlatSound : Sound leaf5352Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5352CertificateValid
    leaf5352InnerLogValid leaf5352CoversExact leaf5352LowerChecked

private noncomputable def leaf5353Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (45/128), chiHi := (91/256) }

private noncomputable def leaf5353Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871327/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357012736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1220991811/1073741824) }, upper := { exponent := 1, mantissa := (18839/16384) } }, logOuter := sk163LogOuterCertificate, logK := sk163LogKCertificate, logChi := chi299LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715735295/68714025472) } }, logDArg := sk163LogDArgCertificate }

private noncomputable def leaf5353InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf5353LocalValidity :
    LeafFacts leaf5353Box leaf5353Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5353Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357012736) }) = true
      norm_num [leaf5353Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5353CertificateValid :
    WideCertificateValid leaf5353Box leaf5353Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk163ValidityFacts chi299ValidityFacts
    leaf5353LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5353CoverageChecked :
    coverageCheck (innerAD leaf5353Box) leaf5353InnerLog = true := by
  rfl'

private theorem leaf5353InnerLogValid :
    leaf5353InnerLog.Valid 8 (innerAD leaf5353Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf5353CoverageChecked

private noncomputable def leaf5353InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814749/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5353InputLogOnePlusV_eq :
    leaf5353InputLogOnePlusV = outerEnclosure 24
      (leaf5353Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5353RoundedFacts : LeafRoundedFacts 8
    leaf5353Certificate.logOnePlusV leaf5353InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5353InputLogOnePlusV_eq }

private noncomputable def leaf5353Inputs : Inputs :=
  inputsOfCaches globalInput sk163RoundedInputs
    chi299InputQChi innerPair264Input
    leaf5353InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5353LowerChecked :
    lowerCheck 24 leaf5353Box leaf5353Inputs = true := by
  rfl'

private theorem leaf5353CoversExact : CoversExact 8
    leaf5353Box leaf5353Certificate leaf5353InnerLog leaf5353Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk163RoundedFacts chi299RoundedFacts
    innerPair264RoundedFacts leaf5353RoundedFacts (by rfl)

private theorem leaf5353FlatSound : Sound leaf5353Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5353CertificateValid
    leaf5353InnerLogValid leaf5353CoversExact leaf5353LowerChecked

private noncomputable def leaf5354Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (91/256), chiHi := (23/64) }

private noncomputable def leaf5354Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871329/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356982784) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1228593521/1073741824) }, upper := { exponent := 1, mantissa := (4739/4096) } }, logOuter := sk163LogOuterCertificate, logK := sk163LogKCertificate, logChi := chi300LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715705343/68713965568) } }, logDArg := sk163LogDArgCertificate }

private noncomputable def leaf5354InnerLog : WideLogData :=
  innerPair563Data

set_option maxRecDepth 1000000 in
private theorem leaf5354LocalValidity :
    LeafFacts leaf5354Box leaf5354Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5354Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356982784) }) = true
      norm_num [leaf5354Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5354CertificateValid :
    WideCertificateValid leaf5354Box leaf5354Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk163ValidityFacts chi300ValidityFacts
    leaf5354LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5354CoverageChecked :
    coverageCheck (innerAD leaf5354Box) leaf5354InnerLog = true := by
  rfl'

private theorem leaf5354InnerLogValid :
    leaf5354InnerLog.Valid 8 (innerAD leaf5354Box) :=
  wideLogDataValid_of_cachedCheck endpoint295PositiveFacts
    endpoint296PositiveFacts.valid leaf5354CoverageChecked

private noncomputable def leaf5354InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814753/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5354InputLogOnePlusV_eq :
    leaf5354InputLogOnePlusV = outerEnclosure 24
      (leaf5354Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5354RoundedFacts : LeafRoundedFacts 8
    leaf5354Certificate.logOnePlusV leaf5354InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5354InputLogOnePlusV_eq }

private noncomputable def leaf5354Inputs : Inputs :=
  inputsOfCaches globalInput sk163RoundedInputs
    chi300InputQChi innerPair563Input
    leaf5354InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5354LowerChecked :
    lowerCheck 24 leaf5354Box leaf5354Inputs = true := by
  rfl'

private theorem leaf5354CoversExact : CoversExact 8
    leaf5354Box leaf5354Certificate leaf5354InnerLog leaf5354Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk163RoundedFacts chi300RoundedFacts
    innerPair563RoundedFacts leaf5354RoundedFacts (by rfl)

private theorem leaf5354FlatSound : Sound leaf5354Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5354CertificateValid
    leaf5354InnerLogValid leaf5354CoversExact leaf5354LowerChecked

private noncomputable def leaf5355Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (45/128), chiHi := (91/256) }

private noncomputable def leaf5355Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871329/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356989440) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1226889689/1073741824) }, upper := { exponent := 1, mantissa := (9465/8192) } }, logOuter := sk164LogOuterCertificate, logK := sk164LogKCertificate, logChi := chi299LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715711999/68713978880) } }, logDArg := sk164LogDArgCertificate }

private noncomputable def leaf5355InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf5355LocalValidity :
    LeafFacts leaf5355Box leaf5355Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5355Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356989440) }) = true
      norm_num [leaf5355Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5355CertificateValid :
    WideCertificateValid leaf5355Box leaf5355Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk164ValidityFacts chi299ValidityFacts
    leaf5355LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5355CoverageChecked :
    coverageCheck (innerAD leaf5355Box) leaf5355InnerLog = true := by
  rfl'

private theorem leaf5355InnerLogValid :
    leaf5355InnerLog.Valid 8 (innerAD leaf5355Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf5355CoverageChecked

private noncomputable def leaf5355InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (181711/262144) }

set_option maxRecDepth 1000000 in
private theorem leaf5355InputLogOnePlusV_eq :
    leaf5355InputLogOnePlusV = outerEnclosure 24
      (leaf5355Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5355RoundedFacts : LeafRoundedFacts 8
    leaf5355Certificate.logOnePlusV leaf5355InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5355InputLogOnePlusV_eq }

private noncomputable def leaf5355Inputs : Inputs :=
  inputsOfCaches globalInput sk164RoundedInputs
    chi299InputQChi innerPair264Input
    leaf5355InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5355LowerChecked :
    lowerCheck 24 leaf5355Box leaf5355Inputs = true := by
  rfl'

private theorem leaf5355CoversExact : CoversExact 8
    leaf5355Box leaf5355Certificate leaf5355InnerLog leaf5355Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk164RoundedFacts chi299RoundedFacts
    innerPair264RoundedFacts leaf5355RoundedFacts (by rfl)

private theorem leaf5355FlatSound : Sound leaf5355Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5355CertificateValid
    leaf5355InnerLogValid leaf5355CoversExact leaf5355LowerChecked

private noncomputable def leaf5356Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (91/256), chiHi := (23/64) }

private noncomputable def leaf5356Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871331/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356959232) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1234556931/1073741824) }, upper := { exponent := 1, mantissa := (2381/2048) } }, logOuter := sk164LogOuterCertificate, logK := sk164LogKCertificate, logChi := chi300LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715681791/68713918464) } }, logDArg := sk164LogDArgCertificate }

private noncomputable def leaf5356InnerLog : WideLogData :=
  innerPair571Data

set_option maxRecDepth 1000000 in
private theorem leaf5356LocalValidity :
    LeafFacts leaf5356Box leaf5356Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5356Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356959232) }) = true
      norm_num [leaf5356Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5356CertificateValid :
    WideCertificateValid leaf5356Box leaf5356Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk164ValidityFacts chi300ValidityFacts
    leaf5356LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5356CoverageChecked :
    coverageCheck (innerAD leaf5356Box) leaf5356InnerLog = true := by
  rfl'

private theorem leaf5356InnerLogValid :
    leaf5356InnerLog.Valid 8 (innerAD leaf5356Box) :=
  wideLogDataValid_of_cachedCheck endpoint298PositiveFacts
    endpoint296PositiveFacts.valid leaf5356CoverageChecked

private noncomputable def leaf5356InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629511/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5356InputLogOnePlusV_eq :
    leaf5356InputLogOnePlusV = outerEnclosure 24
      (leaf5356Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5356RoundedFacts : LeafRoundedFacts 8
    leaf5356Certificate.logOnePlusV leaf5356InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5356InputLogOnePlusV_eq }

private noncomputable def leaf5356Inputs : Inputs :=
  inputsOfCaches globalInput sk164RoundedInputs
    chi300InputQChi innerPair571Input
    leaf5356InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5356LowerChecked :
    lowerCheck 24 leaf5356Box leaf5356Inputs = true := by
  rfl'

private theorem leaf5356CoversExact : CoversExact 8
    leaf5356Box leaf5356Certificate leaf5356InnerLog leaf5356Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk164RoundedFacts chi300RoundedFacts
    innerPair571RoundedFacts leaf5356RoundedFacts (by rfl)

private theorem leaf5356FlatSound : Sound leaf5356Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5356CertificateValid
    leaf5356InnerLogValid leaf5356CoversExact leaf5356LowerChecked

private noncomputable def leaf5357Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (11/32), chiHi := (89/256) }

private noncomputable def leaf5357Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871327/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357027072) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1217322019/1073741824) }, upper := { exponent := 1, mantissa := (18783/16384) } }, logOuter := sk165LogOuterCertificate, logK := sk165LogKCertificate, logChi := chi297LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715749631/68714054144) } }, logDArg := sk165LogDArgCertificate }

private noncomputable def leaf5357InnerLog : WideLogData :=
  innerPair561Data

set_option maxRecDepth 1000000 in
private theorem leaf5357LocalValidity :
    LeafFacts leaf5357Box leaf5357Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5357Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357027072) }) = true
      norm_num [leaf5357Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5357CertificateValid :
    WideCertificateValid leaf5357Box leaf5357Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk165ValidityFacts chi297ValidityFacts
    leaf5357LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5357CoverageChecked :
    coverageCheck (innerAD leaf5357Box) leaf5357InnerLog = true := by
  rfl'

private theorem leaf5357InnerLogValid :
    leaf5357InnerLog.Valid 8 (innerAD leaf5357Box) :=
  wideLogDataValid_of_cachedCheck endpoint292PositiveFacts
    endpoint298PositiveFacts.valid leaf5357CoverageChecked

private noncomputable def leaf5357InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629495/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5357InputLogOnePlusV_eq :
    leaf5357InputLogOnePlusV = outerEnclosure 24
      (leaf5357Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5357RoundedFacts : LeafRoundedFacts 8
    leaf5357Certificate.logOnePlusV leaf5357InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5357InputLogOnePlusV_eq }

private noncomputable def leaf5357Inputs : Inputs :=
  inputsOfCaches globalInput sk165RoundedInputs
    chi297InputQChi innerPair561Input
    leaf5357InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5357LowerChecked :
    lowerCheck 24 leaf5357Box leaf5357Inputs = true := by
  rfl'

private theorem leaf5357CoversExact : CoversExact 8
    leaf5357Box leaf5357Certificate leaf5357InnerLog leaf5357Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk165RoundedFacts chi297RoundedFacts
    innerPair561RoundedFacts leaf5357RoundedFacts (by rfl)

private theorem leaf5357FlatSound : Sound leaf5357Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5357CertificateValid
    leaf5357InnerLogValid leaf5357CoversExact leaf5357LowerChecked

private noncomputable def leaf5358Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (89/256), chiHi := (45/128) }

private noncomputable def leaf5358Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871329/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356996608) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1225054793/1073741824) }, upper := { exponent := 1, mantissa := (9451/8192) } }, logOuter := sk165LogOuterCertificate, logK := sk165LogKCertificate, logChi := chi298LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715719167/68713993216) } }, logDArg := sk165LogDArgCertificate }

private noncomputable def leaf5358InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf5358LocalValidity :
    LeafFacts leaf5358Box leaf5358Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5358Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356996608) }) = true
      norm_num [leaf5358Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5358CertificateValid :
    WideCertificateValid leaf5358Box leaf5358Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk165ValidityFacts chi298ValidityFacts
    leaf5358LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5358CoverageChecked :
    coverageCheck (innerAD leaf5358Box) leaf5358InnerLog = true := by
  rfl'

private theorem leaf5358InnerLogValid :
    leaf5358InnerLog.Valid 8 (innerAD leaf5358Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf5358CoverageChecked

private noncomputable def leaf5358InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814751/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5358InputLogOnePlusV_eq :
    leaf5358InputLogOnePlusV = outerEnclosure 24
      (leaf5358Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5358RoundedFacts : LeafRoundedFacts 8
    leaf5358Certificate.logOnePlusV leaf5358InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5358InputLogOnePlusV_eq }

private noncomputable def leaf5358Inputs : Inputs :=
  inputsOfCaches globalInput sk165RoundedInputs
    chi298InputQChi innerPair264Input
    leaf5358InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5358LowerChecked :
    lowerCheck 24 leaf5358Box leaf5358Inputs = true := by
  rfl'

private theorem leaf5358CoversExact : CoversExact 8
    leaf5358Box leaf5358Certificate leaf5358InnerLog leaf5358Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk165RoundedFacts chi298RoundedFacts
    innerPair264RoundedFacts leaf5358RoundedFacts (by rfl)

private theorem leaf5358FlatSound : Sound leaf5358Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5358CertificateValid
    leaf5358InnerLogValid leaf5358CoversExact leaf5358LowerChecked

private noncomputable def leaf5359Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (11/32), chiHi := (89/256) }

private noncomputable def leaf5359Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871329/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357004288) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1223088833/1073741824) }, upper := { exponent := 1, mantissa := (2359/2048) } }, logOuter := sk166LogOuterCertificate, logK := sk166LogKCertificate, logChi := chi297LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715726847/68714008576) } }, logDArg := sk166LogDArgCertificate }

private noncomputable def leaf5359InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf5359LocalValidity :
    LeafFacts leaf5359Box leaf5359Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5359Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357004288) }) = true
      norm_num [leaf5359Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5359CertificateValid :
    WideCertificateValid leaf5359Box leaf5359Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk166ValidityFacts chi297ValidityFacts
    leaf5359LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5359CoverageChecked :
    coverageCheck (innerAD leaf5359Box) leaf5359InnerLog = true := by
  rfl'

private theorem leaf5359InnerLogValid :
    leaf5359InnerLog.Valid 8 (innerAD leaf5359Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf5359CoverageChecked

private noncomputable def leaf5359InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907375/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5359InputLogOnePlusV_eq :
    leaf5359InputLogOnePlusV = outerEnclosure 24
      (leaf5359Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5359RoundedFacts : LeafRoundedFacts 8
    leaf5359Certificate.logOnePlusV leaf5359InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5359InputLogOnePlusV_eq }

private noncomputable def leaf5359Inputs : Inputs :=
  inputsOfCaches globalInput sk166RoundedInputs
    chi297InputQChi innerPair264Input
    leaf5359InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5359LowerChecked :
    lowerCheck 24 leaf5359Box leaf5359Inputs = true := by
  rfl'

private theorem leaf5359CoversExact : CoversExact 8
    leaf5359Box leaf5359Certificate leaf5359InnerLog leaf5359Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk166RoundedFacts chi297RoundedFacts
    innerPair264RoundedFacts leaf5359RoundedFacts (by rfl)

private theorem leaf5359FlatSound : Sound leaf5359Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5359CertificateValid
    leaf5359InnerLogValid leaf5359CoversExact leaf5359LowerChecked

private noncomputable def leaf5360Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (89/256), chiHi := (45/128) }

private noncomputable def leaf5360Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871331/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356973568) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1230887139/1073741824) }, upper := { exponent := 1, mantissa := (1187/1024) } }, logOuter := sk166LogOuterCertificate, logK := sk166LogKCertificate, logChi := chi298LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715696127/68713947136) } }, logDArg := sk166LogDArgCertificate }

private noncomputable def leaf5360InnerLog : WideLogData :=
  innerPair563Data

set_option maxRecDepth 1000000 in
private theorem leaf5360LocalValidity :
    LeafFacts leaf5360Box leaf5360Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5360Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356973568) }) = true
      norm_num [leaf5360Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5360CertificateValid :
    WideCertificateValid leaf5360Box leaf5360Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk166ValidityFacts chi298ValidityFacts
    leaf5360LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5360CoverageChecked :
    coverageCheck (innerAD leaf5360Box) leaf5360InnerLog = true := by
  rfl'

private theorem leaf5360InnerLogValid :
    leaf5360InnerLog.Valid 8 (innerAD leaf5360Box) :=
  wideLogDataValid_of_cachedCheck endpoint295PositiveFacts
    endpoint296PositiveFacts.valid leaf5360CoverageChecked

private noncomputable def leaf5360InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907377/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5360InputLogOnePlusV_eq :
    leaf5360InputLogOnePlusV = outerEnclosure 24
      (leaf5360Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5360RoundedFacts : LeafRoundedFacts 8
    leaf5360Certificate.logOnePlusV leaf5360InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5360InputLogOnePlusV_eq }

private noncomputable def leaf5360Inputs : Inputs :=
  inputsOfCaches globalInput sk166RoundedInputs
    chi298InputQChi innerPair563Input
    leaf5360InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5360LowerChecked :
    lowerCheck 24 leaf5360Box leaf5360Inputs = true := by
  rfl'

private theorem leaf5360CoversExact : CoversExact 8
    leaf5360Box leaf5360Certificate leaf5360InnerLog leaf5360Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk166RoundedFacts chi298RoundedFacts
    innerPair563RoundedFacts leaf5360RoundedFacts (by rfl)

private theorem leaf5360FlatSound : Sound leaf5360Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5360CertificateValid
    leaf5360InnerLogValid leaf5360CoversExact leaf5360LowerChecked

private noncomputable def leaf5361Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (45/128), chiHi := (91/256) }

private noncomputable def leaf5361Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871331/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356966144) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1232787567/1073741824) }, upper := { exponent := 1, mantissa := (19021/16384) } }, logOuter := sk165LogOuterCertificate, logK := sk165LogKCertificate, logChi := chi299LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715688703/68713932288) } }, logDArg := sk165LogDArgCertificate }

private noncomputable def leaf5361InnerLog : WideLogData :=
  innerPair563Data

set_option maxRecDepth 1000000 in
private theorem leaf5361LocalValidity :
    LeafFacts leaf5361Box leaf5361Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5361Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356966144) }) = true
      norm_num [leaf5361Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5361CertificateValid :
    WideCertificateValid leaf5361Box leaf5361Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk165ValidityFacts chi299ValidityFacts
    leaf5361LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5361CoverageChecked :
    coverageCheck (innerAD leaf5361Box) leaf5361InnerLog = true := by
  rfl'

private theorem leaf5361InnerLogValid :
    leaf5361InnerLog.Valid 8 (innerAD leaf5361Box) :=
  wideLogDataValid_of_cachedCheck endpoint295PositiveFacts
    endpoint296PositiveFacts.valid leaf5361CoverageChecked

private noncomputable def leaf5361InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814755/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5361InputLogOnePlusV_eq :
    leaf5361InputLogOnePlusV = outerEnclosure 24
      (leaf5361Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5361RoundedFacts : LeafRoundedFacts 8
    leaf5361Certificate.logOnePlusV leaf5361InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5361InputLogOnePlusV_eq }

private noncomputable def leaf5361Inputs : Inputs :=
  inputsOfCaches globalInput sk165RoundedInputs
    chi299InputQChi innerPair563Input
    leaf5361InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5361LowerChecked :
    lowerCheck 24 leaf5361Box leaf5361Inputs = true := by
  rfl'

private theorem leaf5361CoversExact : CoversExact 8
    leaf5361Box leaf5361Certificate leaf5361InnerLog leaf5361Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk165RoundedFacts chi299RoundedFacts
    innerPair563RoundedFacts leaf5361RoundedFacts (by rfl)

private theorem leaf5361FlatSound : Sound leaf5361Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5361CertificateValid
    leaf5361InnerLogValid leaf5361CoversExact leaf5361LowerChecked

private noncomputable def leaf5362Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (91/256), chiHi := (23/64) }

private noncomputable def leaf5362Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871333/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356935680) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1240520341/1073741824) }, upper := { exponent := 1, mantissa := (4785/4096) } }, logOuter := sk165LogOuterCertificate, logK := sk165LogKCertificate, logChi := chi300LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715658239/68713871360) } }, logDArg := sk165LogDArgCertificate }

private noncomputable def leaf5362InnerLog : WideLogData :=
  innerPair572Data

set_option maxRecDepth 1000000 in
private theorem leaf5362LocalValidity :
    LeafFacts leaf5362Box leaf5362Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5362Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356935680) }) = true
      norm_num [leaf5362Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5362CertificateValid :
    WideCertificateValid leaf5362Box leaf5362Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk165ValidityFacts chi300ValidityFacts
    leaf5362LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5362CoverageChecked :
    coverageCheck (innerAD leaf5362Box) leaf5362InnerLog = true := by
  rfl'

private theorem leaf5362InnerLogValid :
    leaf5362InnerLog.Valid 8 (innerAD leaf5362Box) :=
  wideLogDataValid_of_cachedCheck endpoint298PositiveFacts
    endpoint297PositiveFacts.valid leaf5362CoverageChecked

private noncomputable def leaf5362InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629517/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5362InputLogOnePlusV_eq :
    leaf5362InputLogOnePlusV = outerEnclosure 24
      (leaf5362Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5362RoundedFacts : LeafRoundedFacts 8
    leaf5362Certificate.logOnePlusV leaf5362InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5362InputLogOnePlusV_eq }

private noncomputable def leaf5362Inputs : Inputs :=
  inputsOfCaches globalInput sk165RoundedInputs
    chi300InputQChi innerPair572Input
    leaf5362InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5362LowerChecked :
    lowerCheck 24 leaf5362Box leaf5362Inputs = true := by
  rfl'

private theorem leaf5362CoversExact : CoversExact 8
    leaf5362Box leaf5362Certificate leaf5362InnerLog leaf5362Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk165RoundedFacts chi300RoundedFacts
    innerPair572RoundedFacts leaf5362RoundedFacts (by rfl)

private theorem leaf5362FlatSound : Sound leaf5362Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5362CertificateValid
    leaf5362InnerLogValid leaf5362CoversExact leaf5362LowerChecked

private noncomputable def leaf5363Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (45/128), chiHi := (91/256) }

private noncomputable def leaf5363Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871333/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356942848) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1238685445/1073741824) }, upper := { exponent := 1, mantissa := (2389/2048) } }, logOuter := sk166LogOuterCertificate, logK := sk166LogKCertificate, logChi := chi299LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715665407/68713885696) } }, logDArg := sk166LogDArgCertificate }

private noncomputable def leaf5363InnerLog : WideLogData :=
  innerPair572Data

set_option maxRecDepth 1000000 in
private theorem leaf5363LocalValidity :
    LeafFacts leaf5363Box leaf5363Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5363Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356942848) }) = true
      norm_num [leaf5363Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5363CertificateValid :
    WideCertificateValid leaf5363Box leaf5363Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk166ValidityFacts chi299ValidityFacts
    leaf5363LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5363CoverageChecked :
    coverageCheck (innerAD leaf5363Box) leaf5363InnerLog = true := by
  rfl'

private theorem leaf5363InnerLogValid :
    leaf5363InnerLog.Valid 8 (innerAD leaf5363Box) :=
  wideLogDataValid_of_cachedCheck endpoint298PositiveFacts
    endpoint297PositiveFacts.valid leaf5363CoverageChecked

private noncomputable def leaf5363InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629515/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5363InputLogOnePlusV_eq :
    leaf5363InputLogOnePlusV = outerEnclosure 24
      (leaf5363Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5363RoundedFacts : LeafRoundedFacts 8
    leaf5363Certificate.logOnePlusV leaf5363InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5363InputLogOnePlusV_eq }

private noncomputable def leaf5363Inputs : Inputs :=
  inputsOfCaches globalInput sk166RoundedInputs
    chi299InputQChi innerPair572Input
    leaf5363InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5363LowerChecked :
    lowerCheck 24 leaf5363Box leaf5363Inputs = true := by
  rfl'

private theorem leaf5363CoversExact : CoversExact 8
    leaf5363Box leaf5363Certificate leaf5363InnerLog leaf5363Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk166RoundedFacts chi299RoundedFacts
    innerPair572RoundedFacts leaf5363RoundedFacts (by rfl)

private theorem leaf5363FlatSound : Sound leaf5363Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5363CertificateValid
    leaf5363InnerLogValid leaf5363CoversExact leaf5363LowerChecked

private noncomputable def leaf5364Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (91/256), chiHi := (23/64) }

private noncomputable def leaf5364Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871335/536870912) }, vSqrt := { lower := (8191/8192), upper := (158335127/158326784) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1246483751/1073741824) }, upper := { exponent := 1, mantissa := (601/512) } }, logOuter := sk166LogOuterCertificate, logK := sk166LogKCertificate, logChi := chi300LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (316661911/316653568) } }, logDArg := sk166LogDArgCertificate }

private noncomputable def leaf5364InnerLog : WideLogData :=
  innerPair277Data

set_option maxRecDepth 1000000 in
private theorem leaf5364LocalValidity :
    LeafFacts leaf5364Box leaf5364Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5364Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (158335127/158326784) }) = true
      norm_num [leaf5364Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5364CertificateValid :
    WideCertificateValid leaf5364Box leaf5364Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk166ValidityFacts chi300ValidityFacts
    leaf5364LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5364CoverageChecked :
    coverageCheck (innerAD leaf5364Box) leaf5364InnerLog = true := by
  rfl'

private theorem leaf5364InnerLogValid :
    leaf5364InnerLog.Valid 8 (innerAD leaf5364Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint299PositiveFacts.valid leaf5364CoverageChecked

private noncomputable def leaf5364InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629523/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5364InputLogOnePlusV_eq :
    leaf5364InputLogOnePlusV = outerEnclosure 24
      (leaf5364Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5364RoundedFacts : LeafRoundedFacts 8
    leaf5364Certificate.logOnePlusV leaf5364InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5364InputLogOnePlusV_eq }

private noncomputable def leaf5364Inputs : Inputs :=
  inputsOfCaches globalInput sk166RoundedInputs
    chi300InputQChi innerPair277Input
    leaf5364InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5364LowerChecked :
    lowerCheck 24 leaf5364Box leaf5364Inputs = true := by
  rfl'

private theorem leaf5364CoversExact : CoversExact 8
    leaf5364Box leaf5364Certificate leaf5364InnerLog leaf5364Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk166RoundedFacts chi300RoundedFacts
    innerPair277RoundedFacts leaf5364RoundedFacts (by rfl)

private theorem leaf5364FlatSound : Sound leaf5364Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5364CertificateValid
    leaf5364InnerLogValid leaf5364CoversExact leaf5364LowerChecked

private noncomputable def leaf5365Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (23/64), chiHi := (93/256) }

private noncomputable def leaf5365Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871331/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356952832) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1236195231/1073741824) }, upper := { exponent := 1, mantissa := (19073/16384) } }, logOuter := sk163LogOuterCertificate, logK := sk163LogKCertificate, logChi := chi301LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715675391/68713905664) } }, logDArg := sk163LogDArgCertificate }

private noncomputable def leaf5365InnerLog : WideLogData :=
  innerPair572Data

set_option maxRecDepth 1000000 in
private theorem leaf5365LocalValidity :
    LeafFacts leaf5365Box leaf5365Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5365Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356952832) }) = true
      norm_num [leaf5365Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5365CertificateValid :
    WideCertificateValid leaf5365Box leaf5365Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk163ValidityFacts chi301ValidityFacts
    leaf5365LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5365CoverageChecked :
    coverageCheck (innerAD leaf5365Box) leaf5365InnerLog = true := by
  rfl'

private theorem leaf5365InnerLogValid :
    leaf5365InnerLog.Valid 8 (innerAD leaf5365Box) :=
  wideLogDataValid_of_cachedCheck endpoint298PositiveFacts
    endpoint297PositiveFacts.valid leaf5365CoverageChecked

private noncomputable def leaf5365InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629513/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5365InputLogOnePlusV_eq :
    leaf5365InputLogOnePlusV = outerEnclosure 24
      (leaf5365Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5365RoundedFacts : LeafRoundedFacts 8
    leaf5365Certificate.logOnePlusV leaf5365InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5365InputLogOnePlusV_eq }

private noncomputable def leaf5365Inputs : Inputs :=
  inputsOfCaches globalInput sk163RoundedInputs
    chi301InputQChi innerPair572Input
    leaf5365InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5365LowerChecked :
    lowerCheck 24 leaf5365Box leaf5365Inputs = true := by
  rfl'

private theorem leaf5365CoversExact : CoversExact 8
    leaf5365Box leaf5365Certificate leaf5365InnerLog leaf5365Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk163RoundedFacts chi301RoundedFacts
    innerPair572RoundedFacts leaf5365RoundedFacts (by rfl)

private theorem leaf5365FlatSound : Sound leaf5365Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5365CertificateValid
    leaf5365InnerLogValid leaf5365CoversExact leaf5365LowerChecked

private noncomputable def leaf5366Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (93/256), chiHi := (47/128) }

private noncomputable def leaf5366Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871333/536870912) }, vSqrt := { lower := (8191/8192), upper := (4908388937/4908131840) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1243796941/1073741824) }, upper := { exponent := 1, mantissa := (9595/8192) } }, logOuter := sk163LogOuterCertificate, logK := sk163LogKCertificate, logChi := chi302LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (9816520777/9816263680) } }, logDArg := sk163LogDArgCertificate }

private noncomputable def leaf5366InnerLog : WideLogData :=
  innerPair272Data

set_option maxRecDepth 1000000 in
private theorem leaf5366LocalValidity :
    LeafFacts leaf5366Box leaf5366Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5366Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4908388937/4908131840) }) = true
      norm_num [leaf5366Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5366CertificateValid :
    WideCertificateValid leaf5366Box leaf5366Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk163ValidityFacts chi302ValidityFacts
    leaf5366LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5366CoverageChecked :
    coverageCheck (innerAD leaf5366Box) leaf5366InnerLog = true := by
  rfl'

private theorem leaf5366InnerLogValid :
    leaf5366InnerLog.Valid 8 (innerAD leaf5366Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint77PositiveFacts.valid leaf5366CoverageChecked

private noncomputable def leaf5366InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726845/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf5366InputLogOnePlusV_eq :
    leaf5366InputLogOnePlusV = outerEnclosure 24
      (leaf5366Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5366RoundedFacts : LeafRoundedFacts 8
    leaf5366Certificate.logOnePlusV leaf5366InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5366InputLogOnePlusV_eq }

private noncomputable def leaf5366Inputs : Inputs :=
  inputsOfCaches globalInput sk163RoundedInputs
    chi302InputQChi innerPair272Input
    leaf5366InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5366LowerChecked :
    lowerCheck 24 leaf5366Box leaf5366Inputs = true := by
  rfl'

private theorem leaf5366CoversExact : CoversExact 8
    leaf5366Box leaf5366Certificate leaf5366InnerLog leaf5366Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk163RoundedFacts chi302RoundedFacts
    innerPair272RoundedFacts leaf5366RoundedFacts (by rfl)

private theorem leaf5366FlatSound : Sound leaf5366Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5366CertificateValid
    leaf5366InnerLogValid leaf5366CoversExact leaf5366LowerChecked

private noncomputable def leaf5367Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (23/64), chiHi := (93/256) }

private noncomputable def leaf5367Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871333/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356929024) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1242224173/1073741824) }, upper := { exponent := 1, mantissa := (9583/8192) } }, logOuter := sk164LogOuterCertificate, logK := sk164LogKCertificate, logChi := chi301LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715651583/68713858048) } }, logDArg := sk164LogDArgCertificate }

private noncomputable def leaf5367InnerLog : WideLogData :=
  innerPair276Data

set_option maxRecDepth 1000000 in
private theorem leaf5367LocalValidity :
    LeafFacts leaf5367Box leaf5367Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5367Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356929024) }) = true
      norm_num [leaf5367Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5367CertificateValid :
    WideCertificateValid leaf5367Box leaf5367Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk164ValidityFacts chi301ValidityFacts
    leaf5367LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5367CoverageChecked :
    coverageCheck (innerAD leaf5367Box) leaf5367InnerLog = true := by
  rfl'

private theorem leaf5367InnerLogValid :
    leaf5367InnerLog.Valid 8 (innerAD leaf5367Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint297PositiveFacts.valid leaf5367CoverageChecked

private noncomputable def leaf5367InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629519/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5367InputLogOnePlusV_eq :
    leaf5367InputLogOnePlusV = outerEnclosure 24
      (leaf5367Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5367RoundedFacts : LeafRoundedFacts 8
    leaf5367Certificate.logOnePlusV leaf5367InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5367InputLogOnePlusV_eq }

private noncomputable def leaf5367Inputs : Inputs :=
  inputsOfCaches globalInput sk164RoundedInputs
    chi301InputQChi innerPair276Input
    leaf5367InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5367LowerChecked :
    lowerCheck 24 leaf5367Box leaf5367Inputs = true := by
  rfl'

private theorem leaf5367CoversExact : CoversExact 8
    leaf5367Box leaf5367Certificate leaf5367InnerLog leaf5367Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk164RoundedFacts chi301RoundedFacts
    innerPair276RoundedFacts leaf5367RoundedFacts (by rfl)

private theorem leaf5367FlatSound : Sound leaf5367Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5367CertificateValid
    leaf5367InnerLogValid leaf5367CoversExact leaf5367LowerChecked

private noncomputable def leaf5368Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (93/256), chiHi := (47/128) }

private noncomputable def leaf5368Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871335/536870912) }, vSqrt := { lower := (8191/8192), upper := (2021101327/2020994048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1249891415/1073741824) }, upper := { exponent := 1, mantissa := (4821/4096) } }, logOuter := sk164LogOuterCertificate, logK := sk164LogKCertificate, logChi := chi302LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (4042095375/4041988096) } }, logDArg := sk164LogDArgCertificate }

private noncomputable def leaf5368InnerLog : WideLogData :=
  innerPair272Data

set_option maxRecDepth 1000000 in
private theorem leaf5368LocalValidity :
    LeafFacts leaf5368Box leaf5368Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5368Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (2021101327/2020994048) }) = true
      norm_num [leaf5368Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5368CertificateValid :
    WideCertificateValid leaf5368Box leaf5368Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk164ValidityFacts chi302ValidityFacts
    leaf5368LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5368CoverageChecked :
    coverageCheck (innerAD leaf5368Box) leaf5368InnerLog = true := by
  rfl'

private theorem leaf5368InnerLogValid :
    leaf5368InnerLog.Valid 8 (innerAD leaf5368Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint77PositiveFacts.valid leaf5368CoverageChecked

private noncomputable def leaf5368InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814763/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5368InputLogOnePlusV_eq :
    leaf5368InputLogOnePlusV = outerEnclosure 24
      (leaf5368Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5368RoundedFacts : LeafRoundedFacts 8
    leaf5368Certificate.logOnePlusV leaf5368InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5368InputLogOnePlusV_eq }

private noncomputable def leaf5368Inputs : Inputs :=
  inputsOfCaches globalInput sk164RoundedInputs
    chi302InputQChi innerPair272Input
    leaf5368InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5368LowerChecked :
    lowerCheck 24 leaf5368Box leaf5368Inputs = true := by
  rfl'

private theorem leaf5368CoversExact : CoversExact 8
    leaf5368Box leaf5368Certificate leaf5368InnerLog leaf5368Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk164RoundedFacts chi302RoundedFacts
    innerPair272RoundedFacts leaf5368RoundedFacts (by rfl)

private theorem leaf5368FlatSound : Sound leaf5368Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5368CertificateValid
    leaf5368InnerLogValid leaf5368CoversExact leaf5368LowerChecked

private noncomputable def leaf5369Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (47/128), chiHi := (95/256) }

private noncomputable def leaf5369Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871335/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356892928) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1251398651/1073741824) }, upper := { exponent := 1, mantissa := (19307/16384) } }, logOuter := sk163LogOuterCertificate, logK := sk163LogKCertificate, logChi := chi303LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715615487/68713785856) } }, logDArg := sk163LogDArgCertificate }

private noncomputable def leaf5369InnerLog : WideLogData :=
  innerPair272Data

set_option maxRecDepth 1000000 in
private theorem leaf5369LocalValidity :
    LeafFacts leaf5369Box leaf5369Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5369Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356892928) }) = true
      norm_num [leaf5369Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5369CertificateValid :
    WideCertificateValid leaf5369Box leaf5369Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk163ValidityFacts chi303ValidityFacts
    leaf5369LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5369CoverageChecked :
    coverageCheck (innerAD leaf5369Box) leaf5369InnerLog = true := by
  rfl'

private theorem leaf5369InnerLogValid :
    leaf5369InnerLog.Valid 8 (innerAD leaf5369Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint77PositiveFacts.valid leaf5369CoverageChecked

private noncomputable def leaf5369InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629527/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5369InputLogOnePlusV_eq :
    leaf5369InputLogOnePlusV = outerEnclosure 24
      (leaf5369Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5369RoundedFacts : LeafRoundedFacts 8
    leaf5369Certificate.logOnePlusV leaf5369InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5369InputLogOnePlusV_eq }

private noncomputable def leaf5369Inputs : Inputs :=
  inputsOfCaches globalInput sk163RoundedInputs
    chi303InputQChi innerPair272Input
    leaf5369InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5369LowerChecked :
    lowerCheck 24 leaf5369Box leaf5369Inputs = true := by
  rfl'

private theorem leaf5369CoversExact : CoversExact 8
    leaf5369Box leaf5369Certificate leaf5369InnerLog leaf5369Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk163RoundedFacts chi303RoundedFacts
    innerPair272RoundedFacts leaf5369RoundedFacts (by rfl)

private theorem leaf5369FlatSound : Sound leaf5369Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5369CertificateValid
    leaf5369InnerLogValid leaf5369CoversExact leaf5369LowerChecked

private noncomputable def leaf5370Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (95/256), chiHi := (3/8) }

private noncomputable def leaf5370Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871337/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356862976) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1259000361/1073741824) }, upper := { exponent := 1, mantissa := (607/512) } }, logOuter := sk163LogOuterCertificate, logK := sk163LogKCertificate, logChi := chi304LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715585535/68713725952) } }, logDArg := sk163LogDArgCertificate }

private noncomputable def leaf5370InnerLog : WideLogData :=
  innerPair272Data

set_option maxRecDepth 1000000 in
private theorem leaf5370LocalValidity :
    LeafFacts leaf5370Box leaf5370Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5370Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356862976) }) = true
      norm_num [leaf5370Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5370CertificateValid :
    WideCertificateValid leaf5370Box leaf5370Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk163ValidityFacts chi304ValidityFacts
    leaf5370LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5370CoverageChecked :
    coverageCheck (innerAD leaf5370Box) leaf5370InnerLog = true := by
  rfl'

private theorem leaf5370InnerLogValid :
    leaf5370InnerLog.Valid 8 (innerAD leaf5370Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint77PositiveFacts.valid leaf5370CoverageChecked

private noncomputable def leaf5370InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629535/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5370InputLogOnePlusV_eq :
    leaf5370InputLogOnePlusV = outerEnclosure 24
      (leaf5370Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5370RoundedFacts : LeafRoundedFacts 8
    leaf5370Certificate.logOnePlusV leaf5370InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5370InputLogOnePlusV_eq }

private noncomputable def leaf5370Inputs : Inputs :=
  inputsOfCaches globalInput sk163RoundedInputs
    chi304InputQChi innerPair272Input
    leaf5370InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5370LowerChecked :
    lowerCheck 24 leaf5370Box leaf5370Inputs = true := by
  rfl'

private theorem leaf5370CoversExact : CoversExact 8
    leaf5370Box leaf5370Certificate leaf5370InnerLog leaf5370Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk163RoundedFacts chi304RoundedFacts
    innerPair272RoundedFacts leaf5370RoundedFacts (by rfl)

private theorem leaf5370FlatSound : Sound leaf5370Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5370CertificateValid
    leaf5370InnerLogValid leaf5370CoversExact leaf5370LowerChecked

private noncomputable def leaf5371Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (47/128), chiHi := (95/256) }

private noncomputable def leaf5371Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871337/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356868608) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1257558657/1073741824) }, upper := { exponent := 1, mantissa := (9701/8192) } }, logOuter := sk164LogOuterCertificate, logK := sk164LogKCertificate, logChi := chi303LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715591167/68713737216) } }, logDArg := sk164LogDArgCertificate }

private noncomputable def leaf5371InnerLog : WideLogData :=
  innerPair272Data

set_option maxRecDepth 1000000 in
private theorem leaf5371LocalValidity :
    LeafFacts leaf5371Box leaf5371Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5371Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356868608) }) = true
      norm_num [leaf5371Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5371CertificateValid :
    WideCertificateValid leaf5371Box leaf5371Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk164ValidityFacts chi303ValidityFacts
    leaf5371LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5371CoverageChecked :
    coverageCheck (innerAD leaf5371Box) leaf5371InnerLog = true := by
  rfl'

private theorem leaf5371InnerLogValid :
    leaf5371InnerLog.Valid 8 (innerAD leaf5371Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint77PositiveFacts.valid leaf5371CoverageChecked

private noncomputable def leaf5371InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629533/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5371InputLogOnePlusV_eq :
    leaf5371InputLogOnePlusV = outerEnclosure 24
      (leaf5371Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5371RoundedFacts : LeafRoundedFacts 8
    leaf5371Certificate.logOnePlusV leaf5371InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5371InputLogOnePlusV_eq }

private noncomputable def leaf5371Inputs : Inputs :=
  inputsOfCaches globalInput sk164RoundedInputs
    chi303InputQChi innerPair272Input
    leaf5371InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5371LowerChecked :
    lowerCheck 24 leaf5371Box leaf5371Inputs = true := by
  rfl'

private theorem leaf5371CoversExact : CoversExact 8
    leaf5371Box leaf5371Certificate leaf5371InnerLog leaf5371Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk164RoundedFacts chi303RoundedFacts
    innerPair272RoundedFacts leaf5371RoundedFacts (by rfl)

private theorem leaf5371FlatSound : Sound leaf5371Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5371CertificateValid
    leaf5371InnerLogValid leaf5371CoversExact leaf5371LowerChecked

private noncomputable def leaf5372Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (95/256), chiHi := (3/8) }

private noncomputable def leaf5372Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871339/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356838400) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1265225899/1073741824) }, upper := { exponent := 1, mantissa := (305/256) } }, logOuter := sk164LogOuterCertificate, logK := sk164LogKCertificate, logChi := chi304LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715560959/68713676800) } }, logDArg := sk164LogDArgCertificate }

private noncomputable def leaf5372InnerLog : WideLogData :=
  innerPair569Data

set_option maxRecDepth 1000000 in
private theorem leaf5372LocalValidity :
    LeafFacts leaf5372Box leaf5372Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5372Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356838400) }) = true
      norm_num [leaf5372Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5372CertificateValid :
    WideCertificateValid leaf5372Box leaf5372Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk164ValidityFacts chi304ValidityFacts
    leaf5372LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5372CoverageChecked :
    coverageCheck (innerAD leaf5372Box) leaf5372InnerLog = true := by
  rfl'

private theorem leaf5372InnerLogValid :
    leaf5372InnerLog.Valid 8 (innerAD leaf5372Box) :=
  wideLogDataValid_of_cachedCheck endpoint297PositiveFacts
    endpoint304PositiveFacts.valid leaf5372CoverageChecked

private noncomputable def leaf5372InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629541/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5372InputLogOnePlusV_eq :
    leaf5372InputLogOnePlusV = outerEnclosure 24
      (leaf5372Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5372RoundedFacts : LeafRoundedFacts 8
    leaf5372Certificate.logOnePlusV leaf5372InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5372InputLogOnePlusV_eq }

private noncomputable def leaf5372Inputs : Inputs :=
  inputsOfCaches globalInput sk164RoundedInputs
    chi304InputQChi innerPair569Input
    leaf5372InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5372LowerChecked :
    lowerCheck 24 leaf5372Box leaf5372Inputs = true := by
  rfl'

private theorem leaf5372CoversExact : CoversExact 8
    leaf5372Box leaf5372Certificate leaf5372InnerLog leaf5372Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk164RoundedFacts chi304RoundedFacts
    innerPair569RoundedFacts leaf5372RoundedFacts (by rfl)

private theorem leaf5372FlatSound : Sound leaf5372Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5372CertificateValid
    leaf5372InnerLogValid leaf5372CoversExact leaf5372LowerChecked

private noncomputable def leaf5373Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (23/64), chiHi := (93/256) }

private noncomputable def leaf5373Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871335/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356905216) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1248253115/1073741824) }, upper := { exponent := 1, mantissa := (19259/16384) } }, logOuter := sk165LogOuterCertificate, logK := sk165LogKCertificate, logChi := chi301LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715627775/68713810432) } }, logDArg := sk165LogDArgCertificate }

private noncomputable def leaf5373InnerLog : WideLogData :=
  innerPair272Data

set_option maxRecDepth 1000000 in
private theorem leaf5373LocalValidity :
    LeafFacts leaf5373Box leaf5373Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5373Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356905216) }) = true
      norm_num [leaf5373Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5373CertificateValid :
    WideCertificateValid leaf5373Box leaf5373Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk165ValidityFacts chi301ValidityFacts
    leaf5373LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5373CoverageChecked :
    coverageCheck (innerAD leaf5373Box) leaf5373InnerLog = true := by
  rfl'

private theorem leaf5373InnerLogValid :
    leaf5373InnerLog.Valid 8 (innerAD leaf5373Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint77PositiveFacts.valid leaf5373CoverageChecked

private noncomputable def leaf5373InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907381/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5373InputLogOnePlusV_eq :
    leaf5373InputLogOnePlusV = outerEnclosure 24
      (leaf5373Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5373RoundedFacts : LeafRoundedFacts 8
    leaf5373Certificate.logOnePlusV leaf5373InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5373InputLogOnePlusV_eq }

private noncomputable def leaf5373Inputs : Inputs :=
  inputsOfCaches globalInput sk165RoundedInputs
    chi301InputQChi innerPair272Input
    leaf5373InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5373LowerChecked :
    lowerCheck 24 leaf5373Box leaf5373Inputs = true := by
  rfl'

private theorem leaf5373CoversExact : CoversExact 8
    leaf5373Box leaf5373Certificate leaf5373InnerLog leaf5373Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk165RoundedFacts chi301RoundedFacts
    innerPair272RoundedFacts leaf5373RoundedFacts (by rfl)

private theorem leaf5373FlatSound : Sound leaf5373Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5373CertificateValid
    leaf5373InnerLogValid leaf5373CoversExact leaf5373LowerChecked

private noncomputable def leaf5374Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (93/256), chiHi := (47/128) }

private noncomputable def leaf5374Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871337/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356874752) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1255985889/1073741824) }, upper := { exponent := 1, mantissa := (9689/8192) } }, logOuter := sk165LogOuterCertificate, logK := sk165LogKCertificate, logChi := chi302LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715597311/68713749504) } }, logDArg := sk165LogDArgCertificate }

private noncomputable def leaf5374InnerLog : WideLogData :=
  innerPair272Data

set_option maxRecDepth 1000000 in
private theorem leaf5374LocalValidity :
    LeafFacts leaf5374Box leaf5374Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5374Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356874752) }) = true
      norm_num [leaf5374Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5374CertificateValid :
    WideCertificateValid leaf5374Box leaf5374Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk165ValidityFacts chi302ValidityFacts
    leaf5374LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5374CoverageChecked :
    coverageCheck (innerAD leaf5374Box) leaf5374InnerLog = true := by
  rfl'

private theorem leaf5374InnerLogValid :
    leaf5374InnerLog.Valid 8 (innerAD leaf5374Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint77PositiveFacts.valid leaf5374CoverageChecked

private noncomputable def leaf5374InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907383/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5374InputLogOnePlusV_eq :
    leaf5374InputLogOnePlusV = outerEnclosure 24
      (leaf5374Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5374RoundedFacts : LeafRoundedFacts 8
    leaf5374Certificate.logOnePlusV leaf5374InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5374InputLogOnePlusV_eq }

private noncomputable def leaf5374Inputs : Inputs :=
  inputsOfCaches globalInput sk165RoundedInputs
    chi302InputQChi innerPair272Input
    leaf5374InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5374LowerChecked :
    lowerCheck 24 leaf5374Box leaf5374Inputs = true := by
  rfl'

private theorem leaf5374CoversExact : CoversExact 8
    leaf5374Box leaf5374Certificate leaf5374InnerLog leaf5374Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk165RoundedFacts chi302RoundedFacts
    innerPair272RoundedFacts leaf5374RoundedFacts (by rfl)

private theorem leaf5374FlatSound : Sound leaf5374Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5374CertificateValid
    leaf5374InnerLogValid leaf5374CoversExact leaf5374LowerChecked

private noncomputable def leaf5375Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (23/64), chiHi := (93/256) }

private noncomputable def leaf5375Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871337/536870912) }, vSqrt := { lower := (8191/8192), upper := (2021101327/2020993024) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1254282057/1073741824) }, upper := { exponent := 1, mantissa := (2419/2048) } }, logOuter := sk166LogOuterCertificate, logK := sk166LogKCertificate, logChi := chi301LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (4042094351/4041986048) } }, logDArg := sk166LogDArgCertificate }

private noncomputable def leaf5375InnerLog : WideLogData :=
  innerPair272Data

set_option maxRecDepth 1000000 in
private theorem leaf5375LocalValidity :
    LeafFacts leaf5375Box leaf5375Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5375Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (2021101327/2020993024) }) = true
      norm_num [leaf5375Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5375CertificateValid :
    WideCertificateValid leaf5375Box leaf5375Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk166ValidityFacts chi301ValidityFacts
    leaf5375LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5375CoverageChecked :
    coverageCheck (innerAD leaf5375Box) leaf5375InnerLog = true := by
  rfl'

private theorem leaf5375InnerLogValid :
    leaf5375InnerLog.Valid 8 (innerAD leaf5375Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint77PositiveFacts.valid leaf5375CoverageChecked

private noncomputable def leaf5375InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814765/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5375InputLogOnePlusV_eq :
    leaf5375InputLogOnePlusV = outerEnclosure 24
      (leaf5375Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5375RoundedFacts : LeafRoundedFacts 8
    leaf5375Certificate.logOnePlusV leaf5375InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5375InputLogOnePlusV_eq }

private noncomputable def leaf5375Inputs : Inputs :=
  inputsOfCaches globalInput sk166RoundedInputs
    chi301InputQChi innerPair272Input
    leaf5375InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5375LowerChecked :
    lowerCheck 24 leaf5375Box leaf5375Inputs = true := by
  rfl'

private theorem leaf5375CoversExact : CoversExact 8
    leaf5375Box leaf5375Certificate leaf5375InnerLog leaf5375Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk166RoundedFacts chi301RoundedFacts
    innerPair272RoundedFacts leaf5375RoundedFacts (by rfl)

private theorem leaf5375FlatSound : Sound leaf5375Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5375CertificateValid
    leaf5375InnerLogValid leaf5375CoversExact leaf5375LowerChecked

private noncomputable def leaf5376Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (93/256), chiHi := (47/128) }

private noncomputable def leaf5376Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871339/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356850688) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1262080363/1073741824) }, upper := { exponent := 1, mantissa := (1217/1024) } }, logOuter := sk166LogOuterCertificate, logK := sk166LogKCertificate, logChi := chi302LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715573247/68713701376) } }, logDArg := sk166LogDArgCertificate }

private noncomputable def leaf5376InnerLog : WideLogData :=
  innerPair569Data

set_option maxRecDepth 1000000 in
private theorem leaf5376LocalValidity :
    LeafFacts leaf5376Box leaf5376Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5376Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356850688) }) = true
      norm_num [leaf5376Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5376CertificateValid :
    WideCertificateValid leaf5376Box leaf5376Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk166ValidityFacts chi302ValidityFacts
    leaf5376LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5376CoverageChecked :
    coverageCheck (innerAD leaf5376Box) leaf5376InnerLog = true := by
  rfl'

private theorem leaf5376InnerLogValid :
    leaf5376InnerLog.Valid 8 (innerAD leaf5376Box) :=
  wideLogDataValid_of_cachedCheck endpoint297PositiveFacts
    endpoint304PositiveFacts.valid leaf5376CoverageChecked

private noncomputable def leaf5376InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814769/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5376InputLogOnePlusV_eq :
    leaf5376InputLogOnePlusV = outerEnclosure 24
      (leaf5376Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5376RoundedFacts : LeafRoundedFacts 8
    leaf5376Certificate.logOnePlusV leaf5376InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5376InputLogOnePlusV_eq }

private noncomputable def leaf5376Inputs : Inputs :=
  inputsOfCaches globalInput sk166RoundedInputs
    chi302InputQChi innerPair569Input
    leaf5376InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5376LowerChecked :
    lowerCheck 24 leaf5376Box leaf5376Inputs = true := by
  rfl'

private theorem leaf5376CoversExact : CoversExact 8
    leaf5376Box leaf5376Certificate leaf5376InnerLog leaf5376Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk166RoundedFacts chi302RoundedFacts
    innerPair569RoundedFacts leaf5376RoundedFacts (by rfl)

private theorem leaf5376FlatSound : Sound leaf5376Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5376CertificateValid
    leaf5376InnerLogValid leaf5376CoversExact leaf5376LowerChecked

private noncomputable def leaf5377Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (47/128), chiHi := (95/256) }

private noncomputable def leaf5377Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871339/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356844288) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1263718663/1073741824) }, upper := { exponent := 1, mantissa := (19497/16384) } }, logOuter := sk165LogOuterCertificate, logK := sk165LogKCertificate, logChi := chi303LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715566847/68713688576) } }, logDArg := sk165LogDArgCertificate }

private noncomputable def leaf5377InnerLog : WideLogData :=
  innerPair569Data

set_option maxRecDepth 1000000 in
private theorem leaf5377LocalValidity :
    LeafFacts leaf5377Box leaf5377Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5377Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356844288) }) = true
      norm_num [leaf5377Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5377CertificateValid :
    WideCertificateValid leaf5377Box leaf5377Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk165ValidityFacts chi303ValidityFacts
    leaf5377LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5377CoverageChecked :
    coverageCheck (innerAD leaf5377Box) leaf5377InnerLog = true := by
  rfl'

private theorem leaf5377InnerLogValid :
    leaf5377InnerLog.Valid 8 (innerAD leaf5377Box) :=
  wideLogDataValid_of_cachedCheck endpoint297PositiveFacts
    endpoint304PositiveFacts.valid leaf5377CoverageChecked

private noncomputable def leaf5377InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629539/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5377InputLogOnePlusV_eq :
    leaf5377InputLogOnePlusV = outerEnclosure 24
      (leaf5377Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5377RoundedFacts : LeafRoundedFacts 8
    leaf5377Certificate.logOnePlusV leaf5377InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5377InputLogOnePlusV_eq }

private noncomputable def leaf5377Inputs : Inputs :=
  inputsOfCaches globalInput sk165RoundedInputs
    chi303InputQChi innerPair569Input
    leaf5377InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5377LowerChecked :
    lowerCheck 24 leaf5377Box leaf5377Inputs = true := by
  rfl'

private theorem leaf5377CoversExact : CoversExact 8
    leaf5377Box leaf5377Certificate leaf5377InnerLog leaf5377Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk165RoundedFacts chi303RoundedFacts
    innerPair569RoundedFacts leaf5377RoundedFacts (by rfl)

private theorem leaf5377FlatSound : Sound leaf5377Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5377CertificateValid
    leaf5377InnerLogValid leaf5377CoversExact leaf5377LowerChecked

private noncomputable def leaf5378Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (95/256), chiHi := (3/8) }

private noncomputable def leaf5378Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871341/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356813824) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1271451437/1073741824) }, upper := { exponent := 1, mantissa := (613/512) } }, logOuter := sk165LogOuterCertificate, logK := sk165LogKCertificate, logChi := chi304LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715536383/68713627648) } }, logDArg := sk165LogDArgCertificate }

private noncomputable def leaf5378InnerLog : WideLogData :=
  innerPair576Data

set_option maxRecDepth 1000000 in
private theorem leaf5378LocalValidity :
    LeafFacts leaf5378Box leaf5378Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5378Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356813824) }) = true
      norm_num [leaf5378Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5378CertificateValid :
    WideCertificateValid leaf5378Box leaf5378Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk165ValidityFacts chi304ValidityFacts
    leaf5378LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5378CoverageChecked :
    coverageCheck (innerAD leaf5378Box) leaf5378InnerLog = true := by
  rfl'

private theorem leaf5378InnerLogValid :
    leaf5378InnerLog.Valid 8 (innerAD leaf5378Box) :=
  wideLogDataValid_of_cachedCheck endpoint299PositiveFacts
    endpoint305PositiveFacts.valid leaf5378CoverageChecked

private noncomputable def leaf5378InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629547/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5378InputLogOnePlusV_eq :
    leaf5378InputLogOnePlusV = outerEnclosure 24
      (leaf5378Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5378RoundedFacts : LeafRoundedFacts 8
    leaf5378Certificate.logOnePlusV leaf5378InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5378InputLogOnePlusV_eq }

private noncomputable def leaf5378Inputs : Inputs :=
  inputsOfCaches globalInput sk165RoundedInputs
    chi304InputQChi innerPair576Input
    leaf5378InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5378LowerChecked :
    lowerCheck 24 leaf5378Box leaf5378Inputs = true := by
  rfl'

private theorem leaf5378CoversExact : CoversExact 8
    leaf5378Box leaf5378Certificate leaf5378InnerLog leaf5378Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk165RoundedFacts chi304RoundedFacts
    innerPair576RoundedFacts leaf5378RoundedFacts (by rfl)

private theorem leaf5378FlatSound : Sound leaf5378Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5378CertificateValid
    leaf5378InnerLogValid leaf5378CoversExact leaf5378LowerChecked

private noncomputable def leaf5379Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (47/128), chiHi := (95/256) }

private noncomputable def leaf5379Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871341/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356819968) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1269878669/1073741824) }, upper := { exponent := 1, mantissa := (2449/2048) } }, logOuter := sk166LogOuterCertificate, logK := sk166LogKCertificate, logChi := chi303LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715542527/68713639936) } }, logDArg := sk166LogDArgCertificate }

private noncomputable def leaf5379InnerLog : WideLogData :=
  innerPair576Data

set_option maxRecDepth 1000000 in
private theorem leaf5379LocalValidity :
    LeafFacts leaf5379Box leaf5379Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5379Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356819968) }) = true
      norm_num [leaf5379Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5379CertificateValid :
    WideCertificateValid leaf5379Box leaf5379Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk166ValidityFacts chi303ValidityFacts
    leaf5379LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5379CoverageChecked :
    coverageCheck (innerAD leaf5379Box) leaf5379InnerLog = true := by
  rfl'

private theorem leaf5379InnerLogValid :
    leaf5379InnerLog.Valid 8 (innerAD leaf5379Box) :=
  wideLogDataValid_of_cachedCheck endpoint299PositiveFacts
    endpoint305PositiveFacts.valid leaf5379CoverageChecked

private noncomputable def leaf5379InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629545/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5379InputLogOnePlusV_eq :
    leaf5379InputLogOnePlusV = outerEnclosure 24
      (leaf5379Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5379RoundedFacts : LeafRoundedFacts 8
    leaf5379Certificate.logOnePlusV leaf5379InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5379InputLogOnePlusV_eq }

private noncomputable def leaf5379Inputs : Inputs :=
  inputsOfCaches globalInput sk166RoundedInputs
    chi303InputQChi innerPair576Input
    leaf5379InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5379LowerChecked :
    lowerCheck 24 leaf5379Box leaf5379Inputs = true := by
  rfl'

private theorem leaf5379CoversExact : CoversExact 8
    leaf5379Box leaf5379Certificate leaf5379InnerLog leaf5379Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk166RoundedFacts chi303RoundedFacts
    innerPair576RoundedFacts leaf5379RoundedFacts (by rfl)

private theorem leaf5379FlatSound : Sound leaf5379Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5379CertificateValid
    leaf5379InnerLogValid leaf5379CoversExact leaf5379LowerChecked

private noncomputable def leaf5380Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (95/256), chiHi := (3/8) }

private noncomputable def leaf5380Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871343/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356789248) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1277676975/1073741824) }, upper := { exponent := 1, mantissa := (77/64) } }, logOuter := sk166LogOuterCertificate, logK := sk166LogKCertificate, logChi := chi304LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715511807/68713578496) } }, logDArg := sk166LogDArgCertificate }

private noncomputable def leaf5380InnerLog : WideLogData :=
  innerPair278Data

set_option maxRecDepth 1000000 in
private theorem leaf5380LocalValidity :
    LeafFacts leaf5380Box leaf5380Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5380Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356789248) }) = true
      norm_num [leaf5380Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5380CertificateValid :
    WideCertificateValid leaf5380Box leaf5380Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk166ValidityFacts chi304ValidityFacts
    leaf5380LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5380CoverageChecked :
    coverageCheck (innerAD leaf5380Box) leaf5380InnerLog = true := by
  rfl'

private theorem leaf5380InnerLogValid :
    leaf5380InnerLog.Valid 8 (innerAD leaf5380Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint78PositiveFacts.valid leaf5380CoverageChecked

private noncomputable def leaf5380InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629553/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5380InputLogOnePlusV_eq :
    leaf5380InputLogOnePlusV = outerEnclosure 24
      (leaf5380Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5380RoundedFacts : LeafRoundedFacts 8
    leaf5380Certificate.logOnePlusV leaf5380InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5380InputLogOnePlusV_eq }

private noncomputable def leaf5380Inputs : Inputs :=
  inputsOfCaches globalInput sk166RoundedInputs
    chi304InputQChi innerPair278Input
    leaf5380InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5380LowerChecked :
    lowerCheck 24 leaf5380Box leaf5380Inputs = true := by
  rfl'

private theorem leaf5380CoversExact : CoversExact 8
    leaf5380Box leaf5380Certificate leaf5380InnerLog leaf5380Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk166RoundedFacts chi304RoundedFacts
    innerPair278RoundedFacts leaf5380RoundedFacts (by rfl)

private theorem leaf5380FlatSound : Sound leaf5380Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5380CertificateValid
    leaf5380InnerLogValid leaf5380CoversExact leaf5380LowerChecked

private noncomputable def component108Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (11/32), chiHi := (45/128) }

set_option maxRecDepth 1000000 in
private theorem component108Node0_sound : Sound component108Node0Box :=
  sound_of_literal_split component108Node0Box leaf5317Box leaf5318Box
    .chi (89/256) (by rfl) (by rfl)
    leaf5317FlatSound leaf5318FlatSound

private noncomputable def component108Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (11/32), chiHi := (45/128) }

set_option maxRecDepth 1000000 in
private theorem component108Node1_sound : Sound component108Node1Box :=
  sound_of_literal_split component108Node1Box leaf5319Box leaf5320Box
    .chi (89/256) (by rfl) (by rfl)
    leaf5319FlatSound leaf5320FlatSound

private noncomputable def component108Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (11/32), chiHi := (45/128) }

set_option maxRecDepth 1000000 in
private theorem component108Node2_sound : Sound component108Node2Box :=
  sound_of_literal_split component108Node2Box component108Node0Box component108Node1Box
    .k (113/32) (by rfl) (by rfl)
    component108Node0_sound component108Node1_sound

private noncomputable def component108Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (45/128), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component108Node3_sound : Sound component108Node3Box :=
  sound_of_literal_split component108Node3Box leaf5321Box leaf5322Box
    .chi (91/256) (by rfl) (by rfl)
    leaf5321FlatSound leaf5322FlatSound

private noncomputable def component108Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (45/128), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component108Node4_sound : Sound component108Node4Box :=
  sound_of_literal_split component108Node4Box leaf5323Box leaf5324Box
    .chi (91/256) (by rfl) (by rfl)
    leaf5323FlatSound leaf5324FlatSound

private noncomputable def component108Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (45/128), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component108Node5_sound : Sound component108Node5Box :=
  sound_of_literal_split component108Node5Box component108Node3Box component108Node4Box
    .k (113/32) (by rfl) (by rfl)
    component108Node3_sound component108Node4_sound

private noncomputable def component108Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (11/32), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component108Node6_sound : Sound component108Node6Box :=
  sound_of_literal_split component108Node6Box component108Node2Box component108Node5Box
    .chi (45/128) (by rfl) (by rfl)
    component108Node2_sound component108Node5_sound

private noncomputable def component108Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (11/32), chiHi := (45/128) }

set_option maxRecDepth 1000000 in
private theorem component108Node7_sound : Sound component108Node7Box :=
  sound_of_literal_split component108Node7Box leaf5325Box leaf5326Box
    .chi (89/256) (by rfl) (by rfl)
    leaf5325FlatSound leaf5326FlatSound

private noncomputable def component108Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (11/32), chiHi := (45/128) }

set_option maxRecDepth 1000000 in
private theorem component108Node8_sound : Sound component108Node8Box :=
  sound_of_literal_split component108Node8Box leaf5327Box leaf5328Box
    .chi (89/256) (by rfl) (by rfl)
    leaf5327FlatSound leaf5328FlatSound

private noncomputable def component108Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (11/32), chiHi := (45/128) }

set_option maxRecDepth 1000000 in
private theorem component108Node9_sound : Sound component108Node9Box :=
  sound_of_literal_split component108Node9Box component108Node7Box component108Node8Box
    .k (115/32) (by rfl) (by rfl)
    component108Node7_sound component108Node8_sound

private noncomputable def component108Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (45/128), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component108Node10_sound : Sound component108Node10Box :=
  sound_of_literal_split component108Node10Box leaf5329Box leaf5330Box
    .chi (91/256) (by rfl) (by rfl)
    leaf5329FlatSound leaf5330FlatSound

private noncomputable def component108Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (45/128), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component108Node11_sound : Sound component108Node11Box :=
  sound_of_literal_split component108Node11Box leaf5331Box leaf5332Box
    .chi (91/256) (by rfl) (by rfl)
    leaf5331FlatSound leaf5332FlatSound

private noncomputable def component108Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (45/128), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component108Node12_sound : Sound component108Node12Box :=
  sound_of_literal_split component108Node12Box component108Node10Box component108Node11Box
    .k (115/32) (by rfl) (by rfl)
    component108Node10_sound component108Node11_sound

private noncomputable def component108Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (11/32), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component108Node13_sound : Sound component108Node13Box :=
  sound_of_literal_split component108Node13Box component108Node9Box component108Node12Box
    .chi (45/128) (by rfl) (by rfl)
    component108Node9_sound component108Node12_sound

private noncomputable def component108Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (11/32), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component108Node14_sound : Sound component108Node14Box :=
  sound_of_literal_split component108Node14Box component108Node6Box component108Node13Box
    .k (57/16) (by rfl) (by rfl)
    component108Node6_sound component108Node13_sound

private noncomputable def component108Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (23/64), chiHi := (47/128) }

set_option maxRecDepth 1000000 in
private theorem component108Node15_sound : Sound component108Node15Box :=
  sound_of_literal_split component108Node15Box leaf5333Box leaf5334Box
    .chi (93/256) (by rfl) (by rfl)
    leaf5333FlatSound leaf5334FlatSound

private noncomputable def component108Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (23/64), chiHi := (47/128) }

set_option maxRecDepth 1000000 in
private theorem component108Node16_sound : Sound component108Node16Box :=
  sound_of_literal_split component108Node16Box leaf5335Box leaf5336Box
    .chi (93/256) (by rfl) (by rfl)
    leaf5335FlatSound leaf5336FlatSound

private noncomputable def component108Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (23/64), chiHi := (47/128) }

set_option maxRecDepth 1000000 in
private theorem component108Node17_sound : Sound component108Node17Box :=
  sound_of_literal_split component108Node17Box component108Node15Box component108Node16Box
    .k (113/32) (by rfl) (by rfl)
    component108Node15_sound component108Node16_sound

private noncomputable def component108Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (47/128), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component108Node18_sound : Sound component108Node18Box :=
  sound_of_literal_split component108Node18Box leaf5337Box leaf5338Box
    .chi (95/256) (by rfl) (by rfl)
    leaf5337FlatSound leaf5338FlatSound

private noncomputable def component108Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (47/128), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component108Node19_sound : Sound component108Node19Box :=
  sound_of_literal_split component108Node19Box leaf5339Box leaf5340Box
    .chi (95/256) (by rfl) (by rfl)
    leaf5339FlatSound leaf5340FlatSound

private noncomputable def component108Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (47/128), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component108Node20_sound : Sound component108Node20Box :=
  sound_of_literal_split component108Node20Box component108Node18Box component108Node19Box
    .k (113/32) (by rfl) (by rfl)
    component108Node18_sound component108Node19_sound

private noncomputable def component108Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (23/64), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component108Node21_sound : Sound component108Node21Box :=
  sound_of_literal_split component108Node21Box component108Node17Box component108Node20Box
    .chi (47/128) (by rfl) (by rfl)
    component108Node17_sound component108Node20_sound

private noncomputable def component108Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (23/64), chiHi := (47/128) }

set_option maxRecDepth 1000000 in
private theorem component108Node22_sound : Sound component108Node22Box :=
  sound_of_literal_split component108Node22Box leaf5341Box leaf5342Box
    .chi (93/256) (by rfl) (by rfl)
    leaf5341FlatSound leaf5342FlatSound

private noncomputable def component108Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (23/64), chiHi := (47/128) }

set_option maxRecDepth 1000000 in
private theorem component108Node23_sound : Sound component108Node23Box :=
  sound_of_literal_split component108Node23Box leaf5343Box leaf5344Box
    .chi (93/256) (by rfl) (by rfl)
    leaf5343FlatSound leaf5344FlatSound

private noncomputable def component108Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (23/64), chiHi := (47/128) }

set_option maxRecDepth 1000000 in
private theorem component108Node24_sound : Sound component108Node24Box :=
  sound_of_literal_split component108Node24Box component108Node22Box component108Node23Box
    .k (115/32) (by rfl) (by rfl)
    component108Node22_sound component108Node23_sound

private noncomputable def component108Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (47/128), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component108Node25_sound : Sound component108Node25Box :=
  sound_of_literal_split component108Node25Box leaf5345Box leaf5346Box
    .chi (95/256) (by rfl) (by rfl)
    leaf5345FlatSound leaf5346FlatSound

private noncomputable def component108Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (47/128), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component108Node26_sound : Sound component108Node26Box :=
  sound_of_literal_split component108Node26Box leaf5347Box leaf5348Box
    .chi (95/256) (by rfl) (by rfl)
    leaf5347FlatSound leaf5348FlatSound

private noncomputable def component108Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (47/128), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component108Node27_sound : Sound component108Node27Box :=
  sound_of_literal_split component108Node27Box component108Node25Box component108Node26Box
    .k (115/32) (by rfl) (by rfl)
    component108Node25_sound component108Node26_sound

private noncomputable def component108Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (23/64), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component108Node28_sound : Sound component108Node28Box :=
  sound_of_literal_split component108Node28Box component108Node24Box component108Node27Box
    .chi (47/128) (by rfl) (by rfl)
    component108Node24_sound component108Node27_sound

private noncomputable def component108Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (23/64), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component108Node29_sound : Sound component108Node29Box :=
  sound_of_literal_split component108Node29Box component108Node21Box component108Node28Box
    .k (57/16) (by rfl) (by rfl)
    component108Node21_sound component108Node28_sound

private noncomputable def component108Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (11/32), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component108Node30_sound : Sound component108Node30Box :=
  sound_of_literal_split component108Node30Box component108Node14Box component108Node29Box
    .chi (23/64) (by rfl) (by rfl)
    component108Node14_sound component108Node29_sound

private noncomputable def component108Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (11/32), chiHi := (45/128) }

set_option maxRecDepth 1000000 in
private theorem component108Node31_sound : Sound component108Node31Box :=
  sound_of_literal_split component108Node31Box leaf5349Box leaf5350Box
    .chi (89/256) (by rfl) (by rfl)
    leaf5349FlatSound leaf5350FlatSound

private noncomputable def component108Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (11/32), chiHi := (45/128) }

set_option maxRecDepth 1000000 in
private theorem component108Node32_sound : Sound component108Node32Box :=
  sound_of_literal_split component108Node32Box leaf5351Box leaf5352Box
    .chi (89/256) (by rfl) (by rfl)
    leaf5351FlatSound leaf5352FlatSound

private noncomputable def component108Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (11/32), chiHi := (45/128) }

set_option maxRecDepth 1000000 in
private theorem component108Node33_sound : Sound component108Node33Box :=
  sound_of_literal_split component108Node33Box component108Node31Box component108Node32Box
    .k (117/32) (by rfl) (by rfl)
    component108Node31_sound component108Node32_sound

private noncomputable def component108Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (45/128), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component108Node34_sound : Sound component108Node34Box :=
  sound_of_literal_split component108Node34Box leaf5353Box leaf5354Box
    .chi (91/256) (by rfl) (by rfl)
    leaf5353FlatSound leaf5354FlatSound

private noncomputable def component108Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (45/128), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component108Node35_sound : Sound component108Node35Box :=
  sound_of_literal_split component108Node35Box leaf5355Box leaf5356Box
    .chi (91/256) (by rfl) (by rfl)
    leaf5355FlatSound leaf5356FlatSound

private noncomputable def component108Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (45/128), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component108Node36_sound : Sound component108Node36Box :=
  sound_of_literal_split component108Node36Box component108Node34Box component108Node35Box
    .k (117/32) (by rfl) (by rfl)
    component108Node34_sound component108Node35_sound

private noncomputable def component108Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (11/32), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component108Node37_sound : Sound component108Node37Box :=
  sound_of_literal_split component108Node37Box component108Node33Box component108Node36Box
    .chi (45/128) (by rfl) (by rfl)
    component108Node33_sound component108Node36_sound

private noncomputable def component108Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (11/32), chiHi := (45/128) }

set_option maxRecDepth 1000000 in
private theorem component108Node38_sound : Sound component108Node38Box :=
  sound_of_literal_split component108Node38Box leaf5357Box leaf5358Box
    .chi (89/256) (by rfl) (by rfl)
    leaf5357FlatSound leaf5358FlatSound

private noncomputable def component108Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (11/32), chiHi := (45/128) }

set_option maxRecDepth 1000000 in
private theorem component108Node39_sound : Sound component108Node39Box :=
  sound_of_literal_split component108Node39Box leaf5359Box leaf5360Box
    .chi (89/256) (by rfl) (by rfl)
    leaf5359FlatSound leaf5360FlatSound

private noncomputable def component108Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (11/32), chiHi := (45/128) }

set_option maxRecDepth 1000000 in
private theorem component108Node40_sound : Sound component108Node40Box :=
  sound_of_literal_split component108Node40Box component108Node38Box component108Node39Box
    .k (119/32) (by rfl) (by rfl)
    component108Node38_sound component108Node39_sound

private noncomputable def component108Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (45/128), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component108Node41_sound : Sound component108Node41Box :=
  sound_of_literal_split component108Node41Box leaf5361Box leaf5362Box
    .chi (91/256) (by rfl) (by rfl)
    leaf5361FlatSound leaf5362FlatSound

private noncomputable def component108Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (45/128), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component108Node42_sound : Sound component108Node42Box :=
  sound_of_literal_split component108Node42Box leaf5363Box leaf5364Box
    .chi (91/256) (by rfl) (by rfl)
    leaf5363FlatSound leaf5364FlatSound

private noncomputable def component108Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (45/128), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component108Node43_sound : Sound component108Node43Box :=
  sound_of_literal_split component108Node43Box component108Node41Box component108Node42Box
    .k (119/32) (by rfl) (by rfl)
    component108Node41_sound component108Node42_sound

private noncomputable def component108Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (11/32), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component108Node44_sound : Sound component108Node44Box :=
  sound_of_literal_split component108Node44Box component108Node40Box component108Node43Box
    .chi (45/128) (by rfl) (by rfl)
    component108Node40_sound component108Node43_sound

private noncomputable def component108Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (11/32), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component108Node45_sound : Sound component108Node45Box :=
  sound_of_literal_split component108Node45Box component108Node37Box component108Node44Box
    .k (59/16) (by rfl) (by rfl)
    component108Node37_sound component108Node44_sound

private noncomputable def component108Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (23/64), chiHi := (47/128) }

set_option maxRecDepth 1000000 in
private theorem component108Node46_sound : Sound component108Node46Box :=
  sound_of_literal_split component108Node46Box leaf5365Box leaf5366Box
    .chi (93/256) (by rfl) (by rfl)
    leaf5365FlatSound leaf5366FlatSound

private noncomputable def component108Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (23/64), chiHi := (47/128) }

set_option maxRecDepth 1000000 in
private theorem component108Node47_sound : Sound component108Node47Box :=
  sound_of_literal_split component108Node47Box leaf5367Box leaf5368Box
    .chi (93/256) (by rfl) (by rfl)
    leaf5367FlatSound leaf5368FlatSound

private noncomputable def component108Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (23/64), chiHi := (47/128) }

set_option maxRecDepth 1000000 in
private theorem component108Node48_sound : Sound component108Node48Box :=
  sound_of_literal_split component108Node48Box component108Node46Box component108Node47Box
    .k (117/32) (by rfl) (by rfl)
    component108Node46_sound component108Node47_sound

private noncomputable def component108Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (47/128), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component108Node49_sound : Sound component108Node49Box :=
  sound_of_literal_split component108Node49Box leaf5369Box leaf5370Box
    .chi (95/256) (by rfl) (by rfl)
    leaf5369FlatSound leaf5370FlatSound

private noncomputable def component108Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (47/128), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component108Node50_sound : Sound component108Node50Box :=
  sound_of_literal_split component108Node50Box leaf5371Box leaf5372Box
    .chi (95/256) (by rfl) (by rfl)
    leaf5371FlatSound leaf5372FlatSound

private noncomputable def component108Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (47/128), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component108Node51_sound : Sound component108Node51Box :=
  sound_of_literal_split component108Node51Box component108Node49Box component108Node50Box
    .k (117/32) (by rfl) (by rfl)
    component108Node49_sound component108Node50_sound

private noncomputable def component108Node52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (23/64), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component108Node52_sound : Sound component108Node52Box :=
  sound_of_literal_split component108Node52Box component108Node48Box component108Node51Box
    .chi (47/128) (by rfl) (by rfl)
    component108Node48_sound component108Node51_sound

private noncomputable def component108Node53Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (23/64), chiHi := (47/128) }

set_option maxRecDepth 1000000 in
private theorem component108Node53_sound : Sound component108Node53Box :=
  sound_of_literal_split component108Node53Box leaf5373Box leaf5374Box
    .chi (93/256) (by rfl) (by rfl)
    leaf5373FlatSound leaf5374FlatSound

private noncomputable def component108Node54Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (23/64), chiHi := (47/128) }

set_option maxRecDepth 1000000 in
private theorem component108Node54_sound : Sound component108Node54Box :=
  sound_of_literal_split component108Node54Box leaf5375Box leaf5376Box
    .chi (93/256) (by rfl) (by rfl)
    leaf5375FlatSound leaf5376FlatSound

private noncomputable def component108Node55Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (23/64), chiHi := (47/128) }

set_option maxRecDepth 1000000 in
private theorem component108Node55_sound : Sound component108Node55Box :=
  sound_of_literal_split component108Node55Box component108Node53Box component108Node54Box
    .k (119/32) (by rfl) (by rfl)
    component108Node53_sound component108Node54_sound

private noncomputable def component108Node56Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (47/128), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component108Node56_sound : Sound component108Node56Box :=
  sound_of_literal_split component108Node56Box leaf5377Box leaf5378Box
    .chi (95/256) (by rfl) (by rfl)
    leaf5377FlatSound leaf5378FlatSound

private noncomputable def component108Node57Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (47/128), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component108Node57_sound : Sound component108Node57Box :=
  sound_of_literal_split component108Node57Box leaf5379Box leaf5380Box
    .chi (95/256) (by rfl) (by rfl)
    leaf5379FlatSound leaf5380FlatSound

private noncomputable def component108Node58Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (47/128), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component108Node58_sound : Sound component108Node58Box :=
  sound_of_literal_split component108Node58Box component108Node56Box component108Node57Box
    .k (119/32) (by rfl) (by rfl)
    component108Node56_sound component108Node57_sound

private noncomputable def component108Node59Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (23/64), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component108Node59_sound : Sound component108Node59Box :=
  sound_of_literal_split component108Node59Box component108Node55Box component108Node58Box
    .chi (47/128) (by rfl) (by rfl)
    component108Node55_sound component108Node58_sound

private noncomputable def component108Node60Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (23/64), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component108Node60_sound : Sound component108Node60Box :=
  sound_of_literal_split component108Node60Box component108Node52Box component108Node59Box
    .k (59/16) (by rfl) (by rfl)
    component108Node52_sound component108Node59_sound

private noncomputable def component108Node61Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (11/32), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component108Node61_sound : Sound component108Node61Box :=
  sound_of_literal_split component108Node61Box component108Node45Box component108Node60Box
    .chi (23/64) (by rfl) (by rfl)
    component108Node45_sound component108Node60_sound

noncomputable def component108Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (15/4), chiLo := (11/32), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
theorem component108_sound : Sound component108Box :=
  sound_of_literal_split component108Box component108Node30Box component108Node61Box
    .k (29/8) (by rfl) (by rfl)
    component108Node30_sound component108Node61_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
