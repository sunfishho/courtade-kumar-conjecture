import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch6
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch10
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

private noncomputable def leaf5499Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (11/32), chiHi := (89/256) }

private noncomputable def leaf5499Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871331/536870912) }, vSqrt := { lower := (8191/8192), upper := (2021101327/2020998912) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1228855647/1073741824) }, upper := { exponent := 1, mantissa := (18961/16384) } }, logOuter := sk169LogOuterCertificate, logK := sk169LogKCertificate, logChi := chi297LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (4042100239/4041997824) } }, logDArg := sk169LogDArgCertificate }

private noncomputable def leaf5499InnerLog : WideLogData :=
  innerPair645Data

set_option maxRecDepth 1000000 in
private theorem leaf5499LocalValidity :
    LeafFacts leaf5499Box leaf5499Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5499Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (2021101327/2020998912) }) = true
      norm_num [leaf5499Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5499CertificateValid :
    WideCertificateValid leaf5499Box leaf5499Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk169ValidityFacts chi297ValidityFacts
    leaf5499LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5499CoverageChecked :
    coverageCheck (innerAD leaf5499Box) leaf5499InnerLog = true := by
  rfl'

private theorem leaf5499InnerLogValid :
    leaf5499InnerLog.Valid 8 (innerAD leaf5499Box) :=
  wideLogDataValid_of_cachedCheck endpoint388PositiveFacts
    endpoint397PositiveFacts.valid leaf5499CoverageChecked

private noncomputable def leaf5499InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814753/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5499InputLogOnePlusV_eq :
    leaf5499InputLogOnePlusV = outerEnclosure 24
      (leaf5499Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5499RoundedFacts : LeafRoundedFacts 8
    leaf5499Certificate.logOnePlusV leaf5499InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5499InputLogOnePlusV_eq }

private noncomputable def leaf5499Inputs : Inputs :=
  inputsOfCaches globalInput sk169RoundedInputs
    chi297InputQChi innerPair645Input
    leaf5499InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5499LowerChecked :
    lowerCheck 24 leaf5499Box leaf5499Inputs = true := by
  rfl'

private theorem leaf5499CoversExact : CoversExact 8
    leaf5499Box leaf5499Certificate leaf5499InnerLog leaf5499Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk169RoundedFacts chi297RoundedFacts
    innerPair645RoundedFacts leaf5499RoundedFacts (by rfl)

private theorem leaf5499FlatSound : Sound leaf5499Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5499CertificateValid
    leaf5499InnerLogValid leaf5499CoversExact leaf5499LowerChecked

private noncomputable def leaf5500Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (89/256), chiHi := (45/128) }

private noncomputable def leaf5500Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871333/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356950528) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1236719485/1073741824) }, upper := { exponent := 1, mantissa := (9541/8192) } }, logOuter := sk169LogOuterCertificate, logK := sk169LogKCertificate, logChi := chi298LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715673087/68713901056) } }, logDArg := sk169LogDArgCertificate }

private noncomputable def leaf5500InnerLog : WideLogData :=
  innerPair648Data

set_option maxRecDepth 1000000 in
private theorem leaf5500LocalValidity :
    LeafFacts leaf5500Box leaf5500Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5500Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356950528) }) = true
      norm_num [leaf5500Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5500CertificateValid :
    WideCertificateValid leaf5500Box leaf5500Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk169ValidityFacts chi298ValidityFacts
    leaf5500LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5500CoverageChecked :
    coverageCheck (innerAD leaf5500Box) leaf5500InnerLog = true := by
  rfl'

private theorem leaf5500InnerLogValid :
    leaf5500InnerLog.Valid 8 (innerAD leaf5500Box) :=
  wideLogDataValid_of_cachedCheck endpoint390PositiveFacts
    endpoint396PositiveFacts.valid leaf5500CoverageChecked

private noncomputable def leaf5500InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629513/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5500InputLogOnePlusV_eq :
    leaf5500InputLogOnePlusV = outerEnclosure 24
      (leaf5500Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5500RoundedFacts : LeafRoundedFacts 8
    leaf5500Certificate.logOnePlusV leaf5500InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5500InputLogOnePlusV_eq }

private noncomputable def leaf5500Inputs : Inputs :=
  inputsOfCaches globalInput sk169RoundedInputs
    chi298InputQChi innerPair648Input
    leaf5500InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5500LowerChecked :
    lowerCheck 24 leaf5500Box leaf5500Inputs = true := by
  rfl'

private theorem leaf5500CoversExact : CoversExact 8
    leaf5500Box leaf5500Certificate leaf5500InnerLog leaf5500Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk169RoundedFacts chi298RoundedFacts
    innerPair648RoundedFacts leaf5500RoundedFacts (by rfl)

private theorem leaf5500FlatSound : Sound leaf5500Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5500CertificateValid
    leaf5500InnerLogValid leaf5500CoversExact leaf5500LowerChecked

private noncomputable def leaf5501Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (11/32), chiHi := (89/256) }

private noncomputable def leaf5501Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871333/536870912) }, vSqrt := { lower := (8191/8192), upper := (4908388937/4908136960) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1234622461/1073741824) }, upper := { exponent := 1, mantissa := (9525/8192) } }, logOuter := sk170LogOuterCertificate, logK := sk170LogKCertificate, logChi := chi297LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (9816525897/9816273920) } }, logDArg := sk170LogDArgCertificate }

private noncomputable def leaf5501InnerLog : WideLogData :=
  innerPair571Data

set_option maxRecDepth 1000000 in
private theorem leaf5501LocalValidity :
    LeafFacts leaf5501Box leaf5501Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5501Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4908388937/4908136960) }) = true
      norm_num [leaf5501Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5501CertificateValid :
    WideCertificateValid leaf5501Box leaf5501Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk170ValidityFacts chi297ValidityFacts
    leaf5501LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5501CoverageChecked :
    coverageCheck (innerAD leaf5501Box) leaf5501InnerLog = true := by
  rfl'

private theorem leaf5501InnerLogValid :
    leaf5501InnerLog.Valid 8 (innerAD leaf5501Box) :=
  wideLogDataValid_of_cachedCheck endpoint298PositiveFacts
    endpoint296PositiveFacts.valid leaf5501CoverageChecked

private noncomputable def leaf5501InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629511/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5501InputLogOnePlusV_eq :
    leaf5501InputLogOnePlusV = outerEnclosure 24
      (leaf5501Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5501RoundedFacts : LeafRoundedFacts 8
    leaf5501Certificate.logOnePlusV leaf5501InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5501InputLogOnePlusV_eq }

private noncomputable def leaf5501Inputs : Inputs :=
  inputsOfCaches globalInput sk170RoundedInputs
    chi297InputQChi innerPair571Input
    leaf5501InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5501LowerChecked :
    lowerCheck 24 leaf5501Box leaf5501Inputs = true := by
  rfl'

private theorem leaf5501CoversExact : CoversExact 8
    leaf5501Box leaf5501Certificate leaf5501InnerLog leaf5501Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk170RoundedFacts chi297RoundedFacts
    innerPair571RoundedFacts leaf5501RoundedFacts (by rfl)

private theorem leaf5501FlatSound : Sound leaf5501Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5501CertificateValid
    leaf5501InnerLogValid leaf5501CoversExact leaf5501LowerChecked

private noncomputable def leaf5502Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (89/256), chiHi := (45/128) }

private noncomputable def leaf5502Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871335/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356927488) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1242551831/1073741824) }, upper := { exponent := 1, mantissa := (4793/4096) } }, logOuter := sk170LogOuterCertificate, logK := sk170LogKCertificate, logChi := chi298LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715650047/68713854976) } }, logDArg := sk170LogDArgCertificate }

private noncomputable def leaf5502InnerLog : WideLogData :=
  innerPair276Data

set_option maxRecDepth 1000000 in
private theorem leaf5502LocalValidity :
    LeafFacts leaf5502Box leaf5502Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5502Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356927488) }) = true
      norm_num [leaf5502Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5502CertificateValid :
    WideCertificateValid leaf5502Box leaf5502Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk170ValidityFacts chi298ValidityFacts
    leaf5502LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5502CoverageChecked :
    coverageCheck (innerAD leaf5502Box) leaf5502InnerLog = true := by
  rfl'

private theorem leaf5502InnerLogValid :
    leaf5502InnerLog.Valid 8 (innerAD leaf5502Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint297PositiveFacts.valid leaf5502CoverageChecked

private noncomputable def leaf5502InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629519/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5502InputLogOnePlusV_eq :
    leaf5502InputLogOnePlusV = outerEnclosure 24
      (leaf5502Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5502RoundedFacts : LeafRoundedFacts 8
    leaf5502Certificate.logOnePlusV leaf5502InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5502InputLogOnePlusV_eq }

private noncomputable def leaf5502Inputs : Inputs :=
  inputsOfCaches globalInput sk170RoundedInputs
    chi298InputQChi innerPair276Input
    leaf5502InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5502LowerChecked :
    lowerCheck 24 leaf5502Box leaf5502Inputs = true := by
  rfl'

private theorem leaf5502CoversExact : CoversExact 8
    leaf5502Box leaf5502Certificate leaf5502InnerLog leaf5502Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk170RoundedFacts chi298RoundedFacts
    innerPair276RoundedFacts leaf5502RoundedFacts (by rfl)

private theorem leaf5502FlatSound : Sound leaf5502Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5502CertificateValid
    leaf5502InnerLogValid leaf5502CoversExact leaf5502LowerChecked

private noncomputable def leaf5503Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (45/128), chiHi := (91/256) }

private noncomputable def leaf5503Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871335/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356919552) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1244583323/1073741824) }, upper := { exponent := 1, mantissa := (19203/16384) } }, logOuter := sk169LogOuterCertificate, logK := sk169LogKCertificate, logChi := chi299LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715642111/68713839104) } }, logDArg := sk169LogDArgCertificate }

private noncomputable def leaf5503InnerLog : WideLogData :=
  innerPair277Data

set_option maxRecDepth 1000000 in
private theorem leaf5503LocalValidity :
    LeafFacts leaf5503Box leaf5503Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5503Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356919552) }) = true
      norm_num [leaf5503Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5503CertificateValid :
    WideCertificateValid leaf5503Box leaf5503Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk169ValidityFacts chi299ValidityFacts
    leaf5503LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5503CoverageChecked :
    coverageCheck (innerAD leaf5503Box) leaf5503InnerLog = true := by
  rfl'

private theorem leaf5503InnerLogValid :
    leaf5503InnerLog.Valid 8 (innerAD leaf5503Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint299PositiveFacts.valid leaf5503CoverageChecked

private noncomputable def leaf5503InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629521/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5503InputLogOnePlusV_eq :
    leaf5503InputLogOnePlusV = outerEnclosure 24
      (leaf5503Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5503RoundedFacts : LeafRoundedFacts 8
    leaf5503Certificate.logOnePlusV leaf5503InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5503InputLogOnePlusV_eq }

private noncomputable def leaf5503Inputs : Inputs :=
  inputsOfCaches globalInput sk169RoundedInputs
    chi299InputQChi innerPair277Input
    leaf5503InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5503LowerChecked :
    lowerCheck 24 leaf5503Box leaf5503Inputs = true := by
  rfl'

private theorem leaf5503CoversExact : CoversExact 8
    leaf5503Box leaf5503Certificate leaf5503InnerLog leaf5503Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk169RoundedFacts chi299RoundedFacts
    innerPair277RoundedFacts leaf5503RoundedFacts (by rfl)

private theorem leaf5503FlatSound : Sound leaf5503Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5503CertificateValid
    leaf5503InnerLogValid leaf5503CoversExact leaf5503LowerChecked

private noncomputable def leaf5504Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (91/256), chiHi := (23/64) }

private noncomputable def leaf5504Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871337/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356888576) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1252447161/1073741824) }, upper := { exponent := 1, mantissa := (4831/4096) } }, logOuter := sk169LogOuterCertificate, logK := sk169LogKCertificate, logChi := chi300LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715611135/68713777152) } }, logDArg := sk169LogDArgCertificate }

private noncomputable def leaf5504InnerLog : WideLogData :=
  innerPair272Data

set_option maxRecDepth 1000000 in
private theorem leaf5504LocalValidity :
    LeafFacts leaf5504Box leaf5504Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5504Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356888576) }) = true
      norm_num [leaf5504Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5504CertificateValid :
    WideCertificateValid leaf5504Box leaf5504Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk169ValidityFacts chi300ValidityFacts
    leaf5504LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5504CoverageChecked :
    coverageCheck (innerAD leaf5504Box) leaf5504InnerLog = true := by
  rfl'

private theorem leaf5504InnerLogValid :
    leaf5504InnerLog.Valid 8 (innerAD leaf5504Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint77PositiveFacts.valid leaf5504CoverageChecked

private noncomputable def leaf5504InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629529/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5504InputLogOnePlusV_eq :
    leaf5504InputLogOnePlusV = outerEnclosure 24
      (leaf5504Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5504RoundedFacts : LeafRoundedFacts 8
    leaf5504Certificate.logOnePlusV leaf5504InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5504InputLogOnePlusV_eq }

private noncomputable def leaf5504Inputs : Inputs :=
  inputsOfCaches globalInput sk169RoundedInputs
    chi300InputQChi innerPair272Input
    leaf5504InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5504LowerChecked :
    lowerCheck 24 leaf5504Box leaf5504Inputs = true := by
  rfl'

private theorem leaf5504CoversExact : CoversExact 8
    leaf5504Box leaf5504Certificate leaf5504InnerLog leaf5504Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk169RoundedFacts chi300RoundedFacts
    innerPair272RoundedFacts leaf5504RoundedFacts (by rfl)

private theorem leaf5504FlatSound : Sound leaf5504Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5504CertificateValid
    leaf5504InnerLogValid leaf5504CoversExact leaf5504LowerChecked

private noncomputable def leaf5505Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (45/128), chiHi := (91/256) }

private noncomputable def leaf5505Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871337/536870912) }, vSqrt := { lower := (8191/8192), upper := (1108345889/1108286976) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1250481201/1073741824) }, upper := { exponent := 1, mantissa := (9647/8192) } }, logOuter := sk170LogOuterCertificate, logK := sk170LogKCertificate, logChi := chi299LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (2216632865/2216573952) } }, logDArg := sk170LogDArgCertificate }

private noncomputable def leaf5505InnerLog : WideLogData :=
  innerPair566Data

set_option maxRecDepth 1000000 in
private theorem leaf5505LocalValidity :
    LeafFacts leaf5505Box leaf5505Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5505Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (1108345889/1108286976) }) = true
      norm_num [leaf5505Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5505CertificateValid :
    WideCertificateValid leaf5505Box leaf5505Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk170ValidityFacts chi299ValidityFacts
    leaf5505LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5505CoverageChecked :
    coverageCheck (innerAD leaf5505Box) leaf5505InnerLog = true := by
  rfl'

private theorem leaf5505InnerLogValid :
    leaf5505InnerLog.Valid 8 (innerAD leaf5505Box) :=
  wideLogDataValid_of_cachedCheck endpoint296PositiveFacts
    endpoint299PositiveFacts.valid leaf5505CoverageChecked

private noncomputable def leaf5505InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629527/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5505InputLogOnePlusV_eq :
    leaf5505InputLogOnePlusV = outerEnclosure 24
      (leaf5505Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5505RoundedFacts : LeafRoundedFacts 8
    leaf5505Certificate.logOnePlusV leaf5505InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5505InputLogOnePlusV_eq }

private noncomputable def leaf5505Inputs : Inputs :=
  inputsOfCaches globalInput sk170RoundedInputs
    chi299InputQChi innerPair566Input
    leaf5505InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5505LowerChecked :
    lowerCheck 24 leaf5505Box leaf5505Inputs = true := by
  rfl'

private theorem leaf5505CoversExact : CoversExact 8
    leaf5505Box leaf5505Certificate leaf5505InnerLog leaf5505Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk170RoundedFacts chi299RoundedFacts
    innerPair566RoundedFacts leaf5505RoundedFacts (by rfl)

private theorem leaf5505FlatSound : Sound leaf5505Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5505CertificateValid
    leaf5505InnerLogValid leaf5505CoversExact leaf5505LowerChecked

private noncomputable def leaf5506Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (91/256), chiHi := (23/64) }

private noncomputable def leaf5506Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871339/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356865024) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1258410571/1073741824) }, upper := { exponent := 1, mantissa := (2427/2048) } }, logOuter := sk170LogOuterCertificate, logK := sk170LogKCertificate, logChi := chi300LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715587583/68713730048) } }, logDArg := sk170LogDArgCertificate }

private noncomputable def leaf5506InnerLog : WideLogData :=
  innerPair272Data

set_option maxRecDepth 1000000 in
private theorem leaf5506LocalValidity :
    LeafFacts leaf5506Box leaf5506Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5506Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356865024) }) = true
      norm_num [leaf5506Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5506CertificateValid :
    WideCertificateValid leaf5506Box leaf5506Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk170ValidityFacts chi300ValidityFacts
    leaf5506LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5506CoverageChecked :
    coverageCheck (innerAD leaf5506Box) leaf5506InnerLog = true := by
  rfl'

private theorem leaf5506InnerLogValid :
    leaf5506InnerLog.Valid 8 (innerAD leaf5506Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint77PositiveFacts.valid leaf5506CoverageChecked

private noncomputable def leaf5506InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814767/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5506InputLogOnePlusV_eq :
    leaf5506InputLogOnePlusV = outerEnclosure 24
      (leaf5506Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5506RoundedFacts : LeafRoundedFacts 8
    leaf5506Certificate.logOnePlusV leaf5506InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5506InputLogOnePlusV_eq }

private noncomputable def leaf5506Inputs : Inputs :=
  inputsOfCaches globalInput sk170RoundedInputs
    chi300InputQChi innerPair272Input
    leaf5506InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5506LowerChecked :
    lowerCheck 24 leaf5506Box leaf5506Inputs = true := by
  rfl'

private theorem leaf5506CoversExact : CoversExact 8
    leaf5506Box leaf5506Certificate leaf5506InnerLog leaf5506Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk170RoundedFacts chi300RoundedFacts
    innerPair272RoundedFacts leaf5506RoundedFacts (by rfl)

private theorem leaf5506FlatSound : Sound leaf5506Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5506CertificateValid
    leaf5506InnerLogValid leaf5506CoversExact leaf5506LowerChecked

private noncomputable def leaf5507Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (11/32), chiHi := (89/256) }

private noncomputable def leaf5507Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871335/536870912) }, vSqrt := { lower := (8191/8192), upper := (1108345889/1108288256) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1240389275/1073741824) }, upper := { exponent := 1, mantissa := (19139/16384) } }, logOuter := sk171LogOuterCertificate, logK := sk171LogKCertificate, logChi := chi297LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (2216634145/2216576512) } }, logDArg := sk171LogDArgCertificate }

private noncomputable def leaf5507InnerLog : WideLogData :=
  innerPair581Data

set_option maxRecDepth 1000000 in
private theorem leaf5507LocalValidity :
    LeafFacts leaf5507Box leaf5507Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5507Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (1108345889/1108288256) }) = true
      norm_num [leaf5507Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5507CertificateValid :
    WideCertificateValid leaf5507Box leaf5507Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk171ValidityFacts chi297ValidityFacts
    leaf5507LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5507CoverageChecked :
    coverageCheck (innerAD leaf5507Box) leaf5507InnerLog = true := by
  rfl'

private theorem leaf5507InnerLogValid :
    leaf5507InnerLog.Valid 8 (innerAD leaf5507Box) :=
  wideLogDataValid_of_cachedCheck endpoint302PositiveFacts
    endpoint306PositiveFacts.valid leaf5507CoverageChecked

private noncomputable def leaf5507InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629517/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5507InputLogOnePlusV_eq :
    leaf5507InputLogOnePlusV = outerEnclosure 24
      (leaf5507Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5507RoundedFacts : LeafRoundedFacts 8
    leaf5507Certificate.logOnePlusV leaf5507InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5507InputLogOnePlusV_eq }

private noncomputable def leaf5507Inputs : Inputs :=
  inputsOfCaches globalInput sk171RoundedInputs
    chi297InputQChi innerPair581Input
    leaf5507InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5507LowerChecked :
    lowerCheck 24 leaf5507Box leaf5507Inputs = true := by
  rfl'

private theorem leaf5507CoversExact : CoversExact 8
    leaf5507Box leaf5507Certificate leaf5507InnerLog leaf5507Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk171RoundedFacts chi297RoundedFacts
    innerPair581RoundedFacts leaf5507RoundedFacts (by rfl)

private theorem leaf5507FlatSound : Sound leaf5507Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5507CertificateValid
    leaf5507InnerLogValid leaf5507CoversExact leaf5507LowerChecked

private noncomputable def leaf5508Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (89/256), chiHi := (45/128) }

private noncomputable def leaf5508Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871337/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356904448) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1248384177/1073741824) }, upper := { exponent := 1, mantissa := (9631/8192) } }, logOuter := sk171LogOuterCertificate, logK := sk171LogKCertificate, logChi := chi298LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715627007/68713808896) } }, logDArg := sk171LogDArgCertificate }

private noncomputable def leaf5508InnerLog : WideLogData :=
  innerPair277Data

set_option maxRecDepth 1000000 in
private theorem leaf5508LocalValidity :
    LeafFacts leaf5508Box leaf5508Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5508Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356904448) }) = true
      norm_num [leaf5508Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5508CertificateValid :
    WideCertificateValid leaf5508Box leaf5508Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk171ValidityFacts chi298ValidityFacts
    leaf5508LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5508CoverageChecked :
    coverageCheck (innerAD leaf5508Box) leaf5508InnerLog = true := by
  rfl'

private theorem leaf5508InnerLogValid :
    leaf5508InnerLog.Valid 8 (innerAD leaf5508Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint299PositiveFacts.valid leaf5508CoverageChecked

private noncomputable def leaf5508InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629525/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5508InputLogOnePlusV_eq :
    leaf5508InputLogOnePlusV = outerEnclosure 24
      (leaf5508Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5508RoundedFacts : LeafRoundedFacts 8
    leaf5508Certificate.logOnePlusV leaf5508InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5508InputLogOnePlusV_eq }

private noncomputable def leaf5508Inputs : Inputs :=
  inputsOfCaches globalInput sk171RoundedInputs
    chi298InputQChi innerPair277Input
    leaf5508InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5508LowerChecked :
    lowerCheck 24 leaf5508Box leaf5508Inputs = true := by
  rfl'

private theorem leaf5508CoversExact : CoversExact 8
    leaf5508Box leaf5508Certificate leaf5508InnerLog leaf5508Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk171RoundedFacts chi298RoundedFacts
    innerPair277RoundedFacts leaf5508RoundedFacts (by rfl)

private theorem leaf5508FlatSound : Sound leaf5508Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5508CertificateValid
    leaf5508InnerLogValid leaf5508CoversExact leaf5508LowerChecked

private noncomputable def leaf5509Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (11/32), chiHi := (89/256) }

private noncomputable def leaf5509Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871337/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356913152) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1246156089/1073741824) }, upper := { exponent := 1, mantissa := (4807/4096) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi297LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715635711/68713826304) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf5509InnerLog : WideLogData :=
  innerPair654Data

set_option maxRecDepth 1000000 in
private theorem leaf5509LocalValidity :
    LeafFacts leaf5509Box leaf5509Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5509Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356913152) }) = true
      norm_num [leaf5509Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5509CertificateValid :
    WideCertificateValid leaf5509Box leaf5509Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi297ValidityFacts
    leaf5509LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5509CoverageChecked :
    coverageCheck (innerAD leaf5509Box) leaf5509InnerLog = true := by
  rfl'

private theorem leaf5509InnerLogValid :
    leaf5509InnerLog.Valid 8 (innerAD leaf5509Box) :=
  wideLogDataValid_of_cachedCheck endpoint398PositiveFacts
    endpoint399PositiveFacts.valid leaf5509CoverageChecked

private noncomputable def leaf5509InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629523/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5509InputLogOnePlusV_eq :
    leaf5509InputLogOnePlusV = outerEnclosure 24
      (leaf5509Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5509RoundedFacts : LeafRoundedFacts 8
    leaf5509Certificate.logOnePlusV leaf5509InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5509InputLogOnePlusV_eq }

private noncomputable def leaf5509Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi297InputQChi innerPair654Input
    leaf5509InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5509LowerChecked :
    lowerCheck 24 leaf5509Box leaf5509Inputs = true := by
  rfl'

private theorem leaf5509CoversExact : CoversExact 8
    leaf5509Box leaf5509Certificate leaf5509InnerLog leaf5509Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi297RoundedFacts
    innerPair654RoundedFacts leaf5509RoundedFacts (by rfl)

private theorem leaf5509FlatSound : Sound leaf5509Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5509CertificateValid
    leaf5509InnerLogValid leaf5509CoversExact leaf5509LowerChecked

private noncomputable def leaf5510Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (89/256), chiHi := (45/128) }

private noncomputable def leaf5510Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871339/536870912) }, vSqrt := { lower := (8191/8192), upper := (2021101327/2020993024) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1254216523/1073741824) }, upper := { exponent := 1, mantissa := (2419/2048) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi298LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (4042094351/4041986048) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf5510InnerLog : WideLogData :=
  innerPair656Data

set_option maxRecDepth 1000000 in
private theorem leaf5510LocalValidity :
    LeafFacts leaf5510Box leaf5510Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5510Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (2021101327/2020993024) }) = true
      norm_num [leaf5510Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5510CertificateValid :
    WideCertificateValid leaf5510Box leaf5510Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi298ValidityFacts
    leaf5510LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5510CoverageChecked :
    coverageCheck (innerAD leaf5510Box) leaf5510InnerLog = true := by
  rfl'

private theorem leaf5510InnerLogValid :
    leaf5510InnerLog.Valid 8 (innerAD leaf5510Box) :=
  wideLogDataValid_of_cachedCheck endpoint400PositiveFacts
    endpoint303PositiveFacts.valid leaf5510CoverageChecked

private noncomputable def leaf5510InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814765/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5510InputLogOnePlusV_eq :
    leaf5510InputLogOnePlusV = outerEnclosure 24
      (leaf5510Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5510RoundedFacts : LeafRoundedFacts 8
    leaf5510Certificate.logOnePlusV leaf5510InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5510InputLogOnePlusV_eq }

private noncomputable def leaf5510Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi298InputQChi innerPair656Input
    leaf5510InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5510LowerChecked :
    lowerCheck 24 leaf5510Box leaf5510Inputs = true := by
  rfl'

private theorem leaf5510CoversExact : CoversExact 8
    leaf5510Box leaf5510Certificate leaf5510InnerLog leaf5510Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi298RoundedFacts
    innerPair656RoundedFacts leaf5510RoundedFacts (by rfl)

private theorem leaf5510FlatSound : Sound leaf5510Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5510CertificateValid
    leaf5510InnerLogValid leaf5510CoversExact leaf5510LowerChecked

private noncomputable def leaf5511Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (45/128), chiHi := (91/256) }

private noncomputable def leaf5511Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871339/536870912) }, vSqrt := { lower := (8191/8192), upper := (227541209/227528960) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1256379079/1073741824) }, upper := { exponent := 1, mantissa := (19385/16384) } }, logOuter := sk171LogOuterCertificate, logK := sk171LogKCertificate, logChi := chi299LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (455070169/455057920) } }, logDArg := sk171LogDArgCertificate }

private noncomputable def leaf5511InnerLog : WideLogData :=
  innerPair272Data

set_option maxRecDepth 1000000 in
private theorem leaf5511LocalValidity :
    LeafFacts leaf5511Box leaf5511Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5511Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (227541209/227528960) }) = true
      norm_num [leaf5511Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5511CertificateValid :
    WideCertificateValid leaf5511Box leaf5511Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk171ValidityFacts chi299ValidityFacts
    leaf5511LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5511CoverageChecked :
    coverageCheck (innerAD leaf5511Box) leaf5511InnerLog = true := by
  rfl'

private theorem leaf5511InnerLogValid :
    leaf5511InnerLog.Valid 8 (innerAD leaf5511Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint77PositiveFacts.valid leaf5511CoverageChecked

private noncomputable def leaf5511InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907383/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5511InputLogOnePlusV_eq :
    leaf5511InputLogOnePlusV = outerEnclosure 24
      (leaf5511Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5511RoundedFacts : LeafRoundedFacts 8
    leaf5511Certificate.logOnePlusV leaf5511InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5511InputLogOnePlusV_eq }

private noncomputable def leaf5511Inputs : Inputs :=
  inputsOfCaches globalInput sk171RoundedInputs
    chi299InputQChi innerPair272Input
    leaf5511InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5511LowerChecked :
    lowerCheck 24 leaf5511Box leaf5511Inputs = true := by
  rfl'

private theorem leaf5511CoversExact : CoversExact 8
    leaf5511Box leaf5511Certificate leaf5511InnerLog leaf5511Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk171RoundedFacts chi299RoundedFacts
    innerPair272RoundedFacts leaf5511RoundedFacts (by rfl)

private theorem leaf5511FlatSound : Sound leaf5511Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5511CertificateValid
    leaf5511InnerLogValid leaf5511CoversExact leaf5511LowerChecked

private noncomputable def leaf5512Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (91/256), chiHi := (23/64) }

private noncomputable def leaf5512Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871341/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356841472) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1264373981/1073741824) }, upper := { exponent := 1, mantissa := (4877/4096) } }, logOuter := sk171LogOuterCertificate, logK := sk171LogKCertificate, logChi := chi300LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715564031/68713682944) } }, logDArg := sk171LogDArgCertificate }

private noncomputable def leaf5512InnerLog : WideLogData :=
  innerPair569Data

set_option maxRecDepth 1000000 in
private theorem leaf5512LocalValidity :
    LeafFacts leaf5512Box leaf5512Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5512Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356841472) }) = true
      norm_num [leaf5512Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5512CertificateValid :
    WideCertificateValid leaf5512Box leaf5512Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk171ValidityFacts chi300ValidityFacts
    leaf5512LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5512CoverageChecked :
    coverageCheck (innerAD leaf5512Box) leaf5512InnerLog = true := by
  rfl'

private theorem leaf5512InnerLogValid :
    leaf5512InnerLog.Valid 8 (innerAD leaf5512Box) :=
  wideLogDataValid_of_cachedCheck endpoint297PositiveFacts
    endpoint304PositiveFacts.valid leaf5512CoverageChecked

private noncomputable def leaf5512InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907385/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5512InputLogOnePlusV_eq :
    leaf5512InputLogOnePlusV = outerEnclosure 24
      (leaf5512Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5512RoundedFacts : LeafRoundedFacts 8
    leaf5512Certificate.logOnePlusV leaf5512InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5512InputLogOnePlusV_eq }

private noncomputable def leaf5512Inputs : Inputs :=
  inputsOfCaches globalInput sk171RoundedInputs
    chi300InputQChi innerPair569Input
    leaf5512InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5512LowerChecked :
    lowerCheck 24 leaf5512Box leaf5512Inputs = true := by
  rfl'

private theorem leaf5512CoversExact : CoversExact 8
    leaf5512Box leaf5512Certificate leaf5512InnerLog leaf5512Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk171RoundedFacts chi300RoundedFacts
    innerPair569RoundedFacts leaf5512RoundedFacts (by rfl)

private theorem leaf5512FlatSound : Sound leaf5512Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5512CertificateValid
    leaf5512InnerLogValid leaf5512CoversExact leaf5512LowerChecked

private noncomputable def leaf5513Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (45/128), chiHi := (91/256) }

private noncomputable def leaf5513Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871341/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356849664) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1262276957/1073741824) }, upper := { exponent := 1, mantissa := (4869/4096) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi299LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715572223/68713699328) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf5513InnerLog : WideLogData :=
  innerPair655Data

set_option maxRecDepth 1000000 in
private theorem leaf5513LocalValidity :
    LeafFacts leaf5513Box leaf5513Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5513Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356849664) }) = true
      norm_num [leaf5513Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5513CertificateValid :
    WideCertificateValid leaf5513Box leaf5513Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi299ValidityFacts
    leaf5513LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5513CoverageChecked :
    coverageCheck (innerAD leaf5513Box) leaf5513InnerLog = true := by
  rfl'

private theorem leaf5513InnerLogValid :
    leaf5513InnerLog.Valid 8 (innerAD leaf5513Box) :=
  wideLogDataValid_of_cachedCheck endpoint399PositiveFacts
    endpoint401PositiveFacts.valid leaf5513CoverageChecked

private noncomputable def leaf5513InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814769/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5513InputLogOnePlusV_eq :
    leaf5513InputLogOnePlusV = outerEnclosure 24
      (leaf5513Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5513RoundedFacts : LeafRoundedFacts 8
    leaf5513Certificate.logOnePlusV leaf5513InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5513InputLogOnePlusV_eq }

private noncomputable def leaf5513Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi299InputQChi innerPair655Input
    leaf5513InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5513LowerChecked :
    lowerCheck 24 leaf5513Box leaf5513Inputs = true := by
  rfl'

private theorem leaf5513CoversExact : CoversExact 8
    leaf5513Box leaf5513Certificate leaf5513InnerLog leaf5513Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi299RoundedFacts
    innerPair655RoundedFacts leaf5513RoundedFacts (by rfl)

private theorem leaf5513FlatSound : Sound leaf5513Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5513CertificateValid
    leaf5513InnerLogValid leaf5513CoversExact leaf5513LowerChecked

private noncomputable def leaf5514Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (91/256), chiHi := (23/64) }

private noncomputable def leaf5514Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871343/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356817920) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1270337391/1073741824) }, upper := { exponent := 1, mantissa := (1225/1024) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi300LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715540479/68713635840) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf5514InnerLog : WideLogData :=
  innerPair582Data

set_option maxRecDepth 1000000 in
private theorem leaf5514LocalValidity :
    LeafFacts leaf5514Box leaf5514Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5514Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356817920) }) = true
      norm_num [leaf5514Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5514CertificateValid :
    WideCertificateValid leaf5514Box leaf5514Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi300ValidityFacts
    leaf5514LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5514CoverageChecked :
    coverageCheck (innerAD leaf5514Box) leaf5514InnerLog = true := by
  rfl'

private theorem leaf5514InnerLogValid :
    leaf5514InnerLog.Valid 8 (innerAD leaf5514Box) :=
  wideLogDataValid_of_cachedCheck endpoint303PositiveFacts
    endpoint402PositiveFacts.valid leaf5514CoverageChecked

private noncomputable def leaf5514InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814773/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5514InputLogOnePlusV_eq :
    leaf5514InputLogOnePlusV = outerEnclosure 24
      (leaf5514Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5514RoundedFacts : LeafRoundedFacts 8
    leaf5514Certificate.logOnePlusV leaf5514InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5514InputLogOnePlusV_eq }

private noncomputable def leaf5514Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi300InputQChi innerPair582Input
    leaf5514InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5514LowerChecked :
    lowerCheck 24 leaf5514Box leaf5514Inputs = true := by
  rfl'

private theorem leaf5514CoversExact : CoversExact 8
    leaf5514Box leaf5514Certificate leaf5514InnerLog leaf5514Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi300RoundedFacts
    innerPair582RoundedFacts leaf5514RoundedFacts (by rfl)

private theorem leaf5514FlatSound : Sound leaf5514Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5514CertificateValid
    leaf5514InnerLogValid leaf5514CoversExact leaf5514LowerChecked

private noncomputable def leaf5515Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (23/64), chiHi := (93/256) }

private noncomputable def leaf5515Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871339/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356857600) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1260310999/1073741824) }, upper := { exponent := 1, mantissa := (19445/16384) } }, logOuter := sk169LogOuterCertificate, logK := sk169LogKCertificate, logChi := chi301LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715580159/68713715200) } }, logDArg := sk169LogDArgCertificate }

private noncomputable def leaf5515InnerLog : WideLogData :=
  innerPair272Data

set_option maxRecDepth 1000000 in
private theorem leaf5515LocalValidity :
    LeafFacts leaf5515Box leaf5515Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5515Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356857600) }) = true
      norm_num [leaf5515Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5515CertificateValid :
    WideCertificateValid leaf5515Box leaf5515Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk169ValidityFacts chi301ValidityFacts
    leaf5515LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5515CoverageChecked :
    coverageCheck (innerAD leaf5515Box) leaf5515InnerLog = true := by
  rfl'

private theorem leaf5515InnerLogValid :
    leaf5515InnerLog.Valid 8 (innerAD leaf5515Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint77PositiveFacts.valid leaf5515CoverageChecked

private noncomputable def leaf5515InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (363423/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf5515InputLogOnePlusV_eq :
    leaf5515InputLogOnePlusV = outerEnclosure 24
      (leaf5515Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5515RoundedFacts : LeafRoundedFacts 8
    leaf5515Certificate.logOnePlusV leaf5515InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5515InputLogOnePlusV_eq }

private noncomputable def leaf5515Inputs : Inputs :=
  inputsOfCaches globalInput sk169RoundedInputs
    chi301InputQChi innerPair272Input
    leaf5515InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5515LowerChecked :
    lowerCheck 24 leaf5515Box leaf5515Inputs = true := by
  rfl'

private theorem leaf5515CoversExact : CoversExact 8
    leaf5515Box leaf5515Certificate leaf5515InnerLog leaf5515Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk169RoundedFacts chi301RoundedFacts
    innerPair272RoundedFacts leaf5515RoundedFacts (by rfl)

private theorem leaf5515FlatSound : Sound leaf5515Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5515CertificateValid
    leaf5515InnerLogValid leaf5515CoversExact leaf5515LowerChecked

private noncomputable def leaf5516Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (93/256), chiHi := (47/128) }

private noncomputable def leaf5516Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871341/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356826624) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1268174837/1073741824) }, upper := { exponent := 1, mantissa := (9783/8192) } }, logOuter := sk169LogOuterCertificate, logK := sk169LogKCertificate, logChi := chi302LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715549183/68713653248) } }, logDArg := sk169LogDArgCertificate }

private noncomputable def leaf5516InnerLog : WideLogData :=
  innerPair575Data

set_option maxRecDepth 1000000 in
private theorem leaf5516LocalValidity :
    LeafFacts leaf5516Box leaf5516Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5516Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356826624) }) = true
      norm_num [leaf5516Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5516CertificateValid :
    WideCertificateValid leaf5516Box leaf5516Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk169ValidityFacts chi302ValidityFacts
    leaf5516LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5516CoverageChecked :
    coverageCheck (innerAD leaf5516Box) leaf5516InnerLog = true := by
  rfl'

private theorem leaf5516InnerLogValid :
    leaf5516InnerLog.Valid 8 (innerAD leaf5516Box) :=
  wideLogDataValid_of_cachedCheck endpoint299PositiveFacts
    endpoint304PositiveFacts.valid leaf5516CoverageChecked

private noncomputable def leaf5516InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453693/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf5516InputLogOnePlusV_eq :
    leaf5516InputLogOnePlusV = outerEnclosure 24
      (leaf5516Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5516RoundedFacts : LeafRoundedFacts 8
    leaf5516Certificate.logOnePlusV leaf5516InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5516InputLogOnePlusV_eq }

private noncomputable def leaf5516Inputs : Inputs :=
  inputsOfCaches globalInput sk169RoundedInputs
    chi302InputQChi innerPair575Input
    leaf5516InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5516LowerChecked :
    lowerCheck 24 leaf5516Box leaf5516Inputs = true := by
  rfl'

private theorem leaf5516CoversExact : CoversExact 8
    leaf5516Box leaf5516Certificate leaf5516InnerLog leaf5516Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk169RoundedFacts chi302RoundedFacts
    innerPair575RoundedFacts leaf5516RoundedFacts (by rfl)

private theorem leaf5516FlatSound : Sound leaf5516Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5516CertificateValid
    leaf5516InnerLogValid leaf5516CoversExact leaf5516LowerChecked

private noncomputable def leaf5517Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (23/64), chiHi := (93/256) }

private noncomputable def leaf5517Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871341/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356833792) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1266339941/1073741824) }, upper := { exponent := 1, mantissa := (9769/8192) } }, logOuter := sk170LogOuterCertificate, logK := sk170LogKCertificate, logChi := chi301LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715556351/68713667584) } }, logDArg := sk170LogDArgCertificate }

private noncomputable def leaf5517InnerLog : WideLogData :=
  innerPair569Data

set_option maxRecDepth 1000000 in
private theorem leaf5517LocalValidity :
    LeafFacts leaf5517Box leaf5517Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5517Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356833792) }) = true
      norm_num [leaf5517Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5517CertificateValid :
    WideCertificateValid leaf5517Box leaf5517Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk170ValidityFacts chi301ValidityFacts
    leaf5517LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5517CoverageChecked :
    coverageCheck (innerAD leaf5517Box) leaf5517InnerLog = true := by
  rfl'

private theorem leaf5517InnerLogValid :
    leaf5517InnerLog.Valid 8 (innerAD leaf5517Box) :=
  wideLogDataValid_of_cachedCheck endpoint297PositiveFacts
    endpoint304PositiveFacts.valid leaf5517CoverageChecked

private noncomputable def leaf5517InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814771/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5517InputLogOnePlusV_eq :
    leaf5517InputLogOnePlusV = outerEnclosure 24
      (leaf5517Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5517RoundedFacts : LeafRoundedFacts 8
    leaf5517Certificate.logOnePlusV leaf5517InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5517InputLogOnePlusV_eq }

private noncomputable def leaf5517Inputs : Inputs :=
  inputsOfCaches globalInput sk170RoundedInputs
    chi301InputQChi innerPair569Input
    leaf5517InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5517LowerChecked :
    lowerCheck 24 leaf5517Box leaf5517Inputs = true := by
  rfl'

private theorem leaf5517CoversExact : CoversExact 8
    leaf5517Box leaf5517Certificate leaf5517InnerLog leaf5517Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk170RoundedFacts chi301RoundedFacts
    innerPair569RoundedFacts leaf5517RoundedFacts (by rfl)

private theorem leaf5517FlatSound : Sound leaf5517Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5517CertificateValid
    leaf5517InnerLogValid leaf5517CoversExact leaf5517LowerChecked

private noncomputable def leaf5518Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (93/256), chiHi := (47/128) }

private noncomputable def leaf5518Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871343/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356802560) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1274269311/1073741824) }, upper := { exponent := 1, mantissa := (4915/4096) } }, logOuter := sk170LogOuterCertificate, logK := sk170LogKCertificate, logChi := chi302LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715525119/68713605120) } }, logDArg := sk170LogDArgCertificate }

private noncomputable def leaf5518InnerLog : WideLogData :=
  innerPair576Data

set_option maxRecDepth 1000000 in
private theorem leaf5518LocalValidity :
    LeafFacts leaf5518Box leaf5518Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5518Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356802560) }) = true
      norm_num [leaf5518Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5518CertificateValid :
    WideCertificateValid leaf5518Box leaf5518Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk170ValidityFacts chi302ValidityFacts
    leaf5518LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5518CoverageChecked :
    coverageCheck (innerAD leaf5518Box) leaf5518InnerLog = true := by
  rfl'

private theorem leaf5518InnerLogValid :
    leaf5518InnerLog.Valid 8 (innerAD leaf5518Box) :=
  wideLogDataValid_of_cachedCheck endpoint299PositiveFacts
    endpoint305PositiveFacts.valid leaf5518CoverageChecked

private noncomputable def leaf5518InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814775/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5518InputLogOnePlusV_eq :
    leaf5518InputLogOnePlusV = outerEnclosure 24
      (leaf5518Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5518RoundedFacts : LeafRoundedFacts 8
    leaf5518Certificate.logOnePlusV leaf5518InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5518InputLogOnePlusV_eq }

private noncomputable def leaf5518Inputs : Inputs :=
  inputsOfCaches globalInput sk170RoundedInputs
    chi302InputQChi innerPair576Input
    leaf5518InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5518LowerChecked :
    lowerCheck 24 leaf5518Box leaf5518Inputs = true := by
  rfl'

private theorem leaf5518CoversExact : CoversExact 8
    leaf5518Box leaf5518Certificate leaf5518InnerLog leaf5518Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk170RoundedFacts chi302RoundedFacts
    innerPair576RoundedFacts leaf5518RoundedFacts (by rfl)

private theorem leaf5518FlatSound : Sound leaf5518Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5518CertificateValid
    leaf5518InnerLogValid leaf5518CoversExact leaf5518LowerChecked

private noncomputable def leaf5519Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (47/128), chiHi := (95/256) }

private noncomputable def leaf5519Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871343/536870912) }, vSqrt := { lower := (8191/8192), upper := (32505887/32504064) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1276038675/1073741824) }, upper := { exponent := 1, mantissa := (19687/16384) } }, logOuter := sk169LogOuterCertificate, logK := sk169LogKCertificate, logChi := chi303LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (65009951/65008128) } }, logDArg := sk169LogDArgCertificate }

private noncomputable def leaf5519InnerLog : WideLogData :=
  innerPair282Data

set_option maxRecDepth 1000000 in
private theorem leaf5519LocalValidity :
    LeafFacts leaf5519Box leaf5519Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5519Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (32505887/32504064) }) = true
      norm_num [leaf5519Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5519CertificateValid :
    WideCertificateValid leaf5519Box leaf5519Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk169ValidityFacts chi303ValidityFacts
    leaf5519LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5519CoverageChecked :
    coverageCheck (innerAD leaf5519Box) leaf5519InnerLog = true := by
  rfl'

private theorem leaf5519InnerLogValid :
    leaf5519InnerLog.Valid 8 (innerAD leaf5519Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint305PositiveFacts.valid leaf5519CoverageChecked

private noncomputable def leaf5519InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629551/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5519InputLogOnePlusV_eq :
    leaf5519InputLogOnePlusV = outerEnclosure 24
      (leaf5519Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5519RoundedFacts : LeafRoundedFacts 8
    leaf5519Certificate.logOnePlusV leaf5519InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5519InputLogOnePlusV_eq }

private noncomputable def leaf5519Inputs : Inputs :=
  inputsOfCaches globalInput sk169RoundedInputs
    chi303InputQChi innerPair282Input
    leaf5519InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5519LowerChecked :
    lowerCheck 24 leaf5519Box leaf5519Inputs = true := by
  rfl'

private theorem leaf5519CoversExact : CoversExact 8
    leaf5519Box leaf5519Certificate leaf5519InnerLog leaf5519Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk169RoundedFacts chi303RoundedFacts
    innerPair282RoundedFacts leaf5519RoundedFacts (by rfl)

private theorem leaf5519FlatSound : Sound leaf5519Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5519CertificateValid
    leaf5519InnerLogValid leaf5519CoversExact leaf5519LowerChecked

private noncomputable def leaf5520Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (95/256), chiHi := (3/8) }

private noncomputable def leaf5520Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871345/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356764672) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1283902513/1073741824) }, upper := { exponent := 1, mantissa := (619/512) } }, logOuter := sk169LogOuterCertificate, logK := sk169LogKCertificate, logChi := chi304LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715487231/68713529344) } }, logDArg := sk169LogDArgCertificate }

private noncomputable def leaf5520InnerLog : WideLogData :=
  innerPair278Data

set_option maxRecDepth 1000000 in
private theorem leaf5520LocalValidity :
    LeafFacts leaf5520Box leaf5520Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5520Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356764672) }) = true
      norm_num [leaf5520Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5520CertificateValid :
    WideCertificateValid leaf5520Box leaf5520Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk169ValidityFacts chi304ValidityFacts
    leaf5520LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5520CoverageChecked :
    coverageCheck (innerAD leaf5520Box) leaf5520InnerLog = true := by
  rfl'

private theorem leaf5520InnerLogValid :
    leaf5520InnerLog.Valid 8 (innerAD leaf5520Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint78PositiveFacts.valid leaf5520CoverageChecked

private noncomputable def leaf5520InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629559/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5520InputLogOnePlusV_eq :
    leaf5520InputLogOnePlusV = outerEnclosure 24
      (leaf5520Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5520RoundedFacts : LeafRoundedFacts 8
    leaf5520Certificate.logOnePlusV leaf5520InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5520InputLogOnePlusV_eq }

private noncomputable def leaf5520Inputs : Inputs :=
  inputsOfCaches globalInput sk169RoundedInputs
    chi304InputQChi innerPair278Input
    leaf5520InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5520LowerChecked :
    lowerCheck 24 leaf5520Box leaf5520Inputs = true := by
  rfl'

private theorem leaf5520CoversExact : CoversExact 8
    leaf5520Box leaf5520Certificate leaf5520InnerLog leaf5520Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk169RoundedFacts chi304RoundedFacts
    innerPair278RoundedFacts leaf5520RoundedFacts (by rfl)

private theorem leaf5520FlatSound : Sound leaf5520Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5520CertificateValid
    leaf5520InnerLogValid leaf5520CoversExact leaf5520LowerChecked

private noncomputable def leaf5521Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (47/128), chiHi := (95/256) }

private noncomputable def leaf5521Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871345/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356771328) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1282198681/1073741824) }, upper := { exponent := 1, mantissa := (9891/8192) } }, logOuter := sk170LogOuterCertificate, logK := sk170LogKCertificate, logChi := chi303LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715493887/68713542656) } }, logDArg := sk170LogDArgCertificate }

private noncomputable def leaf5521InnerLog : WideLogData :=
  innerPair278Data

set_option maxRecDepth 1000000 in
private theorem leaf5521LocalValidity :
    LeafFacts leaf5521Box leaf5521Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5521Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356771328) }) = true
      norm_num [leaf5521Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5521CertificateValid :
    WideCertificateValid leaf5521Box leaf5521Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk170ValidityFacts chi303ValidityFacts
    leaf5521LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5521CoverageChecked :
    coverageCheck (innerAD leaf5521Box) leaf5521InnerLog = true := by
  rfl'

private theorem leaf5521InnerLogValid :
    leaf5521InnerLog.Valid 8 (innerAD leaf5521Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint78PositiveFacts.valid leaf5521CoverageChecked

private noncomputable def leaf5521InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629557/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5521InputLogOnePlusV_eq :
    leaf5521InputLogOnePlusV = outerEnclosure 24
      (leaf5521Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5521RoundedFacts : LeafRoundedFacts 8
    leaf5521Certificate.logOnePlusV leaf5521InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5521InputLogOnePlusV_eq }

private noncomputable def leaf5521Inputs : Inputs :=
  inputsOfCaches globalInput sk170RoundedInputs
    chi303InputQChi innerPair278Input
    leaf5521InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5521LowerChecked :
    lowerCheck 24 leaf5521Box leaf5521Inputs = true := by
  rfl'

private theorem leaf5521CoversExact : CoversExact 8
    leaf5521Box leaf5521Certificate leaf5521InnerLog leaf5521Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk170RoundedFacts chi303RoundedFacts
    innerPair278RoundedFacts leaf5521RoundedFacts (by rfl)

private theorem leaf5521FlatSound : Sound leaf5521Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5521CertificateValid
    leaf5521InnerLogValid leaf5521CoversExact leaf5521LowerChecked

private noncomputable def leaf5522Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (95/256), chiHi := (3/8) }

private noncomputable def leaf5522Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871347/536870912) }, vSqrt := { lower := (8191/8192), upper := (4908388937/4908105728) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1290128051/1073741824) }, upper := { exponent := 1, mantissa := (311/256) } }, logOuter := sk170LogOuterCertificate, logK := sk170LogKCertificate, logChi := chi304LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (9816494665/9816211456) } }, logDArg := sk170LogDArgCertificate }

private noncomputable def leaf5522InnerLog : WideLogData :=
  innerPair278Data

set_option maxRecDepth 1000000 in
private theorem leaf5522LocalValidity :
    LeafFacts leaf5522Box leaf5522Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5522Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4908388937/4908105728) }) = true
      norm_num [leaf5522Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5522CertificateValid :
    WideCertificateValid leaf5522Box leaf5522Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk170ValidityFacts chi304ValidityFacts
    leaf5522LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5522CoverageChecked :
    coverageCheck (innerAD leaf5522Box) leaf5522InnerLog = true := by
  rfl'

private theorem leaf5522InnerLogValid :
    leaf5522InnerLog.Valid 8 (innerAD leaf5522Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint78PositiveFacts.valid leaf5522CoverageChecked

private noncomputable def leaf5522InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629565/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5522InputLogOnePlusV_eq :
    leaf5522InputLogOnePlusV = outerEnclosure 24
      (leaf5522Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5522RoundedFacts : LeafRoundedFacts 8
    leaf5522Certificate.logOnePlusV leaf5522InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5522InputLogOnePlusV_eq }

private noncomputable def leaf5522Inputs : Inputs :=
  inputsOfCaches globalInput sk170RoundedInputs
    chi304InputQChi innerPair278Input
    leaf5522InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5522LowerChecked :
    lowerCheck 24 leaf5522Box leaf5522Inputs = true := by
  rfl'

private theorem leaf5522CoversExact : CoversExact 8
    leaf5522Box leaf5522Certificate leaf5522InnerLog leaf5522Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk170RoundedFacts chi304RoundedFacts
    innerPair278RoundedFacts leaf5522RoundedFacts (by rfl)

private theorem leaf5522FlatSound : Sound leaf5522Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5522CertificateValid
    leaf5522InnerLogValid leaf5522CoversExact leaf5522LowerChecked

private noncomputable def leaf5523Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (23/64), chiHi := (93/256) }

private noncomputable def leaf5523Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871343/536870912) }, vSqrt := { lower := (8191/8192), upper := (4908388937/4908115712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1272368883/1073741824) }, upper := { exponent := 1, mantissa := (19631/16384) } }, logOuter := sk171LogOuterCertificate, logK := sk171LogKCertificate, logChi := chi301LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (9816504649/9816231424) } }, logDArg := sk171LogDArgCertificate }

private noncomputable def leaf5523InnerLog : WideLogData :=
  innerPair576Data

set_option maxRecDepth 1000000 in
private theorem leaf5523LocalValidity :
    LeafFacts leaf5523Box leaf5523Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5523Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4908388937/4908115712) }) = true
      norm_num [leaf5523Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5523CertificateValid :
    WideCertificateValid leaf5523Box leaf5523Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk171ValidityFacts chi301ValidityFacts
    leaf5523LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5523CoverageChecked :
    coverageCheck (innerAD leaf5523Box) leaf5523InnerLog = true := by
  rfl'

private theorem leaf5523InnerLogValid :
    leaf5523InnerLog.Valid 8 (innerAD leaf5523Box) :=
  wideLogDataValid_of_cachedCheck endpoint299PositiveFacts
    endpoint305PositiveFacts.valid leaf5523CoverageChecked

private noncomputable def leaf5523InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907387/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5523InputLogOnePlusV_eq :
    leaf5523InputLogOnePlusV = outerEnclosure 24
      (leaf5523Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5523RoundedFacts : LeafRoundedFacts 8
    leaf5523Certificate.logOnePlusV leaf5523InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5523InputLogOnePlusV_eq }

private noncomputable def leaf5523Inputs : Inputs :=
  inputsOfCaches globalInput sk171RoundedInputs
    chi301InputQChi innerPair576Input
    leaf5523InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5523LowerChecked :
    lowerCheck 24 leaf5523Box leaf5523Inputs = true := by
  rfl'

private theorem leaf5523CoversExact : CoversExact 8
    leaf5523Box leaf5523Certificate leaf5523InnerLog leaf5523Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk171RoundedFacts chi301RoundedFacts
    innerPair576RoundedFacts leaf5523RoundedFacts (by rfl)

private theorem leaf5523FlatSound : Sound leaf5523Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5523CertificateValid
    leaf5523InnerLogValid leaf5523CoversExact leaf5523LowerChecked

private noncomputable def leaf5524Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (93/256), chiHi := (47/128) }

private noncomputable def leaf5524Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871345/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356778496) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1280363785/1073741824) }, upper := { exponent := 1, mantissa := (9877/8192) } }, logOuter := sk171LogOuterCertificate, logK := sk171LogKCertificate, logChi := chi302LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715501055/68713556992) } }, logDArg := sk171LogDArgCertificate }

private noncomputable def leaf5524InnerLog : WideLogData :=
  innerPair283Data

set_option maxRecDepth 1000000 in
private theorem leaf5524LocalValidity :
    LeafFacts leaf5524Box leaf5524Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5524Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356778496) }) = true
      norm_num [leaf5524Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5524CertificateValid :
    WideCertificateValid leaf5524Box leaf5524Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk171ValidityFacts chi302ValidityFacts
    leaf5524LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5524CoverageChecked :
    coverageCheck (innerAD leaf5524Box) leaf5524InnerLog = true := by
  rfl'

private theorem leaf5524InnerLogValid :
    leaf5524InnerLog.Valid 8 (innerAD leaf5524Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint308PositiveFacts.valid leaf5524CoverageChecked

private noncomputable def leaf5524InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629555/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5524InputLogOnePlusV_eq :
    leaf5524InputLogOnePlusV = outerEnclosure 24
      (leaf5524Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5524RoundedFacts : LeafRoundedFacts 8
    leaf5524Certificate.logOnePlusV leaf5524InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5524InputLogOnePlusV_eq }

private noncomputable def leaf5524Inputs : Inputs :=
  inputsOfCaches globalInput sk171RoundedInputs
    chi302InputQChi innerPair283Input
    leaf5524InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5524LowerChecked :
    lowerCheck 24 leaf5524Box leaf5524Inputs = true := by
  rfl'

private theorem leaf5524CoversExact : CoversExact 8
    leaf5524Box leaf5524Certificate leaf5524InnerLog leaf5524Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk171RoundedFacts chi302RoundedFacts
    innerPair283RoundedFacts leaf5524RoundedFacts (by rfl)

private theorem leaf5524FlatSound : Sound leaf5524Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5524CertificateValid
    leaf5524InnerLogValid leaf5524CoversExact leaf5524LowerChecked

private noncomputable def leaf5525Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (23/64), chiHi := (93/256) }

private noncomputable def leaf5525Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871345/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356786176) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1278397825/1073741824) }, upper := { exponent := 1, mantissa := (4931/4096) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi301LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715508735/68713572352) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf5525InnerLog : WideLogData :=
  innerPair283Data

set_option maxRecDepth 1000000 in
private theorem leaf5525LocalValidity :
    LeafFacts leaf5525Box leaf5525Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5525Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356786176) }) = true
      norm_num [leaf5525Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5525CertificateValid :
    WideCertificateValid leaf5525Box leaf5525Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi301ValidityFacts
    leaf5525LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5525CoverageChecked :
    coverageCheck (innerAD leaf5525Box) leaf5525InnerLog = true := by
  rfl'

private theorem leaf5525InnerLogValid :
    leaf5525InnerLog.Valid 8 (innerAD leaf5525Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint308PositiveFacts.valid leaf5525CoverageChecked

private noncomputable def leaf5525InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814777/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5525InputLogOnePlusV_eq :
    leaf5525InputLogOnePlusV = outerEnclosure 24
      (leaf5525Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5525RoundedFacts : LeafRoundedFacts 8
    leaf5525Certificate.logOnePlusV leaf5525InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5525InputLogOnePlusV_eq }

private noncomputable def leaf5525Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi301InputQChi innerPair283Input
    leaf5525InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5525LowerChecked :
    lowerCheck 24 leaf5525Box leaf5525Inputs = true := by
  rfl'

private theorem leaf5525CoversExact : CoversExact 8
    leaf5525Box leaf5525Certificate leaf5525InnerLog leaf5525Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi301RoundedFacts
    innerPair283RoundedFacts leaf5525RoundedFacts (by rfl)

private theorem leaf5525FlatSound : Sound leaf5525Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5525CertificateValid
    leaf5525InnerLogValid leaf5525CoversExact leaf5525LowerChecked

private noncomputable def leaf5526Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (93/256), chiHi := (47/128) }

private noncomputable def leaf5526Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871347/536870912) }, vSqrt := { lower := (8191/8192), upper := (4908388937/4908107776) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1286458259/1073741824) }, upper := { exponent := 1, mantissa := (2481/2048) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi302LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (9816496713/9816215552) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf5526InnerLog : WideLogData :=
  innerPair278Data

set_option maxRecDepth 1000000 in
private theorem leaf5526LocalValidity :
    LeafFacts leaf5526Box leaf5526Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5526Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4908388937/4908107776) }) = true
      norm_num [leaf5526Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5526CertificateValid :
    WideCertificateValid leaf5526Box leaf5526Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi302ValidityFacts
    leaf5526LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5526CoverageChecked :
    coverageCheck (innerAD leaf5526Box) leaf5526InnerLog = true := by
  rfl'

private theorem leaf5526InnerLogValid :
    leaf5526InnerLog.Valid 8 (innerAD leaf5526Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint78PositiveFacts.valid leaf5526CoverageChecked

private noncomputable def leaf5526InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629561/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5526InputLogOnePlusV_eq :
    leaf5526InputLogOnePlusV = outerEnclosure 24
      (leaf5526Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5526RoundedFacts : LeafRoundedFacts 8
    leaf5526Certificate.logOnePlusV leaf5526InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5526InputLogOnePlusV_eq }

private noncomputable def leaf5526Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi302InputQChi innerPair278Input
    leaf5526InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5526LowerChecked :
    lowerCheck 24 leaf5526Box leaf5526Inputs = true := by
  rfl'

private theorem leaf5526CoversExact : CoversExact 8
    leaf5526Box leaf5526Certificate leaf5526InnerLog leaf5526Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi302RoundedFacts
    innerPair278RoundedFacts leaf5526RoundedFacts (by rfl)

private theorem leaf5526FlatSound : Sound leaf5526Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5526CertificateValid
    leaf5526InnerLogValid leaf5526CoversExact leaf5526LowerChecked

private noncomputable def leaf5527Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (47/128), chiHi := (95/256) }

private noncomputable def leaf5527Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871347/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356747008) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1288358687/1073741824) }, upper := { exponent := 1, mantissa := (19877/16384) } }, logOuter := sk171LogOuterCertificate, logK := sk171LogKCertificate, logChi := chi303LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715469567/68713494016) } }, logDArg := sk171LogDArgCertificate }

private noncomputable def leaf5527InnerLog : WideLogData :=
  innerPair278Data

set_option maxRecDepth 1000000 in
private theorem leaf5527LocalValidity :
    LeafFacts leaf5527Box leaf5527Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5527Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356747008) }) = true
      norm_num [leaf5527Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5527CertificateValid :
    WideCertificateValid leaf5527Box leaf5527Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk171ValidityFacts chi303ValidityFacts
    leaf5527LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5527CoverageChecked :
    coverageCheck (innerAD leaf5527Box) leaf5527InnerLog = true := by
  rfl'

private theorem leaf5527InnerLogValid :
    leaf5527InnerLog.Valid 8 (innerAD leaf5527Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint78PositiveFacts.valid leaf5527CoverageChecked

private noncomputable def leaf5527InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629563/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5527InputLogOnePlusV_eq :
    leaf5527InputLogOnePlusV = outerEnclosure 24
      (leaf5527Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5527RoundedFacts : LeafRoundedFacts 8
    leaf5527Certificate.logOnePlusV leaf5527InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5527InputLogOnePlusV_eq }

private noncomputable def leaf5527Inputs : Inputs :=
  inputsOfCaches globalInput sk171RoundedInputs
    chi303InputQChi innerPair278Input
    leaf5527InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5527LowerChecked :
    lowerCheck 24 leaf5527Box leaf5527Inputs = true := by
  rfl'

private theorem leaf5527CoversExact : CoversExact 8
    leaf5527Box leaf5527Certificate leaf5527InnerLog leaf5527Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk171RoundedFacts chi303RoundedFacts
    innerPair278RoundedFacts leaf5527RoundedFacts (by rfl)

private theorem leaf5527FlatSound : Sound leaf5527Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5527CertificateValid
    leaf5527InnerLogValid leaf5527CoversExact leaf5527LowerChecked

private noncomputable def leaf5528Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (95/256), chiHi := (3/8) }

private noncomputable def leaf5528Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871349/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356715520) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1296353589/1073741824) }, upper := { exponent := 1, mantissa := (625/512) } }, logOuter := sk171LogOuterCertificate, logK := sk171LogKCertificate, logChi := chi304LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715438079/68713431040) } }, logDArg := sk171LogDArgCertificate }

private noncomputable def leaf5528InnerLog : WideLogData :=
  innerPair590Data

set_option maxRecDepth 1000000 in
private theorem leaf5528LocalValidity :
    LeafFacts leaf5528Box leaf5528Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5528Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356715520) }) = true
      norm_num [leaf5528Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5528CertificateValid :
    WideCertificateValid leaf5528Box leaf5528Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk171ValidityFacts chi304ValidityFacts
    leaf5528LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5528CoverageChecked :
    coverageCheck (innerAD leaf5528Box) leaf5528InnerLog = true := by
  rfl'

private theorem leaf5528InnerLogValid :
    leaf5528InnerLog.Valid 8 (innerAD leaf5528Box) :=
  wideLogDataValid_of_cachedCheck endpoint305PositiveFacts
    endpoint403PositiveFacts.valid leaf5528CoverageChecked

private noncomputable def leaf5528InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629571/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5528InputLogOnePlusV_eq :
    leaf5528InputLogOnePlusV = outerEnclosure 24
      (leaf5528Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5528RoundedFacts : LeafRoundedFacts 8
    leaf5528Certificate.logOnePlusV leaf5528InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5528InputLogOnePlusV_eq }

private noncomputable def leaf5528Inputs : Inputs :=
  inputsOfCaches globalInput sk171RoundedInputs
    chi304InputQChi innerPair590Input
    leaf5528InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5528LowerChecked :
    lowerCheck 24 leaf5528Box leaf5528Inputs = true := by
  rfl'

private theorem leaf5528CoversExact : CoversExact 8
    leaf5528Box leaf5528Certificate leaf5528InnerLog leaf5528Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk171RoundedFacts chi304RoundedFacts
    innerPair590RoundedFacts leaf5528RoundedFacts (by rfl)

private theorem leaf5528FlatSound : Sound leaf5528Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5528CertificateValid
    leaf5528InnerLogValid leaf5528CoversExact leaf5528LowerChecked

private noncomputable def leaf5529Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (47/128), chiHi := (95/256) }

private noncomputable def leaf5529Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871349/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356722688) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1294518693/1073741824) }, upper := { exponent := 1, mantissa := (4993/4096) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi303LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715445247/68713445376) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf5529InnerLog : WideLogData :=
  innerPair590Data

set_option maxRecDepth 1000000 in
private theorem leaf5529LocalValidity :
    LeafFacts leaf5529Box leaf5529Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5529Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356722688) }) = true
      norm_num [leaf5529Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5529CertificateValid :
    WideCertificateValid leaf5529Box leaf5529Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi303ValidityFacts
    leaf5529LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5529CoverageChecked :
    coverageCheck (innerAD leaf5529Box) leaf5529InnerLog = true := by
  rfl'

private theorem leaf5529InnerLogValid :
    leaf5529InnerLog.Valid 8 (innerAD leaf5529Box) :=
  wideLogDataValid_of_cachedCheck endpoint305PositiveFacts
    endpoint403PositiveFacts.valid leaf5529CoverageChecked

private noncomputable def leaf5529InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629569/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5529InputLogOnePlusV_eq :
    leaf5529InputLogOnePlusV = outerEnclosure 24
      (leaf5529Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5529RoundedFacts : LeafRoundedFacts 8
    leaf5529Certificate.logOnePlusV leaf5529InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5529InputLogOnePlusV_eq }

private noncomputable def leaf5529Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi303InputQChi innerPair590Input
    leaf5529InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5529LowerChecked :
    lowerCheck 24 leaf5529Box leaf5529Inputs = true := by
  rfl'

private theorem leaf5529CoversExact : CoversExact 8
    leaf5529Box leaf5529Certificate leaf5529InnerLog leaf5529Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi303RoundedFacts
    innerPair590RoundedFacts leaf5529RoundedFacts (by rfl)

private theorem leaf5529FlatSound : Sound leaf5529Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5529CertificateValid
    leaf5529InnerLogValid leaf5529CoversExact leaf5529LowerChecked

private noncomputable def leaf5530Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (95/256), chiHi := (3/8) }

private noncomputable def leaf5530Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871351/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356690944) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1302579127/1073741824) }, upper := { exponent := 1, mantissa := (157/128) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi304LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715413503/68713381888) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf5530InnerLog : WideLogData :=
  innerPair593Data

set_option maxRecDepth 1000000 in
private theorem leaf5530LocalValidity :
    LeafFacts leaf5530Box leaf5530Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5530Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356690944) }) = true
      norm_num [leaf5530Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5530CertificateValid :
    WideCertificateValid leaf5530Box leaf5530Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi304ValidityFacts
    leaf5530LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5530CoverageChecked :
    coverageCheck (innerAD leaf5530Box) leaf5530InnerLog = true := by
  rfl'

private theorem leaf5530InnerLogValid :
    leaf5530InnerLog.Valid 8 (innerAD leaf5530Box) :=
  wideLogDataValid_of_cachedCheck endpoint308PositiveFacts
    endpoint403PositiveFacts.valid leaf5530CoverageChecked

private noncomputable def leaf5530InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629577/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5530InputLogOnePlusV_eq :
    leaf5530InputLogOnePlusV = outerEnclosure 24
      (leaf5530Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5530RoundedFacts : LeafRoundedFacts 8
    leaf5530Certificate.logOnePlusV leaf5530InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5530InputLogOnePlusV_eq }

private noncomputable def leaf5530Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi304InputQChi innerPair593Input
    leaf5530InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5530LowerChecked :
    lowerCheck 24 leaf5530Box leaf5530Inputs = true := by
  rfl'

private theorem leaf5530CoversExact : CoversExact 8
    leaf5530Box leaf5530Certificate leaf5530InnerLog leaf5530Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi304RoundedFacts
    innerPair593RoundedFacts leaf5530RoundedFacts (by rfl)

private theorem leaf5530FlatSound : Sound leaf5530Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5530CertificateValid
    leaf5530InnerLogValid leaf5530CoversExact leaf5530LowerChecked

private noncomputable def component111Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (11/32), chiHi := (45/128) }

set_option maxRecDepth 1000000 in
private theorem component111Node0_sound : Sound component111Node0Box :=
  sound_of_literal_split component111Node0Box leaf5499Box leaf5500Box
    .chi (89/256) (by rfl) (by rfl)
    leaf5499FlatSound leaf5500FlatSound

private noncomputable def component111Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (11/32), chiHi := (45/128) }

set_option maxRecDepth 1000000 in
private theorem component111Node1_sound : Sound component111Node1Box :=
  sound_of_literal_split component111Node1Box leaf5501Box leaf5502Box
    .chi (89/256) (by rfl) (by rfl)
    leaf5501FlatSound leaf5502FlatSound

private noncomputable def component111Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (11/32), chiHi := (45/128) }

set_option maxRecDepth 1000000 in
private theorem component111Node2_sound : Sound component111Node2Box :=
  sound_of_literal_split component111Node2Box component111Node0Box component111Node1Box
    .k (121/32) (by rfl) (by rfl)
    component111Node0_sound component111Node1_sound

private noncomputable def component111Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (45/128), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component111Node3_sound : Sound component111Node3Box :=
  sound_of_literal_split component111Node3Box leaf5503Box leaf5504Box
    .chi (91/256) (by rfl) (by rfl)
    leaf5503FlatSound leaf5504FlatSound

private noncomputable def component111Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (45/128), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component111Node4_sound : Sound component111Node4Box :=
  sound_of_literal_split component111Node4Box leaf5505Box leaf5506Box
    .chi (91/256) (by rfl) (by rfl)
    leaf5505FlatSound leaf5506FlatSound

private noncomputable def component111Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (45/128), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component111Node5_sound : Sound component111Node5Box :=
  sound_of_literal_split component111Node5Box component111Node3Box component111Node4Box
    .k (121/32) (by rfl) (by rfl)
    component111Node3_sound component111Node4_sound

private noncomputable def component111Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (11/32), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component111Node6_sound : Sound component111Node6Box :=
  sound_of_literal_split component111Node6Box component111Node2Box component111Node5Box
    .chi (45/128) (by rfl) (by rfl)
    component111Node2_sound component111Node5_sound

private noncomputable def component111Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (11/32), chiHi := (45/128) }

set_option maxRecDepth 1000000 in
private theorem component111Node7_sound : Sound component111Node7Box :=
  sound_of_literal_split component111Node7Box leaf5507Box leaf5508Box
    .chi (89/256) (by rfl) (by rfl)
    leaf5507FlatSound leaf5508FlatSound

private noncomputable def component111Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (11/32), chiHi := (45/128) }

set_option maxRecDepth 1000000 in
private theorem component111Node8_sound : Sound component111Node8Box :=
  sound_of_literal_split component111Node8Box leaf5509Box leaf5510Box
    .chi (89/256) (by rfl) (by rfl)
    leaf5509FlatSound leaf5510FlatSound

private noncomputable def component111Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (11/32), chiHi := (45/128) }

set_option maxRecDepth 1000000 in
private theorem component111Node9_sound : Sound component111Node9Box :=
  sound_of_literal_split component111Node9Box component111Node7Box component111Node8Box
    .k (123/32) (by rfl) (by rfl)
    component111Node7_sound component111Node8_sound

private noncomputable def component111Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (45/128), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component111Node10_sound : Sound component111Node10Box :=
  sound_of_literal_split component111Node10Box leaf5511Box leaf5512Box
    .chi (91/256) (by rfl) (by rfl)
    leaf5511FlatSound leaf5512FlatSound

private noncomputable def component111Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (45/128), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component111Node11_sound : Sound component111Node11Box :=
  sound_of_literal_split component111Node11Box leaf5513Box leaf5514Box
    .chi (91/256) (by rfl) (by rfl)
    leaf5513FlatSound leaf5514FlatSound

private noncomputable def component111Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (45/128), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component111Node12_sound : Sound component111Node12Box :=
  sound_of_literal_split component111Node12Box component111Node10Box component111Node11Box
    .k (123/32) (by rfl) (by rfl)
    component111Node10_sound component111Node11_sound

private noncomputable def component111Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (11/32), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component111Node13_sound : Sound component111Node13Box :=
  sound_of_literal_split component111Node13Box component111Node9Box component111Node12Box
    .chi (45/128) (by rfl) (by rfl)
    component111Node9_sound component111Node12_sound

private noncomputable def component111Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (11/32), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component111Node14_sound : Sound component111Node14Box :=
  sound_of_literal_split component111Node14Box component111Node6Box component111Node13Box
    .k (61/16) (by rfl) (by rfl)
    component111Node6_sound component111Node13_sound

private noncomputable def component111Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (23/64), chiHi := (47/128) }

set_option maxRecDepth 1000000 in
private theorem component111Node15_sound : Sound component111Node15Box :=
  sound_of_literal_split component111Node15Box leaf5515Box leaf5516Box
    .chi (93/256) (by rfl) (by rfl)
    leaf5515FlatSound leaf5516FlatSound

private noncomputable def component111Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (23/64), chiHi := (47/128) }

set_option maxRecDepth 1000000 in
private theorem component111Node16_sound : Sound component111Node16Box :=
  sound_of_literal_split component111Node16Box leaf5517Box leaf5518Box
    .chi (93/256) (by rfl) (by rfl)
    leaf5517FlatSound leaf5518FlatSound

private noncomputable def component111Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (23/64), chiHi := (47/128) }

set_option maxRecDepth 1000000 in
private theorem component111Node17_sound : Sound component111Node17Box :=
  sound_of_literal_split component111Node17Box component111Node15Box component111Node16Box
    .k (121/32) (by rfl) (by rfl)
    component111Node15_sound component111Node16_sound

private noncomputable def component111Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (47/128), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component111Node18_sound : Sound component111Node18Box :=
  sound_of_literal_split component111Node18Box leaf5519Box leaf5520Box
    .chi (95/256) (by rfl) (by rfl)
    leaf5519FlatSound leaf5520FlatSound

private noncomputable def component111Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (47/128), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component111Node19_sound : Sound component111Node19Box :=
  sound_of_literal_split component111Node19Box leaf5521Box leaf5522Box
    .chi (95/256) (by rfl) (by rfl)
    leaf5521FlatSound leaf5522FlatSound

private noncomputable def component111Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (47/128), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component111Node20_sound : Sound component111Node20Box :=
  sound_of_literal_split component111Node20Box component111Node18Box component111Node19Box
    .k (121/32) (by rfl) (by rfl)
    component111Node18_sound component111Node19_sound

private noncomputable def component111Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (23/64), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component111Node21_sound : Sound component111Node21Box :=
  sound_of_literal_split component111Node21Box component111Node17Box component111Node20Box
    .chi (47/128) (by rfl) (by rfl)
    component111Node17_sound component111Node20_sound

private noncomputable def component111Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (23/64), chiHi := (47/128) }

set_option maxRecDepth 1000000 in
private theorem component111Node22_sound : Sound component111Node22Box :=
  sound_of_literal_split component111Node22Box leaf5523Box leaf5524Box
    .chi (93/256) (by rfl) (by rfl)
    leaf5523FlatSound leaf5524FlatSound

private noncomputable def component111Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (23/64), chiHi := (47/128) }

set_option maxRecDepth 1000000 in
private theorem component111Node23_sound : Sound component111Node23Box :=
  sound_of_literal_split component111Node23Box leaf5525Box leaf5526Box
    .chi (93/256) (by rfl) (by rfl)
    leaf5525FlatSound leaf5526FlatSound

private noncomputable def component111Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (23/64), chiHi := (47/128) }

set_option maxRecDepth 1000000 in
private theorem component111Node24_sound : Sound component111Node24Box :=
  sound_of_literal_split component111Node24Box component111Node22Box component111Node23Box
    .k (123/32) (by rfl) (by rfl)
    component111Node22_sound component111Node23_sound

private noncomputable def component111Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (47/128), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component111Node25_sound : Sound component111Node25Box :=
  sound_of_literal_split component111Node25Box leaf5527Box leaf5528Box
    .chi (95/256) (by rfl) (by rfl)
    leaf5527FlatSound leaf5528FlatSound

private noncomputable def component111Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (47/128), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component111Node26_sound : Sound component111Node26Box :=
  sound_of_literal_split component111Node26Box leaf5529Box leaf5530Box
    .chi (95/256) (by rfl) (by rfl)
    leaf5529FlatSound leaf5530FlatSound

private noncomputable def component111Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (47/128), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component111Node27_sound : Sound component111Node27Box :=
  sound_of_literal_split component111Node27Box component111Node25Box component111Node26Box
    .k (123/32) (by rfl) (by rfl)
    component111Node25_sound component111Node26_sound

private noncomputable def component111Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (23/64), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component111Node28_sound : Sound component111Node28Box :=
  sound_of_literal_split component111Node28Box component111Node24Box component111Node27Box
    .chi (47/128) (by rfl) (by rfl)
    component111Node24_sound component111Node27_sound

private noncomputable def component111Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (23/64), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component111Node29_sound : Sound component111Node29Box :=
  sound_of_literal_split component111Node29Box component111Node21Box component111Node28Box
    .k (61/16) (by rfl) (by rfl)
    component111Node21_sound component111Node28_sound

noncomputable def component111Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (11/32), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
theorem component111_sound : Sound component111Box :=
  sound_of_literal_split component111Box component111Node14Box component111Node29Box
    .chi (23/64) (by rfl) (by rfl)
    component111Node14_sound component111Node29_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
