import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch7
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

private noncomputable def leaf3401Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (249/64), chiLo := (13/64), chiHi := (53/256) }

private noncomputable def leaf3401Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742427/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432196608) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1918809127/1073741824) }, upper := { exponent := 0, mantissa := (29581/16384) } }, logOuter := sk233LogOuterCertificate, logK := sk233LogKCertificate, logChi := chi195LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869118463/274864393216) } }, logDArg := sk233LogDArgCertificate }

private noncomputable def leaf3401InnerLog : WideLogData :=
  innerPair464Data

set_option maxRecDepth 1000000 in
private theorem leaf3401LocalValidity :
    LeafFacts leaf3401Box leaf3401Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3401Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432196608) }) = true
      norm_num [leaf3401Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3401CertificateValid :
    WideCertificateValid leaf3401Box leaf3401Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk233ValidityFacts chi195ValidityFacts
    leaf3401LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3401CoverageChecked :
    coverageCheck (innerAD leaf3401Box) leaf3401InnerLog = true := by
  rfl'

private theorem leaf3401InnerLogValid :
    leaf3401InnerLog.Valid 8 (innerAD leaf3401Box) :=
  wideLogDataValid_of_cachedCheck endpoint183PositiveFacts
    endpoint221PositiveFacts.valid leaf3401CoverageChecked

private noncomputable def leaf3401InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629369/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3401InputLogOnePlusV_eq :
    leaf3401InputLogOnePlusV = outerEnclosure 24
      (leaf3401Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3401RoundedFacts : LeafRoundedFacts 8
    leaf3401Certificate.logOnePlusV leaf3401InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3401InputLogOnePlusV_eq }

private noncomputable def leaf3401Inputs : Inputs :=
  inputsOfCaches globalInput sk233RoundedInputs
    chi195InputQChi innerPair464Input
    leaf3401InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3401LowerChecked :
    lowerCheck 24 leaf3401Box leaf3401Inputs = true := by
  rfl'

private theorem leaf3401CoversExact : CoversExact 8
    leaf3401Box leaf3401Certificate leaf3401InnerLog leaf3401Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk233RoundedFacts chi195RoundedFacts
    innerPair464RoundedFacts leaf3401RoundedFacts (by rfl)

private theorem leaf3401FlatSound : Sound leaf3401Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3401CertificateValid
    leaf3401InnerLogValid leaf3401CoversExact leaf3401LowerChecked

private noncomputable def leaf3402Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (249/64), kHi := (125/32), chiLo := (13/64), chiHi := (53/256) }

private noncomputable def leaf3402Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742429/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432169472) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1922216789/1073741824) }, upper := { exponent := 0, mantissa := (14817/8192) } }, logOuter := sk234LogOuterCertificate, logK := sk234LogKCertificate, logChi := chi195LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869091327/274864338944) } }, logDArg := sk234LogDArgCertificate }

private noncomputable def leaf3402InnerLog : WideLogData :=
  innerPair506Data

set_option maxRecDepth 1000000 in
private theorem leaf3402LocalValidity :
    LeafFacts leaf3402Box leaf3402Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3402Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432169472) }) = true
      norm_num [leaf3402Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3402CertificateValid :
    WideCertificateValid leaf3402Box leaf3402Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk234ValidityFacts chi195ValidityFacts
    leaf3402LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3402CoverageChecked :
    coverageCheck (innerAD leaf3402Box) leaf3402InnerLog = true := by
  rfl'

private theorem leaf3402InnerLogValid :
    leaf3402InnerLog.Valid 8 (innerAD leaf3402Box) :=
  wideLogDataValid_of_cachedCheck endpoint234PositiveFacts
    endpoint235PositiveFacts.valid leaf3402CoverageChecked

private noncomputable def leaf3402InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629371/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3402InputLogOnePlusV_eq :
    leaf3402InputLogOnePlusV = outerEnclosure 24
      (leaf3402Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3402RoundedFacts : LeafRoundedFacts 8
    leaf3402Certificate.logOnePlusV leaf3402InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3402InputLogOnePlusV_eq }

private noncomputable def leaf3402Inputs : Inputs :=
  inputsOfCaches globalInput sk234RoundedInputs
    chi195InputQChi innerPair506Input
    leaf3402InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3402LowerChecked :
    lowerCheck 24 leaf3402Box leaf3402Inputs = true := by
  rfl'

private theorem leaf3402CoversExact : CoversExact 8
    leaf3402Box leaf3402Certificate leaf3402InnerLog leaf3402Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk234RoundedFacts chi195RoundedFacts
    innerPair506RoundedFacts leaf3402RoundedFacts (by rfl)

private theorem leaf3402FlatSound : Sound leaf3402Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3402CertificateValid
    leaf3402InnerLogValid leaf3402CoversExact leaf3402LowerChecked

private noncomputable def leaf3403Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (249/64), chiLo := (53/256), chiHi := (27/128) }

private noncomputable def leaf3403Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742429/1073741824) }, vSqrt := { lower := (8191/8192), upper := (1616904963/1616847872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1935061061/1073741824) }, upper := { exponent := 0, mantissa := (14915/8192) } }, logOuter := sk233LogOuterCertificate, logK := sk233LogKCertificate, logChi := chi196LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (3233752835/3233695744) } }, logDArg := sk233LogDArgCertificate }

private noncomputable def leaf3403InnerLog : WideLogData :=
  innerPair468Data

set_option maxRecDepth 1000000 in
private theorem leaf3403LocalValidity :
    LeafFacts leaf3403Box leaf3403Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3403Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (1616904963/1616847872) }) = true
      norm_num [leaf3403Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3403CertificateValid :
    WideCertificateValid leaf3403Box leaf3403Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk233ValidityFacts chi196ValidityFacts
    leaf3403LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3403CoverageChecked :
    coverageCheck (innerAD leaf3403Box) leaf3403InnerLog = true := by
  rfl'

private theorem leaf3403InnerLogValid :
    leaf3403InnerLog.Valid 8 (innerAD leaf3403Box) :=
  wideLogDataValid_of_cachedCheck endpoint187PositiveFacts
    endpoint188PositiveFacts.valid leaf3403CoverageChecked

private noncomputable def leaf3403InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629377/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3403InputLogOnePlusV_eq :
    leaf3403InputLogOnePlusV = outerEnclosure 24
      (leaf3403Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3403RoundedFacts : LeafRoundedFacts 8
    leaf3403Certificate.logOnePlusV leaf3403InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3403InputLogOnePlusV_eq }

private noncomputable def leaf3403Inputs : Inputs :=
  inputsOfCaches globalInput sk233RoundedInputs
    chi196InputQChi innerPair468Input
    leaf3403InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3403LowerChecked :
    lowerCheck 24 leaf3403Box leaf3403Inputs = true := by
  rfl'

private theorem leaf3403CoversExact : CoversExact 8
    leaf3403Box leaf3403Certificate leaf3403InnerLog leaf3403Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk233RoundedFacts chi196RoundedFacts
    innerPair468RoundedFacts leaf3403RoundedFacts (by rfl)

private theorem leaf3403FlatSound : Sound leaf3403Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3403CertificateValid
    leaf3403InnerLogValid leaf3403CoversExact leaf3403LowerChecked

private noncomputable def leaf3404Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (249/64), kHi := (125/32), chiLo := (53/256), chiHi := (27/128) }

private noncomputable def leaf3404Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742431/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432041472) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1938534255/1073741824) }, upper := { exponent := 0, mantissa := (7471/4096) } }, logOuter := sk234LogOuterCertificate, logK := sk234LogKCertificate, logChi := chi196LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868963327/274864082944) } }, logDArg := sk234LogDArgCertificate }

private noncomputable def leaf3404InnerLog : WideLogData :=
  innerPair466Data

set_option maxRecDepth 1000000 in
private theorem leaf3404LocalValidity :
    LeafFacts leaf3404Box leaf3404Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3404Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432041472) }) = true
      norm_num [leaf3404Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3404CertificateValid :
    WideCertificateValid leaf3404Box leaf3404Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk234ValidityFacts chi196ValidityFacts
    leaf3404LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3404CoverageChecked :
    coverageCheck (innerAD leaf3404Box) leaf3404InnerLog = true := by
  rfl'

private theorem leaf3404InnerLogValid :
    leaf3404InnerLog.Valid 8 (innerAD leaf3404Box) :=
  wideLogDataValid_of_cachedCheck endpoint185PositiveFacts
    endpoint188PositiveFacts.valid leaf3404CoverageChecked

private noncomputable def leaf3404InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629379/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3404InputLogOnePlusV_eq :
    leaf3404InputLogOnePlusV = outerEnclosure 24
      (leaf3404Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3404RoundedFacts : LeafRoundedFacts 8
    leaf3404Certificate.logOnePlusV leaf3404InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3404InputLogOnePlusV_eq }

private noncomputable def leaf3404Inputs : Inputs :=
  inputsOfCaches globalInput sk234RoundedInputs
    chi196InputQChi innerPair466Input
    leaf3404InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3404LowerChecked :
    lowerCheck 24 leaf3404Box leaf3404Inputs = true := by
  rfl'

private theorem leaf3404CoversExact : CoversExact 8
    leaf3404Box leaf3404Certificate leaf3404InnerLog leaf3404Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk234RoundedFacts chi196RoundedFacts
    innerPair466RoundedFacts leaf3404RoundedFacts (by rfl)

private theorem leaf3404FlatSound : Sound leaf3404Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3404CertificateValid
    leaf3404InnerLogValid leaf3404CoversExact leaf3404LowerChecked

private noncomputable def leaf3405Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (251/64), chiLo := (13/64), chiHi := (53/256) }

private noncomputable def leaf3405Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742431/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810714112) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1925624451/1073741824) }, upper := { exponent := 0, mantissa := (29687/16384) } }, logOuter := sk235LogOuterCertificate, logK := sk235LogKCertificate, logChi := chi195LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623021397/91621428224) } }, logDArg := sk235LogDArgCertificate }

private noncomputable def leaf3405InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3405LocalValidity :
    LeafFacts leaf3405Box leaf3405Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3405Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810714112) }) = true
      norm_num [leaf3405Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3405CertificateValid :
    WideCertificateValid leaf3405Box leaf3405Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk235ValidityFacts chi195ValidityFacts
    leaf3405LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3405CoverageChecked :
    coverageCheck (innerAD leaf3405Box) leaf3405InnerLog = true := by
  rfl'

private theorem leaf3405InnerLogValid :
    leaf3405InnerLog.Valid 8 (innerAD leaf3405Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3405CoverageChecked

private noncomputable def leaf3405InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907343/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3405InputLogOnePlusV_eq :
    leaf3405InputLogOnePlusV = outerEnclosure 24
      (leaf3405Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3405RoundedFacts : LeafRoundedFacts 8
    leaf3405Certificate.logOnePlusV leaf3405InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3405InputLogOnePlusV_eq }

private noncomputable def leaf3405Inputs : Inputs :=
  inputsOfCaches globalInput sk235RoundedInputs
    chi195InputQChi innerPair71Input
    leaf3405InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3405LowerChecked :
    lowerCheck 24 leaf3405Box leaf3405Inputs = true := by
  rfl'

private theorem leaf3405CoversExact : CoversExact 8
    leaf3405Box leaf3405Certificate leaf3405InnerLog leaf3405Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk235RoundedFacts chi195RoundedFacts
    innerPair71RoundedFacts leaf3405RoundedFacts (by rfl)

private theorem leaf3405FlatSound : Sound leaf3405Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3405CertificateValid
    leaf3405InnerLogValid leaf3405CoversExact leaf3405LowerChecked

private noncomputable def leaf3406Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (503/128), chiLo := (13/64), chiHi := (53/256) }

private noncomputable def leaf3406Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484759/2147483648) }, vSqrt := { lower := (8191/8192), upper := (274873778175/274864257536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3858097099/2147483648) }, upper := { exponent := 0, mantissa := (59427/32768) } }, logOuter := sk241LogOuterCertificate, logK := sk241LogKCertificate, logChi := chi195LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (549738035711/549728515072) } }, logDArg := sk241LogDArgCertificate }

private noncomputable def leaf3406InnerLog : WideLogData :=
  innerPair226Data

set_option maxRecDepth 1000000 in
private theorem leaf3406LocalValidity :
    LeafFacts leaf3406Box leaf3406Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3406Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (274873778175/274864257536) }) = true
      norm_num [leaf3406Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3406CertificateValid :
    WideCertificateValid leaf3406Box leaf3406Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk241ValidityFacts chi195ValidityFacts
    leaf3406LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3406CoverageChecked :
    coverageCheck (innerAD leaf3406Box) leaf3406InnerLog = true := by
  rfl'

private theorem leaf3406InnerLogValid :
    leaf3406InnerLog.Valid 8 (innerAD leaf3406Box) :=
  wideLogDataValid_of_cachedCheck endpoint68PositiveFacts
    endpoint64PositiveFacts.valid leaf3406CoverageChecked

private noncomputable def leaf3406InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629371/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3406InputLogOnePlusV_eq :
    leaf3406InputLogOnePlusV = outerEnclosure 24
      (leaf3406Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3406RoundedFacts : LeafRoundedFacts 8
    leaf3406Certificate.logOnePlusV leaf3406InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3406InputLogOnePlusV_eq }

private noncomputable def leaf3406Inputs : Inputs :=
  inputsOfCaches globalInput sk241RoundedInputs
    chi195InputQChi innerPair226Input
    leaf3406InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3406LowerChecked :
    lowerCheck 24 leaf3406Box leaf3406Inputs = true := by
  rfl'

private theorem leaf3406CoversExact : CoversExact 8
    leaf3406Box leaf3406Certificate leaf3406InnerLog leaf3406Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk241RoundedFacts chi195RoundedFacts
    innerPair226RoundedFacts leaf3406RoundedFacts (by rfl)

private theorem leaf3406FlatSound : Sound leaf3406Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3406CertificateValid
    leaf3406InnerLogValid leaf3406CoversExact leaf3406LowerChecked

private noncomputable def leaf3407Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (503/128), kHi := (63/16), chiLo := (13/64), chiHi := (53/256) }

private noncomputable def leaf3407Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484761/2147483648) }, vSqrt := { lower := (8191/8192), upper := (10994951127/10994569216) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3861504761/2147483648) }, upper := { exponent := 0, mantissa := (7435/4096) } }, logOuter := sk242LogOuterCertificate, logK := sk242LogKCertificate, logChi := chi195LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (21989520343/21989138432) } }, logDArg := sk242LogDArgCertificate }

private noncomputable def leaf3407InnerLog : WideLogData :=
  innerPair221Data

set_option maxRecDepth 1000000 in
private theorem leaf3407LocalValidity :
    LeafFacts leaf3407Box leaf3407Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3407Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (10994951127/10994569216) }) = true
      norm_num [leaf3407Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3407CertificateValid :
    WideCertificateValid leaf3407Box leaf3407Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk242ValidityFacts chi195ValidityFacts
    leaf3407LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3407CoverageChecked :
    coverageCheck (innerAD leaf3407Box) leaf3407InnerLog = true := by
  rfl'

private theorem leaf3407InnerLogValid :
    leaf3407InnerLog.Valid 8 (innerAD leaf3407Box) :=
  wideLogDataValid_of_cachedCheck endpoint67PositiveFacts
    endpoint64PositiveFacts.valid leaf3407CoverageChecked

private noncomputable def leaf3407InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907343/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3407InputLogOnePlusV_eq :
    leaf3407InputLogOnePlusV = outerEnclosure 24
      (leaf3407Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3407RoundedFacts : LeafRoundedFacts 8
    leaf3407Certificate.logOnePlusV leaf3407InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3407InputLogOnePlusV_eq }

private noncomputable def leaf3407Inputs : Inputs :=
  inputsOfCaches globalInput sk242RoundedInputs
    chi195InputQChi innerPair221Input
    leaf3407InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3407LowerChecked :
    lowerCheck 24 leaf3407Box leaf3407Inputs = true := by
  rfl'

private theorem leaf3407CoversExact : CoversExact 8
    leaf3407Box leaf3407Certificate leaf3407InnerLog leaf3407Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk242RoundedFacts chi195RoundedFacts
    innerPair221RoundedFacts leaf3407RoundedFacts (by rfl)

private theorem leaf3407FlatSound : Sound leaf3407Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3407CertificateValid
    leaf3407InnerLogValid leaf3407CoversExact leaf3407LowerChecked

private noncomputable def leaf3408Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (251/64), chiLo := (53/256), chiHi := (27/128) }

private noncomputable def leaf3408Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742433/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432013824) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1942007449/1073741824) }, upper := { exponent := 0, mantissa := (14969/8192) } }, logOuter := sk235LogOuterCertificate, logK := sk235LogKCertificate, logChi := chi196LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868935679/274864027648) } }, logDArg := sk235LogDArgCertificate }

private noncomputable def leaf3408InnerLog : WideLogData :=
  innerPair221Data

set_option maxRecDepth 1000000 in
private theorem leaf3408LocalValidity :
    LeafFacts leaf3408Box leaf3408Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3408Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432013824) }) = true
      norm_num [leaf3408Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3408CertificateValid :
    WideCertificateValid leaf3408Box leaf3408Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk235ValidityFacts chi196ValidityFacts
    leaf3408LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3408CoverageChecked :
    coverageCheck (innerAD leaf3408Box) leaf3408InnerLog = true := by
  rfl'

private theorem leaf3408InnerLogValid :
    leaf3408InnerLog.Valid 8 (innerAD leaf3408Box) :=
  wideLogDataValid_of_cachedCheck endpoint67PositiveFacts
    endpoint64PositiveFacts.valid leaf3408CoverageChecked

private noncomputable def leaf3408InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907345/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3408InputLogOnePlusV_eq :
    leaf3408InputLogOnePlusV = outerEnclosure 24
      (leaf3408Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3408RoundedFacts : LeafRoundedFacts 8
    leaf3408Certificate.logOnePlusV leaf3408InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3408InputLogOnePlusV_eq }

private noncomputable def leaf3408Inputs : Inputs :=
  inputsOfCaches globalInput sk235RoundedInputs
    chi196InputQChi innerPair221Input
    leaf3408InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3408LowerChecked :
    lowerCheck 24 leaf3408Box leaf3408Inputs = true := by
  rfl'

private theorem leaf3408CoversExact : CoversExact 8
    leaf3408Box leaf3408Certificate leaf3408InnerLog leaf3408Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk235RoundedFacts chi196RoundedFacts
    innerPair221RoundedFacts leaf3408RoundedFacts (by rfl)

private theorem leaf3408FlatSound : Sound leaf3408Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3408CertificateValid
    leaf3408InnerLogValid leaf3408CoversExact leaf3408LowerChecked

private noncomputable def leaf3409Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (63/16), chiLo := (53/256), chiHi := (107/512) }

private noncomputable def leaf3409Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484365/2147483648) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432050688) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3890994557/2147483648) }, upper := { exponent := 0, mantissa := (14933/8192) } }, logOuter := sk236LogOuterCertificate, logK := sk236LogKCertificate, logChi := chi223LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868972543/274864101376) } }, logDArg := sk236LogDArgCertificate }

private noncomputable def leaf3409InnerLog : WideLogData :=
  innerPair221Data

set_option maxRecDepth 1000000 in
private theorem leaf3409LocalValidity :
    LeafFacts leaf3409Box leaf3409Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3409Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432050688) }) = true
      norm_num [leaf3409Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3409CertificateValid :
    WideCertificateValid leaf3409Box leaf3409Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk236ValidityFacts chi223ValidityFacts
    leaf3409LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3409CoverageChecked :
    coverageCheck (innerAD leaf3409Box) leaf3409InnerLog = true := by
  rfl'

private theorem leaf3409InnerLogValid :
    leaf3409InnerLog.Valid 8 (innerAD leaf3409Box) :=
  wideLogDataValid_of_cachedCheck endpoint67PositiveFacts
    endpoint64PositiveFacts.valid leaf3409CoverageChecked

private noncomputable def leaf3409InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814689/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3409InputLogOnePlusV_eq :
    leaf3409InputLogOnePlusV = outerEnclosure 24
      (leaf3409Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3409RoundedFacts : LeafRoundedFacts 8
    leaf3409Certificate.logOnePlusV leaf3409InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3409InputLogOnePlusV_eq }

private noncomputable def leaf3409Inputs : Inputs :=
  inputsOfCaches globalInput sk236RoundedInputs
    chi223InputQChi innerPair221Input
    leaf3409InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3409LowerChecked :
    lowerCheck 24 leaf3409Box leaf3409Inputs = true := by
  rfl'

private theorem leaf3409CoversExact : CoversExact 8
    leaf3409Box leaf3409Certificate leaf3409InnerLog leaf3409Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk236RoundedFacts chi223RoundedFacts
    innerPair221RoundedFacts leaf3409RoundedFacts (by rfl)

private theorem leaf3409FlatSound : Sound leaf3409Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3409CertificateValid
    leaf3409InnerLogValid leaf3409CoversExact leaf3409LowerChecked

private noncomputable def leaf3410Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (63/16), chiLo := (107/512), chiHi := (27/128) }

private noncomputable def leaf3410Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484367/2147483648) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431986176) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3907443087/2147483648) }, upper := { exponent := 0, mantissa := (3749/2048) } }, logOuter := sk236LogOuterCertificate, logK := sk236LogKCertificate, logChi := chi224LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868908031/274863972352) } }, logDArg := sk236LogDArgCertificate }

private noncomputable def leaf3410InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3410LocalValidity :
    LeafFacts leaf3410Box leaf3410Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3410Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431986176) }) = true
      norm_num [leaf3410Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3410CertificateValid :
    WideCertificateValid leaf3410Box leaf3410Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk236ValidityFacts chi224ValidityFacts
    leaf3410LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3410CoverageChecked :
    coverageCheck (innerAD leaf3410Box) leaf3410InnerLog = true := by
  rfl'

private theorem leaf3410InnerLogValid :
    leaf3410InnerLog.Valid 8 (innerAD leaf3410Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3410CoverageChecked

private noncomputable def leaf3410InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814691/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3410InputLogOnePlusV_eq :
    leaf3410InputLogOnePlusV = outerEnclosure 24
      (leaf3410Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3410RoundedFacts : LeafRoundedFacts 8
    leaf3410Certificate.logOnePlusV leaf3410InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3410InputLogOnePlusV_eq }

private noncomputable def leaf3410Inputs : Inputs :=
  inputsOfCaches globalInput sk236RoundedInputs
    chi224InputQChi innerPair91Input
    leaf3410InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3410LowerChecked :
    lowerCheck 24 leaf3410Box leaf3410Inputs = true := by
  rfl'

private theorem leaf3410CoversExact : CoversExact 8
    leaf3410Box leaf3410Certificate leaf3410InnerLog leaf3410Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk236RoundedFacts chi224RoundedFacts
    innerPair91RoundedFacts leaf3410RoundedFacts (by rfl)

private theorem leaf3410FlatSound : Sound leaf3410Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3410CertificateValid
    leaf3410InnerLogValid leaf3410CoversExact leaf3410LowerChecked

private noncomputable def leaf3411Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (249/64), chiLo := (27/128), chiHi := (55/256) }

private noncomputable def leaf3411Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742431/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431941632) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1951312995/1073741824) }, upper := { exponent := 0, mantissa := (30079/16384) } }, logOuter := sk233LogOuterCertificate, logK := sk233LogKCertificate, logChi := chi197LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868863487/274863883264) } }, logDArg := sk233LogDArgCertificate }

private noncomputable def leaf3411InnerLog : WideLogData :=
  innerPair467Data

set_option maxRecDepth 1000000 in
private theorem leaf3411LocalValidity :
    LeafFacts leaf3411Box leaf3411Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3411Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431941632) }) = true
      norm_num [leaf3411Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3411CertificateValid :
    WideCertificateValid leaf3411Box leaf3411Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk233ValidityFacts chi197ValidityFacts
    leaf3411LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3411CoverageChecked :
    coverageCheck (innerAD leaf3411Box) leaf3411InnerLog = true := by
  rfl'

private theorem leaf3411InnerLogValid :
    leaf3411InnerLog.Valid 8 (innerAD leaf3411Box) :=
  wideLogDataValid_of_cachedCheck endpoint186PositiveFacts
    endpoint189PositiveFacts.valid leaf3411CoverageChecked

private noncomputable def leaf3411InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629385/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3411InputLogOnePlusV_eq :
    leaf3411InputLogOnePlusV = outerEnclosure 24
      (leaf3411Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3411RoundedFacts : LeafRoundedFacts 8
    leaf3411Certificate.logOnePlusV leaf3411InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3411InputLogOnePlusV_eq }

private noncomputable def leaf3411Inputs : Inputs :=
  inputsOfCaches globalInput sk233RoundedInputs
    chi197InputQChi innerPair467Input
    leaf3411InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3411LowerChecked :
    lowerCheck 24 leaf3411Box leaf3411Inputs = true := by
  rfl'

private theorem leaf3411CoversExact : CoversExact 8
    leaf3411Box leaf3411Certificate leaf3411InnerLog leaf3411Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk233RoundedFacts chi197RoundedFacts
    innerPair467RoundedFacts leaf3411RoundedFacts (by rfl)

private theorem leaf3411FlatSound : Sound leaf3411Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3411CertificateValid
    leaf3411InnerLogValid leaf3411CoversExact leaf3411LowerChecked

private noncomputable def leaf3412Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (249/64), kHi := (125/32), chiLo := (27/128), chiHi := (55/256) }

private noncomputable def leaf3412Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742433/1073741824) }, vSqrt := { lower := (8191/8192), upper := (15270769095/15270212608) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1954851721/1073741824) }, upper := { exponent := 0, mantissa := (15067/8192) } }, logOuter := sk234LogOuterCertificate, logK := sk234LogKCertificate, logChi := chi197LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (30540981703/30540425216) } }, logDArg := sk234LogDArgCertificate }

private noncomputable def leaf3412InnerLog : WideLogData :=
  innerPair495Data

set_option maxRecDepth 1000000 in
private theorem leaf3412LocalValidity :
    LeafFacts leaf3412Box leaf3412Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3412Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (15270769095/15270212608) }) = true
      norm_num [leaf3412Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3412CertificateValid :
    WideCertificateValid leaf3412Box leaf3412Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk234ValidityFacts chi197ValidityFacts
    leaf3412LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3412CoverageChecked :
    coverageCheck (innerAD leaf3412Box) leaf3412InnerLog = true := by
  rfl'

private theorem leaf3412InnerLogValid :
    leaf3412InnerLog.Valid 8 (innerAD leaf3412Box) :=
  wideLogDataValid_of_cachedCheck endpoint220PositiveFacts
    endpoint236PositiveFacts.valid leaf3412CoverageChecked

private noncomputable def leaf3412InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814693/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3412InputLogOnePlusV_eq :
    leaf3412InputLogOnePlusV = outerEnclosure 24
      (leaf3412Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3412RoundedFacts : LeafRoundedFacts 8
    leaf3412Certificate.logOnePlusV leaf3412InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3412InputLogOnePlusV_eq }

private noncomputable def leaf3412Inputs : Inputs :=
  inputsOfCaches globalInput sk234RoundedInputs
    chi197InputQChi innerPair495Input
    leaf3412InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3412LowerChecked :
    lowerCheck 24 leaf3412Box leaf3412Inputs = true := by
  rfl'

private theorem leaf3412CoversExact : CoversExact 8
    leaf3412Box leaf3412Certificate leaf3412InnerLog leaf3412Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk234RoundedFacts chi197RoundedFacts
    innerPair495RoundedFacts leaf3412RoundedFacts (by rfl)

private theorem leaf3412FlatSound : Sound leaf3412Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3412CertificateValid
    leaf3412InnerLogValid leaf3412CoversExact leaf3412LowerChecked

private noncomputable def leaf3413Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (249/64), chiLo := (55/256), chiHi := (7/32) }

private noncomputable def leaf3413Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742433/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431814144) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1967564929/1073741824) }, upper := { exponent := 0, mantissa := (3791/2048) } }, logOuter := sk233LogOuterCertificate, logK := sk233LogKCertificate, logChi := chi198LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868735999/274863628288) } }, logDArg := sk233LogDArgCertificate }

private noncomputable def leaf3413InnerLog : WideLogData :=
  innerPair497Data

set_option maxRecDepth 1000000 in
private theorem leaf3413LocalValidity :
    LeafFacts leaf3413Box leaf3413Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3413Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431814144) }) = true
      norm_num [leaf3413Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3413CertificateValid :
    WideCertificateValid leaf3413Box leaf3413Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk233ValidityFacts chi198ValidityFacts
    leaf3413LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3413CoverageChecked :
    coverageCheck (innerAD leaf3413Box) leaf3413InnerLog = true := by
  rfl'

private theorem leaf3413InnerLogValid :
    leaf3413InnerLog.Valid 8 (innerAD leaf3413Box) :=
  wideLogDataValid_of_cachedCheck endpoint222PositiveFacts
    endpoint237PositiveFacts.valid leaf3413CoverageChecked

private noncomputable def leaf3413InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629393/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3413InputLogOnePlusV_eq :
    leaf3413InputLogOnePlusV = outerEnclosure 24
      (leaf3413Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3413RoundedFacts : LeafRoundedFacts 8
    leaf3413Certificate.logOnePlusV leaf3413InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3413InputLogOnePlusV_eq }

private noncomputable def leaf3413Inputs : Inputs :=
  inputsOfCaches globalInput sk233RoundedInputs
    chi198InputQChi innerPair497Input
    leaf3413InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3413LowerChecked :
    lowerCheck 24 leaf3413Box leaf3413Inputs = true := by
  rfl'

private theorem leaf3413CoversExact : CoversExact 8
    leaf3413Box leaf3413Certificate leaf3413InnerLog leaf3413Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk233RoundedFacts chi198RoundedFacts
    innerPair497RoundedFacts leaf3413RoundedFacts (by rfl)

private theorem leaf3413FlatSound : Sound leaf3413Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3413CertificateValid
    leaf3413InnerLogValid leaf3413CoversExact leaf3413LowerChecked

private noncomputable def leaf3414Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (249/64), kHi := (125/32), chiLo := (55/256), chiHi := (7/32) }

private noncomputable def leaf3414Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742435/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431785472) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1971169187/1073741824) }, upper := { exponent := 0, mantissa := (1899/1024) } }, logOuter := sk234LogOuterCertificate, logK := sk234LogKCertificate, logChi := chi198LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868707327/274863570944) } }, logDArg := sk234LogDArgCertificate }

private noncomputable def leaf3414InnerLog : WideLogData :=
  innerPair498Data

set_option maxRecDepth 1000000 in
private theorem leaf3414LocalValidity :
    LeafFacts leaf3414Box leaf3414Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3414Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431785472) }) = true
      norm_num [leaf3414Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3414CertificateValid :
    WideCertificateValid leaf3414Box leaf3414Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk234ValidityFacts chi198ValidityFacts
    leaf3414LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3414CoverageChecked :
    coverageCheck (innerAD leaf3414Box) leaf3414InnerLog = true := by
  rfl'

private theorem leaf3414InnerLogValid :
    leaf3414InnerLog.Valid 8 (innerAD leaf3414Box) :=
  wideLogDataValid_of_cachedCheck endpoint222PositiveFacts
    endpoint238PositiveFacts.valid leaf3414CoverageChecked

private noncomputable def leaf3414InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814697/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3414InputLogOnePlusV_eq :
    leaf3414InputLogOnePlusV = outerEnclosure 24
      (leaf3414Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3414RoundedFacts : LeafRoundedFacts 8
    leaf3414Certificate.logOnePlusV leaf3414InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3414InputLogOnePlusV_eq }

private noncomputable def leaf3414Inputs : Inputs :=
  inputsOfCaches globalInput sk234RoundedInputs
    chi198InputQChi innerPair498Input
    leaf3414InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3414LowerChecked :
    lowerCheck 24 leaf3414Box leaf3414Inputs = true := by
  rfl'

private theorem leaf3414CoversExact : CoversExact 8
    leaf3414Box leaf3414Certificate leaf3414InnerLog leaf3414Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk234RoundedFacts chi198RoundedFacts
    innerPair498RoundedFacts leaf3414RoundedFacts (by rfl)

private theorem leaf3414FlatSound : Sound leaf3414Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3414CertificateValid
    leaf3414InnerLogValid leaf3414CoversExact leaf3414LowerChecked

private noncomputable def leaf3415Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (251/64), chiLo := (27/128), chiHi := (55/256) }

private noncomputable def leaf3415Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742435/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431885312) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1958390447/1073741824) }, upper := { exponent := 0, mantissa := (30189/16384) } }, logOuter := sk235LogOuterCertificate, logK := sk235LogKCertificate, logChi := chi197LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868807167/274863770624) } }, logDArg := sk235LogDArgCertificate }

private noncomputable def leaf3415InnerLog : WideLogData :=
  innerPair94Data

set_option maxRecDepth 1000000 in
private theorem leaf3415LocalValidity :
    LeafFacts leaf3415Box leaf3415Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3415Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431885312) }) = true
      norm_num [leaf3415Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3415CertificateValid :
    WideCertificateValid leaf3415Box leaf3415Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk235ValidityFacts chi197ValidityFacts
    leaf3415LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3415CoverageChecked :
    coverageCheck (innerAD leaf3415Box) leaf3415InnerLog = true := by
  rfl'

private theorem leaf3415InnerLogValid :
    leaf3415InnerLog.Valid 8 (innerAD leaf3415Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint61PositiveFacts.valid leaf3415CoverageChecked

private noncomputable def leaf3415InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907347/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3415InputLogOnePlusV_eq :
    leaf3415InputLogOnePlusV = outerEnclosure 24
      (leaf3415Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3415RoundedFacts : LeafRoundedFacts 8
    leaf3415Certificate.logOnePlusV leaf3415InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3415InputLogOnePlusV_eq }

private noncomputable def leaf3415Inputs : Inputs :=
  inputsOfCaches globalInput sk235RoundedInputs
    chi197InputQChi innerPair94Input
    leaf3415InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3415LowerChecked :
    lowerCheck 24 leaf3415Box leaf3415Inputs = true := by
  rfl'

private theorem leaf3415CoversExact : CoversExact 8
    leaf3415Box leaf3415Certificate leaf3415InnerLog leaf3415Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk235RoundedFacts chi197RoundedFacts
    innerPair94RoundedFacts leaf3415RoundedFacts (by rfl)

private theorem leaf3415FlatSound : Sound leaf3415Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3415CertificateValid
    leaf3415InnerLogValid leaf3415CoversExact leaf3415LowerChecked

private noncomputable def leaf3416Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (63/16), chiLo := (27/128), chiHi := (109/512) }

private noncomputable def leaf3416Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484369/2147483648) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431921664) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3923891617/2147483648) }, upper := { exponent := 0, mantissa := (15059/8192) } }, logOuter := sk236LogOuterCertificate, logK := sk236LogKCertificate, logChi := chi225LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868843519/274863843328) } }, logDArg := sk236LogDArgCertificate }

private noncomputable def leaf3416InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3416LocalValidity :
    LeafFacts leaf3416Box leaf3416Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3416Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431921664) }) = true
      norm_num [leaf3416Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3416CertificateValid :
    WideCertificateValid leaf3416Box leaf3416Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk236ValidityFacts chi225ValidityFacts
    leaf3416LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3416CoverageChecked :
    coverageCheck (innerAD leaf3416Box) leaf3416InnerLog = true := by
  rfl'

private theorem leaf3416InnerLogValid :
    leaf3416InnerLog.Valid 8 (innerAD leaf3416Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3416CoverageChecked

private noncomputable def leaf3416InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814693/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3416InputLogOnePlusV_eq :
    leaf3416InputLogOnePlusV = outerEnclosure 24
      (leaf3416Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3416RoundedFacts : LeafRoundedFacts 8
    leaf3416Certificate.logOnePlusV leaf3416InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3416InputLogOnePlusV_eq }

private noncomputable def leaf3416Inputs : Inputs :=
  inputsOfCaches globalInput sk236RoundedInputs
    chi225InputQChi innerPair91Input
    leaf3416InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3416LowerChecked :
    lowerCheck 24 leaf3416Box leaf3416Inputs = true := by
  rfl'

private theorem leaf3416CoversExact : CoversExact 8
    leaf3416Box leaf3416Certificate leaf3416InnerLog leaf3416Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk236RoundedFacts chi225RoundedFacts
    innerPair91RoundedFacts leaf3416RoundedFacts (by rfl)

private theorem leaf3416FlatSound : Sound leaf3416Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3416CertificateValid
    leaf3416InnerLogValid leaf3416CoversExact leaf3416LowerChecked

private noncomputable def leaf3417Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (63/16), chiLo := (109/512), chiHi := (55/256) }

private noncomputable def leaf3417Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484371/2147483648) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431857152) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3940340147/2147483648) }, upper := { exponent := 0, mantissa := (7561/4096) } }, logOuter := sk236LogOuterCertificate, logK := sk236LogKCertificate, logChi := chi226LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868779007/274863714304) } }, logDArg := sk236LogDArgCertificate }

private noncomputable def leaf3417InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3417LocalValidity :
    LeafFacts leaf3417Box leaf3417Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3417Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431857152) }) = true
      norm_num [leaf3417Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3417CertificateValid :
    WideCertificateValid leaf3417Box leaf3417Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk236ValidityFacts chi226ValidityFacts
    leaf3417LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3417CoverageChecked :
    coverageCheck (innerAD leaf3417Box) leaf3417InnerLog = true := by
  rfl'

private theorem leaf3417InnerLogValid :
    leaf3417InnerLog.Valid 8 (innerAD leaf3417Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3417CoverageChecked

private noncomputable def leaf3417InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814695/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3417InputLogOnePlusV_eq :
    leaf3417InputLogOnePlusV = outerEnclosure 24
      (leaf3417Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3417RoundedFacts : LeafRoundedFacts 8
    leaf3417Certificate.logOnePlusV leaf3417InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3417InputLogOnePlusV_eq }

private noncomputable def leaf3417Inputs : Inputs :=
  inputsOfCaches globalInput sk236RoundedInputs
    chi226InputQChi innerPair91Input
    leaf3417InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3417LowerChecked :
    lowerCheck 24 leaf3417Box leaf3417Inputs = true := by
  rfl'

private theorem leaf3417CoversExact : CoversExact 8
    leaf3417Box leaf3417Certificate leaf3417InnerLog leaf3417Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk236RoundedFacts chi226RoundedFacts
    innerPair91RoundedFacts leaf3417RoundedFacts (by rfl)

private theorem leaf3417FlatSound : Sound leaf3417Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3417CertificateValid
    leaf3417InnerLogValid leaf3417CoversExact leaf3417LowerChecked

private noncomputable def leaf3418Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (251/64), chiLo := (55/256), chiHi := (7/32) }

private noncomputable def leaf3418Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742437/1073741824) }, vSqrt := { lower := (8191/8192), upper := (3054153819/3054039040) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1974773445/1073741824) }, upper := { exponent := 0, mantissa := (3805/2048) } }, logOuter := sk235LogOuterCertificate, logK := sk235LogKCertificate, logChi := chi198LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (6108192859/6108078080) } }, logDArg := sk235LogDArgCertificate }

private noncomputable def leaf3418InnerLog : WideLogData :=
  innerPair214Data

set_option maxRecDepth 1000000 in
private theorem leaf3418LocalValidity :
    LeafFacts leaf3418Box leaf3418Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3418Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (3054153819/3054039040) }) = true
      norm_num [leaf3418Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3418CertificateValid :
    WideCertificateValid leaf3418Box leaf3418Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk235ValidityFacts chi198ValidityFacts
    leaf3418LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3418CoverageChecked :
    coverageCheck (innerAD leaf3418Box) leaf3418InnerLog = true := by
  rfl'

private theorem leaf3418InnerLogValid :
    leaf3418InnerLog.Valid 8 (innerAD leaf3418Box) :=
  wideLogDataValid_of_cachedCheck endpoint64PositiveFacts
    endpoint211PositiveFacts.valid leaf3418CoverageChecked

private noncomputable def leaf3418InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907349/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3418InputLogOnePlusV_eq :
    leaf3418InputLogOnePlusV = outerEnclosure 24
      (leaf3418Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3418RoundedFacts : LeafRoundedFacts 8
    leaf3418Certificate.logOnePlusV leaf3418InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3418InputLogOnePlusV_eq }

private noncomputable def leaf3418Inputs : Inputs :=
  inputsOfCaches globalInput sk235RoundedInputs
    chi198InputQChi innerPair214Input
    leaf3418InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3418LowerChecked :
    lowerCheck 24 leaf3418Box leaf3418Inputs = true := by
  rfl'

private theorem leaf3418CoversExact : CoversExact 8
    leaf3418Box leaf3418Certificate leaf3418InnerLog leaf3418Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk235RoundedFacts chi198RoundedFacts
    innerPair214RoundedFacts leaf3418RoundedFacts (by rfl)

private theorem leaf3418FlatSound : Sound leaf3418Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3418CertificateValid
    leaf3418InnerLogValid leaf3418CoversExact leaf3418LowerChecked

private noncomputable def leaf3419Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (63/16), chiLo := (55/256), chiHi := (7/32) }

private noncomputable def leaf3419Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742439/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431728128) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1978377703/1073741824) }, upper := { exponent := 0, mantissa := (953/512) } }, logOuter := sk236LogOuterCertificate, logK := sk236LogKCertificate, logChi := chi198LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868649983/274863456256) } }, logDArg := sk236LogDArgCertificate }

private noncomputable def leaf3419InnerLog : WideLogData :=
  innerPair511Data

set_option maxRecDepth 1000000 in
private theorem leaf3419LocalValidity :
    LeafFacts leaf3419Box leaf3419Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3419Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431728128) }) = true
      norm_num [leaf3419Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3419CertificateValid :
    WideCertificateValid leaf3419Box leaf3419Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk236ValidityFacts chi198ValidityFacts
    leaf3419LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3419CoverageChecked :
    coverageCheck (innerAD leaf3419Box) leaf3419InnerLog = true := by
  rfl'

private theorem leaf3419InnerLogValid :
    leaf3419InnerLog.Valid 8 (innerAD leaf3419Box) :=
  wideLogDataValid_of_cachedCheck endpoint239PositiveFacts
    endpoint240PositiveFacts.valid leaf3419CoverageChecked

private noncomputable def leaf3419InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814699/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3419InputLogOnePlusV_eq :
    leaf3419InputLogOnePlusV = outerEnclosure 24
      (leaf3419Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3419RoundedFacts : LeafRoundedFacts 8
    leaf3419Certificate.logOnePlusV leaf3419InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3419InputLogOnePlusV_eq }

private noncomputable def leaf3419Inputs : Inputs :=
  inputsOfCaches globalInput sk236RoundedInputs
    chi198InputQChi innerPair511Input
    leaf3419InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3419LowerChecked :
    lowerCheck 24 leaf3419Box leaf3419Inputs = true := by
  rfl'

private theorem leaf3419CoversExact : CoversExact 8
    leaf3419Box leaf3419Certificate leaf3419InnerLog leaf3419Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk236RoundedFacts chi198RoundedFacts
    innerPair511RoundedFacts leaf3419RoundedFacts (by rfl)

private theorem leaf3419FlatSound : Sound leaf3419Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3419CertificateValid
    leaf3419InnerLogValid leaf3419CoversExact leaf3419LowerChecked

private noncomputable def leaf3420Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (505/128), chiLo := (13/64), chiHi := (53/256) }

private noncomputable def leaf3420Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484763/2147483648) }, vSqrt := { lower := (8191/8192), upper := (91624592725/91621401088) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3864912423/2147483648) }, upper := { exponent := 0, mantissa := (59533/32768) } }, logOuter := sk243LogOuterCertificate, logK := sk243LogKCertificate, logChi := chi195LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (183245993813/183242802176) } }, logDArg := sk243LogDArgCertificate }

private noncomputable def leaf3420InnerLog : WideLogData :=
  innerPair221Data

set_option maxRecDepth 1000000 in
private theorem leaf3420LocalValidity :
    LeafFacts leaf3420Box leaf3420Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3420Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (91624592725/91621401088) }) = true
      norm_num [leaf3420Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3420CertificateValid :
    WideCertificateValid leaf3420Box leaf3420Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk243ValidityFacts chi195ValidityFacts
    leaf3420LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3420CoverageChecked :
    coverageCheck (innerAD leaf3420Box) leaf3420InnerLog = true := by
  rfl'

private theorem leaf3420InnerLogValid :
    leaf3420InnerLog.Valid 8 (innerAD leaf3420Box) :=
  wideLogDataValid_of_cachedCheck endpoint67PositiveFacts
    endpoint64PositiveFacts.valid leaf3420CoverageChecked

private noncomputable def leaf3420InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629373/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3420InputLogOnePlusV_eq :
    leaf3420InputLogOnePlusV = outerEnclosure 24
      (leaf3420Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3420RoundedFacts : LeafRoundedFacts 8
    leaf3420Certificate.logOnePlusV leaf3420InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3420InputLogOnePlusV_eq }

private noncomputable def leaf3420Inputs : Inputs :=
  inputsOfCaches globalInput sk243RoundedInputs
    chi195InputQChi innerPair221Input
    leaf3420InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3420LowerChecked :
    lowerCheck 24 leaf3420Box leaf3420Inputs = true := by
  rfl'

private theorem leaf3420CoversExact : CoversExact 8
    leaf3420Box leaf3420Certificate leaf3420InnerLog leaf3420Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk243RoundedFacts chi195RoundedFacts
    innerPair221RoundedFacts leaf3420RoundedFacts (by rfl)

private theorem leaf3420FlatSound : Sound leaf3420Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3420CertificateValid
    leaf3420InnerLogValid leaf3420CoversExact leaf3420LowerChecked

private noncomputable def leaf3421Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (505/128), kHi := (253/64), chiLo := (13/64), chiHi := (53/256) }

private noncomputable def leaf3421Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484765/2147483648) }, vSqrt := { lower := (8191/8192), upper := (274873778175/274864176128) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3868320085/2147483648) }, upper := { exponent := 0, mantissa := (29793/16384) } }, logOuter := sk244LogOuterCertificate, logK := sk244LogKCertificate, logChi := chi195LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (549737954303/549728352256) } }, logDArg := sk244LogDArgCertificate }

private noncomputable def leaf3421InnerLog : WideLogData :=
  innerPair221Data

set_option maxRecDepth 1000000 in
private theorem leaf3421LocalValidity :
    LeafFacts leaf3421Box leaf3421Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3421Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (274873778175/274864176128) }) = true
      norm_num [leaf3421Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3421CertificateValid :
    WideCertificateValid leaf3421Box leaf3421Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk244ValidityFacts chi195ValidityFacts
    leaf3421LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3421CoverageChecked :
    coverageCheck (innerAD leaf3421Box) leaf3421InnerLog = true := by
  rfl'

private theorem leaf3421InnerLogValid :
    leaf3421InnerLog.Valid 8 (innerAD leaf3421Box) :=
  wideLogDataValid_of_cachedCheck endpoint67PositiveFacts
    endpoint64PositiveFacts.valid leaf3421CoverageChecked

private noncomputable def leaf3421InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814687/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3421InputLogOnePlusV_eq :
    leaf3421InputLogOnePlusV = outerEnclosure 24
      (leaf3421Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3421RoundedFacts : LeafRoundedFacts 8
    leaf3421Certificate.logOnePlusV leaf3421InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3421InputLogOnePlusV_eq }

private noncomputable def leaf3421Inputs : Inputs :=
  inputsOfCaches globalInput sk244RoundedInputs
    chi195InputQChi innerPair221Input
    leaf3421InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3421LowerChecked :
    lowerCheck 24 leaf3421Box leaf3421Inputs = true := by
  rfl'

private theorem leaf3421CoversExact : CoversExact 8
    leaf3421Box leaf3421Certificate leaf3421InnerLog leaf3421Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk244RoundedFacts chi195RoundedFacts
    innerPair221RoundedFacts leaf3421RoundedFacts (by rfl)

private theorem leaf3421FlatSound : Sound leaf3421Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3421CertificateValid
    leaf3421InnerLogValid leaf3421CoversExact leaf3421LowerChecked

private noncomputable def leaf3422Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (507/128), chiLo := (13/64), chiHi := (53/256) }

private noncomputable def leaf3422Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484767/2147483648) }, vSqrt := { lower := (8191/8192), upper := (274873778175/274864148992) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3871727747/2147483648) }, upper := { exponent := 0, mantissa := (59639/32768) } }, logOuter := sk245LogOuterCertificate, logK := sk245LogKCertificate, logChi := chi195LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (549737927167/549728297984) } }, logDArg := sk245LogDArgCertificate }

private noncomputable def leaf3422InnerLog : WideLogData :=
  innerPair221Data

set_option maxRecDepth 1000000 in
private theorem leaf3422LocalValidity :
    LeafFacts leaf3422Box leaf3422Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3422Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (274873778175/274864148992) }) = true
      norm_num [leaf3422Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3422CertificateValid :
    WideCertificateValid leaf3422Box leaf3422Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk245ValidityFacts chi195ValidityFacts
    leaf3422LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3422CoverageChecked :
    coverageCheck (innerAD leaf3422Box) leaf3422InnerLog = true := by
  rfl'

private theorem leaf3422InnerLogValid :
    leaf3422InnerLog.Valid 8 (innerAD leaf3422Box) :=
  wideLogDataValid_of_cachedCheck endpoint67PositiveFacts
    endpoint64PositiveFacts.valid leaf3422CoverageChecked

private noncomputable def leaf3422InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629375/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3422InputLogOnePlusV_eq :
    leaf3422InputLogOnePlusV = outerEnclosure 24
      (leaf3422Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3422RoundedFacts : LeafRoundedFacts 8
    leaf3422Certificate.logOnePlusV leaf3422InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3422InputLogOnePlusV_eq }

private noncomputable def leaf3422Inputs : Inputs :=
  inputsOfCaches globalInput sk245RoundedInputs
    chi195InputQChi innerPair221Input
    leaf3422InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3422LowerChecked :
    lowerCheck 24 leaf3422Box leaf3422Inputs = true := by
  rfl'

private theorem leaf3422CoversExact : CoversExact 8
    leaf3422Box leaf3422Certificate leaf3422InnerLog leaf3422Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk245RoundedFacts chi195RoundedFacts
    innerPair221RoundedFacts leaf3422RoundedFacts (by rfl)

private theorem leaf3422FlatSound : Sound leaf3422Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3422CertificateValid
    leaf3422InnerLogValid leaf3422CoversExact leaf3422LowerChecked

private noncomputable def leaf3423Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (507/128), kHi := (127/32), chiLo := (13/64), chiHi := (53/256) }

private noncomputable def leaf3423Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484769/2147483648) }, vSqrt := { lower := (8191/8192), upper := (91624592725/91621373952) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3875135409/2147483648) }, upper := { exponent := 0, mantissa := (14923/8192) } }, logOuter := sk246LogOuterCertificate, logK := sk246LogKCertificate, logChi := chi195LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (183245966677/183242747904) } }, logDArg := sk246LogDArgCertificate }

private noncomputable def leaf3423InnerLog : WideLogData :=
  innerPair221Data

set_option maxRecDepth 1000000 in
private theorem leaf3423LocalValidity :
    LeafFacts leaf3423Box leaf3423Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3423Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (91624592725/91621373952) }) = true
      norm_num [leaf3423Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3423CertificateValid :
    WideCertificateValid leaf3423Box leaf3423Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk246ValidityFacts chi195ValidityFacts
    leaf3423LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3423CoverageChecked :
    coverageCheck (innerAD leaf3423Box) leaf3423InnerLog = true := by
  rfl'

private theorem leaf3423InnerLogValid :
    leaf3423InnerLog.Valid 8 (innerAD leaf3423Box) :=
  wideLogDataValid_of_cachedCheck endpoint67PositiveFacts
    endpoint64PositiveFacts.valid leaf3423CoverageChecked

private noncomputable def leaf3423InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629375/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3423InputLogOnePlusV_eq :
    leaf3423InputLogOnePlusV = outerEnclosure 24
      (leaf3423Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3423RoundedFacts : LeafRoundedFacts 8
    leaf3423Certificate.logOnePlusV leaf3423InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3423InputLogOnePlusV_eq }

private noncomputable def leaf3423Inputs : Inputs :=
  inputsOfCaches globalInput sk246RoundedInputs
    chi195InputQChi innerPair221Input
    leaf3423InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3423LowerChecked :
    lowerCheck 24 leaf3423Box leaf3423Inputs = true := by
  rfl'

private theorem leaf3423CoversExact : CoversExact 8
    leaf3423Box leaf3423Certificate leaf3423InnerLog leaf3423Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk246RoundedFacts chi195RoundedFacts
    innerPair221RoundedFacts leaf3423RoundedFacts (by rfl)

private theorem leaf3423FlatSound : Sound leaf3423Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3423CertificateValid
    leaf3423InnerLogValid leaf3423CoversExact leaf3423LowerChecked

private noncomputable def leaf3424Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (53/256), chiHi := (107/512) }

private noncomputable def leaf3424Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484367/2147483648) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810674432) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3897940947/2147483648) }, upper := { exponent := 0, mantissa := (59839/32768) } }, logOuter := sk237LogOuterCertificate, logK := sk237LogKCertificate, logChi := chi223LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91622981717/91621348864) } }, logDArg := sk237LogDArgCertificate }

private noncomputable def leaf3424InnerLog : WideLogData :=
  innerPair95Data

set_option maxRecDepth 1000000 in
private theorem leaf3424LocalValidity :
    LeafFacts leaf3424Box leaf3424Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3424Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810674432) }) = true
      norm_num [leaf3424Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3424CertificateValid :
    WideCertificateValid leaf3424Box leaf3424Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk237ValidityFacts chi223ValidityFacts
    leaf3424LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3424CoverageChecked :
    coverageCheck (innerAD leaf3424Box) leaf3424InnerLog = true := by
  rfl'

private theorem leaf3424InnerLogValid :
    leaf3424InnerLog.Valid 8 (innerAD leaf3424Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint64PositiveFacts.valid leaf3424CoverageChecked

private noncomputable def leaf3424InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907345/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3424InputLogOnePlusV_eq :
    leaf3424InputLogOnePlusV = outerEnclosure 24
      (leaf3424Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3424RoundedFacts : LeafRoundedFacts 8
    leaf3424Certificate.logOnePlusV leaf3424InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3424InputLogOnePlusV_eq }

private noncomputable def leaf3424Inputs : Inputs :=
  inputsOfCaches globalInput sk237RoundedInputs
    chi223InputQChi innerPair95Input
    leaf3424InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3424LowerChecked :
    lowerCheck 24 leaf3424Box leaf3424Inputs = true := by
  rfl'

private theorem leaf3424CoversExact : CoversExact 8
    leaf3424Box leaf3424Certificate leaf3424InnerLog leaf3424Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk237RoundedFacts chi223RoundedFacts
    innerPair95RoundedFacts leaf3424RoundedFacts (by rfl)

private theorem leaf3424FlatSound : Sound leaf3424Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3424CertificateValid
    leaf3424InnerLogValid leaf3424CoversExact leaf3424LowerChecked

private noncomputable def leaf3425Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (107/512), chiHi := (27/128) }

private noncomputable def leaf3425Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484369/2147483648) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431958528) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3914455009/2147483648) }, upper := { exponent := 0, mantissa := (15023/8192) } }, logOuter := sk237LogOuterCertificate, logK := sk237LogKCertificate, logChi := chi224LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868880383/274863917056) } }, logDArg := sk237LogDArgCertificate }

private noncomputable def leaf3425InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3425LocalValidity :
    LeafFacts leaf3425Box leaf3425Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3425Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431958528) }) = true
      norm_num [leaf3425Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3425CertificateValid :
    WideCertificateValid leaf3425Box leaf3425Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk237ValidityFacts chi224ValidityFacts
    leaf3425LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3425CoverageChecked :
    coverageCheck (innerAD leaf3425Box) leaf3425InnerLog = true := by
  rfl'

private theorem leaf3425InnerLogValid :
    leaf3425InnerLog.Valid 8 (innerAD leaf3425Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3425CoverageChecked

private noncomputable def leaf3425InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453673/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf3425InputLogOnePlusV_eq :
    leaf3425InputLogOnePlusV = outerEnclosure 24
      (leaf3425Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3425RoundedFacts : LeafRoundedFacts 8
    leaf3425Certificate.logOnePlusV leaf3425InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3425InputLogOnePlusV_eq }

private noncomputable def leaf3425Inputs : Inputs :=
  inputsOfCaches globalInput sk237RoundedInputs
    chi224InputQChi innerPair91Input
    leaf3425InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3425LowerChecked :
    lowerCheck 24 leaf3425Box leaf3425Inputs = true := by
  rfl'

private theorem leaf3425CoversExact : CoversExact 8
    leaf3425Box leaf3425Certificate leaf3425InnerLog leaf3425Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk237RoundedFacts chi224RoundedFacts
    innerPair91RoundedFacts leaf3425RoundedFacts (by rfl)

private theorem leaf3425FlatSound : Sound leaf3425Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3425CertificateValid
    leaf3425InnerLogValid leaf3425CoversExact leaf3425LowerChecked

private noncomputable def leaf3426Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (53/256), chiHi := (107/512) }

private noncomputable def leaf3426Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484369/2147483648) }, vSqrt := { lower := (8191/8192), upper := (3196207485/3196092928) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3904887337/2147483648) }, upper := { exponent := 0, mantissa := (29973/16384) } }, logOuter := sk238LogOuterCertificate, logK := sk238LogKCertificate, logChi := chi223LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (6392300413/6392185856) } }, logDArg := sk238LogDArgCertificate }

private noncomputable def leaf3426InnerLog : WideLogData :=
  innerPair94Data

set_option maxRecDepth 1000000 in
private theorem leaf3426LocalValidity :
    LeafFacts leaf3426Box leaf3426Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3426Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (3196207485/3196092928) }) = true
      norm_num [leaf3426Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3426CertificateValid :
    WideCertificateValid leaf3426Box leaf3426Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk238ValidityFacts chi223ValidityFacts
    leaf3426LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3426CoverageChecked :
    coverageCheck (innerAD leaf3426Box) leaf3426InnerLog = true := by
  rfl'

private theorem leaf3426InnerLogValid :
    leaf3426InnerLog.Valid 8 (innerAD leaf3426Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint61PositiveFacts.valid leaf3426CoverageChecked

private noncomputable def leaf3426InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629381/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3426InputLogOnePlusV_eq :
    leaf3426InputLogOnePlusV = outerEnclosure 24
      (leaf3426Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3426RoundedFacts : LeafRoundedFacts 8
    leaf3426Certificate.logOnePlusV leaf3426InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3426InputLogOnePlusV_eq }

private noncomputable def leaf3426Inputs : Inputs :=
  inputsOfCaches globalInput sk238RoundedInputs
    chi223InputQChi innerPair94Input
    leaf3426InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3426LowerChecked :
    lowerCheck 24 leaf3426Box leaf3426Inputs = true := by
  rfl'

private theorem leaf3426CoversExact : CoversExact 8
    leaf3426Box leaf3426Certificate leaf3426InnerLog leaf3426Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk238RoundedFacts chi223RoundedFacts
    innerPair94RoundedFacts leaf3426RoundedFacts (by rfl)

private theorem leaf3426FlatSound : Sound leaf3426Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3426CertificateValid
    leaf3426InnerLogValid leaf3426CoversExact leaf3426LowerChecked

private noncomputable def leaf3427Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (107/512), chiHi := (27/128) }

private noncomputable def leaf3427Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484371/2147483648) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486386176) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3921466931/2147483648) }, upper := { exponent := 0, mantissa := (7525/4096) } }, logOuter := sk238LogOuterCertificate, logK := sk238LogKCertificate, logChi := chi224LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973770547/54972772352) } }, logDArg := sk238LogDArgCertificate }

private noncomputable def leaf3427InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3427LocalValidity :
    LeafFacts leaf3427Box leaf3427Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3427Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486386176) }) = true
      norm_num [leaf3427Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3427CertificateValid :
    WideCertificateValid leaf3427Box leaf3427Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk238ValidityFacts chi224ValidityFacts
    leaf3427LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3427CoverageChecked :
    coverageCheck (innerAD leaf3427Box) leaf3427InnerLog = true := by
  rfl'

private theorem leaf3427InnerLogValid :
    leaf3427InnerLog.Valid 8 (innerAD leaf3427Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3427CoverageChecked

private noncomputable def leaf3427InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629385/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3427InputLogOnePlusV_eq :
    leaf3427InputLogOnePlusV = outerEnclosure 24
      (leaf3427Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3427RoundedFacts : LeafRoundedFacts 8
    leaf3427Certificate.logOnePlusV leaf3427InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3427InputLogOnePlusV_eq }

private noncomputable def leaf3427Inputs : Inputs :=
  inputsOfCaches globalInput sk238RoundedInputs
    chi224InputQChi innerPair91Input
    leaf3427InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3427LowerChecked :
    lowerCheck 24 leaf3427Box leaf3427Inputs = true := by
  rfl'

private theorem leaf3427CoversExact : CoversExact 8
    leaf3427Box leaf3427Certificate leaf3427InnerLog leaf3427Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk238RoundedFacts chi224RoundedFacts
    innerPair91RoundedFacts leaf3427RoundedFacts (by rfl)

private theorem leaf3427FlatSound : Sound leaf3427Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3427CertificateValid
    leaf3427InnerLogValid leaf3427CoversExact leaf3427LowerChecked

private noncomputable def leaf3428Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (509/128), chiLo := (13/64), chiHi := (53/256) }

private noncomputable def leaf3428Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484771/2147483648) }, vSqrt := { lower := (8191/8192), upper := (3233809155/3233695232) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3878543071/2147483648) }, upper := { exponent := 0, mantissa := (59745/32768) } }, logOuter := sk247LogOuterCertificate, logK := sk247LogKCertificate, logChi := chi195LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (6467504387/6467390464) } }, logDArg := sk247LogDArgCertificate }

private noncomputable def leaf3428InnerLog : WideLogData :=
  innerPair221Data

set_option maxRecDepth 1000000 in
private theorem leaf3428LocalValidity :
    LeafFacts leaf3428Box leaf3428Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3428Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (3233809155/3233695232) }) = true
      norm_num [leaf3428Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3428CertificateValid :
    WideCertificateValid leaf3428Box leaf3428Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk247ValidityFacts chi195ValidityFacts
    leaf3428LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3428CoverageChecked :
    coverageCheck (innerAD leaf3428Box) leaf3428InnerLog = true := by
  rfl'

private theorem leaf3428InnerLogValid :
    leaf3428InnerLog.Valid 8 (innerAD leaf3428Box) :=
  wideLogDataValid_of_cachedCheck endpoint67PositiveFacts
    endpoint64PositiveFacts.valid leaf3428CoverageChecked

private noncomputable def leaf3428InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (181709/262144) }

set_option maxRecDepth 1000000 in
private theorem leaf3428InputLogOnePlusV_eq :
    leaf3428InputLogOnePlusV = outerEnclosure 24
      (leaf3428Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3428RoundedFacts : LeafRoundedFacts 8
    leaf3428Certificate.logOnePlusV leaf3428InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3428InputLogOnePlusV_eq }

private noncomputable def leaf3428Inputs : Inputs :=
  inputsOfCaches globalInput sk247RoundedInputs
    chi195InputQChi innerPair221Input
    leaf3428InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3428LowerChecked :
    lowerCheck 24 leaf3428Box leaf3428Inputs = true := by
  rfl'

private theorem leaf3428CoversExact : CoversExact 8
    leaf3428Box leaf3428Certificate leaf3428InnerLog leaf3428Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk247RoundedFacts chi195RoundedFacts
    innerPair221RoundedFacts leaf3428RoundedFacts (by rfl)

private theorem leaf3428FlatSound : Sound leaf3428Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3428CertificateValid
    leaf3428InnerLogValid leaf3428CoversExact leaf3428LowerChecked

private noncomputable def leaf3429Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (509/128), kHi := (255/64), chiLo := (13/64), chiHi := (53/256) }

private noncomputable def leaf3429Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484773/2147483648) }, vSqrt := { lower := (8191/8192), upper := (274873778175/274864067584) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3881950733/2147483648) }, upper := { exponent := 0, mantissa := (29899/16384) } }, logOuter := sk248LogOuterCertificate, logK := sk248LogKCertificate, logChi := chi195LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (549737845759/549728135168) } }, logDArg := sk248LogDArgCertificate }

private noncomputable def leaf3429InnerLog : WideLogData :=
  innerPair221Data

set_option maxRecDepth 1000000 in
private theorem leaf3429LocalValidity :
    LeafFacts leaf3429Box leaf3429Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3429Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (274873778175/274864067584) }) = true
      norm_num [leaf3429Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3429CertificateValid :
    WideCertificateValid leaf3429Box leaf3429Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk248ValidityFacts chi195ValidityFacts
    leaf3429LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3429CoverageChecked :
    coverageCheck (innerAD leaf3429Box) leaf3429InnerLog = true := by
  rfl'

private theorem leaf3429InnerLogValid :
    leaf3429InnerLog.Valid 8 (innerAD leaf3429Box) :=
  wideLogDataValid_of_cachedCheck endpoint67PositiveFacts
    endpoint64PositiveFacts.valid leaf3429CoverageChecked

private noncomputable def leaf3429InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629377/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3429InputLogOnePlusV_eq :
    leaf3429InputLogOnePlusV = outerEnclosure 24
      (leaf3429Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3429RoundedFacts : LeafRoundedFacts 8
    leaf3429Certificate.logOnePlusV leaf3429InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3429InputLogOnePlusV_eq }

private noncomputable def leaf3429Inputs : Inputs :=
  inputsOfCaches globalInput sk248RoundedInputs
    chi195InputQChi innerPair221Input
    leaf3429InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3429LowerChecked :
    lowerCheck 24 leaf3429Box leaf3429Inputs = true := by
  rfl'

private theorem leaf3429CoversExact : CoversExact 8
    leaf3429Box leaf3429Certificate leaf3429InnerLog leaf3429Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk248RoundedFacts chi195RoundedFacts
    innerPair221RoundedFacts leaf3429RoundedFacts (by rfl)

private theorem leaf3429FlatSound : Sound leaf3429Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3429CertificateValid
    leaf3429InnerLogValid leaf3429CoversExact leaf3429LowerChecked

private noncomputable def leaf3430Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (511/128), chiLo := (13/64), chiHi := (53/256) }

private noncomputable def leaf3430Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484775/2147483648) }, vSqrt := { lower := (65527/65536), upper := (91624592725/91621346816) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3885358395/2147483648) }, upper := { exponent := 0, mantissa := (59851/32768) } }, logOuter := sk249LogOuterCertificate, logK := sk249LogKCertificate, logChi := chi195LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (183245939541/183242693632) } }, logDArg := sk249LogDArgCertificate }

private noncomputable def leaf3430InnerLog : WideLogData :=
  innerPair221Data

set_option maxRecDepth 1000000 in
private theorem leaf3430LocalValidity :
    LeafFacts leaf3430Box leaf3430Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3430Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (91624592725/91621346816) }) = true
      norm_num [leaf3430Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3430CertificateValid :
    WideCertificateValid leaf3430Box leaf3430Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk249ValidityFacts chi195ValidityFacts
    leaf3430LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3430CoverageChecked :
    coverageCheck (innerAD leaf3430Box) leaf3430InnerLog = true := by
  rfl'

private theorem leaf3430InnerLogValid :
    leaf3430InnerLog.Valid 8 (innerAD leaf3430Box) :=
  wideLogDataValid_of_cachedCheck endpoint67PositiveFacts
    endpoint64PositiveFacts.valid leaf3430CoverageChecked

private noncomputable def leaf3430InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (5814689/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3430InputLogOnePlusV_eq :
    leaf3430InputLogOnePlusV = outerEnclosure 24
      (leaf3430Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3430RoundedFacts : LeafRoundedFacts 8
    leaf3430Certificate.logOnePlusV leaf3430InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3430InputLogOnePlusV_eq }

private noncomputable def leaf3430Inputs : Inputs :=
  inputsOfCaches globalInput sk249RoundedInputs
    chi195InputQChi innerPair221Input
    leaf3430InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3430LowerChecked :
    lowerCheck 24 leaf3430Box leaf3430Inputs = true := by
  rfl'

private theorem leaf3430CoversExact : CoversExact 8
    leaf3430Box leaf3430Certificate leaf3430InnerLog leaf3430Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk249RoundedFacts chi195RoundedFacts
    innerPair221RoundedFacts leaf3430RoundedFacts (by rfl)

private theorem leaf3430FlatSound : Sound leaf3430Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3430CertificateValid
    leaf3430InnerLogValid leaf3430CoversExact leaf3430LowerChecked

private noncomputable def leaf3431Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (511/128), kHi := (4), chiLo := (13/64), chiHi := (53/256) }

private noncomputable def leaf3431Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484777/2147483648) }, vSqrt := { lower := (65527/65536), upper := (274873778175/274864013312) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3888766057/2147483648) }, upper := { exponent := 0, mantissa := (117/64) } }, logOuter := sk250LogOuterCertificate, logK := sk250LogKCertificate, logChi := chi195LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (549737791487/549728026624) } }, logDArg := sk250LogDArgCertificate }

private noncomputable def leaf3431InnerLog : WideLogData :=
  innerPair221Data

set_option maxRecDepth 1000000 in
private theorem leaf3431LocalValidity :
    LeafFacts leaf3431Box leaf3431Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3431Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (274873778175/274864013312) }) = true
      norm_num [leaf3431Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3431CertificateValid :
    WideCertificateValid leaf3431Box leaf3431Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk250ValidityFacts chi195ValidityFacts
    leaf3431LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3431CoverageChecked :
    coverageCheck (innerAD leaf3431Box) leaf3431InnerLog = true := by
  rfl'

private theorem leaf3431InnerLogValid :
    leaf3431InnerLog.Valid 8 (innerAD leaf3431Box) :=
  wideLogDataValid_of_cachedCheck endpoint67PositiveFacts
    endpoint64PositiveFacts.valid leaf3431CoverageChecked

private noncomputable def leaf3431InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629379/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3431InputLogOnePlusV_eq :
    leaf3431InputLogOnePlusV = outerEnclosure 24
      (leaf3431Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3431RoundedFacts : LeafRoundedFacts 8
    leaf3431Certificate.logOnePlusV leaf3431InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3431InputLogOnePlusV_eq }

private noncomputable def leaf3431Inputs : Inputs :=
  inputsOfCaches globalInput sk250RoundedInputs
    chi195InputQChi innerPair221Input
    leaf3431InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3431LowerChecked :
    lowerCheck 24 leaf3431Box leaf3431Inputs = true := by
  rfl'

private theorem leaf3431CoversExact : CoversExact 8
    leaf3431Box leaf3431Certificate leaf3431InnerLog leaf3431Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk250RoundedFacts chi195RoundedFacts
    innerPair221RoundedFacts leaf3431RoundedFacts (by rfl)

private theorem leaf3431FlatSound : Sound leaf3431Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3431CertificateValid
    leaf3431InnerLogValid leaf3431CoversExact leaf3431LowerChecked

private noncomputable def leaf3432Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (53/256), chiHi := (107/512) }

private noncomputable def leaf3432Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484371/2147483648) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431968512) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3911833727/2147483648) }, upper := { exponent := 0, mantissa := (60053/32768) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi223LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868890367/274863937024) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf3432InnerLog : WideLogData :=
  innerPair94Data

set_option maxRecDepth 1000000 in
private theorem leaf3432LocalValidity :
    LeafFacts leaf3432Box leaf3432Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3432Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431968512) }) = true
      norm_num [leaf3432Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3432CertificateValid :
    WideCertificateValid leaf3432Box leaf3432Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi223ValidityFacts
    leaf3432LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3432CoverageChecked :
    coverageCheck (innerAD leaf3432Box) leaf3432InnerLog = true := by
  rfl'

private theorem leaf3432InnerLogValid :
    leaf3432InnerLog.Valid 8 (innerAD leaf3432Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint61PositiveFacts.valid leaf3432CoverageChecked

private noncomputable def leaf3432InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629383/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3432InputLogOnePlusV_eq :
    leaf3432InputLogOnePlusV = outerEnclosure 24
      (leaf3432Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3432RoundedFacts : LeafRoundedFacts 8
    leaf3432Certificate.logOnePlusV leaf3432InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3432InputLogOnePlusV_eq }

private noncomputable def leaf3432Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi223InputQChi innerPair94Input
    leaf3432InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3432LowerChecked :
    lowerCheck 24 leaf3432Box leaf3432Inputs = true := by
  rfl'

private theorem leaf3432CoversExact : CoversExact 8
    leaf3432Box leaf3432Certificate leaf3432InnerLog leaf3432Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi223RoundedFacts
    innerPair94RoundedFacts leaf3432RoundedFacts (by rfl)

private theorem leaf3432FlatSound : Sound leaf3432Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3432CertificateValid
    leaf3432InnerLogValid leaf3432CoversExact leaf3432LowerChecked

private noncomputable def leaf3433Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (107/512), chiHi := (27/128) }

private noncomputable def leaf3433Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484373/2147483648) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431903232) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3928478853/2147483648) }, upper := { exponent := 0, mantissa := (15077/8192) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi224LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868825087/274863806464) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf3433InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3433LocalValidity :
    LeafFacts leaf3433Box leaf3433Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3433Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431903232) }) = true
      norm_num [leaf3433Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3433CertificateValid :
    WideCertificateValid leaf3433Box leaf3433Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi224ValidityFacts
    leaf3433LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3433CoverageChecked :
    coverageCheck (innerAD leaf3433Box) leaf3433InnerLog = true := by
  rfl'

private theorem leaf3433InnerLogValid :
    leaf3433InnerLog.Valid 8 (innerAD leaf3433Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3433CoverageChecked

private noncomputable def leaf3433InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629387/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3433InputLogOnePlusV_eq :
    leaf3433InputLogOnePlusV = outerEnclosure 24
      (leaf3433Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3433RoundedFacts : LeafRoundedFacts 8
    leaf3433Certificate.logOnePlusV leaf3433InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3433InputLogOnePlusV_eq }

private noncomputable def leaf3433Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi224InputQChi innerPair91Input
    leaf3433InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3433LowerChecked :
    lowerCheck 24 leaf3433Box leaf3433Inputs = true := by
  rfl'

private theorem leaf3433CoversExact : CoversExact 8
    leaf3433Box leaf3433Certificate leaf3433InnerLog leaf3433Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi224RoundedFacts
    innerPair91RoundedFacts leaf3433RoundedFacts (by rfl)

private theorem leaf3433FlatSound : Sound leaf3433Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3433CertificateValid
    leaf3433InnerLogValid leaf3433CoversExact leaf3433LowerChecked

private noncomputable def leaf3434Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (53/256), chiHi := (107/512) }

private noncomputable def leaf3434Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484373/2147483648) }, vSqrt := { lower := (65527/65536), upper := (3054153819/3054043136) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3918780117/2147483648) }, upper := { exponent := 0, mantissa := (235/128) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi223LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (6108196955/6108086272) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf3434InnerLog : WideLogData :=
  innerPair94Data

set_option maxRecDepth 1000000 in
private theorem leaf3434LocalValidity :
    LeafFacts leaf3434Box leaf3434Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3434Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (3054153819/3054043136) }) = true
      norm_num [leaf3434Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3434CertificateValid :
    WideCertificateValid leaf3434Box leaf3434Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi223ValidityFacts
    leaf3434LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3434CoverageChecked :
    coverageCheck (innerAD leaf3434Box) leaf3434InnerLog = true := by
  rfl'

private theorem leaf3434InnerLogValid :
    leaf3434InnerLog.Valid 8 (innerAD leaf3434Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint61PositiveFacts.valid leaf3434CoverageChecked

private noncomputable def leaf3434InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629385/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3434InputLogOnePlusV_eq :
    leaf3434InputLogOnePlusV = outerEnclosure 24
      (leaf3434Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3434RoundedFacts : LeafRoundedFacts 8
    leaf3434Certificate.logOnePlusV leaf3434InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3434InputLogOnePlusV_eq }

private noncomputable def leaf3434Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi223InputQChi innerPair94Input
    leaf3434InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3434LowerChecked :
    lowerCheck 24 leaf3434Box leaf3434Inputs = true := by
  rfl'

private theorem leaf3434CoversExact : CoversExact 8
    leaf3434Box leaf3434Certificate leaf3434InnerLog leaf3434Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi223RoundedFacts
    innerPair94RoundedFacts leaf3434RoundedFacts (by rfl)

private theorem leaf3434FlatSound : Sound leaf3434Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3434CertificateValid
    leaf3434InnerLogValid leaf3434CoversExact leaf3434LowerChecked

private noncomputable def leaf3435Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (107/512), chiHi := (27/128) }

private noncomputable def leaf3435Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484375/2147483648) }, vSqrt := { lower := (65527/65536), upper := (137436921855/137431875584) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3935490775/2147483648) }, upper := { exponent := 0, mantissa := (59/32) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi224LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (274868797439/274863751168) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf3435InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3435LocalValidity :
    LeafFacts leaf3435Box leaf3435Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3435Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (137436921855/137431875584) }) = true
      norm_num [leaf3435Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3435CertificateValid :
    WideCertificateValid leaf3435Box leaf3435Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi224ValidityFacts
    leaf3435LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3435CoverageChecked :
    coverageCheck (innerAD leaf3435Box) leaf3435InnerLog = true := by
  rfl'

private theorem leaf3435InnerLogValid :
    leaf3435InnerLog.Valid 8 (innerAD leaf3435Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3435CoverageChecked

private noncomputable def leaf3435InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629389/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3435InputLogOnePlusV_eq :
    leaf3435InputLogOnePlusV = outerEnclosure 24
      (leaf3435Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3435RoundedFacts : LeafRoundedFacts 8
    leaf3435Certificate.logOnePlusV leaf3435InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3435InputLogOnePlusV_eq }

private noncomputable def leaf3435Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi224InputQChi innerPair91Input
    leaf3435InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3435LowerChecked :
    lowerCheck 24 leaf3435Box leaf3435Inputs = true := by
  rfl'

private theorem leaf3435CoversExact : CoversExact 8
    leaf3435Box leaf3435Certificate leaf3435InnerLog leaf3435Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi224RoundedFacts
    innerPair91RoundedFacts leaf3435RoundedFacts (by rfl)

private theorem leaf3435FlatSound : Sound leaf3435Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3435CertificateValid
    leaf3435InnerLogValid leaf3435CoversExact leaf3435LowerChecked

private noncomputable def leaf3436Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (27/128), chiHi := (109/512) }

private noncomputable def leaf3436Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484371/2147483648) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486378752) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3930969071/2147483648) }, upper := { exponent := 0, mantissa := (60345/32768) } }, logOuter := sk237LogOuterCertificate, logK := sk237LogKCertificate, logChi := chi225LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973763123/54972757504) } }, logDArg := sk237LogDArgCertificate }

private noncomputable def leaf3436InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3436LocalValidity :
    LeafFacts leaf3436Box leaf3436Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3436Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486378752) }) = true
      norm_num [leaf3436Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3436CertificateValid :
    WideCertificateValid leaf3436Box leaf3436Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk237ValidityFacts chi225ValidityFacts
    leaf3436LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3436CoverageChecked :
    coverageCheck (innerAD leaf3436Box) leaf3436InnerLog = true := by
  rfl'

private theorem leaf3436InnerLogValid :
    leaf3436InnerLog.Valid 8 (innerAD leaf3436Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3436CoverageChecked

private noncomputable def leaf3436InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907347/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3436InputLogOnePlusV_eq :
    leaf3436InputLogOnePlusV = outerEnclosure 24
      (leaf3436Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3436RoundedFacts : LeafRoundedFacts 8
    leaf3436Certificate.logOnePlusV leaf3436InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3436InputLogOnePlusV_eq }

private noncomputable def leaf3436Inputs : Inputs :=
  inputsOfCaches globalInput sk237RoundedInputs
    chi225InputQChi innerPair91Input
    leaf3436InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3436LowerChecked :
    lowerCheck 24 leaf3436Box leaf3436Inputs = true := by
  rfl'

private theorem leaf3436CoversExact : CoversExact 8
    leaf3436Box leaf3436Certificate leaf3436InnerLog leaf3436Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk237RoundedFacts chi225RoundedFacts
    innerPair91RoundedFacts leaf3436RoundedFacts (by rfl)

private theorem leaf3436FlatSound : Sound leaf3436Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3436CertificateValid
    leaf3436InnerLogValid leaf3436CoversExact leaf3436LowerChecked

private noncomputable def leaf3437Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (109/512), chiHi := (55/256) }

private noncomputable def leaf3437Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484373/2147483648) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810609664) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3947483133/2147483648) }, upper := { exponent := 0, mantissa := (30299/16384) } }, logOuter := sk237LogOuterCertificate, logK := sk237LogKCertificate, logChi := chi226LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91622916949/91621219328) } }, logDArg := sk237LogDArgCertificate }

private noncomputable def leaf3437InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3437LocalValidity :
    LeafFacts leaf3437Box leaf3437Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3437Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810609664) }) = true
      norm_num [leaf3437Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3437CertificateValid :
    WideCertificateValid leaf3437Box leaf3437Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk237ValidityFacts chi226ValidityFacts
    leaf3437LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3437CoverageChecked :
    coverageCheck (innerAD leaf3437Box) leaf3437InnerLog = true := by
  rfl'

private theorem leaf3437InnerLogValid :
    leaf3437InnerLog.Valid 8 (innerAD leaf3437Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3437CoverageChecked

private noncomputable def leaf3437InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726837/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf3437InputLogOnePlusV_eq :
    leaf3437InputLogOnePlusV = outerEnclosure 24
      (leaf3437Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3437RoundedFacts : LeafRoundedFacts 8
    leaf3437Certificate.logOnePlusV leaf3437InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3437InputLogOnePlusV_eq }

private noncomputable def leaf3437Inputs : Inputs :=
  inputsOfCaches globalInput sk237RoundedInputs
    chi226InputQChi innerPair91Input
    leaf3437InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3437LowerChecked :
    lowerCheck 24 leaf3437Box leaf3437Inputs = true := by
  rfl'

private theorem leaf3437CoversExact : CoversExact 8
    leaf3437Box leaf3437Certificate leaf3437InnerLog leaf3437Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk237RoundedFacts chi226RoundedFacts
    innerPair91RoundedFacts leaf3437RoundedFacts (by rfl)

private theorem leaf3437FlatSound : Sound leaf3437Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3437CertificateValid
    leaf3437InnerLogValid leaf3437CoversExact leaf3437LowerChecked

private noncomputable def leaf3438Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (27/128), chiHi := (109/512) }

private noncomputable def leaf3438Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484373/2147483648) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810621952) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3938046525/2147483648) }, upper := { exponent := 0, mantissa := (30227/16384) } }, logOuter := sk238LogOuterCertificate, logK := sk238LogKCertificate, logChi := chi225LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91622929237/91621243904) } }, logDArg := sk238LogDArgCertificate }

private noncomputable def leaf3438InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3438LocalValidity :
    LeafFacts leaf3438Box leaf3438Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3438Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810621952) }) = true
      norm_num [leaf3438Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3438CertificateValid :
    WideCertificateValid leaf3438Box leaf3438Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk238ValidityFacts chi225ValidityFacts
    leaf3438LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3438CoverageChecked :
    coverageCheck (innerAD leaf3438Box) leaf3438InnerLog = true := by
  rfl'

private theorem leaf3438InnerLogValid :
    leaf3438InnerLog.Valid 8 (innerAD leaf3438Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3438CoverageChecked

private noncomputable def leaf3438InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629389/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3438InputLogOnePlusV_eq :
    leaf3438InputLogOnePlusV = outerEnclosure 24
      (leaf3438Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3438RoundedFacts : LeafRoundedFacts 8
    leaf3438Certificate.logOnePlusV leaf3438InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3438InputLogOnePlusV_eq }

private noncomputable def leaf3438Inputs : Inputs :=
  inputsOfCaches globalInput sk238RoundedInputs
    chi225InputQChi innerPair91Input
    leaf3438InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3438LowerChecked :
    lowerCheck 24 leaf3438Box leaf3438Inputs = true := by
  rfl'

private theorem leaf3438CoversExact : CoversExact 8
    leaf3438Box leaf3438Certificate leaf3438InnerLog leaf3438Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk238RoundedFacts chi225RoundedFacts
    innerPair91RoundedFacts leaf3438RoundedFacts (by rfl)

private theorem leaf3438FlatSound : Sound leaf3438Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3438CertificateValid
    leaf3438InnerLogValid leaf3438CoversExact leaf3438LowerChecked

private noncomputable def leaf3439Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (109/512), chiHi := (55/256) }

private noncomputable def leaf3439Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484375/2147483648) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431800832) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3954626119/2147483648) }, upper := { exponent := 0, mantissa := (15177/8192) } }, logOuter := sk238LogOuterCertificate, logK := sk238LogKCertificate, logChi := chi226LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868722687/274863601664) } }, logDArg := sk238LogDArgCertificate }

private noncomputable def leaf3439InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3439LocalValidity :
    LeafFacts leaf3439Box leaf3439Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3439Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431800832) }) = true
      norm_num [leaf3439Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3439CertificateValid :
    WideCertificateValid leaf3439Box leaf3439Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk238ValidityFacts chi226ValidityFacts
    leaf3439LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3439CoverageChecked :
    coverageCheck (innerAD leaf3439Box) leaf3439InnerLog = true := by
  rfl'

private theorem leaf3439InnerLogValid :
    leaf3439InnerLog.Valid 8 (innerAD leaf3439Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3439CoverageChecked

private noncomputable def leaf3439InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629393/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3439InputLogOnePlusV_eq :
    leaf3439InputLogOnePlusV = outerEnclosure 24
      (leaf3439Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3439RoundedFacts : LeafRoundedFacts 8
    leaf3439Certificate.logOnePlusV leaf3439InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3439InputLogOnePlusV_eq }

private noncomputable def leaf3439Inputs : Inputs :=
  inputsOfCaches globalInput sk238RoundedInputs
    chi226InputQChi innerPair91Input
    leaf3439InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3439LowerChecked :
    lowerCheck 24 leaf3439Box leaf3439Inputs = true := by
  rfl'

private theorem leaf3439CoversExact : CoversExact 8
    leaf3439Box leaf3439Certificate leaf3439InnerLog leaf3439Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk238RoundedFacts chi226RoundedFacts
    innerPair91RoundedFacts leaf3439RoundedFacts (by rfl)

private theorem leaf3439FlatSound : Sound leaf3439Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3439CertificateValid
    leaf3439InnerLogValid leaf3439CoversExact leaf3439LowerChecked

private noncomputable def leaf3440Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (55/256), chiHi := (111/512) }

private noncomputable def leaf3440Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484375/2147483648) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431764224) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3963997195/2147483648) }, upper := { exponent := 0, mantissa := (60851/32768) } }, logOuter := sk237LogOuterCertificate, logK := sk237LogKCertificate, logChi := chi227LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868686079/274863528448) } }, logDArg := sk237LogDArgCertificate }

private noncomputable def leaf3440InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3440LocalValidity :
    LeafFacts leaf3440Box leaf3440Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3440Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431764224) }) = true
      norm_num [leaf3440Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3440CertificateValid :
    WideCertificateValid leaf3440Box leaf3440Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk237ValidityFacts chi227ValidityFacts
    leaf3440LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3440CoverageChecked :
    coverageCheck (innerAD leaf3440Box) leaf3440InnerLog = true := by
  rfl'

private theorem leaf3440InnerLogValid :
    leaf3440InnerLog.Valid 8 (innerAD leaf3440Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3440CoverageChecked

private noncomputable def leaf3440InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907349/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3440InputLogOnePlusV_eq :
    leaf3440InputLogOnePlusV = outerEnclosure 24
      (leaf3440Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3440RoundedFacts : LeafRoundedFacts 8
    leaf3440Certificate.logOnePlusV leaf3440InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3440InputLogOnePlusV_eq }

private noncomputable def leaf3440Inputs : Inputs :=
  inputsOfCaches globalInput sk237RoundedInputs
    chi227InputQChi innerPair91Input
    leaf3440InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3440LowerChecked :
    lowerCheck 24 leaf3440Box leaf3440Inputs = true := by
  rfl'

private theorem leaf3440CoversExact : CoversExact 8
    leaf3440Box leaf3440Certificate leaf3440InnerLog leaf3440Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk237RoundedFacts chi227RoundedFacts
    innerPair91RoundedFacts leaf3440RoundedFacts (by rfl)

private theorem leaf3440FlatSound : Sound leaf3440Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3440CertificateValid
    leaf3440InnerLogValid leaf3440CoversExact leaf3440LowerChecked

private noncomputable def leaf3441Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (111/512), chiHi := (7/32) }

private noncomputable def leaf3441Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484377/2147483648) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431699456) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3980511257/2147483648) }, upper := { exponent := 0, mantissa := (3819/2048) } }, logOuter := sk237LogOuterCertificate, logK := sk237LogKCertificate, logChi := chi228LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868621311/274863398912) } }, logDArg := sk237LogDArgCertificate }

private noncomputable def leaf3441InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3441LocalValidity :
    LeafFacts leaf3441Box leaf3441Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3441Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431699456) }) = true
      norm_num [leaf3441Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3441CertificateValid :
    WideCertificateValid leaf3441Box leaf3441Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk237ValidityFacts chi228ValidityFacts
    leaf3441LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3441CoverageChecked :
    coverageCheck (innerAD leaf3441Box) leaf3441InnerLog = true := by
  rfl'

private theorem leaf3441InnerLogValid :
    leaf3441InnerLog.Valid 8 (innerAD leaf3441Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3441CoverageChecked

private noncomputable def leaf3441InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453675/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf3441InputLogOnePlusV_eq :
    leaf3441InputLogOnePlusV = outerEnclosure 24
      (leaf3441Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3441RoundedFacts : LeafRoundedFacts 8
    leaf3441Certificate.logOnePlusV leaf3441InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3441InputLogOnePlusV_eq }

private noncomputable def leaf3441Inputs : Inputs :=
  inputsOfCaches globalInput sk237RoundedInputs
    chi228InputQChi innerPair91Input
    leaf3441InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3441LowerChecked :
    lowerCheck 24 leaf3441Box leaf3441Inputs = true := by
  rfl'

private theorem leaf3441CoversExact : CoversExact 8
    leaf3441Box leaf3441Certificate leaf3441InnerLog leaf3441Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk237RoundedFacts chi228RoundedFacts
    innerPair91RoundedFacts leaf3441RoundedFacts (by rfl)

private theorem leaf3441FlatSound : Sound leaf3441Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3441CertificateValid
    leaf3441InnerLogValid leaf3441CoversExact leaf3441LowerChecked

private noncomputable def leaf3442Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (55/256), chiHi := (111/512) }

private noncomputable def leaf3442Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484377/2147483648) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431735808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3971205713/2147483648) }, upper := { exponent := 0, mantissa := (30481/16384) } }, logOuter := sk238LogOuterCertificate, logK := sk238LogKCertificate, logChi := chi227LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868657663/274863471616) } }, logDArg := sk238LogDArgCertificate }

private noncomputable def leaf3442InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3442LocalValidity :
    LeafFacts leaf3442Box leaf3442Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3442Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431735808) }) = true
      norm_num [leaf3442Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3442CertificateValid :
    WideCertificateValid leaf3442Box leaf3442Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk238ValidityFacts chi227ValidityFacts
    leaf3442LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3442CoverageChecked :
    coverageCheck (innerAD leaf3442Box) leaf3442InnerLog = true := by
  rfl'

private theorem leaf3442InnerLogValid :
    leaf3442InnerLog.Valid 8 (innerAD leaf3442Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3442CoverageChecked

private noncomputable def leaf3442InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629397/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3442InputLogOnePlusV_eq :
    leaf3442InputLogOnePlusV = outerEnclosure 24
      (leaf3442Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3442RoundedFacts : LeafRoundedFacts 8
    leaf3442Certificate.logOnePlusV leaf3442InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3442InputLogOnePlusV_eq }

private noncomputable def leaf3442Inputs : Inputs :=
  inputsOfCaches globalInput sk238RoundedInputs
    chi227InputQChi innerPair91Input
    leaf3442InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3442LowerChecked :
    lowerCheck 24 leaf3442Box leaf3442Inputs = true := by
  rfl'

private theorem leaf3442CoversExact : CoversExact 8
    leaf3442Box leaf3442Certificate leaf3442InnerLog leaf3442Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk238RoundedFacts chi227RoundedFacts
    innerPair91RoundedFacts leaf3442RoundedFacts (by rfl)

private theorem leaf3442FlatSound : Sound leaf3442Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3442CertificateValid
    leaf3442InnerLogValid leaf3442CoversExact leaf3442LowerChecked

private noncomputable def leaf3443Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (111/512), chiHi := (7/32) }

private noncomputable def leaf3443Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484379/2147483648) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810556928) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3987785307/2147483648) }, upper := { exponent := 0, mantissa := (1913/1024) } }, logOuter := sk238LogOuterCertificate, logK := sk238LogKCertificate, logChi := chi228LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91622864213/91621113856) } }, logDArg := sk238LogDArgCertificate }

private noncomputable def leaf3443InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3443LocalValidity :
    LeafFacts leaf3443Box leaf3443Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3443Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810556928) }) = true
      norm_num [leaf3443Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3443CertificateValid :
    WideCertificateValid leaf3443Box leaf3443Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk238ValidityFacts chi228ValidityFacts
    leaf3443LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3443CoverageChecked :
    coverageCheck (innerAD leaf3443Box) leaf3443InnerLog = true := by
  rfl'

private theorem leaf3443InnerLogValid :
    leaf3443InnerLog.Valid 8 (innerAD leaf3443Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3443CoverageChecked

private noncomputable def leaf3443InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629401/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3443InputLogOnePlusV_eq :
    leaf3443InputLogOnePlusV = outerEnclosure 24
      (leaf3443Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3443RoundedFacts : LeafRoundedFacts 8
    leaf3443Certificate.logOnePlusV leaf3443InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3443InputLogOnePlusV_eq }

private noncomputable def leaf3443Inputs : Inputs :=
  inputsOfCaches globalInput sk238RoundedInputs
    chi228InputQChi innerPair91Input
    leaf3443InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3443LowerChecked :
    lowerCheck 24 leaf3443Box leaf3443Inputs = true := by
  rfl'

private theorem leaf3443CoversExact : CoversExact 8
    leaf3443Box leaf3443Certificate leaf3443InnerLog leaf3443Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk238RoundedFacts chi228RoundedFacts
    innerPair91RoundedFacts leaf3443RoundedFacts (by rfl)

private theorem leaf3443FlatSound : Sound leaf3443Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3443CertificateValid
    leaf3443InnerLogValid leaf3443CoversExact leaf3443LowerChecked

private noncomputable def leaf3444Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (27/128), chiHi := (109/512) }

private noncomputable def leaf3444Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484375/2147483648) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431837952) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3945123979/2147483648) }, upper := { exponent := 0, mantissa := (60563/32768) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi225LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868759807/274863675904) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf3444InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3444LocalValidity :
    LeafFacts leaf3444Box leaf3444Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3444Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431837952) }) = true
      norm_num [leaf3444Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3444CertificateValid :
    WideCertificateValid leaf3444Box leaf3444Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi225ValidityFacts
    leaf3444LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3444CoverageChecked :
    coverageCheck (innerAD leaf3444Box) leaf3444InnerLog = true := by
  rfl'

private theorem leaf3444InnerLogValid :
    leaf3444InnerLog.Valid 8 (innerAD leaf3444Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3444CoverageChecked

private noncomputable def leaf3444InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629391/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3444InputLogOnePlusV_eq :
    leaf3444InputLogOnePlusV = outerEnclosure 24
      (leaf3444Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3444RoundedFacts : LeafRoundedFacts 8
    leaf3444Certificate.logOnePlusV leaf3444InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3444InputLogOnePlusV_eq }

private noncomputable def leaf3444Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi225InputQChi innerPair91Input
    leaf3444InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3444LowerChecked :
    lowerCheck 24 leaf3444Box leaf3444Inputs = true := by
  rfl'

private theorem leaf3444CoversExact : CoversExact 8
    leaf3444Box leaf3444Certificate leaf3444InnerLog leaf3444Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi225RoundedFacts
    innerPair91RoundedFacts leaf3444RoundedFacts (by rfl)

private theorem leaf3444FlatSound : Sound leaf3444Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3444CertificateValid
    leaf3444InnerLogValid leaf3444CoversExact leaf3444LowerChecked

private noncomputable def leaf3445Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (109/512), chiHi := (55/256) }

private noncomputable def leaf3445Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484377/2147483648) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431772672) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3961769105/2147483648) }, upper := { exponent := 0, mantissa := (30409/16384) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi226LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868694527/274863545344) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf3445InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3445LocalValidity :
    LeafFacts leaf3445Box leaf3445Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3445Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431772672) }) = true
      norm_num [leaf3445Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3445CertificateValid :
    WideCertificateValid leaf3445Box leaf3445Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi226ValidityFacts
    leaf3445LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3445CoverageChecked :
    coverageCheck (innerAD leaf3445Box) leaf3445InnerLog = true := by
  rfl'

private theorem leaf3445InnerLogValid :
    leaf3445InnerLog.Valid 8 (innerAD leaf3445Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3445CoverageChecked

private noncomputable def leaf3445InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629395/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3445InputLogOnePlusV_eq :
    leaf3445InputLogOnePlusV = outerEnclosure 24
      (leaf3445Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3445RoundedFacts : LeafRoundedFacts 8
    leaf3445Certificate.logOnePlusV leaf3445InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3445InputLogOnePlusV_eq }

private noncomputable def leaf3445Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi226InputQChi innerPair91Input
    leaf3445InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3445LowerChecked :
    lowerCheck 24 leaf3445Box leaf3445Inputs = true := by
  rfl'

private theorem leaf3445CoversExact : CoversExact 8
    leaf3445Box leaf3445Certificate leaf3445InnerLog leaf3445Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi226RoundedFacts
    innerPair91RoundedFacts leaf3445RoundedFacts (by rfl)

private theorem leaf3445FlatSound : Sound leaf3445Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3445CertificateValid
    leaf3445InnerLogValid leaf3445CoversExact leaf3445LowerChecked

private noncomputable def leaf3446Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (27/128), chiHi := (109/512) }

private noncomputable def leaf3446Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484377/2147483648) }, vSqrt := { lower := (65527/65536), upper := (137436921855/137431810048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3952201433/2147483648) }, upper := { exponent := 0, mantissa := (237/128) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi225LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (274868731903/274863620096) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf3446InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3446LocalValidity :
    LeafFacts leaf3446Box leaf3446Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3446Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (137436921855/137431810048) }) = true
      norm_num [leaf3446Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3446CertificateValid :
    WideCertificateValid leaf3446Box leaf3446Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi225ValidityFacts
    leaf3446LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3446CoverageChecked :
    coverageCheck (innerAD leaf3446Box) leaf3446InnerLog = true := by
  rfl'

private theorem leaf3446InnerLogValid :
    leaf3446InnerLog.Valid 8 (innerAD leaf3446Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3446CoverageChecked

private noncomputable def leaf3446InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629393/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3446InputLogOnePlusV_eq :
    leaf3446InputLogOnePlusV = outerEnclosure 24
      (leaf3446Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3446RoundedFacts : LeafRoundedFacts 8
    leaf3446Certificate.logOnePlusV leaf3446InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3446InputLogOnePlusV_eq }

private noncomputable def leaf3446Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi225InputQChi innerPair91Input
    leaf3446InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3446LowerChecked :
    lowerCheck 24 leaf3446Box leaf3446Inputs = true := by
  rfl'

private theorem leaf3446CoversExact : CoversExact 8
    leaf3446Box leaf3446Certificate leaf3446InnerLog leaf3446Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi225RoundedFacts
    innerPair91RoundedFacts leaf3446RoundedFacts (by rfl)

private theorem leaf3446FlatSound : Sound leaf3446Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3446CertificateValid
    leaf3446InnerLogValid leaf3446CoversExact leaf3446LowerChecked

private noncomputable def leaf3447Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (109/512), chiHi := (55/256) }

private noncomputable def leaf3447Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484379/2147483648) }, vSqrt := { lower := (65527/65536), upper := (45812307285/45810581504) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3968912091/2147483648) }, upper := { exponent := 0, mantissa := (119/64) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi226LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (91622888789/91621163008) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf3447InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3447LocalValidity :
    LeafFacts leaf3447Box leaf3447Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3447Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (45812307285/45810581504) }) = true
      norm_num [leaf3447Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3447CertificateValid :
    WideCertificateValid leaf3447Box leaf3447Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi226ValidityFacts
    leaf3447LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3447CoverageChecked :
    coverageCheck (innerAD leaf3447Box) leaf3447InnerLog = true := by
  rfl'

private theorem leaf3447InnerLogValid :
    leaf3447InnerLog.Valid 8 (innerAD leaf3447Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3447CoverageChecked

private noncomputable def leaf3447InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629397/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3447InputLogOnePlusV_eq :
    leaf3447InputLogOnePlusV = outerEnclosure 24
      (leaf3447Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3447RoundedFacts : LeafRoundedFacts 8
    leaf3447Certificate.logOnePlusV leaf3447InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3447InputLogOnePlusV_eq }

private noncomputable def leaf3447Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi226InputQChi innerPair91Input
    leaf3447InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3447LowerChecked :
    lowerCheck 24 leaf3447Box leaf3447Inputs = true := by
  rfl'

private theorem leaf3447CoversExact : CoversExact 8
    leaf3447Box leaf3447Certificate leaf3447InnerLog leaf3447Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi226RoundedFacts
    innerPair91RoundedFacts leaf3447RoundedFacts (by rfl)

private theorem leaf3447FlatSound : Sound leaf3447Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3447CertificateValid
    leaf3447InnerLogValid leaf3447CoversExact leaf3447LowerChecked

private noncomputable def leaf3448Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (55/256), chiHi := (111/512) }

private noncomputable def leaf3448Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484379/2147483648) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431707392) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3978414231/2147483648) }, upper := { exponent := 0, mantissa := (61073/32768) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi227LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868629247/274863414784) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf3448InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3448LocalValidity :
    LeafFacts leaf3448Box leaf3448Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3448Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431707392) }) = true
      norm_num [leaf3448Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3448CertificateValid :
    WideCertificateValid leaf3448Box leaf3448Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi227ValidityFacts
    leaf3448LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3448CoverageChecked :
    coverageCheck (innerAD leaf3448Box) leaf3448InnerLog = true := by
  rfl'

private theorem leaf3448InnerLogValid :
    leaf3448InnerLog.Valid 8 (innerAD leaf3448Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3448CoverageChecked

private noncomputable def leaf3448InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629399/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3448InputLogOnePlusV_eq :
    leaf3448InputLogOnePlusV = outerEnclosure 24
      (leaf3448Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3448RoundedFacts : LeafRoundedFacts 8
    leaf3448Certificate.logOnePlusV leaf3448InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3448InputLogOnePlusV_eq }

private noncomputable def leaf3448Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi227InputQChi innerPair91Input
    leaf3448InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3448LowerChecked :
    lowerCheck 24 leaf3448Box leaf3448Inputs = true := by
  rfl'

private theorem leaf3448CoversExact : CoversExact 8
    leaf3448Box leaf3448Certificate leaf3448InnerLog leaf3448Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi227RoundedFacts
    innerPair91RoundedFacts leaf3448RoundedFacts (by rfl)

private theorem leaf3448FlatSound : Sound leaf3448Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3448CertificateValid
    leaf3448InnerLogValid leaf3448CoversExact leaf3448LowerChecked

private noncomputable def leaf3449Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (111/512), chiHi := (7/32) }

private noncomputable def leaf3449Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484381/2147483648) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431642112) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3995059357/2147483648) }, upper := { exponent := 0, mantissa := (3833/2048) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi228LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868563967/274863284224) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf3449InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3449LocalValidity :
    LeafFacts leaf3449Box leaf3449Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3449Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431642112) }) = true
      norm_num [leaf3449Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3449CertificateValid :
    WideCertificateValid leaf3449Box leaf3449Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi228ValidityFacts
    leaf3449LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3449CoverageChecked :
    coverageCheck (innerAD leaf3449Box) leaf3449InnerLog = true := by
  rfl'

private theorem leaf3449InnerLogValid :
    leaf3449InnerLog.Valid 8 (innerAD leaf3449Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3449CoverageChecked

private noncomputable def leaf3449InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629403/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3449InputLogOnePlusV_eq :
    leaf3449InputLogOnePlusV = outerEnclosure 24
      (leaf3449Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3449RoundedFacts : LeafRoundedFacts 8
    leaf3449Certificate.logOnePlusV leaf3449InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3449InputLogOnePlusV_eq }

private noncomputable def leaf3449Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi228InputQChi innerPair91Input
    leaf3449InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3449LowerChecked :
    lowerCheck 24 leaf3449Box leaf3449Inputs = true := by
  rfl'

private theorem leaf3449CoversExact : CoversExact 8
    leaf3449Box leaf3449Certificate leaf3449InnerLog leaf3449Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi228RoundedFacts
    innerPair91RoundedFacts leaf3449RoundedFacts (by rfl)

private theorem leaf3449FlatSound : Sound leaf3449Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3449CertificateValid
    leaf3449InnerLogValid leaf3449CoversExact leaf3449LowerChecked

private noncomputable def leaf3450Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (55/256), chiHi := (111/512) }

private noncomputable def leaf3450Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484381/2147483648) }, vSqrt := { lower := (65527/65536), upper := (137436921855/137431678976) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3985622749/2147483648) }, upper := { exponent := 0, mantissa := (239/128) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi227LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (274868600831/274863357952) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf3450InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3450LocalValidity :
    LeafFacts leaf3450Box leaf3450Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3450Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (137436921855/137431678976) }) = true
      norm_num [leaf3450Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3450CertificateValid :
    WideCertificateValid leaf3450Box leaf3450Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi227ValidityFacts
    leaf3450LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3450CoverageChecked :
    coverageCheck (innerAD leaf3450Box) leaf3450InnerLog = true := by
  rfl'

private theorem leaf3450InnerLogValid :
    leaf3450InnerLog.Valid 8 (innerAD leaf3450Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3450CoverageChecked

private noncomputable def leaf3450InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629401/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3450InputLogOnePlusV_eq :
    leaf3450InputLogOnePlusV = outerEnclosure 24
      (leaf3450Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3450RoundedFacts : LeafRoundedFacts 8
    leaf3450Certificate.logOnePlusV leaf3450InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3450InputLogOnePlusV_eq }

private noncomputable def leaf3450Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi227InputQChi innerPair91Input
    leaf3450InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3450LowerChecked :
    lowerCheck 24 leaf3450Box leaf3450Inputs = true := by
  rfl'

private theorem leaf3450CoversExact : CoversExact 8
    leaf3450Box leaf3450Certificate leaf3450InnerLog leaf3450Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi227RoundedFacts
    innerPair91RoundedFacts leaf3450RoundedFacts (by rfl)

private theorem leaf3450FlatSound : Sound leaf3450Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3450CertificateValid
    leaf3450InnerLogValid leaf3450CoversExact leaf3450LowerChecked

private noncomputable def leaf3451Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (111/512), chiHi := (7/32) }

private noncomputable def leaf3451Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484383/2147483648) }, vSqrt := { lower := (65527/65536), upper := (27487384371/27486322688) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (4002333407/2147483648) }, upper := { exponent := 0, mantissa := (15/8) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi228LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (54973707059/54972645376) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf3451InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3451LocalValidity :
    LeafFacts leaf3451Box leaf3451Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3451Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (27487384371/27486322688) }) = true
      norm_num [leaf3451Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3451CertificateValid :
    WideCertificateValid leaf3451Box leaf3451Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi228ValidityFacts
    leaf3451LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3451CoverageChecked :
    coverageCheck (innerAD leaf3451Box) leaf3451InnerLog = true := by
  rfl'

private theorem leaf3451InnerLogValid :
    leaf3451InnerLog.Valid 8 (innerAD leaf3451Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3451CoverageChecked

private noncomputable def leaf3451InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629405/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3451InputLogOnePlusV_eq :
    leaf3451InputLogOnePlusV = outerEnclosure 24
      (leaf3451Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3451RoundedFacts : LeafRoundedFacts 8
    leaf3451Certificate.logOnePlusV leaf3451InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3451InputLogOnePlusV_eq }

private noncomputable def leaf3451Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi228InputQChi innerPair91Input
    leaf3451InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3451LowerChecked :
    lowerCheck 24 leaf3451Box leaf3451Inputs = true := by
  rfl'

private theorem leaf3451CoversExact : CoversExact 8
    leaf3451Box leaf3451Certificate leaf3451InnerLog leaf3451Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi228RoundedFacts
    innerPair91RoundedFacts leaf3451RoundedFacts (by rfl)

private theorem leaf3451FlatSound : Sound leaf3451Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3451CertificateValid
    leaf3451InnerLogValid leaf3451CoversExact leaf3451LowerChecked

private noncomputable def component70Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (13/64), chiHi := (53/256) }

set_option maxRecDepth 1000000 in
private theorem component70Node0_sound : Sound component70Node0Box :=
  sound_of_literal_split component70Node0Box leaf3401Box leaf3402Box
    .k (249/64) (by rfl) (by rfl)
    leaf3401FlatSound leaf3402FlatSound

private noncomputable def component70Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (53/256), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component70Node1_sound : Sound component70Node1Box :=
  sound_of_literal_split component70Node1Box leaf3403Box leaf3404Box
    .k (249/64) (by rfl) (by rfl)
    leaf3403FlatSound leaf3404FlatSound

private noncomputable def component70Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (13/64), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component70Node2_sound : Sound component70Node2Box :=
  sound_of_literal_split component70Node2Box component70Node0Box component70Node1Box
    .chi (53/256) (by rfl) (by rfl)
    component70Node0_sound component70Node1_sound

private noncomputable def component70Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (63/16), chiLo := (13/64), chiHi := (53/256) }

set_option maxRecDepth 1000000 in
private theorem component70Node3_sound : Sound component70Node3Box :=
  sound_of_literal_split component70Node3Box leaf3406Box leaf3407Box
    .k (503/128) (by rfl) (by rfl)
    leaf3406FlatSound leaf3407FlatSound

private noncomputable def component70Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (13/64), chiHi := (53/256) }

set_option maxRecDepth 1000000 in
private theorem component70Node4_sound : Sound component70Node4Box :=
  sound_of_literal_split component70Node4Box leaf3405Box component70Node3Box
    .k (251/64) (by rfl) (by rfl)
    leaf3405FlatSound component70Node3_sound

private noncomputable def component70Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (63/16), chiLo := (53/256), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component70Node5_sound : Sound component70Node5Box :=
  sound_of_literal_split component70Node5Box leaf3409Box leaf3410Box
    .chi (107/512) (by rfl) (by rfl)
    leaf3409FlatSound leaf3410FlatSound

private noncomputable def component70Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (53/256), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component70Node6_sound : Sound component70Node6Box :=
  sound_of_literal_split component70Node6Box leaf3408Box component70Node5Box
    .k (251/64) (by rfl) (by rfl)
    leaf3408FlatSound component70Node5_sound

private noncomputable def component70Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (13/64), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component70Node7_sound : Sound component70Node7Box :=
  sound_of_literal_split component70Node7Box component70Node4Box component70Node6Box
    .chi (53/256) (by rfl) (by rfl)
    component70Node4_sound component70Node6_sound

private noncomputable def component70Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (13/64), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component70Node8_sound : Sound component70Node8Box :=
  sound_of_literal_split component70Node8Box component70Node2Box component70Node7Box
    .k (125/32) (by rfl) (by rfl)
    component70Node2_sound component70Node7_sound

private noncomputable def component70Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (27/128), chiHi := (55/256) }

set_option maxRecDepth 1000000 in
private theorem component70Node9_sound : Sound component70Node9Box :=
  sound_of_literal_split component70Node9Box leaf3411Box leaf3412Box
    .k (249/64) (by rfl) (by rfl)
    leaf3411FlatSound leaf3412FlatSound

private noncomputable def component70Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (55/256), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component70Node10_sound : Sound component70Node10Box :=
  sound_of_literal_split component70Node10Box leaf3413Box leaf3414Box
    .k (249/64) (by rfl) (by rfl)
    leaf3413FlatSound leaf3414FlatSound

private noncomputable def component70Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (27/128), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component70Node11_sound : Sound component70Node11Box :=
  sound_of_literal_split component70Node11Box component70Node9Box component70Node10Box
    .chi (55/256) (by rfl) (by rfl)
    component70Node9_sound component70Node10_sound

private noncomputable def component70Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (63/16), chiLo := (27/128), chiHi := (55/256) }

set_option maxRecDepth 1000000 in
private theorem component70Node12_sound : Sound component70Node12Box :=
  sound_of_literal_split component70Node12Box leaf3416Box leaf3417Box
    .chi (109/512) (by rfl) (by rfl)
    leaf3416FlatSound leaf3417FlatSound

private noncomputable def component70Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (27/128), chiHi := (55/256) }

set_option maxRecDepth 1000000 in
private theorem component70Node13_sound : Sound component70Node13Box :=
  sound_of_literal_split component70Node13Box leaf3415Box component70Node12Box
    .k (251/64) (by rfl) (by rfl)
    leaf3415FlatSound component70Node12_sound

private noncomputable def component70Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (55/256), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component70Node14_sound : Sound component70Node14Box :=
  sound_of_literal_split component70Node14Box leaf3418Box leaf3419Box
    .k (251/64) (by rfl) (by rfl)
    leaf3418FlatSound leaf3419FlatSound

private noncomputable def component70Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (27/128), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component70Node15_sound : Sound component70Node15Box :=
  sound_of_literal_split component70Node15Box component70Node13Box component70Node14Box
    .chi (55/256) (by rfl) (by rfl)
    component70Node13_sound component70Node14_sound

private noncomputable def component70Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (27/128), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component70Node16_sound : Sound component70Node16Box :=
  sound_of_literal_split component70Node16Box component70Node11Box component70Node15Box
    .k (125/32) (by rfl) (by rfl)
    component70Node11_sound component70Node15_sound

private noncomputable def component70Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component70Node17_sound : Sound component70Node17Box :=
  sound_of_literal_split component70Node17Box component70Node8Box component70Node16Box
    .chi (27/128) (by rfl) (by rfl)
    component70Node8_sound component70Node16_sound

private noncomputable def component70Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (13/64), chiHi := (53/256) }

set_option maxRecDepth 1000000 in
private theorem component70Node18_sound : Sound component70Node18Box :=
  sound_of_literal_split component70Node18Box leaf3420Box leaf3421Box
    .k (505/128) (by rfl) (by rfl)
    leaf3420FlatSound leaf3421FlatSound

private noncomputable def component70Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (13/64), chiHi := (53/256) }

set_option maxRecDepth 1000000 in
private theorem component70Node19_sound : Sound component70Node19Box :=
  sound_of_literal_split component70Node19Box leaf3422Box leaf3423Box
    .k (507/128) (by rfl) (by rfl)
    leaf3422FlatSound leaf3423FlatSound

private noncomputable def component70Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (13/64), chiHi := (53/256) }

set_option maxRecDepth 1000000 in
private theorem component70Node20_sound : Sound component70Node20Box :=
  sound_of_literal_split component70Node20Box component70Node18Box component70Node19Box
    .k (253/64) (by rfl) (by rfl)
    component70Node18_sound component70Node19_sound

private noncomputable def component70Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (53/256), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component70Node21_sound : Sound component70Node21Box :=
  sound_of_literal_split component70Node21Box leaf3424Box leaf3425Box
    .chi (107/512) (by rfl) (by rfl)
    leaf3424FlatSound leaf3425FlatSound

private noncomputable def component70Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (53/256), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component70Node22_sound : Sound component70Node22Box :=
  sound_of_literal_split component70Node22Box leaf3426Box leaf3427Box
    .chi (107/512) (by rfl) (by rfl)
    leaf3426FlatSound leaf3427FlatSound

private noncomputable def component70Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (53/256), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component70Node23_sound : Sound component70Node23Box :=
  sound_of_literal_split component70Node23Box component70Node21Box component70Node22Box
    .k (253/64) (by rfl) (by rfl)
    component70Node21_sound component70Node22_sound

private noncomputable def component70Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (13/64), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component70Node24_sound : Sound component70Node24Box :=
  sound_of_literal_split component70Node24Box component70Node20Box component70Node23Box
    .chi (53/256) (by rfl) (by rfl)
    component70Node20_sound component70Node23_sound

private noncomputable def component70Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (13/64), chiHi := (53/256) }

set_option maxRecDepth 1000000 in
private theorem component70Node25_sound : Sound component70Node25Box :=
  sound_of_literal_split component70Node25Box leaf3428Box leaf3429Box
    .k (509/128) (by rfl) (by rfl)
    leaf3428FlatSound leaf3429FlatSound

private noncomputable def component70Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (13/64), chiHi := (53/256) }

set_option maxRecDepth 1000000 in
private theorem component70Node26_sound : Sound component70Node26Box :=
  sound_of_literal_split component70Node26Box leaf3430Box leaf3431Box
    .k (511/128) (by rfl) (by rfl)
    leaf3430FlatSound leaf3431FlatSound

private noncomputable def component70Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (13/64), chiHi := (53/256) }

set_option maxRecDepth 1000000 in
private theorem component70Node27_sound : Sound component70Node27Box :=
  sound_of_literal_split component70Node27Box component70Node25Box component70Node26Box
    .k (255/64) (by rfl) (by rfl)
    component70Node25_sound component70Node26_sound

private noncomputable def component70Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (53/256), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component70Node28_sound : Sound component70Node28Box :=
  sound_of_literal_split component70Node28Box leaf3432Box leaf3433Box
    .chi (107/512) (by rfl) (by rfl)
    leaf3432FlatSound leaf3433FlatSound

private noncomputable def component70Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (53/256), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component70Node29_sound : Sound component70Node29Box :=
  sound_of_literal_split component70Node29Box leaf3434Box leaf3435Box
    .chi (107/512) (by rfl) (by rfl)
    leaf3434FlatSound leaf3435FlatSound

private noncomputable def component70Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (53/256), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component70Node30_sound : Sound component70Node30Box :=
  sound_of_literal_split component70Node30Box component70Node28Box component70Node29Box
    .k (255/64) (by rfl) (by rfl)
    component70Node28_sound component70Node29_sound

private noncomputable def component70Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (13/64), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component70Node31_sound : Sound component70Node31Box :=
  sound_of_literal_split component70Node31Box component70Node27Box component70Node30Box
    .chi (53/256) (by rfl) (by rfl)
    component70Node27_sound component70Node30_sound

private noncomputable def component70Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (13/64), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component70Node32_sound : Sound component70Node32Box :=
  sound_of_literal_split component70Node32Box component70Node24Box component70Node31Box
    .k (127/32) (by rfl) (by rfl)
    component70Node24_sound component70Node31_sound

private noncomputable def component70Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (27/128), chiHi := (55/256) }

set_option maxRecDepth 1000000 in
private theorem component70Node33_sound : Sound component70Node33Box :=
  sound_of_literal_split component70Node33Box leaf3436Box leaf3437Box
    .chi (109/512) (by rfl) (by rfl)
    leaf3436FlatSound leaf3437FlatSound

private noncomputable def component70Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (27/128), chiHi := (55/256) }

set_option maxRecDepth 1000000 in
private theorem component70Node34_sound : Sound component70Node34Box :=
  sound_of_literal_split component70Node34Box leaf3438Box leaf3439Box
    .chi (109/512) (by rfl) (by rfl)
    leaf3438FlatSound leaf3439FlatSound

private noncomputable def component70Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (27/128), chiHi := (55/256) }

set_option maxRecDepth 1000000 in
private theorem component70Node35_sound : Sound component70Node35Box :=
  sound_of_literal_split component70Node35Box component70Node33Box component70Node34Box
    .k (253/64) (by rfl) (by rfl)
    component70Node33_sound component70Node34_sound

private noncomputable def component70Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (55/256), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component70Node36_sound : Sound component70Node36Box :=
  sound_of_literal_split component70Node36Box leaf3440Box leaf3441Box
    .chi (111/512) (by rfl) (by rfl)
    leaf3440FlatSound leaf3441FlatSound

private noncomputable def component70Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (55/256), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component70Node37_sound : Sound component70Node37Box :=
  sound_of_literal_split component70Node37Box leaf3442Box leaf3443Box
    .chi (111/512) (by rfl) (by rfl)
    leaf3442FlatSound leaf3443FlatSound

private noncomputable def component70Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (55/256), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component70Node38_sound : Sound component70Node38Box :=
  sound_of_literal_split component70Node38Box component70Node36Box component70Node37Box
    .k (253/64) (by rfl) (by rfl)
    component70Node36_sound component70Node37_sound

private noncomputable def component70Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (27/128), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component70Node39_sound : Sound component70Node39Box :=
  sound_of_literal_split component70Node39Box component70Node35Box component70Node38Box
    .chi (55/256) (by rfl) (by rfl)
    component70Node35_sound component70Node38_sound

private noncomputable def component70Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (27/128), chiHi := (55/256) }

set_option maxRecDepth 1000000 in
private theorem component70Node40_sound : Sound component70Node40Box :=
  sound_of_literal_split component70Node40Box leaf3444Box leaf3445Box
    .chi (109/512) (by rfl) (by rfl)
    leaf3444FlatSound leaf3445FlatSound

private noncomputable def component70Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (27/128), chiHi := (55/256) }

set_option maxRecDepth 1000000 in
private theorem component70Node41_sound : Sound component70Node41Box :=
  sound_of_literal_split component70Node41Box leaf3446Box leaf3447Box
    .chi (109/512) (by rfl) (by rfl)
    leaf3446FlatSound leaf3447FlatSound

private noncomputable def component70Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (27/128), chiHi := (55/256) }

set_option maxRecDepth 1000000 in
private theorem component70Node42_sound : Sound component70Node42Box :=
  sound_of_literal_split component70Node42Box component70Node40Box component70Node41Box
    .k (255/64) (by rfl) (by rfl)
    component70Node40_sound component70Node41_sound

private noncomputable def component70Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (55/256), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component70Node43_sound : Sound component70Node43Box :=
  sound_of_literal_split component70Node43Box leaf3448Box leaf3449Box
    .chi (111/512) (by rfl) (by rfl)
    leaf3448FlatSound leaf3449FlatSound

private noncomputable def component70Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (55/256), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component70Node44_sound : Sound component70Node44Box :=
  sound_of_literal_split component70Node44Box leaf3450Box leaf3451Box
    .chi (111/512) (by rfl) (by rfl)
    leaf3450FlatSound leaf3451FlatSound

private noncomputable def component70Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (55/256), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component70Node45_sound : Sound component70Node45Box :=
  sound_of_literal_split component70Node45Box component70Node43Box component70Node44Box
    .k (255/64) (by rfl) (by rfl)
    component70Node43_sound component70Node44_sound

private noncomputable def component70Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (27/128), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component70Node46_sound : Sound component70Node46Box :=
  sound_of_literal_split component70Node46Box component70Node42Box component70Node45Box
    .chi (55/256) (by rfl) (by rfl)
    component70Node42_sound component70Node45_sound

private noncomputable def component70Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (27/128), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component70Node47_sound : Sound component70Node47Box :=
  sound_of_literal_split component70Node47Box component70Node39Box component70Node46Box
    .k (127/32) (by rfl) (by rfl)
    component70Node39_sound component70Node46_sound

private noncomputable def component70Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component70Node48_sound : Sound component70Node48Box :=
  sound_of_literal_split component70Node48Box component70Node32Box component70Node47Box
    .chi (27/128) (by rfl) (by rfl)
    component70Node32_sound component70Node47_sound

noncomputable def component70Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
theorem component70_sound : Sound component70Box :=
  sound_of_literal_split component70Box component70Node17Box component70Node48Box
    .k (63/16) (by rfl) (by rfl)
    component70Node17_sound component70Node48_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
