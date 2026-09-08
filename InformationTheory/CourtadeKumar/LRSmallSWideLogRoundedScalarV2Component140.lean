import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch5
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch7
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch11
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch5
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

private noncomputable def leaf6870Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (1/2), chiHi := (65/128) }

private noncomputable def leaf6870Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435827/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711422976) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (771688079/536870912) }, upper := { exponent := 1, mantissa := (11961/8192) } }, logOuter := sk169LogOuterCertificate, logK := sk169LogKCertificate, logChi := chi329LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137427819517/137422845952) } }, logDArg := sk169LogDArgCertificate }

private noncomputable def leaf6870InnerLog : WideLogData :=
  innerPair368Data

set_option maxRecDepth 1000000 in
private theorem leaf6870LocalValidity :
    LeafFacts leaf6870Box leaf6870Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6870Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711422976) }) = true
      norm_num [leaf6870Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6870CertificateValid :
    WideCertificateValid leaf6870Box leaf6870Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk169ValidityFacts chi329ValidityFacts
    leaf6870LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6870CoverageChecked :
    coverageCheck (innerAD leaf6870Box) leaf6870InnerLog = true := by
  rfl'

private theorem leaf6870InnerLogValid :
    leaf6870InnerLog.Valid 8 (innerAD leaf6870Box) :=
  wideLogDataValid_of_cachedCheck endpoint96PositiveFacts
    endpoint98PositiveFacts.valid leaf6870CoverageChecked

private noncomputable def leaf6870InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453711/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf6870InputLogOnePlusV_eq :
    leaf6870InputLogOnePlusV = outerEnclosure 24
      (leaf6870Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6870RoundedFacts : LeafRoundedFacts 8
    leaf6870Certificate.logOnePlusV leaf6870InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6870InputLogOnePlusV_eq }

private noncomputable def leaf6870Inputs : Inputs :=
  inputsOfCaches globalInput sk169RoundedInputs
    chi329InputQChi innerPair368Input
    leaf6870InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6870LowerChecked :
    lowerCheck 24 leaf6870Box leaf6870Inputs = true := by
  rfl'

private theorem leaf6870CoversExact : CoversExact 8
    leaf6870Box leaf6870Certificate leaf6870InnerLog leaf6870Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk169RoundedFacts chi329RoundedFacts
    innerPair368RoundedFacts leaf6870RoundedFacts (by rfl)

private theorem leaf6870FlatSound : Sound leaf6870Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6870CertificateValid
    leaf6870InnerLogValid leaf6870CoversExact leaf6870LowerChecked

private noncomputable def leaf6871Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (1/2), chiHi := (65/128) }

private noncomputable def leaf6871Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435829/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711356416) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (775882125/536870912) }, upper := { exponent := 1, mantissa := (6013/4096) } }, logOuter := sk170LogOuterCertificate, logK := sk170LogKCertificate, logChi := chi329LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137427752957/137422712832) } }, logDArg := sk170LogDArgCertificate }

private noncomputable def leaf6871InnerLog : WideLogData :=
  innerPair371Data

set_option maxRecDepth 1000000 in
private theorem leaf6871LocalValidity :
    LeafFacts leaf6871Box leaf6871Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6871Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711356416) }) = true
      norm_num [leaf6871Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6871CertificateValid :
    WideCertificateValid leaf6871Box leaf6871Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk170ValidityFacts chi329ValidityFacts
    leaf6871LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6871CoverageChecked :
    coverageCheck (innerAD leaf6871Box) leaf6871InnerLog = true := by
  rfl'

private theorem leaf6871InnerLogValid :
    leaf6871InnerLog.Valid 8 (innerAD leaf6871Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint98PositiveFacts.valid leaf6871CoverageChecked

private noncomputable def leaf6871InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (90857/131072) }

set_option maxRecDepth 1000000 in
private theorem leaf6871InputLogOnePlusV_eq :
    leaf6871InputLogOnePlusV = outerEnclosure 24
      (leaf6871Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6871RoundedFacts : LeafRoundedFacts 8
    leaf6871Certificate.logOnePlusV leaf6871InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6871InputLogOnePlusV_eq }

private noncomputable def leaf6871Inputs : Inputs :=
  inputsOfCaches globalInput sk170RoundedInputs
    chi329InputQChi innerPair371Input
    leaf6871InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6871LowerChecked :
    lowerCheck 24 leaf6871Box leaf6871Inputs = true := by
  rfl'

private theorem leaf6871CoversExact : CoversExact 8
    leaf6871Box leaf6871Certificate leaf6871InnerLog leaf6871Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk170RoundedFacts chi329RoundedFacts
    innerPair371RoundedFacts leaf6871RoundedFacts (by rfl)

private theorem leaf6871FlatSound : Sound leaf6871Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6871CertificateValid
    leaf6871InnerLogValid leaf6871CoversExact leaf6871LowerChecked

private noncomputable def leaf6872Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (65/128), chiHi := (33/64) }

private noncomputable def leaf6872Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435829/268435456) }, vSqrt := { lower := (8191/8192), upper := (5285876657/5285484544) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (779551917/536870912) }, upper := { exponent := 1, mantissa := (6041/4096) } }, logOuter := sk169LogOuterCertificate, logK := sk169LogKCertificate, logChi := chi330LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (10571361201/10570969088) } }, logDArg := sk169LogDArgCertificate }

private noncomputable def leaf6872InnerLog : WideLogData :=
  innerPair372Data

set_option maxRecDepth 1000000 in
private theorem leaf6872LocalValidity :
    LeafFacts leaf6872Box leaf6872Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6872Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5285876657/5285484544) }) = true
      norm_num [leaf6872Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6872CertificateValid :
    WideCertificateValid leaf6872Box leaf6872Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk169ValidityFacts chi330ValidityFacts
    leaf6872LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6872CoverageChecked :
    coverageCheck (innerAD leaf6872Box) leaf6872InnerLog = true := by
  rfl'

private theorem leaf6872InnerLogValid :
    leaf6872InnerLog.Valid 8 (innerAD leaf6872Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint99PositiveFacts.valid leaf6872CoverageChecked

private noncomputable def leaf6872InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629703/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6872InputLogOnePlusV_eq :
    leaf6872InputLogOnePlusV = outerEnclosure 24
      (leaf6872Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6872RoundedFacts : LeafRoundedFacts 8
    leaf6872Certificate.logOnePlusV leaf6872InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6872InputLogOnePlusV_eq }

private noncomputable def leaf6872Inputs : Inputs :=
  inputsOfCaches globalInput sk169RoundedInputs
    chi330InputQChi innerPair372Input
    leaf6872InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6872LowerChecked :
    lowerCheck 24 leaf6872Box leaf6872Inputs = true := by
  rfl'

private theorem leaf6872CoversExact : CoversExact 8
    leaf6872Box leaf6872Certificate leaf6872InnerLog leaf6872Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk169RoundedFacts chi330RoundedFacts
    innerPair372RoundedFacts leaf6872RoundedFacts (by rfl)

private theorem leaf6872FlatSound : Sound leaf6872Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6872CertificateValid
    leaf6872InnerLogValid leaf6872CoversExact leaf6872LowerChecked

private noncomputable def leaf6873Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (65/128), chiHi := (33/64) }

private noncomputable def leaf6873Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435831/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711231488) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (783811495/536870912) }, upper := { exponent := 1, mantissa := (3037/2048) } }, logOuter := sk170LogOuterCertificate, logK := sk170LogKCertificate, logChi := chi330LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137427628029/137422462976) } }, logDArg := sk170LogDArgCertificate }

private noncomputable def leaf6873InnerLog : WideLogData :=
  innerPair372Data

set_option maxRecDepth 1000000 in
private theorem leaf6873LocalValidity :
    LeafFacts leaf6873Box leaf6873Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6873Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711231488) }) = true
      norm_num [leaf6873Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6873CertificateValid :
    WideCertificateValid leaf6873Box leaf6873Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk170ValidityFacts chi330ValidityFacts
    leaf6873LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6873CoverageChecked :
    coverageCheck (innerAD leaf6873Box) leaf6873InnerLog = true := by
  rfl'

private theorem leaf6873InnerLogValid :
    leaf6873InnerLog.Valid 8 (innerAD leaf6873Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint99PositiveFacts.valid leaf6873CoverageChecked

private noncomputable def leaf6873InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629711/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6873InputLogOnePlusV_eq :
    leaf6873InputLogOnePlusV = outerEnclosure 24
      (leaf6873Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6873RoundedFacts : LeafRoundedFacts 8
    leaf6873Certificate.logOnePlusV leaf6873InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6873InputLogOnePlusV_eq }

private noncomputable def leaf6873Inputs : Inputs :=
  inputsOfCaches globalInput sk170RoundedInputs
    chi330InputQChi innerPair372Input
    leaf6873InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6873LowerChecked :
    lowerCheck 24 leaf6873Box leaf6873Inputs = true := by
  rfl'

private theorem leaf6873CoversExact : CoversExact 8
    leaf6873Box leaf6873Certificate leaf6873InnerLog leaf6873Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk170RoundedFacts chi330RoundedFacts
    innerPair372RoundedFacts leaf6873RoundedFacts (by rfl)

private theorem leaf6873FlatSound : Sound leaf6873Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6873CertificateValid
    leaf6873InnerLogValid leaf6873CoversExact leaf6873LowerChecked

private noncomputable def leaf6874Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (1/2), chiHi := (65/128) }

private noncomputable def leaf6874Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435831/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711289856) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (780076171/536870912) }, upper := { exponent := 1, mantissa := (12091/8192) } }, logOuter := sk171LogOuterCertificate, logK := sk171LogKCertificate, logChi := chi329LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137427686397/137422579712) } }, logDArg := sk171LogDArgCertificate }

private noncomputable def leaf6874InnerLog : WideLogData :=
  innerPair372Data

set_option maxRecDepth 1000000 in
private theorem leaf6874LocalValidity :
    LeafFacts leaf6874Box leaf6874Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6874Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711289856) }) = true
      norm_num [leaf6874Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6874CertificateValid :
    WideCertificateValid leaf6874Box leaf6874Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk171ValidityFacts chi329ValidityFacts
    leaf6874LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6874CoverageChecked :
    coverageCheck (innerAD leaf6874Box) leaf6874InnerLog = true := by
  rfl'

private theorem leaf6874InnerLogValid :
    leaf6874InnerLog.Valid 8 (innerAD leaf6874Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint99PositiveFacts.valid leaf6874CoverageChecked

private noncomputable def leaf6874InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453713/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf6874InputLogOnePlusV_eq :
    leaf6874InputLogOnePlusV = outerEnclosure 24
      (leaf6874Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6874RoundedFacts : LeafRoundedFacts 8
    leaf6874Certificate.logOnePlusV leaf6874InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6874InputLogOnePlusV_eq }

private noncomputable def leaf6874Inputs : Inputs :=
  inputsOfCaches globalInput sk171RoundedInputs
    chi329InputQChi innerPair372Input
    leaf6874InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6874LowerChecked :
    lowerCheck 24 leaf6874Box leaf6874Inputs = true := by
  rfl'

private theorem leaf6874CoversExact : CoversExact 8
    leaf6874Box leaf6874Certificate leaf6874InnerLog leaf6874Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk171RoundedFacts chi329RoundedFacts
    innerPair372RoundedFacts leaf6874RoundedFacts (by rfl)

private theorem leaf6874FlatSound : Sound leaf6874Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6874CertificateValid
    leaf6874InnerLogValid leaf6874CoversExact leaf6874LowerChecked

private noncomputable def leaf6875Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (1/2), chiHi := (65/128) }

private noncomputable def leaf6875Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435833/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711223296) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (784270217/536870912) }, upper := { exponent := 1, mantissa := (3039/2048) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi329LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137427619837/137422446592) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf6875InnerLog : WideLogData :=
  innerPair372Data

set_option maxRecDepth 1000000 in
private theorem leaf6875LocalValidity :
    LeafFacts leaf6875Box leaf6875Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6875Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711223296) }) = true
      norm_num [leaf6875Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6875CertificateValid :
    WideCertificateValid leaf6875Box leaf6875Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi329ValidityFacts
    leaf6875LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6875CoverageChecked :
    coverageCheck (innerAD leaf6875Box) leaf6875InnerLog = true := by
  rfl'

private theorem leaf6875InnerLogValid :
    leaf6875InnerLog.Valid 8 (innerAD leaf6875Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint99PositiveFacts.valid leaf6875CoverageChecked

private noncomputable def leaf6875InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726857/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf6875InputLogOnePlusV_eq :
    leaf6875InputLogOnePlusV = outerEnclosure 24
      (leaf6875Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6875RoundedFacts : LeafRoundedFacts 8
    leaf6875Certificate.logOnePlusV leaf6875InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6875InputLogOnePlusV_eq }

private noncomputable def leaf6875Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi329InputQChi innerPair372Input
    leaf6875InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6875LowerChecked :
    lowerCheck 24 leaf6875Box leaf6875Inputs = true := by
  rfl'

private theorem leaf6875CoversExact : CoversExact 8
    leaf6875Box leaf6875Certificate leaf6875InnerLog leaf6875Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi329RoundedFacts
    innerPair372RoundedFacts leaf6875RoundedFacts (by rfl)

private theorem leaf6875FlatSound : Sound leaf6875Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6875CertificateValid
    leaf6875InnerLogValid leaf6875CoversExact leaf6875LowerChecked

private noncomputable def leaf6876Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (65/128), chiHi := (33/64) }

private noncomputable def leaf6876Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435833/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711163904) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (788071073/536870912) }, upper := { exponent := 1, mantissa := (6107/4096) } }, logOuter := sk171LogOuterCertificate, logK := sk171LogKCertificate, logChi := chi330LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137427560445/137422327808) } }, logDArg := sk171LogDArgCertificate }

private noncomputable def leaf6876InnerLog : WideLogData :=
  innerPair372Data

set_option maxRecDepth 1000000 in
private theorem leaf6876LocalValidity :
    LeafFacts leaf6876Box leaf6876Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6876Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711163904) }) = true
      norm_num [leaf6876Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6876CertificateValid :
    WideCertificateValid leaf6876Box leaf6876Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk171ValidityFacts chi330ValidityFacts
    leaf6876LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6876CoverageChecked :
    coverageCheck (innerAD leaf6876Box) leaf6876InnerLog = true := by
  rfl'

private theorem leaf6876InnerLogValid :
    leaf6876InnerLog.Valid 8 (innerAD leaf6876Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint99PositiveFacts.valid leaf6876CoverageChecked

private noncomputable def leaf6876InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453715/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf6876InputLogOnePlusV_eq :
    leaf6876InputLogOnePlusV = outerEnclosure 24
      (leaf6876Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6876RoundedFacts : LeafRoundedFacts 8
    leaf6876Certificate.logOnePlusV leaf6876InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6876InputLogOnePlusV_eq }

private noncomputable def leaf6876Inputs : Inputs :=
  inputsOfCaches globalInput sk171RoundedInputs
    chi330InputQChi innerPair372Input
    leaf6876InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6876LowerChecked :
    lowerCheck 24 leaf6876Box leaf6876Inputs = true := by
  rfl'

private theorem leaf6876CoversExact : CoversExact 8
    leaf6876Box leaf6876Certificate leaf6876InnerLog leaf6876Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk171RoundedFacts chi330RoundedFacts
    innerPair372RoundedFacts leaf6876RoundedFacts (by rfl)

private theorem leaf6876FlatSound : Sound leaf6876Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6876CertificateValid
    leaf6876InnerLogValid leaf6876CoversExact leaf6876LowerChecked

private noncomputable def leaf6877Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (65/128), chiHi := (33/64) }

private noncomputable def leaf6877Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435835/268435456) }, vSqrt := { lower := (8191/8192), upper := (17178836991/17177774080) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (792330651/536870912) }, upper := { exponent := 1, mantissa := (1535/1024) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi330LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34356611071/34355548160) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf6877InnerLog : WideLogData :=
  innerPair375Data

set_option maxRecDepth 1000000 in
private theorem leaf6877LocalValidity :
    LeafFacts leaf6877Box leaf6877Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6877Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178836991/17177774080) }) = true
      norm_num [leaf6877Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6877CertificateValid :
    WideCertificateValid leaf6877Box leaf6877Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi330ValidityFacts
    leaf6877LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6877CoverageChecked :
    coverageCheck (innerAD leaf6877Box) leaf6877InnerLog = true := by
  rfl'

private theorem leaf6877InnerLogValid :
    leaf6877InnerLog.Valid 8 (innerAD leaf6877Box) :=
  wideLogDataValid_of_cachedCheck endpoint98PositiveFacts
    endpoint99PositiveFacts.valid leaf6877CoverageChecked

private noncomputable def leaf6877InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (363425/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf6877InputLogOnePlusV_eq :
    leaf6877InputLogOnePlusV = outerEnclosure 24
      (leaf6877Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6877RoundedFacts : LeafRoundedFacts 8
    leaf6877Certificate.logOnePlusV leaf6877InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6877InputLogOnePlusV_eq }

private noncomputable def leaf6877Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi330InputQChi innerPair375Input
    leaf6877InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6877LowerChecked :
    lowerCheck 24 leaf6877Box leaf6877Inputs = true := by
  rfl'

private theorem leaf6877CoversExact : CoversExact 8
    leaf6877Box leaf6877Certificate leaf6877InnerLog leaf6877Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi330RoundedFacts
    innerPair375RoundedFacts leaf6877RoundedFacts (by rfl)

private theorem leaf6877FlatSound : Sound leaf6877Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6877CertificateValid
    leaf6877InnerLogValid leaf6877CoversExact leaf6877LowerChecked

private noncomputable def leaf6878Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (33/64), chiHi := (67/128) }

private noncomputable def leaf6878Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435831/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711175168) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (787415755/536870912) }, upper := { exponent := 1, mantissa := (12203/8192) } }, logOuter := sk169LogOuterCertificate, logK := sk169LogKCertificate, logChi := chi331LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137427571709/137422350336) } }, logDArg := sk169LogDArgCertificate }

private noncomputable def leaf6878InnerLog : WideLogData :=
  innerPair372Data

set_option maxRecDepth 1000000 in
private theorem leaf6878LocalValidity :
    LeafFacts leaf6878Box leaf6878Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6878Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711175168) }) = true
      norm_num [leaf6878Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6878CertificateValid :
    WideCertificateValid leaf6878Box leaf6878Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk169ValidityFacts chi331ValidityFacts
    leaf6878LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6878CoverageChecked :
    coverageCheck (innerAD leaf6878Box) leaf6878InnerLog = true := by
  rfl'

private theorem leaf6878InnerLogValid :
    leaf6878InnerLog.Valid 8 (innerAD leaf6878Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint99PositiveFacts.valid leaf6878CoverageChecked

private noncomputable def leaf6878InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814859/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6878InputLogOnePlusV_eq :
    leaf6878InputLogOnePlusV = outerEnclosure 24
      (leaf6878Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6878RoundedFacts : LeafRoundedFacts 8
    leaf6878Certificate.logOnePlusV leaf6878InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6878InputLogOnePlusV_eq }

private noncomputable def leaf6878Inputs : Inputs :=
  inputsOfCaches globalInput sk169RoundedInputs
    chi331InputQChi innerPair372Input
    leaf6878InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6878LowerChecked :
    lowerCheck 24 leaf6878Box leaf6878Inputs = true := by
  rfl'

private theorem leaf6878CoversExact : CoversExact 8
    leaf6878Box leaf6878Certificate leaf6878InnerLog leaf6878Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk169RoundedFacts chi331RoundedFacts
    innerPair372RoundedFacts leaf6878RoundedFacts (by rfl)

private theorem leaf6878FlatSound : Sound leaf6878Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6878CertificateValid
    leaf6878InnerLogValid leaf6878CoversExact leaf6878LowerChecked

private noncomputable def leaf6879Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (33/64), chiHi := (67/128) }

private noncomputable def leaf6879Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435833/268435456) }, vSqrt := { lower := (8191/8192), upper := (17178836991/17177776640) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (791740865/536870912) }, upper := { exponent := 1, mantissa := (6135/4096) } }, logOuter := sk170LogOuterCertificate, logK := sk170LogKCertificate, logChi := chi331LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34356613631/34355553280) } }, logDArg := sk170LogDArgCertificate }

private noncomputable def leaf6879InnerLog : WideLogData :=
  innerPair375Data

set_option maxRecDepth 1000000 in
private theorem leaf6879LocalValidity :
    LeafFacts leaf6879Box leaf6879Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6879Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178836991/17177776640) }) = true
      norm_num [leaf6879Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6879CertificateValid :
    WideCertificateValid leaf6879Box leaf6879Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk170ValidityFacts chi331ValidityFacts
    leaf6879LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6879CoverageChecked :
    coverageCheck (innerAD leaf6879Box) leaf6879InnerLog = true := by
  rfl'

private theorem leaf6879InnerLogValid :
    leaf6879InnerLog.Valid 8 (innerAD leaf6879Box) :=
  wideLogDataValid_of_cachedCheck endpoint98PositiveFacts
    endpoint99PositiveFacts.valid leaf6879CoverageChecked

private noncomputable def leaf6879InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629599/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6879InputLogOnePlusV_eq :
    leaf6879InputLogOnePlusV = outerEnclosure 24
      (leaf6879Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6879RoundedFacts : LeafRoundedFacts 8
    leaf6879Certificate.logOnePlusV leaf6879InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6879InputLogOnePlusV_eq }

private noncomputable def leaf6879Inputs : Inputs :=
  inputsOfCaches globalInput sk170RoundedInputs
    chi331InputQChi innerPair375Input
    leaf6879InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6879LowerChecked :
    lowerCheck 24 leaf6879Box leaf6879Inputs = true := by
  rfl'

private theorem leaf6879CoversExact : CoversExact 8
    leaf6879Box leaf6879Certificate leaf6879InnerLog leaf6879Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk170RoundedFacts chi331RoundedFacts
    innerPair375RoundedFacts leaf6879RoundedFacts (by rfl)

private theorem leaf6879FlatSound : Sound leaf6879Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6879CertificateValid
    leaf6879InnerLogValid leaf6879CoversExact leaf6879LowerChecked

private noncomputable def leaf6880Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (67/128), chiHi := (17/32) }

private noncomputable def leaf6880Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435833/268435456) }, vSqrt := { lower := (8191/8192), upper := (17178836991/17177762816) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (795279593/536870912) }, upper := { exponent := 1, mantissa := (3081/2048) } }, logOuter := sk169LogOuterCertificate, logK := sk169LogKCertificate, logChi := chi332LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34356599807/34355525632) } }, logDArg := sk169LogDArgCertificate }

private noncomputable def leaf6880InnerLog : WideLogData :=
  innerPair376Data

set_option maxRecDepth 1000000 in
private theorem leaf6880LocalValidity :
    LeafFacts leaf6880Box leaf6880Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6880Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178836991/17177762816) }) = true
      norm_num [leaf6880Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6880CertificateValid :
    WideCertificateValid leaf6880Box leaf6880Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk169ValidityFacts chi332ValidityFacts
    leaf6880LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6880CoverageChecked :
    coverageCheck (innerAD leaf6880Box) leaf6880InnerLog = true := by
  rfl'

private theorem leaf6880InnerLogValid :
    leaf6880InnerLog.Valid 8 (innerAD leaf6880Box) :=
  wideLogDataValid_of_cachedCheck endpoint98PositiveFacts
    endpoint482PositiveFacts.valid leaf6880CoverageChecked

private noncomputable def leaf6880InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629605/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6880InputLogOnePlusV_eq :
    leaf6880InputLogOnePlusV = outerEnclosure 24
      (leaf6880Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6880RoundedFacts : LeafRoundedFacts 8
    leaf6880Certificate.logOnePlusV leaf6880InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6880InputLogOnePlusV_eq }

private noncomputable def leaf6880Inputs : Inputs :=
  inputsOfCaches globalInput sk169RoundedInputs
    chi332InputQChi innerPair376Input
    leaf6880InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6880LowerChecked :
    lowerCheck 24 leaf6880Box leaf6880Inputs = true := by
  rfl'

private theorem leaf6880CoversExact : CoversExact 8
    leaf6880Box leaf6880Certificate leaf6880InnerLog leaf6880Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk169RoundedFacts chi332RoundedFacts
    innerPair376RoundedFacts leaf6880RoundedFacts (by rfl)

private theorem leaf6880FlatSound : Sound leaf6880Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6880CertificateValid
    leaf6880InnerLogValid leaf6880CoversExact leaf6880LowerChecked

private noncomputable def leaf6881Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (67/128), chiHi := (17/32) }

private noncomputable def leaf6881Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435835/268435456) }, vSqrt := { lower := (8191/8192), upper := (5726278997/5725915136) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (799670235/536870912) }, upper := { exponent := 1, mantissa := (1549/1024) } }, logOuter := sk170LogOuterCertificate, logK := sk170LogKCertificate, logChi := chi332LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (11452194133/11451830272) } }, logDArg := sk170LogDArgCertificate }

private noncomputable def leaf6881InnerLog : WideLogData :=
  innerPair376Data

set_option maxRecDepth 1000000 in
private theorem leaf6881LocalValidity :
    LeafFacts leaf6881Box leaf6881Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6881Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5726278997/5725915136) }) = true
      norm_num [leaf6881Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6881CertificateValid :
    WideCertificateValid leaf6881Box leaf6881Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk170ValidityFacts chi332ValidityFacts
    leaf6881LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6881CoverageChecked :
    coverageCheck (innerAD leaf6881Box) leaf6881InnerLog = true := by
  rfl'

private theorem leaf6881InnerLogValid :
    leaf6881InnerLog.Valid 8 (innerAD leaf6881Box) :=
  wideLogDataValid_of_cachedCheck endpoint98PositiveFacts
    endpoint482PositiveFacts.valid leaf6881CoverageChecked

private noncomputable def leaf6881InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814807/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6881InputLogOnePlusV_eq :
    leaf6881InputLogOnePlusV = outerEnclosure 24
      (leaf6881Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6881RoundedFacts : LeafRoundedFacts 8
    leaf6881Certificate.logOnePlusV leaf6881InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6881InputLogOnePlusV_eq }

private noncomputable def leaf6881Inputs : Inputs :=
  inputsOfCaches globalInput sk170RoundedInputs
    chi332InputQChi innerPair376Input
    leaf6881InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6881LowerChecked :
    lowerCheck 24 leaf6881Box leaf6881Inputs = true := by
  rfl'

private theorem leaf6881CoversExact : CoversExact 8
    leaf6881Box leaf6881Certificate leaf6881InnerLog leaf6881Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk170RoundedFacts chi332RoundedFacts
    innerPair376RoundedFacts leaf6881RoundedFacts (by rfl)

private theorem leaf6881FlatSound : Sound leaf6881Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6881CertificateValid
    leaf6881InnerLogValid leaf6881CoversExact leaf6881LowerChecked

private noncomputable def leaf6882Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (33/64), chiHi := (67/128) }

private noncomputable def leaf6882Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435835/268435456) }, vSqrt := { lower := (8191/8192), upper := (17178836991/17177759488) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (796065975/536870912) }, upper := { exponent := 1, mantissa := (12337/8192) } }, logOuter := sk171LogOuterCertificate, logK := sk171LogKCertificate, logChi := chi331LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34356596479/34355518976) } }, logDArg := sk171LogDArgCertificate }

private noncomputable def leaf6882InnerLog : WideLogData :=
  innerPair376Data

set_option maxRecDepth 1000000 in
private theorem leaf6882LocalValidity :
    LeafFacts leaf6882Box leaf6882Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6882Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178836991/17177759488) }) = true
      norm_num [leaf6882Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6882CertificateValid :
    WideCertificateValid leaf6882Box leaf6882Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk171ValidityFacts chi331ValidityFacts
    leaf6882LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6882CoverageChecked :
    coverageCheck (innerAD leaf6882Box) leaf6882InnerLog = true := by
  rfl'

private theorem leaf6882InnerLogValid :
    leaf6882InnerLog.Valid 8 (innerAD leaf6882Box) :=
  wideLogDataValid_of_cachedCheck endpoint98PositiveFacts
    endpoint482PositiveFacts.valid leaf6882CoverageChecked

private noncomputable def leaf6882InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629607/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6882InputLogOnePlusV_eq :
    leaf6882InputLogOnePlusV = outerEnclosure 24
      (leaf6882Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6882RoundedFacts : LeafRoundedFacts 8
    leaf6882Certificate.logOnePlusV leaf6882InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6882InputLogOnePlusV_eq }

private noncomputable def leaf6882Inputs : Inputs :=
  inputsOfCaches globalInput sk171RoundedInputs
    chi331InputQChi innerPair376Input
    leaf6882InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6882LowerChecked :
    lowerCheck 24 leaf6882Box leaf6882Inputs = true := by
  rfl'

private theorem leaf6882CoversExact : CoversExact 8
    leaf6882Box leaf6882Certificate leaf6882InnerLog leaf6882Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk171RoundedFacts chi331RoundedFacts
    innerPair376RoundedFacts leaf6882RoundedFacts (by rfl)

private theorem leaf6882FlatSound : Sound leaf6882Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6882CertificateValid
    leaf6882InnerLogValid leaf6882CoversExact leaf6882LowerChecked

private noncomputable def leaf6883Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (33/64), chiHi := (67/128) }

private noncomputable def leaf6883Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435837/268435456) }, vSqrt := { lower := (8191/8192), upper := (5726278997/5725914112) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (800391085/536870912) }, upper := { exponent := 1, mantissa := (3101/2048) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi331LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (11452193109/11451828224) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf6883InnerLog : WideLogData :=
  innerPair376Data

set_option maxRecDepth 1000000 in
private theorem leaf6883LocalValidity :
    LeafFacts leaf6883Box leaf6883Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6883Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5726278997/5725914112) }) = true
      norm_num [leaf6883Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6883CertificateValid :
    WideCertificateValid leaf6883Box leaf6883Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi331ValidityFacts
    leaf6883LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6883CoverageChecked :
    coverageCheck (innerAD leaf6883Box) leaf6883InnerLog = true := by
  rfl'

private theorem leaf6883InnerLogValid :
    leaf6883InnerLog.Valid 8 (innerAD leaf6883Box) :=
  wideLogDataValid_of_cachedCheck endpoint98PositiveFacts
    endpoint482PositiveFacts.valid leaf6883CoverageChecked

private noncomputable def leaf6883InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629615/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6883InputLogOnePlusV_eq :
    leaf6883InputLogOnePlusV = outerEnclosure 24
      (leaf6883Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6883RoundedFacts : LeafRoundedFacts 8
    leaf6883Certificate.logOnePlusV leaf6883InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6883InputLogOnePlusV_eq }

private noncomputable def leaf6883Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi331InputQChi innerPair376Input
    leaf6883InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6883LowerChecked :
    lowerCheck 24 leaf6883Box leaf6883Inputs = true := by
  rfl'

private theorem leaf6883CoversExact : CoversExact 8
    leaf6883Box leaf6883Certificate leaf6883InnerLog leaf6883Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi331RoundedFacts
    innerPair376RoundedFacts leaf6883RoundedFacts (by rfl)

private theorem leaf6883FlatSound : Sound leaf6883Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6883CertificateValid
    leaf6883InnerLogValid leaf6883CoversExact leaf6883LowerChecked

private noncomputable def leaf6884Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (67/128), chiHi := (17/32) }

private noncomputable def leaf6884Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435837/268435456) }, vSqrt := { lower := (8191/8192), upper := (17178836991/17177728000) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (804060877/536870912) }, upper := { exponent := 1, mantissa := (3115/2048) } }, logOuter := sk171LogOuterCertificate, logK := sk171LogKCertificate, logChi := chi332LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34356564991/34355456000) } }, logDArg := sk171LogDArgCertificate }

private noncomputable def leaf6884InnerLog : WideLogData :=
  innerPair376Data

set_option maxRecDepth 1000000 in
private theorem leaf6884LocalValidity :
    LeafFacts leaf6884Box leaf6884Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6884Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178836991/17177728000) }) = true
      norm_num [leaf6884Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6884CertificateValid :
    WideCertificateValid leaf6884Box leaf6884Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk171ValidityFacts chi332ValidityFacts
    leaf6884LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6884CoverageChecked :
    coverageCheck (innerAD leaf6884Box) leaf6884InnerLog = true := by
  rfl'

private theorem leaf6884InnerLogValid :
    leaf6884InnerLog.Valid 8 (innerAD leaf6884Box) :=
  wideLogDataValid_of_cachedCheck endpoint98PositiveFacts
    endpoint482PositiveFacts.valid leaf6884CoverageChecked

private noncomputable def leaf6884InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814811/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6884InputLogOnePlusV_eq :
    leaf6884InputLogOnePlusV = outerEnclosure 24
      (leaf6884Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6884RoundedFacts : LeafRoundedFacts 8
    leaf6884Certificate.logOnePlusV leaf6884InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6884InputLogOnePlusV_eq }

private noncomputable def leaf6884Inputs : Inputs :=
  inputsOfCaches globalInput sk171RoundedInputs
    chi332InputQChi innerPair376Input
    leaf6884InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6884LowerChecked :
    lowerCheck 24 leaf6884Box leaf6884Inputs = true := by
  rfl'

private theorem leaf6884CoversExact : CoversExact 8
    leaf6884Box leaf6884Certificate leaf6884InnerLog leaf6884Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk171RoundedFacts chi332RoundedFacts
    innerPair376RoundedFacts leaf6884RoundedFacts (by rfl)

private theorem leaf6884FlatSound : Sound leaf6884Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6884CertificateValid
    leaf6884InnerLogValid leaf6884CoversExact leaf6884LowerChecked

private noncomputable def leaf6885Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (67/128), chiHi := (17/32) }

private noncomputable def leaf6885Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435839/268435456) }, vSqrt := { lower := (8191/8192), upper := (17178836991/17177710592) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (808451519/536870912) }, upper := { exponent := 1, mantissa := (783/512) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi332LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34356547583/34355421184) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf6885InnerLog : WideLogData :=
  innerPair381Data

set_option maxRecDepth 1000000 in
private theorem leaf6885LocalValidity :
    LeafFacts leaf6885Box leaf6885Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6885Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178836991/17177710592) }) = true
      norm_num [leaf6885Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6885CertificateValid :
    WideCertificateValid leaf6885Box leaf6885Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi332ValidityFacts
    leaf6885LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6885CoverageChecked :
    coverageCheck (innerAD leaf6885Box) leaf6885InnerLog = true := by
  rfl'

private theorem leaf6885InnerLogValid :
    leaf6885InnerLog.Valid 8 (innerAD leaf6885Box) :=
  wideLogDataValid_of_cachedCheck endpoint99PositiveFacts
    endpoint482PositiveFacts.valid leaf6885CoverageChecked

private noncomputable def leaf6885InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629631/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6885InputLogOnePlusV_eq :
    leaf6885InputLogOnePlusV = outerEnclosure 24
      (leaf6885Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6885RoundedFacts : LeafRoundedFacts 8
    leaf6885Certificate.logOnePlusV leaf6885InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6885InputLogOnePlusV_eq }

private noncomputable def leaf6885Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi332InputQChi innerPair381Input
    leaf6885InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6885LowerChecked :
    lowerCheck 24 leaf6885Box leaf6885Inputs = true := by
  rfl'

private theorem leaf6885CoversExact : CoversExact 8
    leaf6885Box leaf6885Certificate leaf6885InnerLog leaf6885Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi332RoundedFacts
    innerPair381RoundedFacts leaf6885RoundedFacts (by rfl)

private theorem leaf6885FlatSound : Sound leaf6885Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6885CertificateValid
    leaf6885InnerLogValid leaf6885CoversExact leaf6885LowerChecked

private noncomputable def leaf6886Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (1/2), chiHi := (65/128) }

private noncomputable def leaf6886Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435835/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711156736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (788464263/536870912) }, upper := { exponent := 1, mantissa := (12221/8192) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi329LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137427553277/137422313472) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf6886InnerLog : WideLogData :=
  innerPair372Data

set_option maxRecDepth 1000000 in
private theorem leaf6886LocalValidity :
    LeafFacts leaf6886Box leaf6886Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6886Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711156736) }) = true
      norm_num [leaf6886Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6886CertificateValid :
    WideCertificateValid leaf6886Box leaf6886Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi329ValidityFacts
    leaf6886LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6886CoverageChecked :
    coverageCheck (innerAD leaf6886Box) leaf6886InnerLog = true := by
  rfl'

private theorem leaf6886InnerLogValid :
    leaf6886InnerLog.Valid 8 (innerAD leaf6886Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint99PositiveFacts.valid leaf6886CoverageChecked

private noncomputable def leaf6886InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453715/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf6886InputLogOnePlusV_eq :
    leaf6886InputLogOnePlusV = outerEnclosure 24
      (leaf6886Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6886RoundedFacts : LeafRoundedFacts 8
    leaf6886Certificate.logOnePlusV leaf6886InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6886InputLogOnePlusV_eq }

private noncomputable def leaf6886Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi329InputQChi innerPair372Input
    leaf6886InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6886LowerChecked :
    lowerCheck 24 leaf6886Box leaf6886Inputs = true := by
  rfl'

private theorem leaf6886CoversExact : CoversExact 8
    leaf6886Box leaf6886Certificate leaf6886InnerLog leaf6886Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi329RoundedFacts
    innerPair372RoundedFacts leaf6886RoundedFacts (by rfl)

private theorem leaf6886FlatSound : Sound leaf6886Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6886CertificateValid
    leaf6886InnerLogValid leaf6886CoversExact leaf6886LowerChecked

private noncomputable def leaf6887Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (1/2), chiHi := (65/128) }

private noncomputable def leaf6887Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435837/268435456) }, vSqrt := { lower := (8191/8192), upper := (17178836991/17177772544) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (792658309/536870912) }, upper := { exponent := 1, mantissa := (6143/4096) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi329LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34356609535/34355545088) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf6887InnerLog : WideLogData :=
  innerPair375Data

set_option maxRecDepth 1000000 in
private theorem leaf6887LocalValidity :
    LeafFacts leaf6887Box leaf6887Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6887Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178836991/17177772544) }) = true
      norm_num [leaf6887Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6887CertificateValid :
    WideCertificateValid leaf6887Box leaf6887Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi329ValidityFacts
    leaf6887LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6887CoverageChecked :
    coverageCheck (innerAD leaf6887Box) leaf6887InnerLog = true := by
  rfl'

private theorem leaf6887InnerLogValid :
    leaf6887InnerLog.Valid 8 (innerAD leaf6887Box) :=
  wideLogDataValid_of_cachedCheck endpoint98PositiveFacts
    endpoint99PositiveFacts.valid leaf6887CoverageChecked

private noncomputable def leaf6887InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629601/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6887InputLogOnePlusV_eq :
    leaf6887InputLogOnePlusV = outerEnclosure 24
      (leaf6887Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6887RoundedFacts : LeafRoundedFacts 8
    leaf6887Certificate.logOnePlusV leaf6887InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6887InputLogOnePlusV_eq }

private noncomputable def leaf6887Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi329InputQChi innerPair375Input
    leaf6887InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6887LowerChecked :
    lowerCheck 24 leaf6887Box leaf6887Inputs = true := by
  rfl'

private theorem leaf6887CoversExact : CoversExact 8
    leaf6887Box leaf6887Certificate leaf6887InnerLog leaf6887Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi329RoundedFacts
    innerPair375RoundedFacts leaf6887RoundedFacts (by rfl)

private theorem leaf6887FlatSound : Sound leaf6887Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6887CertificateValid
    leaf6887InnerLogValid leaf6887CoversExact leaf6887LowerChecked

private noncomputable def leaf6888Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (65/128), chiHi := (33/64) }

private noncomputable def leaf6888Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435837/268435456) }, vSqrt := { lower := (8191/8192), upper := (17178836991/17177757184) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (796590229/536870912) }, upper := { exponent := 1, mantissa := (6173/4096) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi330LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34356594175/34355514368) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf6888InnerLog : WideLogData :=
  innerPair376Data

set_option maxRecDepth 1000000 in
private theorem leaf6888LocalValidity :
    LeafFacts leaf6888Box leaf6888Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6888Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178836991/17177757184) }) = true
      norm_num [leaf6888Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6888CertificateValid :
    WideCertificateValid leaf6888Box leaf6888Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi330ValidityFacts
    leaf6888LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6888CoverageChecked :
    coverageCheck (innerAD leaf6888Box) leaf6888InnerLog = true := by
  rfl'

private theorem leaf6888InnerLogValid :
    leaf6888InnerLog.Valid 8 (innerAD leaf6888Box) :=
  wideLogDataValid_of_cachedCheck endpoint98PositiveFacts
    endpoint482PositiveFacts.valid leaf6888CoverageChecked

private noncomputable def leaf6888InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453701/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf6888InputLogOnePlusV_eq :
    leaf6888InputLogOnePlusV = outerEnclosure 24
      (leaf6888Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6888RoundedFacts : LeafRoundedFacts 8
    leaf6888Certificate.logOnePlusV leaf6888InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6888InputLogOnePlusV_eq }

private noncomputable def leaf6888Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi330InputQChi innerPair376Input
    leaf6888InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6888LowerChecked :
    lowerCheck 24 leaf6888Box leaf6888Inputs = true := by
  rfl'

private theorem leaf6888CoversExact : CoversExact 8
    leaf6888Box leaf6888Certificate leaf6888InnerLog leaf6888Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi330RoundedFacts
    innerPair376RoundedFacts leaf6888RoundedFacts (by rfl)

private theorem leaf6888FlatSound : Sound leaf6888Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6888CertificateValid
    leaf6888InnerLogValid leaf6888CoversExact leaf6888LowerChecked

private noncomputable def leaf6889Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (65/128), chiHi := (33/64) }

private noncomputable def leaf6889Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435839/268435456) }, vSqrt := { lower := (8191/8192), upper := (17178836991/17177740288) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (800849807/536870912) }, upper := { exponent := 1, mantissa := (3103/2048) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi330LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34356577279/34355480576) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf6889InnerLog : WideLogData :=
  innerPair376Data

set_option maxRecDepth 1000000 in
private theorem leaf6889LocalValidity :
    LeafFacts leaf6889Box leaf6889Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6889Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178836991/17177740288) }) = true
      norm_num [leaf6889Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6889CertificateValid :
    WideCertificateValid leaf6889Box leaf6889Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi330ValidityFacts
    leaf6889LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6889CoverageChecked :
    coverageCheck (innerAD leaf6889Box) leaf6889InnerLog = true := by
  rfl'

private theorem leaf6889InnerLogValid :
    leaf6889InnerLog.Valid 8 (innerAD leaf6889Box) :=
  wideLogDataValid_of_cachedCheck endpoint98PositiveFacts
    endpoint482PositiveFacts.valid leaf6889CoverageChecked

private noncomputable def leaf6889InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726851/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf6889InputLogOnePlusV_eq :
    leaf6889InputLogOnePlusV = outerEnclosure 24
      (leaf6889Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6889RoundedFacts : LeafRoundedFacts 8
    leaf6889Certificate.logOnePlusV leaf6889InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6889InputLogOnePlusV_eq }

private noncomputable def leaf6889Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi330InputQChi innerPair376Input
    leaf6889InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6889LowerChecked :
    lowerCheck 24 leaf6889Box leaf6889Inputs = true := by
  rfl'

private theorem leaf6889CoversExact : CoversExact 8
    leaf6889Box leaf6889Certificate leaf6889InnerLog leaf6889Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi330RoundedFacts
    innerPair376RoundedFacts leaf6889RoundedFacts (by rfl)

private theorem leaf6889FlatSound : Sound leaf6889Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6889CertificateValid
    leaf6889InnerLogValid leaf6889CoversExact leaf6889LowerChecked

private noncomputable def leaf6890Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (1/2), chiHi := (65/128) }

private noncomputable def leaf6890Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435839/268435456) }, vSqrt := { lower := (8191/8192), upper := (17178836991/17177755904) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (796852355/536870912) }, upper := { exponent := 1, mantissa := (12351/8192) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi329LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34356592895/34355511808) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf6890InnerLog : WideLogData :=
  innerPair376Data

set_option maxRecDepth 1000000 in
private theorem leaf6890LocalValidity :
    LeafFacts leaf6890Box leaf6890Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6890Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178836991/17177755904) }) = true
      norm_num [leaf6890Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6890CertificateValid :
    WideCertificateValid leaf6890Box leaf6890Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi329ValidityFacts
    leaf6890LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6890CoverageChecked :
    coverageCheck (innerAD leaf6890Box) leaf6890InnerLog = true := by
  rfl'

private theorem leaf6890InnerLogValid :
    leaf6890InnerLog.Valid 8 (innerAD leaf6890Box) :=
  wideLogDataValid_of_cachedCheck endpoint98PositiveFacts
    endpoint482PositiveFacts.valid leaf6890CoverageChecked

private noncomputable def leaf6890InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629609/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6890InputLogOnePlusV_eq :
    leaf6890InputLogOnePlusV = outerEnclosure 24
      (leaf6890Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6890RoundedFacts : LeafRoundedFacts 8
    leaf6890Certificate.logOnePlusV leaf6890InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6890InputLogOnePlusV_eq }

private noncomputable def leaf6890Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi329InputQChi innerPair376Input
    leaf6890InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6890LowerChecked :
    lowerCheck 24 leaf6890Box leaf6890Inputs = true := by
  rfl'

private theorem leaf6890CoversExact : CoversExact 8
    leaf6890Box leaf6890Certificate leaf6890InnerLog leaf6890Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi329RoundedFacts
    innerPair376RoundedFacts leaf6890RoundedFacts (by rfl)

private theorem leaf6890FlatSound : Sound leaf6890Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6890CertificateValid
    leaf6890InnerLogValid leaf6890CoversExact leaf6890LowerChecked

private noncomputable def leaf6891Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (1/2), chiHi := (65/128) }

private noncomputable def leaf6891Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435841/268435456) }, vSqrt := { lower := (65527/65536), upper := (5726278997/5725913088) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (801046401/536870912) }, upper := { exponent := 1, mantissa := (97/64) } }, logOuter := sk176LogOuterCertificate, logK := sk176LogKCertificate, logChi := chi329LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (11452192085/11451826176) } }, logDArg := sk176LogDArgCertificate }

private noncomputable def leaf6891InnerLog : WideLogData :=
  innerPair376Data

set_option maxRecDepth 1000000 in
private theorem leaf6891LocalValidity :
    LeafFacts leaf6891Box leaf6891Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6891Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (5726278997/5725913088) }) = true
      norm_num [leaf6891Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6891CertificateValid :
    WideCertificateValid leaf6891Box leaf6891Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk176ValidityFacts chi329ValidityFacts
    leaf6891LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6891CoverageChecked :
    coverageCheck (innerAD leaf6891Box) leaf6891InnerLog = true := by
  rfl'

private theorem leaf6891InnerLogValid :
    leaf6891InnerLog.Valid 8 (innerAD leaf6891Box) :=
  wideLogDataValid_of_cachedCheck endpoint98PositiveFacts
    endpoint482PositiveFacts.valid leaf6891CoverageChecked

private noncomputable def leaf6891InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629617/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6891InputLogOnePlusV_eq :
    leaf6891InputLogOnePlusV = outerEnclosure 24
      (leaf6891Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6891RoundedFacts : LeafRoundedFacts 8
    leaf6891Certificate.logOnePlusV leaf6891InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6891InputLogOnePlusV_eq }

private noncomputable def leaf6891Inputs : Inputs :=
  inputsOfCaches globalInput sk176RoundedInputs
    chi329InputQChi innerPair376Input
    leaf6891InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6891LowerChecked :
    lowerCheck 24 leaf6891Box leaf6891Inputs = true := by
  rfl'

private theorem leaf6891CoversExact : CoversExact 8
    leaf6891Box leaf6891Certificate leaf6891InnerLog leaf6891Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk176RoundedFacts chi329RoundedFacts
    innerPair376RoundedFacts leaf6891RoundedFacts (by rfl)

private theorem leaf6891FlatSound : Sound leaf6891Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6891CertificateValid
    leaf6891InnerLogValid leaf6891CoversExact leaf6891LowerChecked

private noncomputable def leaf6892Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (65/128), chiHi := (33/64) }

private noncomputable def leaf6892Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435841/268435456) }, vSqrt := { lower := (8191/8192), upper := (17178836991/17177723392) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (805109385/536870912) }, upper := { exponent := 1, mantissa := (6239/4096) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi330LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34356560383/34355446784) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf6892InnerLog : WideLogData :=
  innerPair376Data

set_option maxRecDepth 1000000 in
private theorem leaf6892LocalValidity :
    LeafFacts leaf6892Box leaf6892Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6892Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178836991/17177723392) }) = true
      norm_num [leaf6892Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6892CertificateValid :
    WideCertificateValid leaf6892Box leaf6892Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi330ValidityFacts
    leaf6892LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6892CoverageChecked :
    coverageCheck (innerAD leaf6892Box) leaf6892InnerLog = true := by
  rfl'

private theorem leaf6892InnerLogValid :
    leaf6892InnerLog.Valid 8 (innerAD leaf6892Box) :=
  wideLogDataValid_of_cachedCheck endpoint98PositiveFacts
    endpoint482PositiveFacts.valid leaf6892CoverageChecked

private noncomputable def leaf6892InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629625/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6892InputLogOnePlusV_eq :
    leaf6892InputLogOnePlusV = outerEnclosure 24
      (leaf6892Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6892RoundedFacts : LeafRoundedFacts 8
    leaf6892Certificate.logOnePlusV leaf6892InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6892InputLogOnePlusV_eq }

private noncomputable def leaf6892Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi330InputQChi innerPair376Input
    leaf6892InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6892LowerChecked :
    lowerCheck 24 leaf6892Box leaf6892Inputs = true := by
  rfl'

private theorem leaf6892CoversExact : CoversExact 8
    leaf6892Box leaf6892Certificate leaf6892InnerLog leaf6892Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi330RoundedFacts
    innerPair376RoundedFacts leaf6892RoundedFacts (by rfl)

private theorem leaf6892FlatSound : Sound leaf6892Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6892CertificateValid
    leaf6892InnerLogValid leaf6892CoversExact leaf6892LowerChecked

private noncomputable def leaf6893Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (65/128), chiHi := (33/64) }

private noncomputable def leaf6893Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435843/268435456) }, vSqrt := { lower := (65527/65536), upper := (17178836991/17177706496) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (809368963/536870912) }, upper := { exponent := 1, mantissa := (49/32) } }, logOuter := sk176LogOuterCertificate, logK := sk176LogKCertificate, logChi := chi330LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (34356543487/34355412992) } }, logDArg := sk176LogDArgCertificate }

private noncomputable def leaf6893InnerLog : WideLogData :=
  innerPair381Data

set_option maxRecDepth 1000000 in
private theorem leaf6893LocalValidity :
    LeafFacts leaf6893Box leaf6893Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6893Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (17178836991/17177706496) }) = true
      norm_num [leaf6893Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6893CertificateValid :
    WideCertificateValid leaf6893Box leaf6893Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk176ValidityFacts chi330ValidityFacts
    leaf6893LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6893CoverageChecked :
    coverageCheck (innerAD leaf6893Box) leaf6893InnerLog = true := by
  rfl'

private theorem leaf6893InnerLogValid :
    leaf6893InnerLog.Valid 8 (innerAD leaf6893Box) :=
  wideLogDataValid_of_cachedCheck endpoint99PositiveFacts
    endpoint482PositiveFacts.valid leaf6893CoverageChecked

private noncomputable def leaf6893InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629633/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6893InputLogOnePlusV_eq :
    leaf6893InputLogOnePlusV = outerEnclosure 24
      (leaf6893Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6893RoundedFacts : LeafRoundedFacts 8
    leaf6893Certificate.logOnePlusV leaf6893InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6893InputLogOnePlusV_eq }

private noncomputable def leaf6893Inputs : Inputs :=
  inputsOfCaches globalInput sk176RoundedInputs
    chi330InputQChi innerPair381Input
    leaf6893InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6893LowerChecked :
    lowerCheck 24 leaf6893Box leaf6893Inputs = true := by
  rfl'

private theorem leaf6893CoversExact : CoversExact 8
    leaf6893Box leaf6893Certificate leaf6893InnerLog leaf6893Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk176RoundedFacts chi330RoundedFacts
    innerPair381RoundedFacts leaf6893RoundedFacts (by rfl)

private theorem leaf6893FlatSound : Sound leaf6893Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6893CertificateValid
    leaf6893InnerLogValid leaf6893CoversExact leaf6893LowerChecked

private noncomputable def leaf6894Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (33/64), chiHi := (67/128) }

private noncomputable def leaf6894Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435839/268435456) }, vSqrt := { lower := (8191/8192), upper := (17178836991/17177725184) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (804716195/536870912) }, upper := { exponent := 1, mantissa := (12471/8192) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi331LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34356562175/34355450368) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf6894InnerLog : WideLogData :=
  innerPair376Data

set_option maxRecDepth 1000000 in
private theorem leaf6894LocalValidity :
    LeafFacts leaf6894Box leaf6894Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6894Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178836991/17177725184) }) = true
      norm_num [leaf6894Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6894CertificateValid :
    WideCertificateValid leaf6894Box leaf6894Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi331ValidityFacts
    leaf6894LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6894CoverageChecked :
    coverageCheck (innerAD leaf6894Box) leaf6894InnerLog = true := by
  rfl'

private theorem leaf6894InnerLogValid :
    leaf6894InnerLog.Valid 8 (innerAD leaf6894Box) :=
  wideLogDataValid_of_cachedCheck endpoint98PositiveFacts
    endpoint482PositiveFacts.valid leaf6894CoverageChecked

private noncomputable def leaf6894InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453703/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf6894InputLogOnePlusV_eq :
    leaf6894InputLogOnePlusV = outerEnclosure 24
      (leaf6894Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6894RoundedFacts : LeafRoundedFacts 8
    leaf6894Certificate.logOnePlusV leaf6894InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6894InputLogOnePlusV_eq }

private noncomputable def leaf6894Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi331InputQChi innerPair376Input
    leaf6894InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6894LowerChecked :
    lowerCheck 24 leaf6894Box leaf6894Inputs = true := by
  rfl'

private theorem leaf6894CoversExact : CoversExact 8
    leaf6894Box leaf6894Certificate leaf6894InnerLog leaf6894Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi331RoundedFacts
    innerPair376RoundedFacts leaf6894RoundedFacts (by rfl)

private theorem leaf6894FlatSound : Sound leaf6894Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6894CertificateValid
    leaf6894InnerLogValid leaf6894CoversExact leaf6894LowerChecked

private noncomputable def leaf6895Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (33/64), chiHi := (67/128) }

private noncomputable def leaf6895Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435841/268435456) }, vSqrt := { lower := (8191/8192), upper := (17178836991/17177708032) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (809041305/536870912) }, upper := { exponent := 1, mantissa := (6269/4096) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi331LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34356545023/34355416064) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf6895InnerLog : WideLogData :=
  innerPair381Data

set_option maxRecDepth 1000000 in
private theorem leaf6895LocalValidity :
    LeafFacts leaf6895Box leaf6895Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6895Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178836991/17177708032) }) = true
      norm_num [leaf6895Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6895CertificateValid :
    WideCertificateValid leaf6895Box leaf6895Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi331ValidityFacts
    leaf6895LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6895CoverageChecked :
    coverageCheck (innerAD leaf6895Box) leaf6895InnerLog = true := by
  rfl'

private theorem leaf6895InnerLogValid :
    leaf6895InnerLog.Valid 8 (innerAD leaf6895Box) :=
  wideLogDataValid_of_cachedCheck endpoint99PositiveFacts
    endpoint482PositiveFacts.valid leaf6895CoverageChecked

private noncomputable def leaf6895InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (181713/262144) }

set_option maxRecDepth 1000000 in
private theorem leaf6895InputLogOnePlusV_eq :
    leaf6895InputLogOnePlusV = outerEnclosure 24
      (leaf6895Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6895RoundedFacts : LeafRoundedFacts 8
    leaf6895Certificate.logOnePlusV leaf6895InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6895InputLogOnePlusV_eq }

private noncomputable def leaf6895Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi331InputQChi innerPair381Input
    leaf6895InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6895LowerChecked :
    lowerCheck 24 leaf6895Box leaf6895Inputs = true := by
  rfl'

private theorem leaf6895CoversExact : CoversExact 8
    leaf6895Box leaf6895Certificate leaf6895InnerLog leaf6895Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi331RoundedFacts
    innerPair381RoundedFacts leaf6895RoundedFacts (by rfl)

private theorem leaf6895FlatSound : Sound leaf6895Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6895CertificateValid
    leaf6895InnerLogValid leaf6895CoversExact leaf6895LowerChecked

private noncomputable def leaf6896Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (67/128), chiHi := (17/32) }

private noncomputable def leaf6896Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435841/268435456) }, vSqrt := { lower := (8191/8192), upper := (5726278997/5725897728) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (812842161/536870912) }, upper := { exponent := 1, mantissa := (3149/2048) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi332LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (11452176725/11451795456) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf6896InnerLog : WideLogData :=
  innerPair382Data

set_option maxRecDepth 1000000 in
private theorem leaf6896LocalValidity :
    LeafFacts leaf6896Box leaf6896Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6896Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5726278997/5725897728) }) = true
      norm_num [leaf6896Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6896CertificateValid :
    WideCertificateValid leaf6896Box leaf6896Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi332ValidityFacts
    leaf6896LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6896CoverageChecked :
    coverageCheck (innerAD leaf6896Box) leaf6896InnerLog = true := by
  rfl'

private theorem leaf6896InnerLogValid :
    leaf6896InnerLog.Valid 8 (innerAD leaf6896Box) :=
  wideLogDataValid_of_cachedCheck endpoint99PositiveFacts
    endpoint483PositiveFacts.valid leaf6896CoverageChecked

private noncomputable def leaf6896InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629639/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6896InputLogOnePlusV_eq :
    leaf6896InputLogOnePlusV = outerEnclosure 24
      (leaf6896Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6896RoundedFacts : LeafRoundedFacts 8
    leaf6896Certificate.logOnePlusV leaf6896InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6896InputLogOnePlusV_eq }

private noncomputable def leaf6896Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi332InputQChi innerPair382Input
    leaf6896InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6896LowerChecked :
    lowerCheck 24 leaf6896Box leaf6896Inputs = true := by
  rfl'

private theorem leaf6896CoversExact : CoversExact 8
    leaf6896Box leaf6896Certificate leaf6896InnerLog leaf6896Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi332RoundedFacts
    innerPair382RoundedFacts leaf6896RoundedFacts (by rfl)

private theorem leaf6896FlatSound : Sound leaf6896Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6896CertificateValid
    leaf6896InnerLogValid leaf6896CoversExact leaf6896LowerChecked

private noncomputable def leaf6897Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (67/128), chiHi := (17/32) }

private noncomputable def leaf6897Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435843/268435456) }, vSqrt := { lower := (8191/8192), upper := (399507837/399480832) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (817232803/536870912) }, upper := { exponent := 1, mantissa := (1583/1024) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi332LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (798988669/798961664) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf6897InnerLog : WideLogData :=
  innerPair382Data

set_option maxRecDepth 1000000 in
private theorem leaf6897LocalValidity :
    LeafFacts leaf6897Box leaf6897Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6897Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (399507837/399480832) }) = true
      norm_num [leaf6897Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6897CertificateValid :
    WideCertificateValid leaf6897Box leaf6897Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi332ValidityFacts
    leaf6897LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6897CoverageChecked :
    coverageCheck (innerAD leaf6897Box) leaf6897InnerLog = true := by
  rfl'

private theorem leaf6897InnerLogValid :
    leaf6897InnerLog.Valid 8 (innerAD leaf6897Box) :=
  wideLogDataValid_of_cachedCheck endpoint99PositiveFacts
    endpoint483PositiveFacts.valid leaf6897CoverageChecked

private noncomputable def leaf6897InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726853/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf6897InputLogOnePlusV_eq :
    leaf6897InputLogOnePlusV = outerEnclosure 24
      (leaf6897Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6897RoundedFacts : LeafRoundedFacts 8
    leaf6897Certificate.logOnePlusV leaf6897InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6897InputLogOnePlusV_eq }

private noncomputable def leaf6897Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi332InputQChi innerPair382Input
    leaf6897InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6897LowerChecked :
    lowerCheck 24 leaf6897Box leaf6897Inputs = true := by
  rfl'

private theorem leaf6897CoversExact : CoversExact 8
    leaf6897Box leaf6897Certificate leaf6897InnerLog leaf6897Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi332RoundedFacts
    innerPair382RoundedFacts leaf6897RoundedFacts (by rfl)

private theorem leaf6897FlatSound : Sound leaf6897Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6897CertificateValid
    leaf6897InnerLogValid leaf6897CoversExact leaf6897LowerChecked

private noncomputable def leaf6898Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (33/64), chiHi := (67/128) }

private noncomputable def leaf6898Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435843/268435456) }, vSqrt := { lower := (8191/8192), upper := (5726278997/5725896960) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (813366415/536870912) }, upper := { exponent := 1, mantissa := (12605/8192) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi331LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (11452175957/11451793920) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf6898InnerLog : WideLogData :=
  innerPair382Data

set_option maxRecDepth 1000000 in
private theorem leaf6898LocalValidity :
    LeafFacts leaf6898Box leaf6898Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6898Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5726278997/5725896960) }) = true
      norm_num [leaf6898Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6898CertificateValid :
    WideCertificateValid leaf6898Box leaf6898Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi331ValidityFacts
    leaf6898LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6898CoverageChecked :
    coverageCheck (innerAD leaf6898Box) leaf6898InnerLog = true := by
  rfl'

private theorem leaf6898InnerLogValid :
    leaf6898InnerLog.Valid 8 (innerAD leaf6898Box) :=
  wideLogDataValid_of_cachedCheck endpoint99PositiveFacts
    endpoint483PositiveFacts.valid leaf6898CoverageChecked

private noncomputable def leaf6898InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453705/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf6898InputLogOnePlusV_eq :
    leaf6898InputLogOnePlusV = outerEnclosure 24
      (leaf6898Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6898RoundedFacts : LeafRoundedFacts 8
    leaf6898Certificate.logOnePlusV leaf6898InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6898InputLogOnePlusV_eq }

private noncomputable def leaf6898Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi331InputQChi innerPair382Input
    leaf6898InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6898LowerChecked :
    lowerCheck 24 leaf6898Box leaf6898Inputs = true := by
  rfl'

private theorem leaf6898CoversExact : CoversExact 8
    leaf6898Box leaf6898Certificate leaf6898InnerLog leaf6898Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi331RoundedFacts
    innerPair382RoundedFacts leaf6898RoundedFacts (by rfl)

private theorem leaf6898FlatSound : Sound leaf6898Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6898CertificateValid
    leaf6898InnerLogValid leaf6898CoversExact leaf6898LowerChecked

private noncomputable def leaf6899Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (33/64), chiHi := (67/128) }

private noncomputable def leaf6899Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435845/268435456) }, vSqrt := { lower := (65527/65536), upper := (17178836991/17177673728) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (817691525/536870912) }, upper := { exponent := 1, mantissa := (99/64) } }, logOuter := sk176LogOuterCertificate, logK := sk176LogKCertificate, logChi := chi331LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (34356510719/34355347456) } }, logDArg := sk176LogDArgCertificate }

private noncomputable def leaf6899InnerLog : WideLogData :=
  innerPair382Data

set_option maxRecDepth 1000000 in
private theorem leaf6899LocalValidity :
    LeafFacts leaf6899Box leaf6899Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6899Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (17178836991/17177673728) }) = true
      norm_num [leaf6899Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6899CertificateValid :
    WideCertificateValid leaf6899Box leaf6899Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk176ValidityFacts chi331ValidityFacts
    leaf6899LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6899CoverageChecked :
    coverageCheck (innerAD leaf6899Box) leaf6899InnerLog = true := by
  rfl'

private theorem leaf6899InnerLogValid :
    leaf6899InnerLog.Valid 8 (innerAD leaf6899Box) :=
  wideLogDataValid_of_cachedCheck endpoint99PositiveFacts
    endpoint483PositiveFacts.valid leaf6899CoverageChecked

private noncomputable def leaf6899InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629649/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6899InputLogOnePlusV_eq :
    leaf6899InputLogOnePlusV = outerEnclosure 24
      (leaf6899Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6899RoundedFacts : LeafRoundedFacts 8
    leaf6899Certificate.logOnePlusV leaf6899InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6899InputLogOnePlusV_eq }

private noncomputable def leaf6899Inputs : Inputs :=
  inputsOfCaches globalInput sk176RoundedInputs
    chi331InputQChi innerPair382Input
    leaf6899InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6899LowerChecked :
    lowerCheck 24 leaf6899Box leaf6899Inputs = true := by
  rfl'

private theorem leaf6899CoversExact : CoversExact 8
    leaf6899Box leaf6899Certificate leaf6899InnerLog leaf6899Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk176RoundedFacts chi331RoundedFacts
    innerPair382RoundedFacts leaf6899RoundedFacts (by rfl)

private theorem leaf6899FlatSound : Sound leaf6899Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6899CertificateValid
    leaf6899InnerLogValid leaf6899CoversExact leaf6899LowerChecked

private noncomputable def leaf6900Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (67/128), chiHi := (17/32) }

private noncomputable def leaf6900Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435845/268435456) }, vSqrt := { lower := (8191/8192), upper := (17178836991/17177658368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (821623445/536870912) }, upper := { exponent := 1, mantissa := (3183/2048) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi332LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34356495359/34355316736) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf6900InnerLog : WideLogData :=
  innerPair382Data

set_option maxRecDepth 1000000 in
private theorem leaf6900LocalValidity :
    LeafFacts leaf6900Box leaf6900Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6900Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178836991/17177658368) }) = true
      norm_num [leaf6900Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6900CertificateValid :
    WideCertificateValid leaf6900Box leaf6900Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi332ValidityFacts
    leaf6900LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6900CoverageChecked :
    coverageCheck (innerAD leaf6900Box) leaf6900InnerLog = true := by
  rfl'

private theorem leaf6900InnerLogValid :
    leaf6900InnerLog.Valid 8 (innerAD leaf6900Box) :=
  wideLogDataValid_of_cachedCheck endpoint99PositiveFacts
    endpoint483PositiveFacts.valid leaf6900CoverageChecked

private noncomputable def leaf6900InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453707/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf6900InputLogOnePlusV_eq :
    leaf6900InputLogOnePlusV = outerEnclosure 24
      (leaf6900Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6900RoundedFacts : LeafRoundedFacts 8
    leaf6900Certificate.logOnePlusV leaf6900InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6900InputLogOnePlusV_eq }

private noncomputable def leaf6900Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi332InputQChi innerPair382Input
    leaf6900InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6900LowerChecked :
    lowerCheck 24 leaf6900Box leaf6900Inputs = true := by
  rfl'

private theorem leaf6900CoversExact : CoversExact 8
    leaf6900Box leaf6900Certificate leaf6900InnerLog leaf6900Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi332RoundedFacts
    innerPair382RoundedFacts leaf6900RoundedFacts (by rfl)

private theorem leaf6900FlatSound : Sound leaf6900Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6900CertificateValid
    leaf6900InnerLogValid leaf6900CoversExact leaf6900LowerChecked

private noncomputable def leaf6901Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (67/128), chiHi := (17/32) }

private noncomputable def leaf6901Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435847/268435456) }, vSqrt := { lower := (65527/65536), upper := (5726278997/5725880320) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (826014087/536870912) }, upper := { exponent := 1, mantissa := (25/16) } }, logOuter := sk176LogOuterCertificate, logK := sk176LogKCertificate, logChi := chi332LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (11452159317/11451760640) } }, logDArg := sk176LogDArgCertificate }

private noncomputable def leaf6901InnerLog : WideLogData :=
  innerPair743Data

set_option maxRecDepth 1000000 in
private theorem leaf6901LocalValidity :
    LeafFacts leaf6901Box leaf6901Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6901Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (5726278997/5725880320) }) = true
      norm_num [leaf6901Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6901CertificateValid :
    WideCertificateValid leaf6901Box leaf6901Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk176ValidityFacts chi332ValidityFacts
    leaf6901LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6901CoverageChecked :
    coverageCheck (innerAD leaf6901Box) leaf6901InnerLog = true := by
  rfl'

private theorem leaf6901InnerLogValid :
    leaf6901InnerLog.Valid 8 (innerAD leaf6901Box) :=
  wideLogDataValid_of_cachedCheck endpoint482PositiveFacts
    endpoint483PositiveFacts.valid leaf6901CoverageChecked

private noncomputable def leaf6901InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629665/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6901InputLogOnePlusV_eq :
    leaf6901InputLogOnePlusV = outerEnclosure 24
      (leaf6901Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6901RoundedFacts : LeafRoundedFacts 8
    leaf6901Certificate.logOnePlusV leaf6901InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6901InputLogOnePlusV_eq }

private noncomputable def leaf6901Inputs : Inputs :=
  inputsOfCaches globalInput sk176RoundedInputs
    chi332InputQChi innerPair743Input
    leaf6901InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6901LowerChecked :
    lowerCheck 24 leaf6901Box leaf6901Inputs = true := by
  rfl'

private theorem leaf6901CoversExact : CoversExact 8
    leaf6901Box leaf6901Certificate leaf6901InnerLog leaf6901Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk176RoundedFacts chi332RoundedFacts
    innerPair743RoundedFacts leaf6901RoundedFacts (by rfl)

private theorem leaf6901FlatSound : Sound leaf6901Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6901CertificateValid
    leaf6901InnerLogValid leaf6901CoversExact leaf6901LowerChecked

private noncomputable def leaf6902Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (17/32), chiHi := (69/128) }

private noncomputable def leaf6902Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435835/268435456) }, vSqrt := { lower := (8191/8192), upper := (17178836991/17177731840) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (803143431/536870912) }, upper := { exponent := 1, mantissa := (12445/8192) } }, logOuter := sk169LogOuterCertificate, logK := sk169LogKCertificate, logChi := chi327LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34356568831/34355463680) } }, logDArg := sk169LogDArgCertificate }

private noncomputable def leaf6902InnerLog : WideLogData :=
  innerPair376Data

set_option maxRecDepth 1000000 in
private theorem leaf6902LocalValidity :
    LeafFacts leaf6902Box leaf6902Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6902Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178836991/17177731840) }) = true
      norm_num [leaf6902Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6902CertificateValid :
    WideCertificateValid leaf6902Box leaf6902Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk169ValidityFacts chi327ValidityFacts
    leaf6902LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6902CoverageChecked :
    coverageCheck (innerAD leaf6902Box) leaf6902InnerLog = true := by
  rfl'

private theorem leaf6902InnerLogValid :
    leaf6902InnerLog.Valid 8 (innerAD leaf6902Box) :=
  wideLogDataValid_of_cachedCheck endpoint98PositiveFacts
    endpoint482PositiveFacts.valid leaf6902CoverageChecked

private noncomputable def leaf6902InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907405/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6902InputLogOnePlusV_eq :
    leaf6902InputLogOnePlusV = outerEnclosure 24
      (leaf6902Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6902RoundedFacts : LeafRoundedFacts 8
    leaf6902Certificate.logOnePlusV leaf6902InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6902InputLogOnePlusV_eq }

private noncomputable def leaf6902Inputs : Inputs :=
  inputsOfCaches globalInput sk169RoundedInputs
    chi327InputQChi innerPair376Input
    leaf6902InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6902LowerChecked :
    lowerCheck 24 leaf6902Box leaf6902Inputs = true := by
  rfl'

private theorem leaf6902CoversExact : CoversExact 8
    leaf6902Box leaf6902Certificate leaf6902InnerLog leaf6902Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk169RoundedFacts chi327RoundedFacts
    innerPair376RoundedFacts leaf6902RoundedFacts (by rfl)

private theorem leaf6902FlatSound : Sound leaf6902Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6902CertificateValid
    leaf6902InnerLogValid leaf6902CoversExact leaf6902LowerChecked

private noncomputable def leaf6903Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (17/32), chiHi := (69/128) }

private noncomputable def leaf6903Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435837/268435456) }, vSqrt := { lower := (8191/8192), upper := (17178836991/17177714176) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (807599605/536870912) }, upper := { exponent := 1, mantissa := (6257/4096) } }, logOuter := sk170LogOuterCertificate, logK := sk170LogKCertificate, logChi := chi327LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34356551167/34355428352) } }, logDArg := sk170LogDArgCertificate }

private noncomputable def leaf6903InnerLog : WideLogData :=
  innerPair381Data

set_option maxRecDepth 1000000 in
private theorem leaf6903LocalValidity :
    LeafFacts leaf6903Box leaf6903Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6903Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178836991/17177714176) }) = true
      norm_num [leaf6903Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6903CertificateValid :
    WideCertificateValid leaf6903Box leaf6903Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk170ValidityFacts chi327ValidityFacts
    leaf6903LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6903CoverageChecked :
    coverageCheck (innerAD leaf6903Box) leaf6903InnerLog = true := by
  rfl'

private theorem leaf6903InnerLogValid :
    leaf6903InnerLog.Valid 8 (innerAD leaf6903Box) :=
  wideLogDataValid_of_cachedCheck endpoint99PositiveFacts
    endpoint482PositiveFacts.valid leaf6903CoverageChecked

private noncomputable def leaf6903InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629629/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6903InputLogOnePlusV_eq :
    leaf6903InputLogOnePlusV = outerEnclosure 24
      (leaf6903Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6903RoundedFacts : LeafRoundedFacts 8
    leaf6903Certificate.logOnePlusV leaf6903InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6903InputLogOnePlusV_eq }

private noncomputable def leaf6903Inputs : Inputs :=
  inputsOfCaches globalInput sk170RoundedInputs
    chi327InputQChi innerPair381Input
    leaf6903InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6903LowerChecked :
    lowerCheck 24 leaf6903Box leaf6903Inputs = true := by
  rfl'

private theorem leaf6903CoversExact : CoversExact 8
    leaf6903Box leaf6903Certificate leaf6903InnerLog leaf6903Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk170RoundedFacts chi327RoundedFacts
    innerPair381RoundedFacts leaf6903RoundedFacts (by rfl)

private theorem leaf6903FlatSound : Sound leaf6903Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6903CertificateValid
    leaf6903InnerLogValid leaf6903CoversExact leaf6903LowerChecked

private noncomputable def leaf6904Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (69/128), chiHi := (35/64) }

private noncomputable def leaf6904Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435837/268435456) }, vSqrt := { lower := (8191/8192), upper := (336839941/336817664) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (811007269/536870912) }, upper := { exponent := 1, mantissa := (6283/4096) } }, logOuter := sk169LogOuterCertificate, logK := sk169LogKCertificate, logChi := chi328LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (673657605/673635328) } }, logDArg := sk169LogDArgCertificate }

private noncomputable def leaf6904InnerLog : WideLogData :=
  innerPair382Data

set_option maxRecDepth 1000000 in
private theorem leaf6904LocalValidity :
    LeafFacts leaf6904Box leaf6904Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6904Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (336839941/336817664) }) = true
      norm_num [leaf6904Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6904CertificateValid :
    WideCertificateValid leaf6904Box leaf6904Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk169ValidityFacts chi328ValidityFacts
    leaf6904LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6904CoverageChecked :
    coverageCheck (innerAD leaf6904Box) leaf6904InnerLog = true := by
  rfl'

private theorem leaf6904InnerLogValid :
    leaf6904InnerLog.Valid 8 (innerAD leaf6904Box) :=
  wideLogDataValid_of_cachedCheck endpoint99PositiveFacts
    endpoint483PositiveFacts.valid leaf6904CoverageChecked

private noncomputable def leaf6904InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907409/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6904InputLogOnePlusV_eq :
    leaf6904InputLogOnePlusV = outerEnclosure 24
      (leaf6904Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6904RoundedFacts : LeafRoundedFacts 8
    leaf6904Certificate.logOnePlusV leaf6904InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6904InputLogOnePlusV_eq }

private noncomputable def leaf6904Inputs : Inputs :=
  inputsOfCaches globalInput sk169RoundedInputs
    chi328InputQChi innerPair382Input
    leaf6904InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6904LowerChecked :
    lowerCheck 24 leaf6904Box leaf6904Inputs = true := by
  rfl'

private theorem leaf6904CoversExact : CoversExact 8
    leaf6904Box leaf6904Certificate leaf6904InnerLog leaf6904Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk169RoundedFacts chi328RoundedFacts
    innerPair382RoundedFacts leaf6904RoundedFacts (by rfl)

private theorem leaf6904FlatSound : Sound leaf6904Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6904CertificateValid
    leaf6904InnerLogValid leaf6904CoversExact leaf6904LowerChecked

private noncomputable def leaf6905Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (69/128), chiHi := (35/64) }

private noncomputable def leaf6905Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435839/268435456) }, vSqrt := { lower := (8191/8192), upper := (17178836991/17177682944) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (815528975/536870912) }, upper := { exponent := 1, mantissa := (3159/2048) } }, logOuter := sk170LogOuterCertificate, logK := sk170LogKCertificate, logChi := chi328LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34356519935/34355365888) } }, logDArg := sk170LogDArgCertificate }

private noncomputable def leaf6905InnerLog : WideLogData :=
  innerPair382Data

set_option maxRecDepth 1000000 in
private theorem leaf6905LocalValidity :
    LeafFacts leaf6905Box leaf6905Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6905Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178836991/17177682944) }) = true
      norm_num [leaf6905Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6905CertificateValid :
    WideCertificateValid leaf6905Box leaf6905Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk170ValidityFacts chi328ValidityFacts
    leaf6905LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6905CoverageChecked :
    coverageCheck (innerAD leaf6905Box) leaf6905InnerLog = true := by
  rfl'

private theorem leaf6905InnerLogValid :
    leaf6905InnerLog.Valid 8 (innerAD leaf6905Box) :=
  wideLogDataValid_of_cachedCheck endpoint99PositiveFacts
    endpoint483PositiveFacts.valid leaf6905CoverageChecked

private noncomputable def leaf6905InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907411/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6905InputLogOnePlusV_eq :
    leaf6905InputLogOnePlusV = outerEnclosure 24
      (leaf6905Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6905RoundedFacts : LeafRoundedFacts 8
    leaf6905Certificate.logOnePlusV leaf6905InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6905InputLogOnePlusV_eq }

private noncomputable def leaf6905Inputs : Inputs :=
  inputsOfCaches globalInput sk170RoundedInputs
    chi328InputQChi innerPair382Input
    leaf6905InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6905LowerChecked :
    lowerCheck 24 leaf6905Box leaf6905Inputs = true := by
  rfl'

private theorem leaf6905CoversExact : CoversExact 8
    leaf6905Box leaf6905Certificate leaf6905InnerLog leaf6905Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk170RoundedFacts chi328RoundedFacts
    innerPair382RoundedFacts leaf6905RoundedFacts (by rfl)

private theorem leaf6905FlatSound : Sound leaf6905Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6905CertificateValid
    leaf6905InnerLogValid leaf6905CoversExact leaf6905LowerChecked

private noncomputable def leaf6906Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (17/32), chiHi := (69/128) }

private noncomputable def leaf6906Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435839/268435456) }, vSqrt := { lower := (8191/8192), upper := (1010519823/1010452736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (812055779/536870912) }, upper := { exponent := 1, mantissa := (12583/8192) } }, logOuter := sk171LogOuterCertificate, logK := sk171LogKCertificate, logChi := chi327LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (2020972559/2020905472) } }, logDArg := sk171LogDArgCertificate }

private noncomputable def leaf6906InnerLog : WideLogData :=
  innerPair382Data

set_option maxRecDepth 1000000 in
private theorem leaf6906LocalValidity :
    LeafFacts leaf6906Box leaf6906Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6906Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (1010519823/1010452736) }) = true
      norm_num [leaf6906Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6906CertificateValid :
    WideCertificateValid leaf6906Box leaf6906Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk171ValidityFacts chi327ValidityFacts
    leaf6906LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6906CoverageChecked :
    coverageCheck (innerAD leaf6906Box) leaf6906InnerLog = true := by
  rfl'

private theorem leaf6906InnerLogValid :
    leaf6906InnerLog.Valid 8 (innerAD leaf6906Box) :=
  wideLogDataValid_of_cachedCheck endpoint99PositiveFacts
    endpoint483PositiveFacts.valid leaf6906CoverageChecked

private noncomputable def leaf6906InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814819/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6906InputLogOnePlusV_eq :
    leaf6906InputLogOnePlusV = outerEnclosure 24
      (leaf6906Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6906RoundedFacts : LeafRoundedFacts 8
    leaf6906Certificate.logOnePlusV leaf6906InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6906InputLogOnePlusV_eq }

private noncomputable def leaf6906Inputs : Inputs :=
  inputsOfCaches globalInput sk171RoundedInputs
    chi327InputQChi innerPair382Input
    leaf6906InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6906LowerChecked :
    lowerCheck 24 leaf6906Box leaf6906Inputs = true := by
  rfl'

private theorem leaf6906CoversExact : CoversExact 8
    leaf6906Box leaf6906Certificate leaf6906InnerLog leaf6906Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk171RoundedFacts chi327RoundedFacts
    innerPair382RoundedFacts leaf6906RoundedFacts (by rfl)

private theorem leaf6906FlatSound : Sound leaf6906Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6906CertificateValid
    leaf6906InnerLogValid leaf6906CoversExact leaf6906LowerChecked

private noncomputable def leaf6907Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (17/32), chiHi := (69/128) }

private noncomputable def leaf6907Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435841/268435456) }, vSqrt := { lower := (8191/8192), upper := (17178836991/17177678848) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (816511953/536870912) }, upper := { exponent := 1, mantissa := (3163/2048) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi327LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34356515839/34355357696) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf6907InnerLog : WideLogData :=
  innerPair382Data

set_option maxRecDepth 1000000 in
private theorem leaf6907LocalValidity :
    LeafFacts leaf6907Box leaf6907Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6907Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178836991/17177678848) }) = true
      norm_num [leaf6907Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6907CertificateValid :
    WideCertificateValid leaf6907Box leaf6907Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi327ValidityFacts
    leaf6907LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6907CoverageChecked :
    coverageCheck (innerAD leaf6907Box) leaf6907InnerLog = true := by
  rfl'

private theorem leaf6907InnerLogValid :
    leaf6907InnerLog.Valid 8 (innerAD leaf6907Box) :=
  wideLogDataValid_of_cachedCheck endpoint99PositiveFacts
    endpoint483PositiveFacts.valid leaf6907CoverageChecked

private noncomputable def leaf6907InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814823/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6907InputLogOnePlusV_eq :
    leaf6907InputLogOnePlusV = outerEnclosure 24
      (leaf6907Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6907RoundedFacts : LeafRoundedFacts 8
    leaf6907Certificate.logOnePlusV leaf6907InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6907InputLogOnePlusV_eq }

private noncomputable def leaf6907Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi327InputQChi innerPair382Input
    leaf6907InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6907LowerChecked :
    lowerCheck 24 leaf6907Box leaf6907Inputs = true := by
  rfl'

private theorem leaf6907CoversExact : CoversExact 8
    leaf6907Box leaf6907Certificate leaf6907InnerLog leaf6907Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi327RoundedFacts
    innerPair382RoundedFacts leaf6907RoundedFacts (by rfl)

private theorem leaf6907FlatSound : Sound leaf6907Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6907CertificateValid
    leaf6907InnerLogValid leaf6907CoversExact leaf6907LowerChecked

private noncomputable def leaf6908Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (69/128), chiHi := (35/64) }

private noncomputable def leaf6908Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435841/268435456) }, vSqrt := { lower := (8191/8192), upper := (17178836991/17177665024) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (820050681/536870912) }, upper := { exponent := 1, mantissa := (6353/4096) } }, logOuter := sk171LogOuterCertificate, logK := sk171LogKCertificate, logChi := chi328LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34356502015/34355330048) } }, logDArg := sk171LogDArgCertificate }

private noncomputable def leaf6908InnerLog : WideLogData :=
  innerPair382Data

set_option maxRecDepth 1000000 in
private theorem leaf6908LocalValidity :
    LeafFacts leaf6908Box leaf6908Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6908Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178836991/17177665024) }) = true
      norm_num [leaf6908Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6908CertificateValid :
    WideCertificateValid leaf6908Box leaf6908Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk171ValidityFacts chi328ValidityFacts
    leaf6908LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6908CoverageChecked :
    coverageCheck (innerAD leaf6908Box) leaf6908InnerLog = true := by
  rfl'

private theorem leaf6908InnerLogValid :
    leaf6908InnerLog.Valid 8 (innerAD leaf6908Box) :=
  wideLogDataValid_of_cachedCheck endpoint99PositiveFacts
    endpoint483PositiveFacts.valid leaf6908CoverageChecked

private noncomputable def leaf6908InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629653/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6908InputLogOnePlusV_eq :
    leaf6908InputLogOnePlusV = outerEnclosure 24
      (leaf6908Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6908RoundedFacts : LeafRoundedFacts 8
    leaf6908Certificate.logOnePlusV leaf6908InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6908InputLogOnePlusV_eq }

private noncomputable def leaf6908Inputs : Inputs :=
  inputsOfCaches globalInput sk171RoundedInputs
    chi328InputQChi innerPair382Input
    leaf6908InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6908LowerChecked :
    lowerCheck 24 leaf6908Box leaf6908Inputs = true := by
  rfl'

private theorem leaf6908CoversExact : CoversExact 8
    leaf6908Box leaf6908Certificate leaf6908InnerLog leaf6908Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk171RoundedFacts chi328RoundedFacts
    innerPair382RoundedFacts leaf6908RoundedFacts (by rfl)

private theorem leaf6908FlatSound : Sound leaf6908Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6908CertificateValid
    leaf6908InnerLogValid leaf6908CoversExact leaf6908LowerChecked

private noncomputable def leaf6909Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (69/128), chiHi := (35/64) }

private noncomputable def leaf6909Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435843/268435456) }, vSqrt := { lower := (8191/8192), upper := (5726278997/5725882368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (824572387/536870912) }, upper := { exponent := 1, mantissa := (1597/1024) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi328LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (11452161365/11451764736) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf6909InnerLog : WideLogData :=
  innerPair743Data

set_option maxRecDepth 1000000 in
private theorem leaf6909LocalValidity :
    LeafFacts leaf6909Box leaf6909Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6909Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5726278997/5725882368) }) = true
      norm_num [leaf6909Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6909CertificateValid :
    WideCertificateValid leaf6909Box leaf6909Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi328ValidityFacts
    leaf6909LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6909CoverageChecked :
    coverageCheck (innerAD leaf6909Box) leaf6909InnerLog = true := by
  rfl'

private theorem leaf6909InnerLogValid :
    leaf6909InnerLog.Valid 8 (innerAD leaf6909Box) :=
  wideLogDataValid_of_cachedCheck endpoint482PositiveFacts
    endpoint483PositiveFacts.valid leaf6909CoverageChecked

private noncomputable def leaf6909InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814831/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6909InputLogOnePlusV_eq :
    leaf6909InputLogOnePlusV = outerEnclosure 24
      (leaf6909Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6909RoundedFacts : LeafRoundedFacts 8
    leaf6909Certificate.logOnePlusV leaf6909InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6909InputLogOnePlusV_eq }

private noncomputable def leaf6909Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi328InputQChi innerPair743Input
    leaf6909InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6909LowerChecked :
    lowerCheck 24 leaf6909Box leaf6909Inputs = true := by
  rfl'

private theorem leaf6909CoversExact : CoversExact 8
    leaf6909Box leaf6909Certificate leaf6909InnerLog leaf6909Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi328RoundedFacts
    innerPair743RoundedFacts leaf6909RoundedFacts (by rfl)

private theorem leaf6909FlatSound : Sound leaf6909Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6909CertificateValid
    leaf6909InnerLogValid leaf6909CoversExact leaf6909LowerChecked

private noncomputable def leaf6910Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (35/64), chiHi := (71/128) }

private noncomputable def leaf6910Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435839/268435456) }, vSqrt := { lower := (8191/8192), upper := (17178836991/17177669888) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (818871107/536870912) }, upper := { exponent := 1, mantissa := (12687/8192) } }, logOuter := sk169LogOuterCertificate, logK := sk169LogKCertificate, logChi := chi333LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34356506879/34355339776) } }, logDArg := sk169LogDArgCertificate }

private noncomputable def leaf6910InnerLog : WideLogData :=
  innerPair382Data

set_option maxRecDepth 1000000 in
private theorem leaf6910LocalValidity :
    LeafFacts leaf6910Box leaf6910Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6910Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178836991/17177669888) }) = true
      norm_num [leaf6910Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6910CertificateValid :
    WideCertificateValid leaf6910Box leaf6910Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk169ValidityFacts chi333ValidityFacts
    leaf6910LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6910CoverageChecked :
    coverageCheck (innerAD leaf6910Box) leaf6910InnerLog = true := by
  rfl'

private theorem leaf6910InnerLogValid :
    leaf6910InnerLog.Valid 8 (innerAD leaf6910Box) :=
  wideLogDataValid_of_cachedCheck endpoint99PositiveFacts
    endpoint483PositiveFacts.valid leaf6910CoverageChecked

private noncomputable def leaf6910InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629651/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6910InputLogOnePlusV_eq :
    leaf6910InputLogOnePlusV = outerEnclosure 24
      (leaf6910Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6910RoundedFacts : LeafRoundedFacts 8
    leaf6910Certificate.logOnePlusV leaf6910InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6910InputLogOnePlusV_eq }

private noncomputable def leaf6910Inputs : Inputs :=
  inputsOfCaches globalInput sk169RoundedInputs
    chi333InputQChi innerPair382Input
    leaf6910InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6910LowerChecked :
    lowerCheck 24 leaf6910Box leaf6910Inputs = true := by
  rfl'

private theorem leaf6910CoversExact : CoversExact 8
    leaf6910Box leaf6910Certificate leaf6910InnerLog leaf6910Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk169RoundedFacts chi333RoundedFacts
    innerPair382RoundedFacts leaf6910RoundedFacts (by rfl)

private theorem leaf6910FlatSound : Sound leaf6910Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6910CertificateValid
    leaf6910InnerLogValid leaf6910CoversExact leaf6910LowerChecked

private noncomputable def leaf6911Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (35/64), chiHi := (71/128) }

private noncomputable def leaf6911Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435841/268435456) }, vSqrt := { lower := (8191/8192), upper := (5726278997/5725883904) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (823458345/536870912) }, upper := { exponent := 1, mantissa := (6379/4096) } }, logOuter := sk170LogOuterCertificate, logK := sk170LogKCertificate, logChi := chi333LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (11452162901/11451767808) } }, logDArg := sk170LogDArgCertificate }

private noncomputable def leaf6911InnerLog : WideLogData :=
  innerPair743Data

set_option maxRecDepth 1000000 in
private theorem leaf6911LocalValidity :
    LeafFacts leaf6911Box leaf6911Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6911Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5726278997/5725883904) }) = true
      norm_num [leaf6911Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6911CertificateValid :
    WideCertificateValid leaf6911Box leaf6911Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk170ValidityFacts chi333ValidityFacts
    leaf6911LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6911CoverageChecked :
    coverageCheck (innerAD leaf6911Box) leaf6911InnerLog = true := by
  rfl'

private theorem leaf6911InnerLogValid :
    leaf6911InnerLog.Valid 8 (innerAD leaf6911Box) :=
  wideLogDataValid_of_cachedCheck endpoint482PositiveFacts
    endpoint483PositiveFacts.valid leaf6911CoverageChecked

private noncomputable def leaf6911InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907415/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6911InputLogOnePlusV_eq :
    leaf6911InputLogOnePlusV = outerEnclosure 24
      (leaf6911Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6911RoundedFacts : LeafRoundedFacts 8
    leaf6911Certificate.logOnePlusV leaf6911InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6911InputLogOnePlusV_eq }

private noncomputable def leaf6911Inputs : Inputs :=
  inputsOfCaches globalInput sk170RoundedInputs
    chi333InputQChi innerPair743Input
    leaf6911InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6911LowerChecked :
    lowerCheck 24 leaf6911Box leaf6911Inputs = true := by
  rfl'

private theorem leaf6911CoversExact : CoversExact 8
    leaf6911Box leaf6911Certificate leaf6911InnerLog leaf6911Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk170RoundedFacts chi333RoundedFacts
    innerPair743RoundedFacts leaf6911RoundedFacts (by rfl)

private theorem leaf6911FlatSound : Sound leaf6911Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6911CertificateValid
    leaf6911InnerLogValid leaf6911CoversExact leaf6911LowerChecked

private noncomputable def leaf6912Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (71/128), chiHi := (9/16) }

private noncomputable def leaf6912Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435841/268435456) }, vSqrt := { lower := (8191/8192), upper := (17178836991/17177638912) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (826734945/536870912) }, upper := { exponent := 1, mantissa := (1601/1024) } }, logOuter := sk169LogOuterCertificate, logK := sk169LogKCertificate, logChi := chi334LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34356475903/34355277824) } }, logDArg := sk169LogDArgCertificate }

private noncomputable def leaf6912InnerLog : WideLogData :=
  innerPair744Data

set_option maxRecDepth 1000000 in
private theorem leaf6912LocalValidity :
    LeafFacts leaf6912Box leaf6912Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6912Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178836991/17177638912) }) = true
      norm_num [leaf6912Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6912CertificateValid :
    WideCertificateValid leaf6912Box leaf6912Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk169ValidityFacts chi334ValidityFacts
    leaf6912LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6912CoverageChecked :
    coverageCheck (innerAD leaf6912Box) leaf6912InnerLog = true := by
  rfl'

private theorem leaf6912InnerLogValid :
    leaf6912InnerLog.Valid 8 (innerAD leaf6912Box) :=
  wideLogDataValid_of_cachedCheck endpoint482PositiveFacts
    endpoint484PositiveFacts.valid leaf6912CoverageChecked

private noncomputable def leaf6912InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814833/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6912InputLogOnePlusV_eq :
    leaf6912InputLogOnePlusV = outerEnclosure 24
      (leaf6912Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6912RoundedFacts : LeafRoundedFacts 8
    leaf6912Certificate.logOnePlusV leaf6912InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6912InputLogOnePlusV_eq }

private noncomputable def leaf6912Inputs : Inputs :=
  inputsOfCaches globalInput sk169RoundedInputs
    chi334InputQChi innerPair744Input
    leaf6912InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6912LowerChecked :
    lowerCheck 24 leaf6912Box leaf6912Inputs = true := by
  rfl'

private theorem leaf6912CoversExact : CoversExact 8
    leaf6912Box leaf6912Certificate leaf6912InnerLog leaf6912Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk169RoundedFacts chi334RoundedFacts
    innerPair744RoundedFacts leaf6912RoundedFacts (by rfl)

private theorem leaf6912FlatSound : Sound leaf6912Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6912CertificateValid
    leaf6912InnerLogValid leaf6912CoversExact leaf6912LowerChecked

private noncomputable def leaf6913Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (71/128), chiHi := (9/16) }

private noncomputable def leaf6913Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435843/268435456) }, vSqrt := { lower := (8191/8192), upper := (17178836991/17177620480) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (831387715/536870912) }, upper := { exponent := 1, mantissa := (805/512) } }, logOuter := sk170LogOuterCertificate, logK := sk170LogKCertificate, logChi := chi334LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34356457471/34355240960) } }, logDArg := sk170LogDArgCertificate }

private noncomputable def leaf6913InnerLog : WideLogData :=
  innerPair744Data

set_option maxRecDepth 1000000 in
private theorem leaf6913LocalValidity :
    LeafFacts leaf6913Box leaf6913Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6913Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178836991/17177620480) }) = true
      norm_num [leaf6913Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6913CertificateValid :
    WideCertificateValid leaf6913Box leaf6913Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk170ValidityFacts chi334ValidityFacts
    leaf6913LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6913CoverageChecked :
    coverageCheck (innerAD leaf6913Box) leaf6913InnerLog = true := by
  rfl'

private theorem leaf6913InnerLogValid :
    leaf6913InnerLog.Valid 8 (innerAD leaf6913Box) :=
  wideLogDataValid_of_cachedCheck endpoint482PositiveFacts
    endpoint484PositiveFacts.valid leaf6913CoverageChecked

private noncomputable def leaf6913InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629675/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6913InputLogOnePlusV_eq :
    leaf6913InputLogOnePlusV = outerEnclosure 24
      (leaf6913Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6913RoundedFacts : LeafRoundedFacts 8
    leaf6913Certificate.logOnePlusV leaf6913InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6913InputLogOnePlusV_eq }

private noncomputable def leaf6913Inputs : Inputs :=
  inputsOfCaches globalInput sk170RoundedInputs
    chi334InputQChi innerPair744Input
    leaf6913InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6913LowerChecked :
    lowerCheck 24 leaf6913Box leaf6913Inputs = true := by
  rfl'

private theorem leaf6913CoversExact : CoversExact 8
    leaf6913Box leaf6913Certificate leaf6913InnerLog leaf6913Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk170RoundedFacts chi334RoundedFacts
    innerPair744RoundedFacts leaf6913RoundedFacts (by rfl)

private theorem leaf6913FlatSound : Sound leaf6913Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6913CertificateValid
    leaf6913InnerLogValid leaf6913CoversExact leaf6913LowerChecked

private noncomputable def leaf6914Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (35/64), chiHi := (71/128) }

private noncomputable def leaf6914Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435843/268435456) }, vSqrt := { lower := (8191/8192), upper := (17178836991/17177633536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (828045583/536870912) }, upper := { exponent := 1, mantissa := (12829/8192) } }, logOuter := sk171LogOuterCertificate, logK := sk171LogKCertificate, logChi := chi333LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34356470527/34355267072) } }, logDArg := sk171LogDArgCertificate }

private noncomputable def leaf6914InnerLog : WideLogData :=
  innerPair744Data

set_option maxRecDepth 1000000 in
private theorem leaf6914LocalValidity :
    LeafFacts leaf6914Box leaf6914Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6914Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178836991/17177633536) }) = true
      norm_num [leaf6914Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6914CertificateValid :
    WideCertificateValid leaf6914Box leaf6914Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk171ValidityFacts chi333ValidityFacts
    leaf6914LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6914CoverageChecked :
    coverageCheck (innerAD leaf6914Box) leaf6914InnerLog = true := by
  rfl'

private theorem leaf6914InnerLogValid :
    leaf6914InnerLog.Valid 8 (innerAD leaf6914Box) :=
  wideLogDataValid_of_cachedCheck endpoint482PositiveFacts
    endpoint484PositiveFacts.valid leaf6914CoverageChecked

private noncomputable def leaf6914InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907417/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6914InputLogOnePlusV_eq :
    leaf6914InputLogOnePlusV = outerEnclosure 24
      (leaf6914Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6914RoundedFacts : LeafRoundedFacts 8
    leaf6914Certificate.logOnePlusV leaf6914InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6914InputLogOnePlusV_eq }

private noncomputable def leaf6914Inputs : Inputs :=
  inputsOfCaches globalInput sk171RoundedInputs
    chi333InputQChi innerPair744Input
    leaf6914InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6914LowerChecked :
    lowerCheck 24 leaf6914Box leaf6914Inputs = true := by
  rfl'

private theorem leaf6914CoversExact : CoversExact 8
    leaf6914Box leaf6914Certificate leaf6914InnerLog leaf6914Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk171RoundedFacts chi333RoundedFacts
    innerPair744RoundedFacts leaf6914RoundedFacts (by rfl)

private theorem leaf6914FlatSound : Sound leaf6914Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6914CertificateValid
    leaf6914InnerLogValid leaf6914CoversExact leaf6914LowerChecked

private noncomputable def leaf6915Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (35/64), chiHi := (71/128) }

private noncomputable def leaf6915Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435845/268435456) }, vSqrt := { lower := (8191/8192), upper := (17178836991/17177615360) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (832632821/536870912) }, upper := { exponent := 1, mantissa := (3225/2048) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi333LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34356452351/34355230720) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf6915InnerLog : WideLogData :=
  innerPair744Data

set_option maxRecDepth 1000000 in
private theorem leaf6915LocalValidity :
    LeafFacts leaf6915Box leaf6915Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6915Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178836991/17177615360) }) = true
      norm_num [leaf6915Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6915CertificateValid :
    WideCertificateValid leaf6915Box leaf6915Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi333ValidityFacts
    leaf6915LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6915CoverageChecked :
    coverageCheck (innerAD leaf6915Box) leaf6915InnerLog = true := by
  rfl'

private theorem leaf6915InnerLogValid :
    leaf6915InnerLog.Valid 8 (innerAD leaf6915Box) :=
  wideLogDataValid_of_cachedCheck endpoint482PositiveFacts
    endpoint484PositiveFacts.valid leaf6915CoverageChecked

private noncomputable def leaf6915InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629677/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6915InputLogOnePlusV_eq :
    leaf6915InputLogOnePlusV = outerEnclosure 24
      (leaf6915Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6915RoundedFacts : LeafRoundedFacts 8
    leaf6915Certificate.logOnePlusV leaf6915InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6915InputLogOnePlusV_eq }

private noncomputable def leaf6915Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi333InputQChi innerPair744Input
    leaf6915InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6915LowerChecked :
    lowerCheck 24 leaf6915Box leaf6915Inputs = true := by
  rfl'

private theorem leaf6915CoversExact : CoversExact 8
    leaf6915Box leaf6915Certificate leaf6915InnerLog leaf6915Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi333RoundedFacts
    innerPair744RoundedFacts leaf6915RoundedFacts (by rfl)

private theorem leaf6915FlatSound : Sound leaf6915Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6915CertificateValid
    leaf6915InnerLogValid leaf6915CoversExact leaf6915LowerChecked

private noncomputable def leaf6916Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (71/128), chiHi := (9/16) }

private noncomputable def leaf6916Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435845/268435456) }, vSqrt := { lower := (8191/8192), upper := (17178836991/17177602048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (836040485/536870912) }, upper := { exponent := 1, mantissa := (1619/1024) } }, logOuter := sk171LogOuterCertificate, logK := sk171LogKCertificate, logChi := chi334LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34356439039/34355204096) } }, logDArg := sk171LogDArgCertificate }

private noncomputable def leaf6916InnerLog : WideLogData :=
  innerPair744Data

set_option maxRecDepth 1000000 in
private theorem leaf6916LocalValidity :
    LeafFacts leaf6916Box leaf6916Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6916Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178836991/17177602048) }) = true
      norm_num [leaf6916Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6916CertificateValid :
    WideCertificateValid leaf6916Box leaf6916Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk171ValidityFacts chi334ValidityFacts
    leaf6916LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6916CoverageChecked :
    coverageCheck (innerAD leaf6916Box) leaf6916InnerLog = true := by
  rfl'

private theorem leaf6916InnerLogValid :
    leaf6916InnerLog.Valid 8 (innerAD leaf6916Box) :=
  wideLogDataValid_of_cachedCheck endpoint482PositiveFacts
    endpoint484PositiveFacts.valid leaf6916CoverageChecked

private noncomputable def leaf6916InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907421/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6916InputLogOnePlusV_eq :
    leaf6916InputLogOnePlusV = outerEnclosure 24
      (leaf6916Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6916RoundedFacts : LeafRoundedFacts 8
    leaf6916Certificate.logOnePlusV leaf6916InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6916InputLogOnePlusV_eq }

private noncomputable def leaf6916Inputs : Inputs :=
  inputsOfCaches globalInput sk171RoundedInputs
    chi334InputQChi innerPair744Input
    leaf6916InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6916LowerChecked :
    lowerCheck 24 leaf6916Box leaf6916Inputs = true := by
  rfl'

private theorem leaf6916CoversExact : CoversExact 8
    leaf6916Box leaf6916Certificate leaf6916InnerLog leaf6916Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk171RoundedFacts chi334RoundedFacts
    innerPair744RoundedFacts leaf6916RoundedFacts (by rfl)

private theorem leaf6916FlatSound : Sound leaf6916Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6916CertificateValid
    leaf6916InnerLogValid leaf6916CoversExact leaf6916LowerChecked

private noncomputable def leaf6917Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (71/128), chiHi := (9/16) }

private noncomputable def leaf6917Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435847/268435456) }, vSqrt := { lower := (8191/8192), upper := (17178836991/17177583616) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (840693255/536870912) }, upper := { exponent := 1, mantissa := (407/256) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi334LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34356420607/34355167232) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf6917InnerLog : WideLogData :=
  innerPair748Data

set_option maxRecDepth 1000000 in
private theorem leaf6917LocalValidity :
    LeafFacts leaf6917Box leaf6917Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6917Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178836991/17177583616) }) = true
      norm_num [leaf6917Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6917CertificateValid :
    WideCertificateValid leaf6917Box leaf6917Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi334ValidityFacts
    leaf6917LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6917CoverageChecked :
    coverageCheck (innerAD leaf6917Box) leaf6917InnerLog = true := by
  rfl'

private theorem leaf6917InnerLogValid :
    leaf6917InnerLog.Valid 8 (innerAD leaf6917Box) :=
  wideLogDataValid_of_cachedCheck endpoint483PositiveFacts
    endpoint484PositiveFacts.valid leaf6917CoverageChecked

private noncomputable def leaf6917InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629693/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6917InputLogOnePlusV_eq :
    leaf6917InputLogOnePlusV = outerEnclosure 24
      (leaf6917Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6917RoundedFacts : LeafRoundedFacts 8
    leaf6917Certificate.logOnePlusV leaf6917InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6917InputLogOnePlusV_eq }

private noncomputable def leaf6917Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi334InputQChi innerPair748Input
    leaf6917InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6917LowerChecked :
    lowerCheck 24 leaf6917Box leaf6917Inputs = true := by
  rfl'

private theorem leaf6917CoversExact : CoversExact 8
    leaf6917Box leaf6917Certificate leaf6917InnerLog leaf6917Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi334RoundedFacts
    innerPair748RoundedFacts leaf6917RoundedFacts (by rfl)

private theorem leaf6917FlatSound : Sound leaf6917Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6917CertificateValid
    leaf6917InnerLogValid leaf6917CoversExact leaf6917LowerChecked

private noncomputable def leaf6918Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (17/32), chiHi := (69/128) }

private noncomputable def leaf6918Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435843/268435456) }, vSqrt := { lower := (8191/8192), upper := (17178836991/17177661184) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (820968127/536870912) }, upper := { exponent := 1, mantissa := (12721/8192) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi327LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34356498175/34355322368) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf6918InnerLog : WideLogData :=
  innerPair382Data

set_option maxRecDepth 1000000 in
private theorem leaf6918LocalValidity :
    LeafFacts leaf6918Box leaf6918Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6918Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178836991/17177661184) }) = true
      norm_num [leaf6918Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6918CertificateValid :
    WideCertificateValid leaf6918Box leaf6918Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi327ValidityFacts
    leaf6918LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6918CoverageChecked :
    coverageCheck (innerAD leaf6918Box) leaf6918InnerLog = true := by
  rfl'

private theorem leaf6918InnerLogValid :
    leaf6918InnerLog.Valid 8 (innerAD leaf6918Box) :=
  wideLogDataValid_of_cachedCheck endpoint99PositiveFacts
    endpoint483PositiveFacts.valid leaf6918CoverageChecked

private noncomputable def leaf6918InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629655/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6918InputLogOnePlusV_eq :
    leaf6918InputLogOnePlusV = outerEnclosure 24
      (leaf6918Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6918RoundedFacts : LeafRoundedFacts 8
    leaf6918Certificate.logOnePlusV leaf6918InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6918InputLogOnePlusV_eq }

private noncomputable def leaf6918Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi327InputQChi innerPair382Input
    leaf6918InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6918LowerChecked :
    lowerCheck 24 leaf6918Box leaf6918Inputs = true := by
  rfl'

private theorem leaf6918CoversExact : CoversExact 8
    leaf6918Box leaf6918Certificate leaf6918InnerLog leaf6918Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi327RoundedFacts
    innerPair382RoundedFacts leaf6918RoundedFacts (by rfl)

private theorem leaf6918FlatSound : Sound leaf6918Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6918CertificateValid
    leaf6918InnerLogValid leaf6918CoversExact leaf6918LowerChecked

private noncomputable def leaf6919Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (17/32), chiHi := (69/128) }

private noncomputable def leaf6919Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435845/268435456) }, vSqrt := { lower := (8191/8192), upper := (17178836991/17177643520) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (825424301/536870912) }, upper := { exponent := 1, mantissa := (6395/4096) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi327LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34356480511/34355287040) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf6919InnerLog : WideLogData :=
  innerPair743Data

set_option maxRecDepth 1000000 in
private theorem leaf6919LocalValidity :
    LeafFacts leaf6919Box leaf6919Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6919Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178836991/17177643520) }) = true
      norm_num [leaf6919Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6919CertificateValid :
    WideCertificateValid leaf6919Box leaf6919Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi327ValidityFacts
    leaf6919LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6919CoverageChecked :
    coverageCheck (innerAD leaf6919Box) leaf6919InnerLog = true := by
  rfl'

private theorem leaf6919InnerLogValid :
    leaf6919InnerLog.Valid 8 (innerAD leaf6919Box) :=
  wideLogDataValid_of_cachedCheck endpoint482PositiveFacts
    endpoint483PositiveFacts.valid leaf6919CoverageChecked

private noncomputable def leaf6919InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (363427/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf6919InputLogOnePlusV_eq :
    leaf6919InputLogOnePlusV = outerEnclosure 24
      (leaf6919Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6919RoundedFacts : LeafRoundedFacts 8
    leaf6919Certificate.logOnePlusV leaf6919InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6919InputLogOnePlusV_eq }

private noncomputable def leaf6919Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi327InputQChi innerPair743Input
    leaf6919InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6919LowerChecked :
    lowerCheck 24 leaf6919Box leaf6919Inputs = true := by
  rfl'

private theorem leaf6919CoversExact : CoversExact 8
    leaf6919Box leaf6919Certificate leaf6919InnerLog leaf6919Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi327RoundedFacts
    innerPair743RoundedFacts leaf6919RoundedFacts (by rfl)

private theorem leaf6919FlatSound : Sound leaf6919Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6919CertificateValid
    leaf6919InnerLogValid leaf6919CoversExact leaf6919LowerChecked

private noncomputable def leaf6920Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (69/128), chiHi := (35/64) }

private noncomputable def leaf6920Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435845/268435456) }, vSqrt := { lower := (8191/8192), upper := (17178836991/17177629184) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (829094093/536870912) }, upper := { exponent := 1, mantissa := (6423/4096) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi328LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34356466175/34355258368) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf6920InnerLog : WideLogData :=
  innerPair744Data

set_option maxRecDepth 1000000 in
private theorem leaf6920LocalValidity :
    LeafFacts leaf6920Box leaf6920Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6920Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178836991/17177629184) }) = true
      norm_num [leaf6920Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6920CertificateValid :
    WideCertificateValid leaf6920Box leaf6920Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi328ValidityFacts
    leaf6920LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6920CoverageChecked :
    coverageCheck (innerAD leaf6920Box) leaf6920InnerLog = true := by
  rfl'

private theorem leaf6920InnerLogValid :
    leaf6920InnerLog.Valid 8 (innerAD leaf6920Box) :=
  wideLogDataValid_of_cachedCheck endpoint482PositiveFacts
    endpoint484PositiveFacts.valid leaf6920CoverageChecked

private noncomputable def leaf6920InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629671/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6920InputLogOnePlusV_eq :
    leaf6920InputLogOnePlusV = outerEnclosure 24
      (leaf6920Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6920RoundedFacts : LeafRoundedFacts 8
    leaf6920Certificate.logOnePlusV leaf6920InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6920InputLogOnePlusV_eq }

private noncomputable def leaf6920Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi328InputQChi innerPair744Input
    leaf6920InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6920LowerChecked :
    lowerCheck 24 leaf6920Box leaf6920Inputs = true := by
  rfl'

private theorem leaf6920CoversExact : CoversExact 8
    leaf6920Box leaf6920Certificate leaf6920InnerLog leaf6920Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi328RoundedFacts
    innerPair744RoundedFacts leaf6920RoundedFacts (by rfl)

private theorem leaf6920FlatSound : Sound leaf6920Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6920CertificateValid
    leaf6920InnerLogValid leaf6920CoversExact leaf6920LowerChecked

private noncomputable def leaf6921Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (69/128), chiHi := (35/64) }

private noncomputable def leaf6921Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435847/268435456) }, vSqrt := { lower := (8191/8192), upper := (17178836991/17177611264) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (833615799/536870912) }, upper := { exponent := 1, mantissa := (3229/2048) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi328LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34356448255/34355222528) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf6921InnerLog : WideLogData :=
  innerPair744Data

set_option maxRecDepth 1000000 in
private theorem leaf6921LocalValidity :
    LeafFacts leaf6921Box leaf6921Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6921Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178836991/17177611264) }) = true
      norm_num [leaf6921Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6921CertificateValid :
    WideCertificateValid leaf6921Box leaf6921Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi328ValidityFacts
    leaf6921LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6921CoverageChecked :
    coverageCheck (innerAD leaf6921Box) leaf6921InnerLog = true := by
  rfl'

private theorem leaf6921InnerLogValid :
    leaf6921InnerLog.Valid 8 (innerAD leaf6921Box) :=
  wideLogDataValid_of_cachedCheck endpoint482PositiveFacts
    endpoint484PositiveFacts.valid leaf6921CoverageChecked

private noncomputable def leaf6921InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629679/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6921InputLogOnePlusV_eq :
    leaf6921InputLogOnePlusV = outerEnclosure 24
      (leaf6921Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6921RoundedFacts : LeafRoundedFacts 8
    leaf6921Certificate.logOnePlusV leaf6921InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6921InputLogOnePlusV_eq }

private noncomputable def leaf6921Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi328InputQChi innerPair744Input
    leaf6921InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6921LowerChecked :
    lowerCheck 24 leaf6921Box leaf6921Inputs = true := by
  rfl'

private theorem leaf6921CoversExact : CoversExact 8
    leaf6921Box leaf6921Certificate leaf6921InnerLog leaf6921Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi328RoundedFacts
    innerPair744RoundedFacts leaf6921RoundedFacts (by rfl)

private theorem leaf6921FlatSound : Sound leaf6921Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6921CertificateValid
    leaf6921InnerLogValid leaf6921CoversExact leaf6921LowerChecked

private noncomputable def leaf6922Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (17/32), chiHi := (69/128) }

private noncomputable def leaf6922Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435847/268435456) }, vSqrt := { lower := (8191/8192), upper := (17178836991/17177625856) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (829880475/536870912) }, upper := { exponent := 1, mantissa := (12859/8192) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi327LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34356462847/34355251712) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf6922InnerLog : WideLogData :=
  innerPair744Data

set_option maxRecDepth 1000000 in
private theorem leaf6922LocalValidity :
    LeafFacts leaf6922Box leaf6922Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6922Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178836991/17177625856) }) = true
      norm_num [leaf6922Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6922CertificateValid :
    WideCertificateValid leaf6922Box leaf6922Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi327ValidityFacts
    leaf6922LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6922CoverageChecked :
    coverageCheck (innerAD leaf6922Box) leaf6922InnerLog = true := by
  rfl'

private theorem leaf6922InnerLogValid :
    leaf6922InnerLog.Valid 8 (innerAD leaf6922Box) :=
  wideLogDataValid_of_cachedCheck endpoint482PositiveFacts
    endpoint484PositiveFacts.valid leaf6922CoverageChecked

private noncomputable def leaf6922InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453709/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf6922InputLogOnePlusV_eq :
    leaf6922InputLogOnePlusV = outerEnclosure 24
      (leaf6922Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6922RoundedFacts : LeafRoundedFacts 8
    leaf6922Certificate.logOnePlusV leaf6922InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6922InputLogOnePlusV_eq }

private noncomputable def leaf6922Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi327InputQChi innerPair744Input
    leaf6922InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6922LowerChecked :
    lowerCheck 24 leaf6922Box leaf6922Inputs = true := by
  rfl'

private theorem leaf6922CoversExact : CoversExact 8
    leaf6922Box leaf6922Certificate leaf6922InnerLog leaf6922Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi327RoundedFacts
    innerPair744RoundedFacts leaf6922RoundedFacts (by rfl)

private theorem leaf6922FlatSound : Sound leaf6922Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6922CertificateValid
    leaf6922InnerLogValid leaf6922CoversExact leaf6922LowerChecked

private noncomputable def leaf6923Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (17/32), chiHi := (69/128) }

private noncomputable def leaf6923Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435849/268435456) }, vSqrt := { lower := (65527/65536), upper := (17178836991/17177608192) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (834336649/536870912) }, upper := { exponent := 1, mantissa := (101/64) } }, logOuter := sk176LogOuterCertificate, logK := sk176LogKCertificate, logChi := chi327LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (34356445183/34355216384) } }, logDArg := sk176LogDArgCertificate }

private noncomputable def leaf6923InnerLog : WideLogData :=
  innerPair744Data

set_option maxRecDepth 1000000 in
private theorem leaf6923LocalValidity :
    LeafFacts leaf6923Box leaf6923Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6923Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (17178836991/17177608192) }) = true
      norm_num [leaf6923Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6923CertificateValid :
    WideCertificateValid leaf6923Box leaf6923Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk176ValidityFacts chi327ValidityFacts
    leaf6923LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6923CoverageChecked :
    coverageCheck (innerAD leaf6923Box) leaf6923InnerLog = true := by
  rfl'

private theorem leaf6923InnerLogValid :
    leaf6923InnerLog.Valid 8 (innerAD leaf6923Box) :=
  wideLogDataValid_of_cachedCheck endpoint482PositiveFacts
    endpoint484PositiveFacts.valid leaf6923CoverageChecked

private noncomputable def leaf6923InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629681/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6923InputLogOnePlusV_eq :
    leaf6923InputLogOnePlusV = outerEnclosure 24
      (leaf6923Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6923RoundedFacts : LeafRoundedFacts 8
    leaf6923Certificate.logOnePlusV leaf6923InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6923InputLogOnePlusV_eq }

private noncomputable def leaf6923Inputs : Inputs :=
  inputsOfCaches globalInput sk176RoundedInputs
    chi327InputQChi innerPair744Input
    leaf6923InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6923LowerChecked :
    lowerCheck 24 leaf6923Box leaf6923Inputs = true := by
  rfl'

private theorem leaf6923CoversExact : CoversExact 8
    leaf6923Box leaf6923Certificate leaf6923InnerLog leaf6923Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk176RoundedFacts chi327RoundedFacts
    innerPair744RoundedFacts leaf6923RoundedFacts (by rfl)

private theorem leaf6923FlatSound : Sound leaf6923Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6923CertificateValid
    leaf6923InnerLogValid leaf6923CoversExact leaf6923LowerChecked

private noncomputable def leaf6924Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (69/128), chiHi := (35/64) }

private noncomputable def leaf6924Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435849/268435456) }, vSqrt := { lower := (8191/8192), upper := (5726278997/5725864448) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (838137505/536870912) }, upper := { exponent := 1, mantissa := (6493/4096) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi328LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (11452143445/11451728896) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf6924InnerLog : WideLogData :=
  innerPair744Data

set_option maxRecDepth 1000000 in
private theorem leaf6924LocalValidity :
    LeafFacts leaf6924Box leaf6924Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6924Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5726278997/5725864448) }) = true
      norm_num [leaf6924Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6924CertificateValid :
    WideCertificateValid leaf6924Box leaf6924Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi328ValidityFacts
    leaf6924LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6924CoverageChecked :
    coverageCheck (innerAD leaf6924Box) leaf6924InnerLog = true := by
  rfl'

private theorem leaf6924InnerLogValid :
    leaf6924InnerLog.Valid 8 (innerAD leaf6924Box) :=
  wideLogDataValid_of_cachedCheck endpoint482PositiveFacts
    endpoint484PositiveFacts.valid leaf6924CoverageChecked

private noncomputable def leaf6924InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453711/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf6924InputLogOnePlusV_eq :
    leaf6924InputLogOnePlusV = outerEnclosure 24
      (leaf6924Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6924RoundedFacts : LeafRoundedFacts 8
    leaf6924Certificate.logOnePlusV leaf6924InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6924InputLogOnePlusV_eq }

private noncomputable def leaf6924Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi328InputQChi innerPair744Input
    leaf6924InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6924LowerChecked :
    lowerCheck 24 leaf6924Box leaf6924Inputs = true := by
  rfl'

private theorem leaf6924CoversExact : CoversExact 8
    leaf6924Box leaf6924Certificate leaf6924InnerLog leaf6924Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi328RoundedFacts
    innerPair744RoundedFacts leaf6924RoundedFacts (by rfl)

private theorem leaf6924FlatSound : Sound leaf6924Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6924CertificateValid
    leaf6924InnerLogValid leaf6924CoversExact leaf6924LowerChecked

private noncomputable def leaf6925Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (69/128), chiHi := (35/64) }

private noncomputable def leaf6925Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435851/268435456) }, vSqrt := { lower := (65527/65536), upper := (17178836991/17177575424) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (842659211/536870912) }, upper := { exponent := 1, mantissa := (51/32) } }, logOuter := sk176LogOuterCertificate, logK := sk176LogKCertificate, logChi := chi328LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (34356412415/34355150848) } }, logDArg := sk176LogDArgCertificate }

private noncomputable def leaf6925InnerLog : WideLogData :=
  innerPair748Data

set_option maxRecDepth 1000000 in
private theorem leaf6925LocalValidity :
    LeafFacts leaf6925Box leaf6925Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6925Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (17178836991/17177575424) }) = true
      norm_num [leaf6925Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6925CertificateValid :
    WideCertificateValid leaf6925Box leaf6925Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk176ValidityFacts chi328ValidityFacts
    leaf6925LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6925CoverageChecked :
    coverageCheck (innerAD leaf6925Box) leaf6925InnerLog = true := by
  rfl'

private theorem leaf6925InnerLogValid :
    leaf6925InnerLog.Valid 8 (innerAD leaf6925Box) :=
  wideLogDataValid_of_cachedCheck endpoint483PositiveFacts
    endpoint484PositiveFacts.valid leaf6925CoverageChecked

private noncomputable def leaf6925InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629697/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6925InputLogOnePlusV_eq :
    leaf6925InputLogOnePlusV = outerEnclosure 24
      (leaf6925Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6925RoundedFacts : LeafRoundedFacts 8
    leaf6925Certificate.logOnePlusV leaf6925InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6925InputLogOnePlusV_eq }

private noncomputable def leaf6925Inputs : Inputs :=
  inputsOfCaches globalInput sk176RoundedInputs
    chi328InputQChi innerPair748Input
    leaf6925InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6925LowerChecked :
    lowerCheck 24 leaf6925Box leaf6925Inputs = true := by
  rfl'

private theorem leaf6925CoversExact : CoversExact 8
    leaf6925Box leaf6925Certificate leaf6925InnerLog leaf6925Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk176RoundedFacts chi328RoundedFacts
    innerPair748RoundedFacts leaf6925RoundedFacts (by rfl)

private theorem leaf6925FlatSound : Sound leaf6925Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6925CertificateValid
    leaf6925InnerLogValid leaf6925CoversExact leaf6925LowerChecked

private noncomputable def leaf6926Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (35/64), chiHi := (71/128) }

private noncomputable def leaf6926Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435847/268435456) }, vSqrt := { lower := (8191/8192), upper := (5726278997/5725865728) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (837220059/536870912) }, upper := { exponent := 1, mantissa := (12971/8192) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi333LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (11452144725/11451731456) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf6926InnerLog : WideLogData :=
  innerPair744Data

set_option maxRecDepth 1000000 in
private theorem leaf6926LocalValidity :
    LeafFacts leaf6926Box leaf6926Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6926Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5726278997/5725865728) }) = true
      norm_num [leaf6926Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6926CertificateValid :
    WideCertificateValid leaf6926Box leaf6926Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi333ValidityFacts
    leaf6926LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6926CoverageChecked :
    coverageCheck (innerAD leaf6926Box) leaf6926InnerLog = true := by
  rfl'

private theorem leaf6926InnerLogValid :
    leaf6926InnerLog.Valid 8 (innerAD leaf6926Box) :=
  wideLogDataValid_of_cachedCheck endpoint482PositiveFacts
    endpoint484PositiveFacts.valid leaf6926CoverageChecked

private noncomputable def leaf6926InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814843/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6926InputLogOnePlusV_eq :
    leaf6926InputLogOnePlusV = outerEnclosure 24
      (leaf6926Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6926RoundedFacts : LeafRoundedFacts 8
    leaf6926Certificate.logOnePlusV leaf6926InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6926InputLogOnePlusV_eq }

private noncomputable def leaf6926Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi333InputQChi innerPair744Input
    leaf6926InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6926LowerChecked :
    lowerCheck 24 leaf6926Box leaf6926Inputs = true := by
  rfl'

private theorem leaf6926CoversExact : CoversExact 8
    leaf6926Box leaf6926Certificate leaf6926InnerLog leaf6926Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi333RoundedFacts
    innerPair744RoundedFacts leaf6926RoundedFacts (by rfl)

private theorem leaf6926FlatSound : Sound leaf6926Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6926CertificateValid
    leaf6926InnerLogValid leaf6926CoversExact leaf6926LowerChecked

private noncomputable def leaf6927Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (35/64), chiHi := (71/128) }

private noncomputable def leaf6927Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435849/268435456) }, vSqrt := { lower := (8191/8192), upper := (1010519823/1010445824) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (841807297/536870912) }, upper := { exponent := 1, mantissa := (6521/4096) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi333LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (2020965647/2020891648) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf6927InnerLog : WideLogData :=
  innerPair748Data

set_option maxRecDepth 1000000 in
private theorem leaf6927LocalValidity :
    LeafFacts leaf6927Box leaf6927Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6927Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (1010519823/1010445824) }) = true
      norm_num [leaf6927Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6927CertificateValid :
    WideCertificateValid leaf6927Box leaf6927Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi333ValidityFacts
    leaf6927LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6927CoverageChecked :
    coverageCheck (innerAD leaf6927Box) leaf6927InnerLog = true := by
  rfl'

private theorem leaf6927InnerLogValid :
    leaf6927InnerLog.Valid 8 (innerAD leaf6927Box) :=
  wideLogDataValid_of_cachedCheck endpoint483PositiveFacts
    endpoint484PositiveFacts.valid leaf6927CoverageChecked

private noncomputable def leaf6927InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629695/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6927InputLogOnePlusV_eq :
    leaf6927InputLogOnePlusV = outerEnclosure 24
      (leaf6927Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6927RoundedFacts : LeafRoundedFacts 8
    leaf6927Certificate.logOnePlusV leaf6927InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6927InputLogOnePlusV_eq }

private noncomputable def leaf6927Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi333InputQChi innerPair748Input
    leaf6927InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6927LowerChecked :
    lowerCheck 24 leaf6927Box leaf6927Inputs = true := by
  rfl'

private theorem leaf6927CoversExact : CoversExact 8
    leaf6927Box leaf6927Certificate leaf6927InnerLog leaf6927Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi333RoundedFacts
    innerPair748RoundedFacts leaf6927RoundedFacts (by rfl)

private theorem leaf6927FlatSound : Sound leaf6927Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6927CertificateValid
    leaf6927InnerLogValid leaf6927CoversExact leaf6927LowerChecked

private noncomputable def leaf6928Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (71/128), chiHi := (9/16) }

private noncomputable def leaf6928Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435849/268435456) }, vSqrt := { lower := (8191/8192), upper := (17178836991/17177565184) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (845346025/536870912) }, upper := { exponent := 1, mantissa := (1637/1024) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi334LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34356402175/34355130368) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf6928InnerLog : WideLogData :=
  innerPair749Data

set_option maxRecDepth 1000000 in
private theorem leaf6928LocalValidity :
    LeafFacts leaf6928Box leaf6928Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6928Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178836991/17177565184) }) = true
      norm_num [leaf6928Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6928CertificateValid :
    WideCertificateValid leaf6928Box leaf6928Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi334ValidityFacts
    leaf6928LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6928CoverageChecked :
    coverageCheck (innerAD leaf6928Box) leaf6928InnerLog = true := by
  rfl'

private theorem leaf6928InnerLogValid :
    leaf6928InnerLog.Valid 8 (innerAD leaf6928Box) :=
  wideLogDataValid_of_cachedCheck endpoint483PositiveFacts
    endpoint485PositiveFacts.valid leaf6928CoverageChecked

private noncomputable def leaf6928InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814851/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6928InputLogOnePlusV_eq :
    leaf6928InputLogOnePlusV = outerEnclosure 24
      (leaf6928Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6928RoundedFacts : LeafRoundedFacts 8
    leaf6928Certificate.logOnePlusV leaf6928InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6928InputLogOnePlusV_eq }

private noncomputable def leaf6928Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi334InputQChi innerPair749Input
    leaf6928InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6928LowerChecked :
    lowerCheck 24 leaf6928Box leaf6928Inputs = true := by
  rfl'

private theorem leaf6928CoversExact : CoversExact 8
    leaf6928Box leaf6928Certificate leaf6928InnerLog leaf6928Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi334RoundedFacts
    innerPair749RoundedFacts leaf6928RoundedFacts (by rfl)

private theorem leaf6928FlatSound : Sound leaf6928Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6928CertificateValid
    leaf6928InnerLogValid leaf6928CoversExact leaf6928LowerChecked

private noncomputable def leaf6929Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (71/128), chiHi := (9/16) }

private noncomputable def leaf6929Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435851/268435456) }, vSqrt := { lower := (8191/8192), upper := (17178836991/17177546752) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (849998795/536870912) }, upper := { exponent := 1, mantissa := (823/512) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi334LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34356383743/34355093504) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf6929InnerLog : WideLogData :=
  innerPair749Data

set_option maxRecDepth 1000000 in
private theorem leaf6929LocalValidity :
    LeafFacts leaf6929Box leaf6929Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6929Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178836991/17177546752) }) = true
      norm_num [leaf6929Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6929CertificateValid :
    WideCertificateValid leaf6929Box leaf6929Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi334ValidityFacts
    leaf6929LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6929CoverageChecked :
    coverageCheck (innerAD leaf6929Box) leaf6929InnerLog = true := by
  rfl'

private theorem leaf6929InnerLogValid :
    leaf6929InnerLog.Valid 8 (innerAD leaf6929Box) :=
  wideLogDataValid_of_cachedCheck endpoint483PositiveFacts
    endpoint485PositiveFacts.valid leaf6929CoverageChecked

private noncomputable def leaf6929InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629711/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6929InputLogOnePlusV_eq :
    leaf6929InputLogOnePlusV = outerEnclosure 24
      (leaf6929Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6929RoundedFacts : LeafRoundedFacts 8
    leaf6929Certificate.logOnePlusV leaf6929InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6929InputLogOnePlusV_eq }

private noncomputable def leaf6929Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi334InputQChi innerPair749Input
    leaf6929InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6929LowerChecked :
    lowerCheck 24 leaf6929Box leaf6929Inputs = true := by
  rfl'

private theorem leaf6929CoversExact : CoversExact 8
    leaf6929Box leaf6929Certificate leaf6929InnerLog leaf6929Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi334RoundedFacts
    innerPair749RoundedFacts leaf6929RoundedFacts (by rfl)

private theorem leaf6929FlatSound : Sound leaf6929Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6929CertificateValid
    leaf6929InnerLogValid leaf6929CoversExact leaf6929LowerChecked

private noncomputable def leaf6930Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (35/64), chiHi := (71/128) }

private noncomputable def leaf6930Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435851/268435456) }, vSqrt := { lower := (8191/8192), upper := (17178836991/17177560832) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (846394535/536870912) }, upper := { exponent := 1, mantissa := (13113/8192) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi333LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34356397823/34355121664) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf6930InnerLog : WideLogData :=
  innerPair749Data

set_option maxRecDepth 1000000 in
private theorem leaf6930LocalValidity :
    LeafFacts leaf6930Box leaf6930Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6930Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178836991/17177560832) }) = true
      norm_num [leaf6930Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6930CertificateValid :
    WideCertificateValid leaf6930Box leaf6930Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi333ValidityFacts
    leaf6930LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6930CoverageChecked :
    coverageCheck (innerAD leaf6930Box) leaf6930InnerLog = true := by
  rfl'

private theorem leaf6930InnerLogValid :
    leaf6930InnerLog.Valid 8 (innerAD leaf6930Box) :=
  wideLogDataValid_of_cachedCheck endpoint483PositiveFacts
    endpoint485PositiveFacts.valid leaf6930CoverageChecked

private noncomputable def leaf6930InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453713/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf6930InputLogOnePlusV_eq :
    leaf6930InputLogOnePlusV = outerEnclosure 24
      (leaf6930Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6930RoundedFacts : LeafRoundedFacts 8
    leaf6930Certificate.logOnePlusV leaf6930InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6930InputLogOnePlusV_eq }

private noncomputable def leaf6930Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi333InputQChi innerPair749Input
    leaf6930InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6930LowerChecked :
    lowerCheck 24 leaf6930Box leaf6930Inputs = true := by
  rfl'

private theorem leaf6930CoversExact : CoversExact 8
    leaf6930Box leaf6930Certificate leaf6930InnerLog leaf6930Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi333RoundedFacts
    innerPair749RoundedFacts leaf6930RoundedFacts (by rfl)

private theorem leaf6930FlatSound : Sound leaf6930Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6930CertificateValid
    leaf6930InnerLogValid leaf6930CoversExact leaf6930LowerChecked

private noncomputable def leaf6931Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (35/64), chiHi := (71/128) }

private noncomputable def leaf6931Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435853/268435456) }, vSqrt := { lower := (65527/65536), upper := (5726278997/5725847552) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (850981773/536870912) }, upper := { exponent := 1, mantissa := (103/64) } }, logOuter := sk176LogOuterCertificate, logK := sk176LogKCertificate, logChi := chi333LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (11452126549/11451695104) } }, logDArg := sk176LogDArgCertificate }

private noncomputable def leaf6931InnerLog : WideLogData :=
  innerPair749Data

set_option maxRecDepth 1000000 in
private theorem leaf6931LocalValidity :
    LeafFacts leaf6931Box leaf6931Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6931Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (5726278997/5725847552) }) = true
      norm_num [leaf6931Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6931CertificateValid :
    WideCertificateValid leaf6931Box leaf6931Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk176ValidityFacts chi333ValidityFacts
    leaf6931LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6931CoverageChecked :
    coverageCheck (innerAD leaf6931Box) leaf6931InnerLog = true := by
  rfl'

private theorem leaf6931InnerLogValid :
    leaf6931InnerLog.Valid 8 (innerAD leaf6931Box) :=
  wideLogDataValid_of_cachedCheck endpoint483PositiveFacts
    endpoint485PositiveFacts.valid leaf6931CoverageChecked

private noncomputable def leaf6931InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629713/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6931InputLogOnePlusV_eq :
    leaf6931InputLogOnePlusV = outerEnclosure 24
      (leaf6931Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6931RoundedFacts : LeafRoundedFacts 8
    leaf6931Certificate.logOnePlusV leaf6931InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6931InputLogOnePlusV_eq }

private noncomputable def leaf6931Inputs : Inputs :=
  inputsOfCaches globalInput sk176RoundedInputs
    chi333InputQChi innerPair749Input
    leaf6931InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6931LowerChecked :
    lowerCheck 24 leaf6931Box leaf6931Inputs = true := by
  rfl'

private theorem leaf6931CoversExact : CoversExact 8
    leaf6931Box leaf6931Certificate leaf6931InnerLog leaf6931Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk176RoundedFacts chi333RoundedFacts
    innerPair749RoundedFacts leaf6931RoundedFacts (by rfl)

private theorem leaf6931FlatSound : Sound leaf6931Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6931CertificateValid
    leaf6931InnerLogValid leaf6931CoversExact leaf6931LowerChecked

private noncomputable def leaf6932Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (71/128), chiHi := (9/16) }

private noncomputable def leaf6932Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435853/268435456) }, vSqrt := { lower := (8191/8192), upper := (17178836991/17177528320) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (854651565/536870912) }, upper := { exponent := 1, mantissa := (1655/1024) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi334LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34356365311/34355056640) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf6932InnerLog : WideLogData :=
  innerPair749Data

set_option maxRecDepth 1000000 in
private theorem leaf6932LocalValidity :
    LeafFacts leaf6932Box leaf6932Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6932Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178836991/17177528320) }) = true
      norm_num [leaf6932Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6932CertificateValid :
    WideCertificateValid leaf6932Box leaf6932Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi334ValidityFacts
    leaf6932LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6932CoverageChecked :
    coverageCheck (innerAD leaf6932Box) leaf6932InnerLog = true := by
  rfl'

private theorem leaf6932InnerLogValid :
    leaf6932InnerLog.Valid 8 (innerAD leaf6932Box) :=
  wideLogDataValid_of_cachedCheck endpoint483PositiveFacts
    endpoint485PositiveFacts.valid leaf6932CoverageChecked

private noncomputable def leaf6932InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453715/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf6932InputLogOnePlusV_eq :
    leaf6932InputLogOnePlusV = outerEnclosure 24
      (leaf6932Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6932RoundedFacts : LeafRoundedFacts 8
    leaf6932Certificate.logOnePlusV leaf6932InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6932InputLogOnePlusV_eq }

private noncomputable def leaf6932Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi334InputQChi innerPair749Input
    leaf6932InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6932LowerChecked :
    lowerCheck 24 leaf6932Box leaf6932Inputs = true := by
  rfl'

private theorem leaf6932CoversExact : CoversExact 8
    leaf6932Box leaf6932Certificate leaf6932InnerLog leaf6932Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi334RoundedFacts
    innerPair749RoundedFacts leaf6932RoundedFacts (by rfl)

private theorem leaf6932FlatSound : Sound leaf6932Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6932CertificateValid
    leaf6932InnerLogValid leaf6932CoversExact leaf6932LowerChecked

private noncomputable def leaf6933Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (71/128), chiHi := (9/16) }

private noncomputable def leaf6933Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435855/268435456) }, vSqrt := { lower := (65527/65536), upper := (17178836991/17177509888) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (859304335/536870912) }, upper := { exponent := 1, mantissa := (13/8) } }, logOuter := sk176LogOuterCertificate, logK := sk176LogKCertificate, logChi := chi334LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (34356346879/34355019776) } }, logDArg := sk176LogDArgCertificate }

private noncomputable def leaf6933InnerLog : WideLogData :=
  innerPair754Data

set_option maxRecDepth 1000000 in
private theorem leaf6933LocalValidity :
    LeafFacts leaf6933Box leaf6933Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6933Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (17178836991/17177509888) }) = true
      norm_num [leaf6933Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6933CertificateValid :
    WideCertificateValid leaf6933Box leaf6933Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk176ValidityFacts chi334ValidityFacts
    leaf6933LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6933CoverageChecked :
    coverageCheck (innerAD leaf6933Box) leaf6933InnerLog = true := by
  rfl'

private theorem leaf6933InnerLogValid :
    leaf6933InnerLog.Valid 8 (innerAD leaf6933Box) :=
  wideLogDataValid_of_cachedCheck endpoint484PositiveFacts
    endpoint485PositiveFacts.valid leaf6933CoverageChecked

private noncomputable def leaf6933InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629729/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6933InputLogOnePlusV_eq :
    leaf6933InputLogOnePlusV = outerEnclosure 24
      (leaf6933Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6933RoundedFacts : LeafRoundedFacts 8
    leaf6933Certificate.logOnePlusV leaf6933InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6933InputLogOnePlusV_eq }

private noncomputable def leaf6933Inputs : Inputs :=
  inputsOfCaches globalInput sk176RoundedInputs
    chi334InputQChi innerPair754Input
    leaf6933InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6933LowerChecked :
    lowerCheck 24 leaf6933Box leaf6933Inputs = true := by
  rfl'

private theorem leaf6933CoversExact : CoversExact 8
    leaf6933Box leaf6933Certificate leaf6933InnerLog leaf6933Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk176RoundedFacts chi334RoundedFacts
    innerPair754RoundedFacts leaf6933RoundedFacts (by rfl)

private theorem leaf6933FlatSound : Sound leaf6933Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6933CertificateValid
    leaf6933InnerLogValid leaf6933CoversExact leaf6933LowerChecked

private noncomputable def component140Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (1/2), chiHi := (65/128) }

set_option maxRecDepth 1000000 in
private theorem component140Node0_sound : Sound component140Node0Box :=
  sound_of_literal_split component140Node0Box leaf6870Box leaf6871Box
    .k (121/32) (by rfl) (by rfl)
    leaf6870FlatSound leaf6871FlatSound

private noncomputable def component140Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (65/128), chiHi := (33/64) }

set_option maxRecDepth 1000000 in
private theorem component140Node1_sound : Sound component140Node1Box :=
  sound_of_literal_split component140Node1Box leaf6872Box leaf6873Box
    .k (121/32) (by rfl) (by rfl)
    leaf6872FlatSound leaf6873FlatSound

private noncomputable def component140Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (1/2), chiHi := (33/64) }

set_option maxRecDepth 1000000 in
private theorem component140Node2_sound : Sound component140Node2Box :=
  sound_of_literal_split component140Node2Box component140Node0Box component140Node1Box
    .chi (65/128) (by rfl) (by rfl)
    component140Node0_sound component140Node1_sound

private noncomputable def component140Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (1/2), chiHi := (65/128) }

set_option maxRecDepth 1000000 in
private theorem component140Node3_sound : Sound component140Node3Box :=
  sound_of_literal_split component140Node3Box leaf6874Box leaf6875Box
    .k (123/32) (by rfl) (by rfl)
    leaf6874FlatSound leaf6875FlatSound

private noncomputable def component140Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (65/128), chiHi := (33/64) }

set_option maxRecDepth 1000000 in
private theorem component140Node4_sound : Sound component140Node4Box :=
  sound_of_literal_split component140Node4Box leaf6876Box leaf6877Box
    .k (123/32) (by rfl) (by rfl)
    leaf6876FlatSound leaf6877FlatSound

private noncomputable def component140Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (1/2), chiHi := (33/64) }

set_option maxRecDepth 1000000 in
private theorem component140Node5_sound : Sound component140Node5Box :=
  sound_of_literal_split component140Node5Box component140Node3Box component140Node4Box
    .chi (65/128) (by rfl) (by rfl)
    component140Node3_sound component140Node4_sound

private noncomputable def component140Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (1/2), chiHi := (33/64) }

set_option maxRecDepth 1000000 in
private theorem component140Node6_sound : Sound component140Node6Box :=
  sound_of_literal_split component140Node6Box component140Node2Box component140Node5Box
    .k (61/16) (by rfl) (by rfl)
    component140Node2_sound component140Node5_sound

private noncomputable def component140Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (33/64), chiHi := (67/128) }

set_option maxRecDepth 1000000 in
private theorem component140Node7_sound : Sound component140Node7Box :=
  sound_of_literal_split component140Node7Box leaf6878Box leaf6879Box
    .k (121/32) (by rfl) (by rfl)
    leaf6878FlatSound leaf6879FlatSound

private noncomputable def component140Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (67/128), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component140Node8_sound : Sound component140Node8Box :=
  sound_of_literal_split component140Node8Box leaf6880Box leaf6881Box
    .k (121/32) (by rfl) (by rfl)
    leaf6880FlatSound leaf6881FlatSound

private noncomputable def component140Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (33/64), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component140Node9_sound : Sound component140Node9Box :=
  sound_of_literal_split component140Node9Box component140Node7Box component140Node8Box
    .chi (67/128) (by rfl) (by rfl)
    component140Node7_sound component140Node8_sound

private noncomputable def component140Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (33/64), chiHi := (67/128) }

set_option maxRecDepth 1000000 in
private theorem component140Node10_sound : Sound component140Node10Box :=
  sound_of_literal_split component140Node10Box leaf6882Box leaf6883Box
    .k (123/32) (by rfl) (by rfl)
    leaf6882FlatSound leaf6883FlatSound

private noncomputable def component140Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (67/128), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component140Node11_sound : Sound component140Node11Box :=
  sound_of_literal_split component140Node11Box leaf6884Box leaf6885Box
    .k (123/32) (by rfl) (by rfl)
    leaf6884FlatSound leaf6885FlatSound

private noncomputable def component140Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (33/64), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component140Node12_sound : Sound component140Node12Box :=
  sound_of_literal_split component140Node12Box component140Node10Box component140Node11Box
    .chi (67/128) (by rfl) (by rfl)
    component140Node10_sound component140Node11_sound

private noncomputable def component140Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (33/64), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component140Node13_sound : Sound component140Node13Box :=
  sound_of_literal_split component140Node13Box component140Node9Box component140Node12Box
    .k (61/16) (by rfl) (by rfl)
    component140Node9_sound component140Node12_sound

private noncomputable def component140Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (1/2), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component140Node14_sound : Sound component140Node14Box :=
  sound_of_literal_split component140Node14Box component140Node6Box component140Node13Box
    .chi (33/64) (by rfl) (by rfl)
    component140Node6_sound component140Node13_sound

private noncomputable def component140Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (1/2), chiHi := (65/128) }

set_option maxRecDepth 1000000 in
private theorem component140Node15_sound : Sound component140Node15Box :=
  sound_of_literal_split component140Node15Box leaf6886Box leaf6887Box
    .k (125/32) (by rfl) (by rfl)
    leaf6886FlatSound leaf6887FlatSound

private noncomputable def component140Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (65/128), chiHi := (33/64) }

set_option maxRecDepth 1000000 in
private theorem component140Node16_sound : Sound component140Node16Box :=
  sound_of_literal_split component140Node16Box leaf6888Box leaf6889Box
    .k (125/32) (by rfl) (by rfl)
    leaf6888FlatSound leaf6889FlatSound

private noncomputable def component140Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (1/2), chiHi := (33/64) }

set_option maxRecDepth 1000000 in
private theorem component140Node17_sound : Sound component140Node17Box :=
  sound_of_literal_split component140Node17Box component140Node15Box component140Node16Box
    .chi (65/128) (by rfl) (by rfl)
    component140Node15_sound component140Node16_sound

private noncomputable def component140Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (1/2), chiHi := (65/128) }

set_option maxRecDepth 1000000 in
private theorem component140Node18_sound : Sound component140Node18Box :=
  sound_of_literal_split component140Node18Box leaf6890Box leaf6891Box
    .k (127/32) (by rfl) (by rfl)
    leaf6890FlatSound leaf6891FlatSound

private noncomputable def component140Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (65/128), chiHi := (33/64) }

set_option maxRecDepth 1000000 in
private theorem component140Node19_sound : Sound component140Node19Box :=
  sound_of_literal_split component140Node19Box leaf6892Box leaf6893Box
    .k (127/32) (by rfl) (by rfl)
    leaf6892FlatSound leaf6893FlatSound

private noncomputable def component140Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (1/2), chiHi := (33/64) }

set_option maxRecDepth 1000000 in
private theorem component140Node20_sound : Sound component140Node20Box :=
  sound_of_literal_split component140Node20Box component140Node18Box component140Node19Box
    .chi (65/128) (by rfl) (by rfl)
    component140Node18_sound component140Node19_sound

private noncomputable def component140Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (1/2), chiHi := (33/64) }

set_option maxRecDepth 1000000 in
private theorem component140Node21_sound : Sound component140Node21Box :=
  sound_of_literal_split component140Node21Box component140Node17Box component140Node20Box
    .k (63/16) (by rfl) (by rfl)
    component140Node17_sound component140Node20_sound

private noncomputable def component140Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (33/64), chiHi := (67/128) }

set_option maxRecDepth 1000000 in
private theorem component140Node22_sound : Sound component140Node22Box :=
  sound_of_literal_split component140Node22Box leaf6894Box leaf6895Box
    .k (125/32) (by rfl) (by rfl)
    leaf6894FlatSound leaf6895FlatSound

private noncomputable def component140Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (67/128), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component140Node23_sound : Sound component140Node23Box :=
  sound_of_literal_split component140Node23Box leaf6896Box leaf6897Box
    .k (125/32) (by rfl) (by rfl)
    leaf6896FlatSound leaf6897FlatSound

private noncomputable def component140Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (33/64), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component140Node24_sound : Sound component140Node24Box :=
  sound_of_literal_split component140Node24Box component140Node22Box component140Node23Box
    .chi (67/128) (by rfl) (by rfl)
    component140Node22_sound component140Node23_sound

private noncomputable def component140Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (33/64), chiHi := (67/128) }

set_option maxRecDepth 1000000 in
private theorem component140Node25_sound : Sound component140Node25Box :=
  sound_of_literal_split component140Node25Box leaf6898Box leaf6899Box
    .k (127/32) (by rfl) (by rfl)
    leaf6898FlatSound leaf6899FlatSound

private noncomputable def component140Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (67/128), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component140Node26_sound : Sound component140Node26Box :=
  sound_of_literal_split component140Node26Box leaf6900Box leaf6901Box
    .k (127/32) (by rfl) (by rfl)
    leaf6900FlatSound leaf6901FlatSound

private noncomputable def component140Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (33/64), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component140Node27_sound : Sound component140Node27Box :=
  sound_of_literal_split component140Node27Box component140Node25Box component140Node26Box
    .chi (67/128) (by rfl) (by rfl)
    component140Node25_sound component140Node26_sound

private noncomputable def component140Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (33/64), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component140Node28_sound : Sound component140Node28Box :=
  sound_of_literal_split component140Node28Box component140Node24Box component140Node27Box
    .k (63/16) (by rfl) (by rfl)
    component140Node24_sound component140Node27_sound

private noncomputable def component140Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (1/2), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component140Node29_sound : Sound component140Node29Box :=
  sound_of_literal_split component140Node29Box component140Node21Box component140Node28Box
    .chi (33/64) (by rfl) (by rfl)
    component140Node21_sound component140Node28_sound

private noncomputable def component140Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (4), chiLo := (1/2), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component140Node30_sound : Sound component140Node30Box :=
  sound_of_literal_split component140Node30Box component140Node14Box component140Node29Box
    .k (31/8) (by rfl) (by rfl)
    component140Node14_sound component140Node29_sound

private noncomputable def component140Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (17/32), chiHi := (69/128) }

set_option maxRecDepth 1000000 in
private theorem component140Node31_sound : Sound component140Node31Box :=
  sound_of_literal_split component140Node31Box leaf6902Box leaf6903Box
    .k (121/32) (by rfl) (by rfl)
    leaf6902FlatSound leaf6903FlatSound

private noncomputable def component140Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (69/128), chiHi := (35/64) }

set_option maxRecDepth 1000000 in
private theorem component140Node32_sound : Sound component140Node32Box :=
  sound_of_literal_split component140Node32Box leaf6904Box leaf6905Box
    .k (121/32) (by rfl) (by rfl)
    leaf6904FlatSound leaf6905FlatSound

private noncomputable def component140Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (17/32), chiHi := (35/64) }

set_option maxRecDepth 1000000 in
private theorem component140Node33_sound : Sound component140Node33Box :=
  sound_of_literal_split component140Node33Box component140Node31Box component140Node32Box
    .chi (69/128) (by rfl) (by rfl)
    component140Node31_sound component140Node32_sound

private noncomputable def component140Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (17/32), chiHi := (69/128) }

set_option maxRecDepth 1000000 in
private theorem component140Node34_sound : Sound component140Node34Box :=
  sound_of_literal_split component140Node34Box leaf6906Box leaf6907Box
    .k (123/32) (by rfl) (by rfl)
    leaf6906FlatSound leaf6907FlatSound

private noncomputable def component140Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (69/128), chiHi := (35/64) }

set_option maxRecDepth 1000000 in
private theorem component140Node35_sound : Sound component140Node35Box :=
  sound_of_literal_split component140Node35Box leaf6908Box leaf6909Box
    .k (123/32) (by rfl) (by rfl)
    leaf6908FlatSound leaf6909FlatSound

private noncomputable def component140Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (17/32), chiHi := (35/64) }

set_option maxRecDepth 1000000 in
private theorem component140Node36_sound : Sound component140Node36Box :=
  sound_of_literal_split component140Node36Box component140Node34Box component140Node35Box
    .chi (69/128) (by rfl) (by rfl)
    component140Node34_sound component140Node35_sound

private noncomputable def component140Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (17/32), chiHi := (35/64) }

set_option maxRecDepth 1000000 in
private theorem component140Node37_sound : Sound component140Node37Box :=
  sound_of_literal_split component140Node37Box component140Node33Box component140Node36Box
    .k (61/16) (by rfl) (by rfl)
    component140Node33_sound component140Node36_sound

private noncomputable def component140Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (35/64), chiHi := (71/128) }

set_option maxRecDepth 1000000 in
private theorem component140Node38_sound : Sound component140Node38Box :=
  sound_of_literal_split component140Node38Box leaf6910Box leaf6911Box
    .k (121/32) (by rfl) (by rfl)
    leaf6910FlatSound leaf6911FlatSound

private noncomputable def component140Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (71/128), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component140Node39_sound : Sound component140Node39Box :=
  sound_of_literal_split component140Node39Box leaf6912Box leaf6913Box
    .k (121/32) (by rfl) (by rfl)
    leaf6912FlatSound leaf6913FlatSound

private noncomputable def component140Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (35/64), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component140Node40_sound : Sound component140Node40Box :=
  sound_of_literal_split component140Node40Box component140Node38Box component140Node39Box
    .chi (71/128) (by rfl) (by rfl)
    component140Node38_sound component140Node39_sound

private noncomputable def component140Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (35/64), chiHi := (71/128) }

set_option maxRecDepth 1000000 in
private theorem component140Node41_sound : Sound component140Node41Box :=
  sound_of_literal_split component140Node41Box leaf6914Box leaf6915Box
    .k (123/32) (by rfl) (by rfl)
    leaf6914FlatSound leaf6915FlatSound

private noncomputable def component140Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (71/128), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component140Node42_sound : Sound component140Node42Box :=
  sound_of_literal_split component140Node42Box leaf6916Box leaf6917Box
    .k (123/32) (by rfl) (by rfl)
    leaf6916FlatSound leaf6917FlatSound

private noncomputable def component140Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (35/64), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component140Node43_sound : Sound component140Node43Box :=
  sound_of_literal_split component140Node43Box component140Node41Box component140Node42Box
    .chi (71/128) (by rfl) (by rfl)
    component140Node41_sound component140Node42_sound

private noncomputable def component140Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (35/64), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component140Node44_sound : Sound component140Node44Box :=
  sound_of_literal_split component140Node44Box component140Node40Box component140Node43Box
    .k (61/16) (by rfl) (by rfl)
    component140Node40_sound component140Node43_sound

private noncomputable def component140Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (17/32), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component140Node45_sound : Sound component140Node45Box :=
  sound_of_literal_split component140Node45Box component140Node37Box component140Node44Box
    .chi (35/64) (by rfl) (by rfl)
    component140Node37_sound component140Node44_sound

private noncomputable def component140Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (17/32), chiHi := (69/128) }

set_option maxRecDepth 1000000 in
private theorem component140Node46_sound : Sound component140Node46Box :=
  sound_of_literal_split component140Node46Box leaf6918Box leaf6919Box
    .k (125/32) (by rfl) (by rfl)
    leaf6918FlatSound leaf6919FlatSound

private noncomputable def component140Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (69/128), chiHi := (35/64) }

set_option maxRecDepth 1000000 in
private theorem component140Node47_sound : Sound component140Node47Box :=
  sound_of_literal_split component140Node47Box leaf6920Box leaf6921Box
    .k (125/32) (by rfl) (by rfl)
    leaf6920FlatSound leaf6921FlatSound

private noncomputable def component140Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (17/32), chiHi := (35/64) }

set_option maxRecDepth 1000000 in
private theorem component140Node48_sound : Sound component140Node48Box :=
  sound_of_literal_split component140Node48Box component140Node46Box component140Node47Box
    .chi (69/128) (by rfl) (by rfl)
    component140Node46_sound component140Node47_sound

private noncomputable def component140Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (17/32), chiHi := (69/128) }

set_option maxRecDepth 1000000 in
private theorem component140Node49_sound : Sound component140Node49Box :=
  sound_of_literal_split component140Node49Box leaf6922Box leaf6923Box
    .k (127/32) (by rfl) (by rfl)
    leaf6922FlatSound leaf6923FlatSound

private noncomputable def component140Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (69/128), chiHi := (35/64) }

set_option maxRecDepth 1000000 in
private theorem component140Node50_sound : Sound component140Node50Box :=
  sound_of_literal_split component140Node50Box leaf6924Box leaf6925Box
    .k (127/32) (by rfl) (by rfl)
    leaf6924FlatSound leaf6925FlatSound

private noncomputable def component140Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (17/32), chiHi := (35/64) }

set_option maxRecDepth 1000000 in
private theorem component140Node51_sound : Sound component140Node51Box :=
  sound_of_literal_split component140Node51Box component140Node49Box component140Node50Box
    .chi (69/128) (by rfl) (by rfl)
    component140Node49_sound component140Node50_sound

private noncomputable def component140Node52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (17/32), chiHi := (35/64) }

set_option maxRecDepth 1000000 in
private theorem component140Node52_sound : Sound component140Node52Box :=
  sound_of_literal_split component140Node52Box component140Node48Box component140Node51Box
    .k (63/16) (by rfl) (by rfl)
    component140Node48_sound component140Node51_sound

private noncomputable def component140Node53Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (35/64), chiHi := (71/128) }

set_option maxRecDepth 1000000 in
private theorem component140Node53_sound : Sound component140Node53Box :=
  sound_of_literal_split component140Node53Box leaf6926Box leaf6927Box
    .k (125/32) (by rfl) (by rfl)
    leaf6926FlatSound leaf6927FlatSound

private noncomputable def component140Node54Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (71/128), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component140Node54_sound : Sound component140Node54Box :=
  sound_of_literal_split component140Node54Box leaf6928Box leaf6929Box
    .k (125/32) (by rfl) (by rfl)
    leaf6928FlatSound leaf6929FlatSound

private noncomputable def component140Node55Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (35/64), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component140Node55_sound : Sound component140Node55Box :=
  sound_of_literal_split component140Node55Box component140Node53Box component140Node54Box
    .chi (71/128) (by rfl) (by rfl)
    component140Node53_sound component140Node54_sound

private noncomputable def component140Node56Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (35/64), chiHi := (71/128) }

set_option maxRecDepth 1000000 in
private theorem component140Node56_sound : Sound component140Node56Box :=
  sound_of_literal_split component140Node56Box leaf6930Box leaf6931Box
    .k (127/32) (by rfl) (by rfl)
    leaf6930FlatSound leaf6931FlatSound

private noncomputable def component140Node57Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (71/128), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component140Node57_sound : Sound component140Node57Box :=
  sound_of_literal_split component140Node57Box leaf6932Box leaf6933Box
    .k (127/32) (by rfl) (by rfl)
    leaf6932FlatSound leaf6933FlatSound

private noncomputable def component140Node58Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (35/64), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component140Node58_sound : Sound component140Node58Box :=
  sound_of_literal_split component140Node58Box component140Node56Box component140Node57Box
    .chi (71/128) (by rfl) (by rfl)
    component140Node56_sound component140Node57_sound

private noncomputable def component140Node59Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (35/64), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component140Node59_sound : Sound component140Node59Box :=
  sound_of_literal_split component140Node59Box component140Node55Box component140Node58Box
    .k (63/16) (by rfl) (by rfl)
    component140Node55_sound component140Node58_sound

private noncomputable def component140Node60Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (17/32), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component140Node60_sound : Sound component140Node60Box :=
  sound_of_literal_split component140Node60Box component140Node52Box component140Node59Box
    .chi (35/64) (by rfl) (by rfl)
    component140Node52_sound component140Node59_sound

private noncomputable def component140Node61Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (4), chiLo := (17/32), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component140Node61_sound : Sound component140Node61Box :=
  sound_of_literal_split component140Node61Box component140Node45Box component140Node60Box
    .k (31/8) (by rfl) (by rfl)
    component140Node45_sound component140Node60_sound

noncomputable def component140Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (4), chiLo := (1/2), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
theorem component140_sound : Sound component140Box :=
  sound_of_literal_split component140Box component140Node30Box component140Node61Box
    .chi (17/32) (by rfl) (by rfl)
    component140Node30_sound component140Node61_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
