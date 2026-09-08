import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch6
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

private noncomputable def leaf2751Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (1/8), chiHi := (65/512) }

private noncomputable def leaf2751Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742195/1073741824) }, vSqrt := { lower := (8191/8192), upper := (268435712/268427591) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1576994447/1073741824) }, upper := { exponent := 0, mantissa := (24249/16384) } }, logOuter := sk169LogOuterCertificate, logK := sk169LogKCertificate, logChi := chi205LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (536863303/536855182) } }, logDArg := sk169LogDArgCertificate }

private noncomputable def leaf2751InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf2751LocalValidity :
    LeafFacts leaf2751Box leaf2751Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2751Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (268435712/268427591) }) = true
      norm_num [leaf2751Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2751CertificateValid :
    WideCertificateValid leaf2751Box leaf2751Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk169ValidityFacts chi205ValidityFacts
    leaf2751LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2751CoverageChecked :
    coverageCheck (innerAD leaf2751Box) leaf2751InnerLog = true := by
  rfl'

private theorem leaf2751InnerLogValid :
    leaf2751InnerLog.Valid 8 (innerAD leaf2751Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf2751CoverageChecked

private noncomputable def leaf2751InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629335/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2751InputLogOnePlusV_eq :
    leaf2751InputLogOnePlusV = outerEnclosure 24
      (leaf2751Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2751RoundedFacts : LeafRoundedFacts 8
    leaf2751Certificate.logOnePlusV leaf2751InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2751InputLogOnePlusV_eq }

private noncomputable def leaf2751Inputs : Inputs :=
  inputsOfCaches globalInput sk169RoundedInputs
    chi205InputQChi innerPair34Input
    leaf2751InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2751LowerChecked :
    lowerCheck 24 leaf2751Box leaf2751Inputs = true := by
  rfl'

private theorem leaf2751CoversExact : CoversExact 8
    leaf2751Box leaf2751Certificate leaf2751InnerLog leaf2751Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk169RoundedFacts chi205RoundedFacts
    innerPair34RoundedFacts leaf2751RoundedFacts (by rfl)

private theorem leaf2751FlatSound : Sound leaf2751Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2751CertificateValid
    leaf2751InnerLogValid leaf2751CoversExact leaf2751LowerChecked

private noncomputable def leaf2752Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (65/512), chiHi := (33/256) }

private noncomputable def leaf2752Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742197/1073741824) }, vSqrt := { lower := (8191/8192), upper := (13743698739/13743486464) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1584858285/1073741824) }, upper := { exponent := 0, mantissa := (12185/8192) } }, logOuter := sk169LogOuterCertificate, logK := sk169LogKCertificate, logChi := chi206LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (27487185203/27486972928) } }, logDArg := sk169LogDArgCertificate }

private noncomputable def leaf2752InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf2752LocalValidity :
    LeafFacts leaf2752Box leaf2752Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2752Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (13743698739/13743486464) }) = true
      norm_num [leaf2752Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2752CertificateValid :
    WideCertificateValid leaf2752Box leaf2752Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk169ValidityFacts chi206ValidityFacts
    leaf2752LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2752CoverageChecked :
    coverageCheck (innerAD leaf2752Box) leaf2752InnerLog = true := by
  rfl'

private theorem leaf2752InnerLogValid :
    leaf2752InnerLog.Valid 8 (innerAD leaf2752Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf2752CoverageChecked

private noncomputable def leaf2752InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814605/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2752InputLogOnePlusV_eq :
    leaf2752InputLogOnePlusV = outerEnclosure 24
      (leaf2752Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2752RoundedFacts : LeafRoundedFacts 8
    leaf2752Certificate.logOnePlusV leaf2752InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2752InputLogOnePlusV_eq }

private noncomputable def leaf2752Inputs : Inputs :=
  inputsOfCaches globalInput sk169RoundedInputs
    chi206InputQChi innerPair34Input
    leaf2752InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2752LowerChecked :
    lowerCheck 24 leaf2752Box leaf2752Inputs = true := by
  rfl'

private theorem leaf2752CoversExact : CoversExact 8
    leaf2752Box leaf2752Certificate leaf2752InnerLog leaf2752Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk169RoundedFacts chi206RoundedFacts
    innerPair34RoundedFacts leaf2752RoundedFacts (by rfl)

private theorem leaf2752FlatSound : Sound leaf2752Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2752CertificateValid
    leaf2752InnerLogValid leaf2752CoversExact leaf2752LowerChecked

private noncomputable def leaf2753Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (33/256), chiHi := (67/512) }

private noncomputable def leaf2753Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742199/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22906164565/22905800448) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1592722123/1073741824) }, upper := { exponent := 0, mantissa := (24491/16384) } }, logOuter := sk169LogOuterCertificate, logK := sk169LogKCertificate, logChi := chi203LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45811965013/45811600896) } }, logDArg := sk169LogDArgCertificate }

private noncomputable def leaf2753InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf2753LocalValidity :
    LeafFacts leaf2753Box leaf2753Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2753Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22906164565/22905800448) }) = true
      norm_num [leaf2753Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2753CertificateValid :
    WideCertificateValid leaf2753Box leaf2753Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk169ValidityFacts chi203ValidityFacts
    leaf2753LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2753CoverageChecked :
    coverageCheck (innerAD leaf2753Box) leaf2753InnerLog = true := by
  rfl'

private theorem leaf2753InnerLogValid :
    leaf2753InnerLog.Valid 8 (innerAD leaf2753Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf2753CoverageChecked

private noncomputable def leaf2753InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814607/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2753InputLogOnePlusV_eq :
    leaf2753InputLogOnePlusV = outerEnclosure 24
      (leaf2753Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2753RoundedFacts : LeafRoundedFacts 8
    leaf2753Certificate.logOnePlusV leaf2753InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2753InputLogOnePlusV_eq }

private noncomputable def leaf2753Inputs : Inputs :=
  inputsOfCaches globalInput sk169RoundedInputs
    chi203InputQChi innerPair34Input
    leaf2753InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2753LowerChecked :
    lowerCheck 24 leaf2753Box leaf2753Inputs = true := by
  rfl'

private theorem leaf2753CoversExact : CoversExact 8
    leaf2753Box leaf2753Certificate leaf2753InnerLog leaf2753Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk169RoundedFacts chi203RoundedFacts
    innerPair34RoundedFacts leaf2753RoundedFacts (by rfl)

private theorem leaf2753FlatSound : Sound leaf2753Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2753CertificateValid
    leaf2753InnerLogValid leaf2753CoversExact leaf2753LowerChecked

private noncomputable def leaf2754Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (67/512), chiHi := (17/128) }

private noncomputable def leaf2754Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742201/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68718493695/68717370368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1600585961/1073741824) }, upper := { exponent := 0, mantissa := (6153/4096) } }, logOuter := sk169LogOuterCertificate, logK := sk169LogKCertificate, logChi := chi204LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137435864063/137434740736) } }, logDArg := sk169LogDArgCertificate }

private noncomputable def leaf2754InnerLog : WideLogData :=
  innerPair409Data

set_option maxRecDepth 1000000 in
private theorem leaf2754LocalValidity :
    LeafFacts leaf2754Box leaf2754Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2754Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68718493695/68717370368) }) = true
      norm_num [leaf2754Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2754CertificateValid :
    WideCertificateValid leaf2754Box leaf2754Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk169ValidityFacts chi204ValidityFacts
    leaf2754LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2754CoverageChecked :
    coverageCheck (innerAD leaf2754Box) leaf2754InnerLog = true := by
  rfl'

private theorem leaf2754InnerLogValid :
    leaf2754InnerLog.Valid 8 (innerAD leaf2754Box) :=
  wideLogDataValid_of_cachedCheck endpoint120PositiveFacts
    endpoint49PositiveFacts.valid leaf2754CoverageChecked

private noncomputable def leaf2754InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814609/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2754InputLogOnePlusV_eq :
    leaf2754InputLogOnePlusV = outerEnclosure 24
      (leaf2754Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2754RoundedFacts : LeafRoundedFacts 8
    leaf2754Certificate.logOnePlusV leaf2754InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2754InputLogOnePlusV_eq }

private noncomputable def leaf2754Inputs : Inputs :=
  inputsOfCaches globalInput sk169RoundedInputs
    chi204InputQChi innerPair409Input
    leaf2754InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2754LowerChecked :
    lowerCheck 24 leaf2754Box leaf2754Inputs = true := by
  rfl'

private theorem leaf2754CoversExact : CoversExact 8
    leaf2754Box leaf2754Certificate leaf2754InnerLog leaf2754Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk169RoundedFacts chi204RoundedFacts
    innerPair409RoundedFacts leaf2754RoundedFacts (by rfl)

private theorem leaf2754FlatSound : Sound leaf2754Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2754CertificateValid
    leaf2754InnerLogValid leaf2754CoversExact leaf2754LowerChecked

private noncomputable def leaf2755Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (1/8), chiHi := (65/512) }

private noncomputable def leaf2755Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742197/1073741824) }, vSqrt := { lower := (8191/8192), upper := (134217856/134213763) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1581188493/1073741824) }, upper := { exponent := 0, mantissa := (12157/8192) } }, logOuter := sk170LogOuterCertificate, logK := sk170LogKCertificate, logChi := chi205LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268431619/268427526) } }, logDArg := sk170LogDArgCertificate }

private noncomputable def leaf2755InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf2755LocalValidity :
    LeafFacts leaf2755Box leaf2755Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2755Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217856/134213763) }) = true
      norm_num [leaf2755Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2755CertificateValid :
    WideCertificateValid leaf2755Box leaf2755Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk170ValidityFacts chi205ValidityFacts
    leaf2755LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2755CoverageChecked :
    coverageCheck (innerAD leaf2755Box) leaf2755InnerLog = true := by
  rfl'

private theorem leaf2755InnerLogValid :
    leaf2755InnerLog.Valid 8 (innerAD leaf2755Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf2755CoverageChecked

private noncomputable def leaf2755InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629337/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2755InputLogOnePlusV_eq :
    leaf2755InputLogOnePlusV = outerEnclosure 24
      (leaf2755Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2755RoundedFacts : LeafRoundedFacts 8
    leaf2755Certificate.logOnePlusV leaf2755InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2755InputLogOnePlusV_eq }

private noncomputable def leaf2755Inputs : Inputs :=
  inputsOfCaches globalInput sk170RoundedInputs
    chi205InputQChi innerPair34Input
    leaf2755InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2755LowerChecked :
    lowerCheck 24 leaf2755Box leaf2755Inputs = true := by
  rfl'

private theorem leaf2755CoversExact : CoversExact 8
    leaf2755Box leaf2755Certificate leaf2755InnerLog leaf2755Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk170RoundedFacts chi205RoundedFacts
    innerPair34RoundedFacts leaf2755RoundedFacts (by rfl)

private theorem leaf2755FlatSound : Sound leaf2755Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2755CertificateValid
    leaf2755InnerLogValid leaf2755CoversExact leaf2755LowerChecked

private noncomputable def leaf2756Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (65/512), chiHi := (33/256) }

private noncomputable def leaf2756Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742199/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68718493695/68717415424) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1589117863/1073741824) }, upper := { exponent := 0, mantissa := (6109/4096) } }, logOuter := sk170LogOuterCertificate, logK := sk170LogKCertificate, logChi := chi206LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137435909119/137434830848) } }, logDArg := sk170LogDArgCertificate }

private noncomputable def leaf2756InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf2756LocalValidity :
    LeafFacts leaf2756Box leaf2756Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2756Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68718493695/68717415424) }) = true
      norm_num [leaf2756Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2756CertificateValid :
    WideCertificateValid leaf2756Box leaf2756Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk170ValidityFacts chi206ValidityFacts
    leaf2756LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2756CoverageChecked :
    coverageCheck (innerAD leaf2756Box) leaf2756InnerLog = true := by
  rfl'

private theorem leaf2756InnerLogValid :
    leaf2756InnerLog.Valid 8 (innerAD leaf2756Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf2756CoverageChecked

private noncomputable def leaf2756InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907303/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2756InputLogOnePlusV_eq :
    leaf2756InputLogOnePlusV = outerEnclosure 24
      (leaf2756Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2756RoundedFacts : LeafRoundedFacts 8
    leaf2756Certificate.logOnePlusV leaf2756InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2756InputLogOnePlusV_eq }

private noncomputable def leaf2756Inputs : Inputs :=
  inputsOfCaches globalInput sk170RoundedInputs
    chi206InputQChi innerPair34Input
    leaf2756InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2756LowerChecked :
    lowerCheck 24 leaf2756Box leaf2756Inputs = true := by
  rfl'

private theorem leaf2756CoversExact : CoversExact 8
    leaf2756Box leaf2756Certificate leaf2756InnerLog leaf2756Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk170RoundedFacts chi206RoundedFacts
    innerPair34RoundedFacts leaf2756RoundedFacts (by rfl)

private theorem leaf2756FlatSound : Sound leaf2756Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2756CertificateValid
    leaf2756InnerLogValid leaf2756CoversExact leaf2756LowerChecked

private noncomputable def leaf2757Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (33/256), chiHi := (67/512) }

private noncomputable def leaf2757Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742201/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68718493695/68717384192) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1597047233/1073741824) }, upper := { exponent := 0, mantissa := (12279/8192) } }, logOuter := sk170LogOuterCertificate, logK := sk170LogKCertificate, logChi := chi203LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137435877887/137434768384) } }, logDArg := sk170LogDArgCertificate }

private noncomputable def leaf2757InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf2757LocalValidity :
    LeafFacts leaf2757Box leaf2757Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2757Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68718493695/68717384192) }) = true
      norm_num [leaf2757Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2757CertificateValid :
    WideCertificateValid leaf2757Box leaf2757Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk170ValidityFacts chi203ValidityFacts
    leaf2757LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2757CoverageChecked :
    coverageCheck (innerAD leaf2757Box) leaf2757InnerLog = true := by
  rfl'

private theorem leaf2757InnerLogValid :
    leaf2757InnerLog.Valid 8 (innerAD leaf2757Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf2757CoverageChecked

private noncomputable def leaf2757InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (363413/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf2757InputLogOnePlusV_eq :
    leaf2757InputLogOnePlusV = outerEnclosure 24
      (leaf2757Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2757RoundedFacts : LeafRoundedFacts 8
    leaf2757Certificate.logOnePlusV leaf2757InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2757InputLogOnePlusV_eq }

private noncomputable def leaf2757Inputs : Inputs :=
  inputsOfCaches globalInput sk170RoundedInputs
    chi203InputQChi innerPair34Input
    leaf2757InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2757LowerChecked :
    lowerCheck 24 leaf2757Box leaf2757Inputs = true := by
  rfl'

private theorem leaf2757CoversExact : CoversExact 8
    leaf2757Box leaf2757Certificate leaf2757InnerLog leaf2757Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk170RoundedFacts chi203RoundedFacts
    innerPair34RoundedFacts leaf2757RoundedFacts (by rfl)

private theorem leaf2757FlatSound : Sound leaf2757Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2757CertificateValid
    leaf2757InnerLogValid leaf2757CoversExact leaf2757LowerChecked

private noncomputable def leaf2758Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (67/512), chiHi := (17/128) }

private noncomputable def leaf2758Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742203/1073741824) }, vSqrt := { lower := (8191/8192), upper := (4581232913/4581156864) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1604976603/1073741824) }, upper := { exponent := 0, mantissa := (3085/2048) } }, logOuter := sk170LogOuterCertificate, logK := sk170LogKCertificate, logChi := chi204LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (9162389777/9162313728) } }, logDArg := sk170LogDArgCertificate }

private noncomputable def leaf2758InnerLog : WideLogData :=
  innerPair409Data

set_option maxRecDepth 1000000 in
private theorem leaf2758LocalValidity :
    LeafFacts leaf2758Box leaf2758Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2758Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4581232913/4581156864) }) = true
      norm_num [leaf2758Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2758CertificateValid :
    WideCertificateValid leaf2758Box leaf2758Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk170ValidityFacts chi204ValidityFacts
    leaf2758LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2758CoverageChecked :
    coverageCheck (innerAD leaf2758Box) leaf2758InnerLog = true := by
  rfl'

private theorem leaf2758InnerLogValid :
    leaf2758InnerLog.Valid 8 (innerAD leaf2758Box) :=
  wideLogDataValid_of_cachedCheck endpoint120PositiveFacts
    endpoint49PositiveFacts.valid leaf2758CoverageChecked

private noncomputable def leaf2758InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907305/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2758InputLogOnePlusV_eq :
    leaf2758InputLogOnePlusV = outerEnclosure 24
      (leaf2758Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2758RoundedFacts : LeafRoundedFacts 8
    leaf2758Certificate.logOnePlusV leaf2758InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2758InputLogOnePlusV_eq }

private noncomputable def leaf2758Inputs : Inputs :=
  inputsOfCaches globalInput sk170RoundedInputs
    chi204InputQChi innerPair409Input
    leaf2758InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2758LowerChecked :
    lowerCheck 24 leaf2758Box leaf2758Inputs = true := by
  rfl'

private theorem leaf2758CoversExact : CoversExact 8
    leaf2758Box leaf2758Certificate leaf2758InnerLog leaf2758Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk170RoundedFacts chi204RoundedFacts
    innerPair409RoundedFacts leaf2758RoundedFacts (by rfl)

private theorem leaf2758FlatSound : Sound leaf2758Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2758CertificateValid
    leaf2758InnerLogValid leaf2758CoversExact leaf2758LowerChecked

private noncomputable def leaf2759Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (241/64), chiLo := (17/128), chiHi := (35/256) }

private noncomputable def leaf2759Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742375/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434634752) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1608449627/1073741824) }, upper := { exponent := 0, mantissa := (24819/16384) } }, logOuter := sk225LogOuterCertificate, logK := sk225LogKCertificate, logChi := chi179LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871556607/274869269504) } }, logDArg := sk225LogDArgCertificate }

private noncomputable def leaf2759InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf2759LocalValidity :
    LeafFacts leaf2759Box leaf2759Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2759Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434634752) }) = true
      norm_num [leaf2759Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2759CertificateValid :
    WideCertificateValid leaf2759Box leaf2759Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk225ValidityFacts chi179ValidityFacts
    leaf2759LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2759CoverageChecked :
    coverageCheck (innerAD leaf2759Box) leaf2759InnerLog = true := by
  rfl'

private theorem leaf2759InnerLogValid :
    leaf2759InnerLog.Valid 8 (innerAD leaf2759Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf2759CoverageChecked

private noncomputable def leaf2759InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907305/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2759InputLogOnePlusV_eq :
    leaf2759InputLogOnePlusV = outerEnclosure 24
      (leaf2759Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2759RoundedFacts : LeafRoundedFacts 8
    leaf2759Certificate.logOnePlusV leaf2759InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2759InputLogOnePlusV_eq }

private noncomputable def leaf2759Inputs : Inputs :=
  inputsOfCaches globalInput sk225RoundedInputs
    chi179InputQChi innerPair35Input
    leaf2759InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2759LowerChecked :
    lowerCheck 24 leaf2759Box leaf2759Inputs = true := by
  rfl'

private theorem leaf2759CoversExact : CoversExact 8
    leaf2759Box leaf2759Certificate leaf2759InnerLog leaf2759Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk225RoundedFacts chi179RoundedFacts
    innerPair35RoundedFacts leaf2759RoundedFacts (by rfl)

private theorem leaf2759FlatSound : Sound leaf2759Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2759CertificateValid
    leaf2759InnerLogValid leaf2759CoversExact leaf2759LowerChecked

private noncomputable def leaf2760Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (241/64), kHi := (121/32), chiLo := (17/128), chiHi := (35/256) }

private noncomputable def leaf2760Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742377/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45811538944) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1610677713/1073741824) }, upper := { exponent := 0, mantissa := (12427/8192) } }, logOuter := sk226LogOuterCertificate, logK := sk226LogKCertificate, logChi := chi179LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623846229/91623077888) } }, logDArg := sk226LogDArgCertificate }

private noncomputable def leaf2760InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2760LocalValidity :
    LeafFacts leaf2760Box leaf2760Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2760Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45811538944) }) = true
      norm_num [leaf2760Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2760CertificateValid :
    WideCertificateValid leaf2760Box leaf2760Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk226ValidityFacts chi179ValidityFacts
    leaf2760LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2760CoverageChecked :
    coverageCheck (innerAD leaf2760Box) leaf2760InnerLog = true := by
  rfl'

private theorem leaf2760InnerLogValid :
    leaf2760InnerLog.Valid 8 (innerAD leaf2760Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2760CoverageChecked

private noncomputable def leaf2760InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629221/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2760InputLogOnePlusV_eq :
    leaf2760InputLogOnePlusV = outerEnclosure 24
      (leaf2760Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2760RoundedFacts : LeafRoundedFacts 8
    leaf2760Certificate.logOnePlusV leaf2760InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2760InputLogOnePlusV_eq }

private noncomputable def leaf2760Inputs : Inputs :=
  inputsOfCaches globalInput sk226RoundedInputs
    chi179InputQChi innerPair40Input
    leaf2760InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2760LowerChecked :
    lowerCheck 24 leaf2760Box leaf2760Inputs = true := by
  rfl'

private theorem leaf2760CoversExact : CoversExact 8
    leaf2760Box leaf2760Certificate leaf2760InnerLog leaf2760Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk226RoundedFacts chi179RoundedFacts
    innerPair40RoundedFacts leaf2760RoundedFacts (by rfl)

private theorem leaf2760FlatSound : Sound leaf2760Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2760CertificateValid
    leaf2760InnerLogValid leaf2760CoversExact leaf2760LowerChecked

private noncomputable def leaf2761Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (241/64), chiLo := (35/256), chiHi := (9/64) }

private noncomputable def leaf2761Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742377/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486902272) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1624177305/1073741824) }, upper := { exponent := 0, mantissa := (6265/4096) } }, logOuter := sk225LogOuterCertificate, logK := sk225LogKCertificate, logChi := chi180LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54974286643/54973804544) } }, logDArg := sk225LogDArgCertificate }

private noncomputable def leaf2761InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2761LocalValidity :
    LeafFacts leaf2761Box leaf2761Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2761Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486902272) }) = true
      norm_num [leaf2761Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2761CertificateValid :
    WideCertificateValid leaf2761Box leaf2761Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk225ValidityFacts chi180ValidityFacts
    leaf2761LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2761CoverageChecked :
    coverageCheck (innerAD leaf2761Box) leaf2761InnerLog = true := by
  rfl'

private theorem leaf2761InnerLogValid :
    leaf2761InnerLog.Valid 8 (innerAD leaf2761Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2761CoverageChecked

private noncomputable def leaf2761InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907307/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2761InputLogOnePlusV_eq :
    leaf2761InputLogOnePlusV = outerEnclosure 24
      (leaf2761Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2761RoundedFacts : LeafRoundedFacts 8
    leaf2761Certificate.logOnePlusV leaf2761InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2761InputLogOnePlusV_eq }

private noncomputable def leaf2761Inputs : Inputs :=
  inputsOfCaches globalInput sk225RoundedInputs
    chi180InputQChi innerPair40Input
    leaf2761InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2761LowerChecked :
    lowerCheck 24 leaf2761Box leaf2761Inputs = true := by
  rfl'

private theorem leaf2761CoversExact : CoversExact 8
    leaf2761Box leaf2761Certificate leaf2761InnerLog leaf2761Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk225RoundedFacts chi180RoundedFacts
    innerPair40RoundedFacts leaf2761RoundedFacts (by rfl)

private theorem leaf2761FlatSound : Sound leaf2761Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2761CertificateValid
    leaf2761InnerLogValid leaf2761CoversExact leaf2761LowerChecked

private noncomputable def leaf2762Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (241/64), kHi := (121/32), chiLo := (35/256), chiHi := (9/64) }

private noncomputable def leaf2762Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742379/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434492928) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1626470923/1073741824) }, upper := { exponent := 0, mantissa := (3137/2048) } }, logOuter := sk226LogOuterCertificate, logK := sk226LogKCertificate, logChi := chi180LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871414783/274868985856) } }, logDArg := sk226LogDArgCertificate }

private noncomputable def leaf2762InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2762LocalValidity :
    LeafFacts leaf2762Box leaf2762Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2762Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434492928) }) = true
      norm_num [leaf2762Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2762CertificateValid :
    WideCertificateValid leaf2762Box leaf2762Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk226ValidityFacts chi180ValidityFacts
    leaf2762LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2762CoverageChecked :
    coverageCheck (innerAD leaf2762Box) leaf2762InnerLog = true := by
  rfl'

private theorem leaf2762InnerLogValid :
    leaf2762InnerLog.Valid 8 (innerAD leaf2762Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2762CoverageChecked

private noncomputable def leaf2762InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629229/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2762InputLogOnePlusV_eq :
    leaf2762InputLogOnePlusV = outerEnclosure 24
      (leaf2762Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2762RoundedFacts : LeafRoundedFacts 8
    leaf2762Certificate.logOnePlusV leaf2762InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2762InputLogOnePlusV_eq }

private noncomputable def leaf2762Inputs : Inputs :=
  inputsOfCaches globalInput sk226RoundedInputs
    chi180InputQChi innerPair40Input
    leaf2762InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2762LowerChecked :
    lowerCheck 24 leaf2762Box leaf2762Inputs = true := by
  rfl'

private theorem leaf2762CoversExact : CoversExact 8
    leaf2762Box leaf2762Certificate leaf2762InnerLog leaf2762Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk226RoundedFacts chi180RoundedFacts
    innerPair40RoundedFacts leaf2762RoundedFacts (by rfl)

private theorem leaf2762FlatSound : Sound leaf2762Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2762CertificateValid
    leaf2762InnerLogValid leaf2762CoversExact leaf2762LowerChecked

private noncomputable def leaf2763Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (243/64), chiLo := (17/128), chiHi := (35/256) }

private noncomputable def leaf2763Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742379/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434598912) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1612905799/1073741824) }, upper := { exponent := 0, mantissa := (24889/16384) } }, logOuter := sk227LogOuterCertificate, logK := sk227LogKCertificate, logChi := chi179LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871520767/274869197824) } }, logDArg := sk227LogDArgCertificate }

private noncomputable def leaf2763InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2763LocalValidity :
    LeafFacts leaf2763Box leaf2763Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2763Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434598912) }) = true
      norm_num [leaf2763Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2763CertificateValid :
    WideCertificateValid leaf2763Box leaf2763Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk227ValidityFacts chi179ValidityFacts
    leaf2763LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2763CoverageChecked :
    coverageCheck (innerAD leaf2763Box) leaf2763InnerLog = true := by
  rfl'

private theorem leaf2763InnerLogValid :
    leaf2763InnerLog.Valid 8 (innerAD leaf2763Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2763CoverageChecked

private noncomputable def leaf2763InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629223/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2763InputLogOnePlusV_eq :
    leaf2763InputLogOnePlusV = outerEnclosure 24
      (leaf2763Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2763RoundedFacts : LeafRoundedFacts 8
    leaf2763Certificate.logOnePlusV leaf2763InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2763InputLogOnePlusV_eq }

private noncomputable def leaf2763Inputs : Inputs :=
  inputsOfCaches globalInput sk227RoundedInputs
    chi179InputQChi innerPair40Input
    leaf2763InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2763LowerChecked :
    lowerCheck 24 leaf2763Box leaf2763Inputs = true := by
  rfl'

private theorem leaf2763CoversExact : CoversExact 8
    leaf2763Box leaf2763Certificate leaf2763InnerLog leaf2763Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk227RoundedFacts chi179RoundedFacts
    innerPair40RoundedFacts leaf2763RoundedFacts (by rfl)

private theorem leaf2763FlatSound : Sound leaf2763Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2763CertificateValid
    leaf2763InnerLogValid leaf2763CoversExact leaf2763LowerChecked

private noncomputable def leaf2764Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (243/64), kHi := (61/16), chiLo := (17/128), chiHi := (35/256) }

private noncomputable def leaf2764Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742381/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434580992) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1615133885/1073741824) }, upper := { exponent := 0, mantissa := (6231/4096) } }, logOuter := sk228LogOuterCertificate, logK := sk228LogKCertificate, logChi := chi179LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871502847/274869161984) } }, logDArg := sk228LogDArgCertificate }

private noncomputable def leaf2764InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2764LocalValidity :
    LeafFacts leaf2764Box leaf2764Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2764Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434580992) }) = true
      norm_num [leaf2764Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2764CertificateValid :
    WideCertificateValid leaf2764Box leaf2764Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk228ValidityFacts chi179ValidityFacts
    leaf2764LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2764CoverageChecked :
    coverageCheck (innerAD leaf2764Box) leaf2764InnerLog = true := by
  rfl'

private theorem leaf2764InnerLogValid :
    leaf2764InnerLog.Valid 8 (innerAD leaf2764Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2764CoverageChecked

private noncomputable def leaf2764InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453653/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf2764InputLogOnePlusV_eq :
    leaf2764InputLogOnePlusV = outerEnclosure 24
      (leaf2764Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2764RoundedFacts : LeafRoundedFacts 8
    leaf2764Certificate.logOnePlusV leaf2764InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2764InputLogOnePlusV_eq }

private noncomputable def leaf2764Inputs : Inputs :=
  inputsOfCaches globalInput sk228RoundedInputs
    chi179InputQChi innerPair40Input
    leaf2764InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2764LowerChecked :
    lowerCheck 24 leaf2764Box leaf2764Inputs = true := by
  rfl'

private theorem leaf2764CoversExact : CoversExact 8
    leaf2764Box leaf2764Certificate leaf2764InnerLog leaf2764Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk228RoundedFacts chi179RoundedFacts
    innerPair40RoundedFacts leaf2764RoundedFacts (by rfl)

private theorem leaf2764FlatSound : Sound leaf2764Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2764CertificateValid
    leaf2764InnerLogValid leaf2764CoversExact leaf2764LowerChecked

private noncomputable def leaf2765Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (243/64), chiLo := (35/256), chiHi := (9/64) }

private noncomputable def leaf2765Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742381/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434474496) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1628764541/1073741824) }, upper := { exponent := 0, mantissa := (6283/4096) } }, logOuter := sk227LogOuterCertificate, logK := sk227LogKCertificate, logChi := chi180LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871396351/274868948992) } }, logDArg := sk227LogDArgCertificate }

private noncomputable def leaf2765InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2765LocalValidity :
    LeafFacts leaf2765Box leaf2765Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2765Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434474496) }) = true
      norm_num [leaf2765Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2765CertificateValid :
    WideCertificateValid leaf2765Box leaf2765Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk227ValidityFacts chi180ValidityFacts
    leaf2765LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2765CoverageChecked :
    coverageCheck (innerAD leaf2765Box) leaf2765InnerLog = true := by
  rfl'

private theorem leaf2765InnerLogValid :
    leaf2765InnerLog.Valid 8 (innerAD leaf2765Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2765CoverageChecked

private noncomputable def leaf2765InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814615/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2765InputLogOnePlusV_eq :
    leaf2765InputLogOnePlusV = outerEnclosure 24
      (leaf2765Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2765RoundedFacts : LeafRoundedFacts 8
    leaf2765Certificate.logOnePlusV leaf2765InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2765InputLogOnePlusV_eq }

private noncomputable def leaf2765Inputs : Inputs :=
  inputsOfCaches globalInput sk227RoundedInputs
    chi180InputQChi innerPair40Input
    leaf2765InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2765LowerChecked :
    lowerCheck 24 leaf2765Box leaf2765Inputs = true := by
  rfl'

private theorem leaf2765CoversExact : CoversExact 8
    leaf2765Box leaf2765Certificate leaf2765InnerLog leaf2765Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk227RoundedFacts chi180RoundedFacts
    innerPair40RoundedFacts leaf2765RoundedFacts (by rfl)

private theorem leaf2765FlatSound : Sound leaf2765Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2765CertificateValid
    leaf2765InnerLogValid leaf2765CoversExact leaf2765LowerChecked

private noncomputable def leaf2766Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (243/64), kHi := (61/16), chiLo := (35/256), chiHi := (9/64) }

private noncomputable def leaf2766Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742383/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434456064) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1631058159/1073741824) }, upper := { exponent := 0, mantissa := (1573/1024) } }, logOuter := sk228LogOuterCertificate, logK := sk228LogKCertificate, logChi := chi180LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871377919/274868912128) } }, logDArg := sk228LogDArgCertificate }

private noncomputable def leaf2766InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2766LocalValidity :
    LeafFacts leaf2766Box leaf2766Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2766Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434456064) }) = true
      norm_num [leaf2766Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2766CertificateValid :
    WideCertificateValid leaf2766Box leaf2766Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk228ValidityFacts chi180ValidityFacts
    leaf2766LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2766CoverageChecked :
    coverageCheck (innerAD leaf2766Box) leaf2766InnerLog = true := by
  rfl'

private theorem leaf2766InnerLogValid :
    leaf2766InnerLog.Valid 8 (innerAD leaf2766Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2766CoverageChecked

private noncomputable def leaf2766InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629231/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2766InputLogOnePlusV_eq :
    leaf2766InputLogOnePlusV = outerEnclosure 24
      (leaf2766Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2766RoundedFacts : LeafRoundedFacts 8
    leaf2766Certificate.logOnePlusV leaf2766InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2766InputLogOnePlusV_eq }

private noncomputable def leaf2766Inputs : Inputs :=
  inputsOfCaches globalInput sk228RoundedInputs
    chi180InputQChi innerPair40Input
    leaf2766InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2766LowerChecked :
    lowerCheck 24 leaf2766Box leaf2766Inputs = true := by
  rfl'

private theorem leaf2766CoversExact : CoversExact 8
    leaf2766Box leaf2766Certificate leaf2766InnerLog leaf2766Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk228RoundedFacts chi180RoundedFacts
    innerPair40RoundedFacts leaf2766RoundedFacts (by rfl)

private theorem leaf2766FlatSound : Sound leaf2766Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2766CertificateValid
    leaf2766InnerLogValid leaf2766CoversExact leaf2766LowerChecked

private noncomputable def leaf2767Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (1/8), chiHi := (65/512) }

private noncomputable def leaf2767Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742199/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68718493695/68717430016) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1585382539/1073741824) }, upper := { exponent := 0, mantissa := (24379/16384) } }, logOuter := sk171LogOuterCertificate, logK := sk171LogKCertificate, logChi := chi205LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137435923711/137434860032) } }, logDArg := sk171LogDArgCertificate }

private noncomputable def leaf2767InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf2767LocalValidity :
    LeafFacts leaf2767Box leaf2767Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2767Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68718493695/68717430016) }) = true
      norm_num [leaf2767Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2767CertificateValid :
    WideCertificateValid leaf2767Box leaf2767Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk171ValidityFacts chi205ValidityFacts
    leaf2767LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2767CoverageChecked :
    coverageCheck (innerAD leaf2767Box) leaf2767InnerLog = true := by
  rfl'

private theorem leaf2767InnerLogValid :
    leaf2767InnerLog.Valid 8 (innerAD leaf2767Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf2767CoverageChecked

private noncomputable def leaf2767InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629211/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2767InputLogOnePlusV_eq :
    leaf2767InputLogOnePlusV = outerEnclosure 24
      (leaf2767Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2767RoundedFacts : LeafRoundedFacts 8
    leaf2767Certificate.logOnePlusV leaf2767InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2767InputLogOnePlusV_eq }

private noncomputable def leaf2767Inputs : Inputs :=
  inputsOfCaches globalInput sk171RoundedInputs
    chi205InputQChi innerPair34Input
    leaf2767InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2767LowerChecked :
    lowerCheck 24 leaf2767Box leaf2767Inputs = true := by
  rfl'

private theorem leaf2767CoversExact : CoversExact 8
    leaf2767Box leaf2767Certificate leaf2767InnerLog leaf2767Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk171RoundedFacts chi205RoundedFacts
    innerPair34RoundedFacts leaf2767RoundedFacts (by rfl)

private theorem leaf2767FlatSound : Sound leaf2767Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2767CertificateValid
    leaf2767InnerLogValid leaf2767CoversExact leaf2767LowerChecked

private noncomputable def leaf2768Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (65/512), chiHi := (33/256) }

private noncomputable def leaf2768Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742201/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68718493695/68717398528) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1593377441/1073741824) }, upper := { exponent := 0, mantissa := (12251/8192) } }, logOuter := sk171LogOuterCertificate, logK := sk171LogKCertificate, logChi := chi206LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137435892223/137434797056) } }, logDArg := sk171LogDArgCertificate }

private noncomputable def leaf2768InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf2768LocalValidity :
    LeafFacts leaf2768Box leaf2768Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2768Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68718493695/68717398528) }) = true
      norm_num [leaf2768Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2768CertificateValid :
    WideCertificateValid leaf2768Box leaf2768Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk171ValidityFacts chi206ValidityFacts
    leaf2768LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2768CoverageChecked :
    coverageCheck (innerAD leaf2768Box) leaf2768InnerLog = true := by
  rfl'

private theorem leaf2768InnerLogValid :
    leaf2768InnerLog.Valid 8 (innerAD leaf2768Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf2768CoverageChecked

private noncomputable def leaf2768InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814607/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2768InputLogOnePlusV_eq :
    leaf2768InputLogOnePlusV = outerEnclosure 24
      (leaf2768Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2768RoundedFacts : LeafRoundedFacts 8
    leaf2768Certificate.logOnePlusV leaf2768InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2768InputLogOnePlusV_eq }

private noncomputable def leaf2768Inputs : Inputs :=
  inputsOfCaches globalInput sk171RoundedInputs
    chi206InputQChi innerPair34Input
    leaf2768InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2768LowerChecked :
    lowerCheck 24 leaf2768Box leaf2768Inputs = true := by
  rfl'

private theorem leaf2768CoversExact : CoversExact 8
    leaf2768Box leaf2768Certificate leaf2768InnerLog leaf2768Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk171RoundedFacts chi206RoundedFacts
    innerPair34RoundedFacts leaf2768RoundedFacts (by rfl)

private theorem leaf2768FlatSound : Sound leaf2768Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2768CertificateValid
    leaf2768InnerLogValid leaf2768CoversExact leaf2768LowerChecked

private noncomputable def leaf2769Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (33/256), chiHi := (67/512) }

private noncomputable def leaf2769Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742203/1073741824) }, vSqrt := { lower := (8191/8192), upper := (13743698739/13743473408) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1601372343/1073741824) }, upper := { exponent := 0, mantissa := (24625/16384) } }, logOuter := sk171LogOuterCertificate, logK := sk171LogKCertificate, logChi := chi203LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (27487172147/27486946816) } }, logDArg := sk171LogDArgCertificate }

private noncomputable def leaf2769InnerLog : WideLogData :=
  innerPair409Data

set_option maxRecDepth 1000000 in
private theorem leaf2769LocalValidity :
    LeafFacts leaf2769Box leaf2769Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2769Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (13743698739/13743473408) }) = true
      norm_num [leaf2769Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2769CertificateValid :
    WideCertificateValid leaf2769Box leaf2769Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk171ValidityFacts chi203ValidityFacts
    leaf2769LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2769CoverageChecked :
    coverageCheck (innerAD leaf2769Box) leaf2769InnerLog = true := by
  rfl'

private theorem leaf2769InnerLogValid :
    leaf2769InnerLog.Valid 8 (innerAD leaf2769Box) :=
  wideLogDataValid_of_cachedCheck endpoint120PositiveFacts
    endpoint49PositiveFacts.valid leaf2769CoverageChecked

private noncomputable def leaf2769InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814609/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2769InputLogOnePlusV_eq :
    leaf2769InputLogOnePlusV = outerEnclosure 24
      (leaf2769Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2769RoundedFacts : LeafRoundedFacts 8
    leaf2769Certificate.logOnePlusV leaf2769InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2769InputLogOnePlusV_eq }

private noncomputable def leaf2769Inputs : Inputs :=
  inputsOfCaches globalInput sk171RoundedInputs
    chi203InputQChi innerPair409Input
    leaf2769InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2769LowerChecked :
    lowerCheck 24 leaf2769Box leaf2769Inputs = true := by
  rfl'

private theorem leaf2769CoversExact : CoversExact 8
    leaf2769Box leaf2769Certificate leaf2769InnerLog leaf2769Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk171RoundedFacts chi203RoundedFacts
    innerPair409RoundedFacts leaf2769RoundedFacts (by rfl)

private theorem leaf2769FlatSound : Sound leaf2769Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2769CertificateValid
    leaf2769InnerLogValid leaf2769CoversExact leaf2769LowerChecked

private noncomputable def leaf2770Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (67/512), chiHi := (17/128) }

private noncomputable def leaf2770Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742205/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68718493695/68717335552) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1609367245/1073741824) }, upper := { exponent := 0, mantissa := (6187/4096) } }, logOuter := sk171LogOuterCertificate, logK := sk171LogKCertificate, logChi := chi204LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137435829247/137434671104) } }, logDArg := sk171LogDArgCertificate }

private noncomputable def leaf2770InnerLog : WideLogData :=
  innerPair409Data

set_option maxRecDepth 1000000 in
private theorem leaf2770LocalValidity :
    LeafFacts leaf2770Box leaf2770Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2770Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68718493695/68717335552) }) = true
      norm_num [leaf2770Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2770CertificateValid :
    WideCertificateValid leaf2770Box leaf2770Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk171ValidityFacts chi204ValidityFacts
    leaf2770LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2770CoverageChecked :
    coverageCheck (innerAD leaf2770Box) leaf2770InnerLog = true := by
  rfl'

private theorem leaf2770InnerLogValid :
    leaf2770InnerLog.Valid 8 (innerAD leaf2770Box) :=
  wideLogDataValid_of_cachedCheck endpoint120PositiveFacts
    endpoint49PositiveFacts.valid leaf2770CoverageChecked

private noncomputable def leaf2770InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814611/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2770InputLogOnePlusV_eq :
    leaf2770InputLogOnePlusV = outerEnclosure 24
      (leaf2770Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2770RoundedFacts : LeafRoundedFacts 8
    leaf2770Certificate.logOnePlusV leaf2770InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2770InputLogOnePlusV_eq }

private noncomputable def leaf2770Inputs : Inputs :=
  inputsOfCaches globalInput sk171RoundedInputs
    chi204InputQChi innerPair409Input
    leaf2770InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2770LowerChecked :
    lowerCheck 24 leaf2770Box leaf2770Inputs = true := by
  rfl'

private theorem leaf2770CoversExact : CoversExact 8
    leaf2770Box leaf2770Certificate leaf2770InnerLog leaf2770Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk171RoundedFacts chi204RoundedFacts
    innerPair409RoundedFacts leaf2770RoundedFacts (by rfl)

private theorem leaf2770FlatSound : Sound leaf2770Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2770CertificateValid
    leaf2770InnerLogValid leaf2770CoversExact leaf2770LowerChecked

private noncomputable def leaf2771Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (1/8), chiHi := (65/512) }

private noncomputable def leaf2771Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742201/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68718493695/68717413376) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1589576585/1073741824) }, upper := { exponent := 0, mantissa := (6111/4096) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi205LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137435907071/137434826752) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf2771InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf2771LocalValidity :
    LeafFacts leaf2771Box leaf2771Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2771Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68718493695/68717413376) }) = true
      norm_num [leaf2771Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2771CertificateValid :
    WideCertificateValid leaf2771Box leaf2771Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi205ValidityFacts
    leaf2771LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2771CoverageChecked :
    coverageCheck (innerAD leaf2771Box) leaf2771InnerLog = true := by
  rfl'

private theorem leaf2771InnerLogValid :
    leaf2771InnerLog.Valid 8 (innerAD leaf2771Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf2771CoverageChecked

private noncomputable def leaf2771InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629213/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2771InputLogOnePlusV_eq :
    leaf2771InputLogOnePlusV = outerEnclosure 24
      (leaf2771Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2771RoundedFacts : LeafRoundedFacts 8
    leaf2771Certificate.logOnePlusV leaf2771InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2771InputLogOnePlusV_eq }

private noncomputable def leaf2771Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi205InputQChi innerPair34Input
    leaf2771InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2771LowerChecked :
    lowerCheck 24 leaf2771Box leaf2771Inputs = true := by
  rfl'

private theorem leaf2771CoversExact : CoversExact 8
    leaf2771Box leaf2771Certificate leaf2771InnerLog leaf2771Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi205RoundedFacts
    innerPair34RoundedFacts leaf2771RoundedFacts (by rfl)

private theorem leaf2771FlatSound : Sound leaf2771Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2771CertificateValid
    leaf2771InnerLogValid leaf2771CoversExact leaf2771LowerChecked

private noncomputable def leaf2772Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (65/512), chiHi := (33/256) }

private noncomputable def leaf2772Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742203/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68718493695/68717381632) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1597637019/1073741824) }, upper := { exponent := 0, mantissa := (3071/2048) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi206LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137435875327/137434763264) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf2772InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf2772LocalValidity :
    LeafFacts leaf2772Box leaf2772Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2772Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68718493695/68717381632) }) = true
      norm_num [leaf2772Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2772CertificateValid :
    WideCertificateValid leaf2772Box leaf2772Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi206ValidityFacts
    leaf2772LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2772CoverageChecked :
    coverageCheck (innerAD leaf2772Box) leaf2772InnerLog = true := by
  rfl'

private theorem leaf2772InnerLogValid :
    leaf2772InnerLog.Valid 8 (innerAD leaf2772Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf2772CoverageChecked

private noncomputable def leaf2772InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (363413/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf2772InputLogOnePlusV_eq :
    leaf2772InputLogOnePlusV = outerEnclosure 24
      (leaf2772Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2772RoundedFacts : LeafRoundedFacts 8
    leaf2772Certificate.logOnePlusV leaf2772InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2772InputLogOnePlusV_eq }

private noncomputable def leaf2772Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi206InputQChi innerPair34Input
    leaf2772InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2772LowerChecked :
    lowerCheck 24 leaf2772Box leaf2772Inputs = true := by
  rfl'

private theorem leaf2772CoversExact : CoversExact 8
    leaf2772Box leaf2772Certificate leaf2772InnerLog leaf2772Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi206RoundedFacts
    innerPair34RoundedFacts leaf2772RoundedFacts (by rfl)

private theorem leaf2772FlatSound : Sound leaf2772Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2772CertificateValid
    leaf2772InnerLogValid leaf2772CoversExact leaf2772LowerChecked

private noncomputable def leaf2773Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (33/256), chiHi := (67/512) }

private noncomputable def leaf2773Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742205/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22906164565/22905783296) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1605697453/1073741824) }, upper := { exponent := 0, mantissa := (6173/4096) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi203LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45811947861/45811566592) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf2773InnerLog : WideLogData :=
  innerPair409Data

set_option maxRecDepth 1000000 in
private theorem leaf2773LocalValidity :
    LeafFacts leaf2773Box leaf2773Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2773Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22906164565/22905783296) }) = true
      norm_num [leaf2773Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2773CertificateValid :
    WideCertificateValid leaf2773Box leaf2773Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi203ValidityFacts
    leaf2773LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2773CoverageChecked :
    coverageCheck (innerAD leaf2773Box) leaf2773InnerLog = true := by
  rfl'

private theorem leaf2773InnerLogValid :
    leaf2773InnerLog.Valid 8 (innerAD leaf2773Box) :=
  wideLogDataValid_of_cachedCheck endpoint120PositiveFacts
    endpoint49PositiveFacts.valid leaf2773CoverageChecked

private noncomputable def leaf2773InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907305/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2773InputLogOnePlusV_eq :
    leaf2773InputLogOnePlusV = outerEnclosure 24
      (leaf2773Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2773RoundedFacts : LeafRoundedFacts 8
    leaf2773Certificate.logOnePlusV leaf2773InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2773InputLogOnePlusV_eq }

private noncomputable def leaf2773Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi203InputQChi innerPair409Input
    leaf2773InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2773LowerChecked :
    lowerCheck 24 leaf2773Box leaf2773Inputs = true := by
  rfl'

private theorem leaf2773CoversExact : CoversExact 8
    leaf2773Box leaf2773Certificate leaf2773InnerLog leaf2773Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi203RoundedFacts
    innerPair409RoundedFacts leaf2773RoundedFacts (by rfl)

private theorem leaf2773FlatSound : Sound leaf2773Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2773CertificateValid
    leaf2773InnerLogValid leaf2773CoversExact leaf2773LowerChecked

private noncomputable def leaf2774Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (67/512), chiHi := (17/128) }

private noncomputable def leaf2774Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742207/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68718493695/68717318144) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1613757887/1073741824) }, upper := { exponent := 0, mantissa := (1551/1024) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi204LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137435811839/137434636288) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf2774InnerLog : WideLogData :=
  innerPair47Data

set_option maxRecDepth 1000000 in
private theorem leaf2774LocalValidity :
    LeafFacts leaf2774Box leaf2774Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2774Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68718493695/68717318144) }) = true
      norm_num [leaf2774Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2774CertificateValid :
    WideCertificateValid leaf2774Box leaf2774Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi204ValidityFacts
    leaf2774LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2774CoverageChecked :
    coverageCheck (innerAD leaf2774Box) leaf2774InnerLog = true := by
  rfl'

private theorem leaf2774InnerLogValid :
    leaf2774InnerLog.Valid 8 (innerAD leaf2774Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint49PositiveFacts.valid leaf2774CoverageChecked

private noncomputable def leaf2774InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453653/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf2774InputLogOnePlusV_eq :
    leaf2774InputLogOnePlusV = outerEnclosure 24
      (leaf2774Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2774RoundedFacts : LeafRoundedFacts 8
    leaf2774Certificate.logOnePlusV leaf2774InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2774InputLogOnePlusV_eq }

private noncomputable def leaf2774Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi204InputQChi innerPair47Input
    leaf2774InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2774LowerChecked :
    lowerCheck 24 leaf2774Box leaf2774Inputs = true := by
  rfl'

private theorem leaf2774CoversExact : CoversExact 8
    leaf2774Box leaf2774Certificate leaf2774InnerLog leaf2774Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi204RoundedFacts
    innerPair47RoundedFacts leaf2774RoundedFacts (by rfl)

private theorem leaf2774FlatSound : Sound leaf2774Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2774CertificateValid
    leaf2774InnerLogValid leaf2774CoversExact leaf2774LowerChecked

private noncomputable def leaf2775Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (245/64), chiLo := (17/128), chiHi := (35/256) }

private noncomputable def leaf2775Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742383/1073741824) }, vSqrt := { lower := (8191/8192), upper := (15270769095/15270507008) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1617361971/1073741824) }, upper := { exponent := 0, mantissa := (24959/16384) } }, logOuter := sk229LogOuterCertificate, logK := sk229LogKCertificate, logChi := chi179LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (30541276103/30541014016) } }, logDArg := sk229LogDArgCertificate }

private noncomputable def leaf2775InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2775LocalValidity :
    LeafFacts leaf2775Box leaf2775Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2775Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (15270769095/15270507008) }) = true
      norm_num [leaf2775Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2775CertificateValid :
    WideCertificateValid leaf2775Box leaf2775Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk229ValidityFacts chi179ValidityFacts
    leaf2775LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2775CoverageChecked :
    coverageCheck (innerAD leaf2775Box) leaf2775InnerLog = true := by
  rfl'

private theorem leaf2775InnerLogValid :
    leaf2775InnerLog.Valid 8 (innerAD leaf2775Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2775CoverageChecked

private noncomputable def leaf2775InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629225/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2775InputLogOnePlusV_eq :
    leaf2775InputLogOnePlusV = outerEnclosure 24
      (leaf2775Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2775RoundedFacts : LeafRoundedFacts 8
    leaf2775Certificate.logOnePlusV leaf2775InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2775InputLogOnePlusV_eq }

private noncomputable def leaf2775Inputs : Inputs :=
  inputsOfCaches globalInput sk229RoundedInputs
    chi179InputQChi innerPair40Input
    leaf2775InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2775LowerChecked :
    lowerCheck 24 leaf2775Box leaf2775Inputs = true := by
  rfl'

private theorem leaf2775CoversExact : CoversExact 8
    leaf2775Box leaf2775Certificate leaf2775InnerLog leaf2775Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk229RoundedFacts chi179RoundedFacts
    innerPair40RoundedFacts leaf2775RoundedFacts (by rfl)

private theorem leaf2775FlatSound : Sound leaf2775Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2775CertificateValid
    leaf2775InnerLogValid leaf2775CoversExact leaf2775LowerChecked

private noncomputable def leaf2776Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (245/64), kHi := (123/32), chiLo := (17/128), chiHi := (35/256) }

private noncomputable def leaf2776Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742385/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434545152) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1619590057/1073741824) }, upper := { exponent := 0, mantissa := (12497/8192) } }, logOuter := sk230LogOuterCertificate, logK := sk230LogKCertificate, logChi := chi179LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871467007/274869090304) } }, logDArg := sk230LogDArgCertificate }

private noncomputable def leaf2776InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2776LocalValidity :
    LeafFacts leaf2776Box leaf2776Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2776Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434545152) }) = true
      norm_num [leaf2776Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2776CertificateValid :
    WideCertificateValid leaf2776Box leaf2776Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk230ValidityFacts chi179ValidityFacts
    leaf2776LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2776CoverageChecked :
    coverageCheck (innerAD leaf2776Box) leaf2776InnerLog = true := by
  rfl'

private theorem leaf2776InnerLogValid :
    leaf2776InnerLog.Valid 8 (innerAD leaf2776Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2776CoverageChecked

private noncomputable def leaf2776InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814613/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2776InputLogOnePlusV_eq :
    leaf2776InputLogOnePlusV = outerEnclosure 24
      (leaf2776Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2776RoundedFacts : LeafRoundedFacts 8
    leaf2776Certificate.logOnePlusV leaf2776InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2776InputLogOnePlusV_eq }

private noncomputable def leaf2776Inputs : Inputs :=
  inputsOfCaches globalInput sk230RoundedInputs
    chi179InputQChi innerPair40Input
    leaf2776InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2776LowerChecked :
    lowerCheck 24 leaf2776Box leaf2776Inputs = true := by
  rfl'

private theorem leaf2776CoversExact : CoversExact 8
    leaf2776Box leaf2776Certificate leaf2776InnerLog leaf2776Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk230RoundedFacts chi179RoundedFacts
    innerPair40RoundedFacts leaf2776RoundedFacts (by rfl)

private theorem leaf2776FlatSound : Sound leaf2776Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2776CertificateValid
    leaf2776InnerLogValid leaf2776CoversExact leaf2776LowerChecked

private noncomputable def leaf2777Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (245/64), chiLo := (35/256), chiHi := (9/64) }

private noncomputable def leaf2777Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742385/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434437632) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1633351777/1073741824) }, upper := { exponent := 0, mantissa := (6301/4096) } }, logOuter := sk229LogOuterCertificate, logK := sk229LogKCertificate, logChi := chi180LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871359487/274868875264) } }, logDArg := sk229LogDArgCertificate }

private noncomputable def leaf2777InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2777LocalValidity :
    LeafFacts leaf2777Box leaf2777Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2777Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434437632) }) = true
      norm_num [leaf2777Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2777CertificateValid :
    WideCertificateValid leaf2777Box leaf2777Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk229ValidityFacts chi180ValidityFacts
    leaf2777LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2777CoverageChecked :
    coverageCheck (innerAD leaf2777Box) leaf2777InnerLog = true := by
  rfl'

private theorem leaf2777InnerLogValid :
    leaf2777InnerLog.Valid 8 (innerAD leaf2777Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2777CoverageChecked

private noncomputable def leaf2777InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726827/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf2777InputLogOnePlusV_eq :
    leaf2777InputLogOnePlusV = outerEnclosure 24
      (leaf2777Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2777RoundedFacts : LeafRoundedFacts 8
    leaf2777Certificate.logOnePlusV leaf2777InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2777InputLogOnePlusV_eq }

private noncomputable def leaf2777Inputs : Inputs :=
  inputsOfCaches globalInput sk229RoundedInputs
    chi180InputQChi innerPair40Input
    leaf2777InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2777LowerChecked :
    lowerCheck 24 leaf2777Box leaf2777Inputs = true := by
  rfl'

private theorem leaf2777CoversExact : CoversExact 8
    leaf2777Box leaf2777Certificate leaf2777InnerLog leaf2777Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk229RoundedFacts chi180RoundedFacts
    innerPair40RoundedFacts leaf2777RoundedFacts (by rfl)

private theorem leaf2777FlatSound : Sound leaf2777Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2777CertificateValid
    leaf2777InnerLogValid leaf2777CoversExact leaf2777LowerChecked

private noncomputable def leaf2778Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (245/64), kHi := (123/32), chiLo := (35/256), chiHi := (9/64) }

private noncomputable def leaf2778Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742387/1073741824) }, vSqrt := { lower := (8191/8192), upper := (1616904963/1616875520) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1635645395/1073741824) }, upper := { exponent := 0, mantissa := (3155/2048) } }, logOuter := sk230LogOuterCertificate, logK := sk230LogKCertificate, logChi := chi180LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (3233780483/3233751040) } }, logDArg := sk230LogDArgCertificate }

private noncomputable def leaf2778InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2778LocalValidity :
    LeafFacts leaf2778Box leaf2778Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2778Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (1616904963/1616875520) }) = true
      norm_num [leaf2778Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2778CertificateValid :
    WideCertificateValid leaf2778Box leaf2778Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk230ValidityFacts chi180ValidityFacts
    leaf2778LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2778CoverageChecked :
    coverageCheck (innerAD leaf2778Box) leaf2778InnerLog = true := by
  rfl'

private theorem leaf2778InnerLogValid :
    leaf2778InnerLog.Valid 8 (innerAD leaf2778Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2778CoverageChecked

private noncomputable def leaf2778InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629233/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2778InputLogOnePlusV_eq :
    leaf2778InputLogOnePlusV = outerEnclosure 24
      (leaf2778Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2778RoundedFacts : LeafRoundedFacts 8
    leaf2778Certificate.logOnePlusV leaf2778InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2778InputLogOnePlusV_eq }

private noncomputable def leaf2778Inputs : Inputs :=
  inputsOfCaches globalInput sk230RoundedInputs
    chi180InputQChi innerPair40Input
    leaf2778InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2778LowerChecked :
    lowerCheck 24 leaf2778Box leaf2778Inputs = true := by
  rfl'

private theorem leaf2778CoversExact : CoversExact 8
    leaf2778Box leaf2778Certificate leaf2778InnerLog leaf2778Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk230RoundedFacts chi180RoundedFacts
    innerPair40RoundedFacts leaf2778RoundedFacts (by rfl)

private theorem leaf2778FlatSound : Sound leaf2778Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2778CertificateValid
    leaf2778InnerLogValid leaf2778CoversExact leaf2778LowerChecked

private noncomputable def leaf2779Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (17/128), chiHi := (69/512) }

private noncomputable def leaf2779Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742209/1073741824) }, vSqrt := { lower := (8191/8192), upper := (13743698739/13743457280) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1621818321/1073741824) }, upper := { exponent := 0, mantissa := (6235/4096) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi207LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (27487156019/27486914560) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf2779InnerLog : WideLogData :=
  innerPair44Data

set_option maxRecDepth 1000000 in
private theorem leaf2779LocalValidity :
    LeafFacts leaf2779Box leaf2779Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2779Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (13743698739/13743457280) }) = true
      norm_num [leaf2779Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2779CertificateValid :
    WideCertificateValid leaf2779Box leaf2779Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi207ValidityFacts
    leaf2779LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2779CoverageChecked :
    coverageCheck (innerAD leaf2779Box) leaf2779InnerLog = true := by
  rfl'

private theorem leaf2779InnerLogValid :
    leaf2779InnerLog.Valid 8 (innerAD leaf2779Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint19PositiveFacts.valid leaf2779CoverageChecked

private noncomputable def leaf2779InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907307/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2779InputLogOnePlusV_eq :
    leaf2779InputLogOnePlusV = outerEnclosure 24
      (leaf2779Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2779RoundedFacts : LeafRoundedFacts 8
    leaf2779Certificate.logOnePlusV leaf2779InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2779InputLogOnePlusV_eq }

private noncomputable def leaf2779Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi207InputQChi innerPair44Input
    leaf2779InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2779LowerChecked :
    lowerCheck 24 leaf2779Box leaf2779Inputs = true := by
  rfl'

private theorem leaf2779CoversExact : CoversExact 8
    leaf2779Box leaf2779Certificate leaf2779InnerLog leaf2779Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi207RoundedFacts
    innerPair44RoundedFacts leaf2779RoundedFacts (by rfl)

private theorem leaf2779FlatSound : Sound leaf2779Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2779CertificateValid
    leaf2779InnerLogValid leaf2779CoversExact leaf2779LowerChecked

private noncomputable def leaf2780Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (69/512), chiHi := (35/256) }

private noncomputable def leaf2780Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742211/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22906164565/22905751552) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1629878755/1073741824) }, upper := { exponent := 0, mantissa := (3133/2048) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi208LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45811916117/45811503104) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf2780InnerLog : WideLogData :=
  innerPair176Data

set_option maxRecDepth 1000000 in
private theorem leaf2780LocalValidity :
    LeafFacts leaf2780Box leaf2780Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2780Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22906164565/22905751552) }) = true
      norm_num [leaf2780Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2780CertificateValid :
    WideCertificateValid leaf2780Box leaf2780Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi208ValidityFacts
    leaf2780LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2780CoverageChecked :
    coverageCheck (innerAD leaf2780Box) leaf2780InnerLog = true := by
  rfl'

private theorem leaf2780InnerLogValid :
    leaf2780InnerLog.Valid 8 (innerAD leaf2780Box) :=
  wideLogDataValid_of_cachedCheck endpoint49PositiveFacts
    endpoint19PositiveFacts.valid leaf2780CoverageChecked

private noncomputable def leaf2780InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726827/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf2780InputLogOnePlusV_eq :
    leaf2780InputLogOnePlusV = outerEnclosure 24
      (leaf2780Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2780RoundedFacts : LeafRoundedFacts 8
    leaf2780Certificate.logOnePlusV leaf2780InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2780InputLogOnePlusV_eq }

private noncomputable def leaf2780Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi208InputQChi innerPair176Input
    leaf2780InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2780LowerChecked :
    lowerCheck 24 leaf2780Box leaf2780Inputs = true := by
  rfl'

private theorem leaf2780CoversExact : CoversExact 8
    leaf2780Box leaf2780Certificate leaf2780InnerLog leaf2780Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi208RoundedFacts
    innerPair176RoundedFacts leaf2780RoundedFacts (by rfl)

private theorem leaf2780FlatSound : Sound leaf2780Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2780CertificateValid
    leaf2780InnerLogValid leaf2780CoversExact leaf2780LowerChecked

private noncomputable def leaf2781Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (247/64), chiLo := (35/256), chiHi := (9/64) }

private noncomputable def leaf2781Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742389/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434400768) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1637939013/1073741824) }, upper := { exponent := 0, mantissa := (6319/4096) } }, logOuter := sk231LogOuterCertificate, logK := sk231LogKCertificate, logChi := chi180LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871322623/274868801536) } }, logDArg := sk231LogDArgCertificate }

private noncomputable def leaf2781InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2781LocalValidity :
    LeafFacts leaf2781Box leaf2781Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2781Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434400768) }) = true
      norm_num [leaf2781Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2781CertificateValid :
    WideCertificateValid leaf2781Box leaf2781Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk231ValidityFacts chi180ValidityFacts
    leaf2781LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2781CoverageChecked :
    coverageCheck (innerAD leaf2781Box) leaf2781InnerLog = true := by
  rfl'

private theorem leaf2781InnerLogValid :
    leaf2781InnerLog.Valid 8 (innerAD leaf2781Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2781CoverageChecked

private noncomputable def leaf2781InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629235/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2781InputLogOnePlusV_eq :
    leaf2781InputLogOnePlusV = outerEnclosure 24
      (leaf2781Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2781RoundedFacts : LeafRoundedFacts 8
    leaf2781Certificate.logOnePlusV leaf2781InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2781InputLogOnePlusV_eq }

private noncomputable def leaf2781Inputs : Inputs :=
  inputsOfCaches globalInput sk231RoundedInputs
    chi180InputQChi innerPair40Input
    leaf2781InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2781LowerChecked :
    lowerCheck 24 leaf2781Box leaf2781Inputs = true := by
  rfl'

private theorem leaf2781CoversExact : CoversExact 8
    leaf2781Box leaf2781Certificate leaf2781InnerLog leaf2781Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk231RoundedFacts chi180RoundedFacts
    innerPair40RoundedFacts leaf2781RoundedFacts (by rfl)

private theorem leaf2781FlatSound : Sound leaf2781Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2781CertificateValid
    leaf2781InnerLogValid leaf2781CoversExact leaf2781LowerChecked

private noncomputable def leaf2782Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (247/64), kHi := (31/8), chiLo := (35/256), chiHi := (9/64) }

private noncomputable def leaf2782Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742391/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434382336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1640232631/1073741824) }, upper := { exponent := 0, mantissa := (791/512) } }, logOuter := sk232LogOuterCertificate, logK := sk232LogKCertificate, logChi := chi180LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871304191/274868764672) } }, logDArg := sk232LogDArgCertificate }

private noncomputable def leaf2782InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2782LocalValidity :
    LeafFacts leaf2782Box leaf2782Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2782Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434382336) }) = true
      norm_num [leaf2782Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2782CertificateValid :
    WideCertificateValid leaf2782Box leaf2782Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk232ValidityFacts chi180ValidityFacts
    leaf2782LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2782CoverageChecked :
    coverageCheck (innerAD leaf2782Box) leaf2782InnerLog = true := by
  rfl'

private theorem leaf2782InnerLogValid :
    leaf2782InnerLog.Valid 8 (innerAD leaf2782Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2782CoverageChecked

private noncomputable def leaf2782InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907309/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2782InputLogOnePlusV_eq :
    leaf2782InputLogOnePlusV = outerEnclosure 24
      (leaf2782Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2782RoundedFacts : LeafRoundedFacts 8
    leaf2782Certificate.logOnePlusV leaf2782InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2782InputLogOnePlusV_eq }

private noncomputable def leaf2782Inputs : Inputs :=
  inputsOfCaches globalInput sk232RoundedInputs
    chi180InputQChi innerPair40Input
    leaf2782InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2782LowerChecked :
    lowerCheck 24 leaf2782Box leaf2782Inputs = true := by
  rfl'

private theorem leaf2782CoversExact : CoversExact 8
    leaf2782Box leaf2782Certificate leaf2782InnerLog leaf2782Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk232RoundedFacts chi180RoundedFacts
    innerPair40RoundedFacts leaf2782RoundedFacts (by rfl)

private theorem leaf2782FlatSound : Sound leaf2782Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2782CertificateValid
    leaf2782InnerLogValid leaf2782CoversExact leaf2782LowerChecked

private noncomputable def leaf2783Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (241/64), chiLo := (9/64), chiHi := (37/256) }

private noncomputable def leaf2783Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742379/1073741824) }, vSqrt := { lower := (8191/8192), upper := (15270769095/15270487552) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1639904983/1073741824) }, upper := { exponent := 0, mantissa := (25301/16384) } }, logOuter := sk225LogOuterCertificate, logK := sk225LogKCertificate, logChi := chi175LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (30541256647/30540975104) } }, logDArg := sk225LogDArgCertificate }

private noncomputable def leaf2783InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2783LocalValidity :
    LeafFacts leaf2783Box leaf2783Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2783Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (15270769095/15270487552) }) = true
      norm_num [leaf2783Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2783CertificateValid :
    WideCertificateValid leaf2783Box leaf2783Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk225ValidityFacts chi175ValidityFacts
    leaf2783LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2783CoverageChecked :
    coverageCheck (innerAD leaf2783Box) leaf2783InnerLog = true := by
  rfl'

private theorem leaf2783InnerLogValid :
    leaf2783InnerLog.Valid 8 (innerAD leaf2783Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2783CoverageChecked

private noncomputable def leaf2783InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629235/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2783InputLogOnePlusV_eq :
    leaf2783InputLogOnePlusV = outerEnclosure 24
      (leaf2783Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2783RoundedFacts : LeafRoundedFacts 8
    leaf2783Certificate.logOnePlusV leaf2783InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2783InputLogOnePlusV_eq }

private noncomputable def leaf2783Inputs : Inputs :=
  inputsOfCaches globalInput sk225RoundedInputs
    chi175InputQChi innerPair40Input
    leaf2783InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2783LowerChecked :
    lowerCheck 24 leaf2783Box leaf2783Inputs = true := by
  rfl'

private theorem leaf2783CoversExact : CoversExact 8
    leaf2783Box leaf2783Certificate leaf2783InnerLog leaf2783Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk225RoundedFacts chi175RoundedFacts
    innerPair40RoundedFacts leaf2783RoundedFacts (by rfl)

private theorem leaf2783FlatSound : Sound leaf2783Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2783CertificateValid
    leaf2783InnerLogValid leaf2783CoversExact leaf2783LowerChecked

private noncomputable def leaf2784Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (241/64), kHi := (121/32), chiLo := (9/64), chiHi := (37/256) }

private noncomputable def leaf2784Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742381/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434369024) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1642264133/1073741824) }, upper := { exponent := 0, mantissa := (12669/8192) } }, logOuter := sk226LogOuterCertificate, logK := sk226LogKCertificate, logChi := chi175LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871290879/274868738048) } }, logDArg := sk226LogDArgCertificate }

private noncomputable def leaf2784InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2784LocalValidity :
    LeafFacts leaf2784Box leaf2784Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2784Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434369024) }) = true
      norm_num [leaf2784Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2784CertificateValid :
    WideCertificateValid leaf2784Box leaf2784Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk226ValidityFacts chi175ValidityFacts
    leaf2784LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2784CoverageChecked :
    coverageCheck (innerAD leaf2784Box) leaf2784InnerLog = true := by
  rfl'

private theorem leaf2784InnerLogValid :
    leaf2784InnerLog.Valid 8 (innerAD leaf2784Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2784CoverageChecked

private noncomputable def leaf2784InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629237/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2784InputLogOnePlusV_eq :
    leaf2784InputLogOnePlusV = outerEnclosure 24
      (leaf2784Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2784RoundedFacts : LeafRoundedFacts 8
    leaf2784Certificate.logOnePlusV leaf2784InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2784InputLogOnePlusV_eq }

private noncomputable def leaf2784Inputs : Inputs :=
  inputsOfCaches globalInput sk226RoundedInputs
    chi175InputQChi innerPair40Input
    leaf2784InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2784LowerChecked :
    lowerCheck 24 leaf2784Box leaf2784Inputs = true := by
  rfl'

private theorem leaf2784CoversExact : CoversExact 8
    leaf2784Box leaf2784Certificate leaf2784InnerLog leaf2784Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk226RoundedFacts chi175RoundedFacts
    innerPair40RoundedFacts leaf2784RoundedFacts (by rfl)

private theorem leaf2784FlatSound : Sound leaf2784Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2784CertificateValid
    leaf2784InnerLogValid leaf2784CoversExact leaf2784LowerChecked

private noncomputable def leaf2785Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (241/64), chiLo := (37/256), chiHi := (19/128) }

private noncomputable def leaf2785Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742381/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434264576) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1655632661/1073741824) }, upper := { exponent := 0, mantissa := (12771/8192) } }, logOuter := sk225LogOuterCertificate, logK := sk225LogKCertificate, logChi := chi176LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871186431/274868529152) } }, logDArg := sk225LogDArgCertificate }

private noncomputable def leaf2785InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2785LocalValidity :
    LeafFacts leaf2785Box leaf2785Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2785Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434264576) }) = true
      norm_num [leaf2785Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2785CertificateValid :
    WideCertificateValid leaf2785Box leaf2785Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk225ValidityFacts chi176ValidityFacts
    leaf2785LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2785CoverageChecked :
    coverageCheck (innerAD leaf2785Box) leaf2785InnerLog = true := by
  rfl'

private theorem leaf2785InnerLogValid :
    leaf2785InnerLog.Valid 8 (innerAD leaf2785Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2785CoverageChecked

private noncomputable def leaf2785InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629243/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2785InputLogOnePlusV_eq :
    leaf2785InputLogOnePlusV = outerEnclosure 24
      (leaf2785Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2785RoundedFacts : LeafRoundedFacts 8
    leaf2785Certificate.logOnePlusV leaf2785InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2785InputLogOnePlusV_eq }

private noncomputable def leaf2785Inputs : Inputs :=
  inputsOfCaches globalInput sk225RoundedInputs
    chi176InputQChi innerPair40Input
    leaf2785InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2785LowerChecked :
    lowerCheck 24 leaf2785Box leaf2785Inputs = true := by
  rfl'

private theorem leaf2785CoversExact : CoversExact 8
    leaf2785Box leaf2785Certificate leaf2785InnerLog leaf2785Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk225RoundedFacts chi176RoundedFacts
    innerPair40RoundedFacts leaf2785RoundedFacts (by rfl)

private theorem leaf2785FlatSound : Sound leaf2785Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2785CertificateValid
    leaf2785InnerLogValid leaf2785CoversExact leaf2785LowerChecked

private noncomputable def leaf2786Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (241/64), kHi := (121/32), chiLo := (37/256), chiHi := (19/128) }

private noncomputable def leaf2786Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742383/1073741824) }, vSqrt := { lower := (8191/8192), upper := (179656107/179652608) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1658057343/1073741824) }, upper := { exponent := 0, mantissa := (6395/4096) } }, logOuter := sk226LogOuterCertificate, logK := sk226LogKCertificate, logChi := chi176LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (359308715/359305216) } }, logDArg := sk226LogDArgCertificate }

private noncomputable def leaf2786InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2786LocalValidity :
    LeafFacts leaf2786Box leaf2786Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2786Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (179656107/179652608) }) = true
      norm_num [leaf2786Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2786CertificateValid :
    WideCertificateValid leaf2786Box leaf2786Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk226ValidityFacts chi176ValidityFacts
    leaf2786LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2786CoverageChecked :
    coverageCheck (innerAD leaf2786Box) leaf2786InnerLog = true := by
  rfl'

private theorem leaf2786InnerLogValid :
    leaf2786InnerLog.Valid 8 (innerAD leaf2786Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2786CoverageChecked

private noncomputable def leaf2786InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907311/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2786InputLogOnePlusV_eq :
    leaf2786InputLogOnePlusV = outerEnclosure 24
      (leaf2786Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2786RoundedFacts : LeafRoundedFacts 8
    leaf2786Certificate.logOnePlusV leaf2786InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2786InputLogOnePlusV_eq }

private noncomputable def leaf2786Inputs : Inputs :=
  inputsOfCaches globalInput sk226RoundedInputs
    chi176InputQChi innerPair40Input
    leaf2786InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2786LowerChecked :
    lowerCheck 24 leaf2786Box leaf2786Inputs = true := by
  rfl'

private theorem leaf2786CoversExact : CoversExact 8
    leaf2786Box leaf2786Certificate leaf2786InnerLog leaf2786Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk226RoundedFacts chi176RoundedFacts
    innerPair40RoundedFacts leaf2786RoundedFacts (by rfl)

private theorem leaf2786FlatSound : Sound leaf2786Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2786CertificateValid
    leaf2786InnerLogValid leaf2786CoversExact leaf2786LowerChecked

private noncomputable def leaf2787Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (243/64), chiLo := (9/64), chiHi := (37/256) }

private noncomputable def leaf2787Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742383/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486870016) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1644623283/1073741824) }, upper := { exponent := 0, mantissa := (25375/16384) } }, logOuter := sk227LogOuterCertificate, logK := sk227LogKCertificate, logChi := chi175LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54974254387/54973740032) } }, logDArg := sk227LogDArgCertificate }

private noncomputable def leaf2787InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2787LocalValidity :
    LeafFacts leaf2787Box leaf2787Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2787Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486870016) }) = true
      norm_num [leaf2787Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2787CertificateValid :
    WideCertificateValid leaf2787Box leaf2787Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk227ValidityFacts chi175ValidityFacts
    leaf2787LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2787CoverageChecked :
    coverageCheck (innerAD leaf2787Box) leaf2787InnerLog = true := by
  rfl'

private theorem leaf2787InnerLogValid :
    leaf2787InnerLog.Valid 8 (innerAD leaf2787Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2787CoverageChecked

private noncomputable def leaf2787InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814619/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2787InputLogOnePlusV_eq :
    leaf2787InputLogOnePlusV = outerEnclosure 24
      (leaf2787Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2787RoundedFacts : LeafRoundedFacts 8
    leaf2787Certificate.logOnePlusV leaf2787InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2787InputLogOnePlusV_eq }

private noncomputable def leaf2787Inputs : Inputs :=
  inputsOfCaches globalInput sk227RoundedInputs
    chi175InputQChi innerPair40Input
    leaf2787InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2787LowerChecked :
    lowerCheck 24 leaf2787Box leaf2787Inputs = true := by
  rfl'

private theorem leaf2787CoversExact : CoversExact 8
    leaf2787Box leaf2787Certificate leaf2787InnerLog leaf2787Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk227RoundedFacts chi175RoundedFacts
    innerPair40RoundedFacts leaf2787RoundedFacts (by rfl)

private theorem leaf2787FlatSound : Sound leaf2787Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2787CertificateValid
    leaf2787InnerLogValid leaf2787CoversExact leaf2787LowerChecked

private noncomputable def leaf2788Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (243/64), kHi := (61/16), chiLo := (9/64), chiHi := (37/256) }

private noncomputable def leaf2788Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742385/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45811443712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1646982433/1073741824) }, upper := { exponent := 0, mantissa := (6353/4096) } }, logOuter := sk228LogOuterCertificate, logK := sk228LogKCertificate, logChi := chi175LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623750997/91622887424) } }, logDArg := sk228LogDArgCertificate }

private noncomputable def leaf2788InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2788LocalValidity :
    LeafFacts leaf2788Box leaf2788Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2788Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45811443712) }) = true
      norm_num [leaf2788Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2788CertificateValid :
    WideCertificateValid leaf2788Box leaf2788Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk228ValidityFacts chi175ValidityFacts
    leaf2788LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2788CoverageChecked :
    coverageCheck (innerAD leaf2788Box) leaf2788InnerLog = true := by
  rfl'

private theorem leaf2788InnerLogValid :
    leaf2788InnerLog.Valid 8 (innerAD leaf2788Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2788CoverageChecked

private noncomputable def leaf2788InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629239/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2788InputLogOnePlusV_eq :
    leaf2788InputLogOnePlusV = outerEnclosure 24
      (leaf2788Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2788RoundedFacts : LeafRoundedFacts 8
    leaf2788Certificate.logOnePlusV leaf2788InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2788InputLogOnePlusV_eq }

private noncomputable def leaf2788Inputs : Inputs :=
  inputsOfCaches globalInput sk228RoundedInputs
    chi175InputQChi innerPair40Input
    leaf2788InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2788LowerChecked :
    lowerCheck 24 leaf2788Box leaf2788Inputs = true := by
  rfl'

private theorem leaf2788CoversExact : CoversExact 8
    leaf2788Box leaf2788Certificate leaf2788InnerLog leaf2788Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk228RoundedFacts chi175RoundedFacts
    innerPair40RoundedFacts leaf2788RoundedFacts (by rfl)

private theorem leaf2788FlatSound : Sound leaf2788Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2788CertificateValid
    leaf2788InnerLogValid leaf2788CoversExact leaf2788LowerChecked

private noncomputable def leaf2789Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (243/64), chiLo := (37/256), chiHi := (19/128) }

private noncomputable def leaf2789Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742385/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434225664) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1660482025/1073741824) }, upper := { exponent := 0, mantissa := (12809/8192) } }, logOuter := sk227LogOuterCertificate, logK := sk227LogKCertificate, logChi := chi176LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871147519/274868451328) } }, logDArg := sk227LogDArgCertificate }

private noncomputable def leaf2789InnerLog : WideLogData :=
  innerPair87Data

set_option maxRecDepth 1000000 in
private theorem leaf2789LocalValidity :
    LeafFacts leaf2789Box leaf2789Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2789Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434225664) }) = true
      norm_num [leaf2789Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2789CertificateValid :
    WideCertificateValid leaf2789Box leaf2789Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk227ValidityFacts chi176ValidityFacts
    leaf2789LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2789CoverageChecked :
    coverageCheck (innerAD leaf2789Box) leaf2789InnerLog = true := by
  rfl'

private theorem leaf2789InnerLogValid :
    leaf2789InnerLog.Valid 8 (innerAD leaf2789Box) :=
  wideLogDataValid_of_cachedCheck endpoint19PositiveFacts
    endpoint47PositiveFacts.valid leaf2789CoverageChecked

private noncomputable def leaf2789InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629245/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2789InputLogOnePlusV_eq :
    leaf2789InputLogOnePlusV = outerEnclosure 24
      (leaf2789Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2789RoundedFacts : LeafRoundedFacts 8
    leaf2789Certificate.logOnePlusV leaf2789InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2789InputLogOnePlusV_eq }

private noncomputable def leaf2789Inputs : Inputs :=
  inputsOfCaches globalInput sk227RoundedInputs
    chi176InputQChi innerPair87Input
    leaf2789InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2789LowerChecked :
    lowerCheck 24 leaf2789Box leaf2789Inputs = true := by
  rfl'

private theorem leaf2789CoversExact : CoversExact 8
    leaf2789Box leaf2789Certificate leaf2789InnerLog leaf2789Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk227RoundedFacts chi176RoundedFacts
    innerPair87RoundedFacts leaf2789RoundedFacts (by rfl)

private theorem leaf2789FlatSound : Sound leaf2789Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2789CertificateValid
    leaf2789InnerLogValid leaf2789CoversExact leaf2789LowerChecked

private noncomputable def leaf2790Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (243/64), kHi := (61/16), chiLo := (37/256), chiHi := (19/128) }

private noncomputable def leaf2790Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742387/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434206208) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1662906707/1073741824) }, upper := { exponent := 0, mantissa := (3207/2048) } }, logOuter := sk228LogOuterCertificate, logK := sk228LogKCertificate, logChi := chi176LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871128063/274868412416) } }, logDArg := sk228LogDArgCertificate }

private noncomputable def leaf2790InnerLog : WideLogData :=
  innerPair156Data

set_option maxRecDepth 1000000 in
private theorem leaf2790LocalValidity :
    LeafFacts leaf2790Box leaf2790Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2790Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434206208) }) = true
      norm_num [leaf2790Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2790CertificateValid :
    WideCertificateValid leaf2790Box leaf2790Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk228ValidityFacts chi176ValidityFacts
    leaf2790LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2790CoverageChecked :
    coverageCheck (innerAD leaf2790Box) leaf2790InnerLog = true := by
  rfl'

private theorem leaf2790InnerLogValid :
    leaf2790InnerLog.Valid 8 (innerAD leaf2790Box) :=
  wideLogDataValid_of_cachedCheck endpoint43PositiveFacts
    endpoint47PositiveFacts.valid leaf2790CoverageChecked

private noncomputable def leaf2790InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814623/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2790InputLogOnePlusV_eq :
    leaf2790InputLogOnePlusV = outerEnclosure 24
      (leaf2790Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2790RoundedFacts : LeafRoundedFacts 8
    leaf2790Certificate.logOnePlusV leaf2790InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2790InputLogOnePlusV_eq }

private noncomputable def leaf2790Inputs : Inputs :=
  inputsOfCaches globalInput sk228RoundedInputs
    chi176InputQChi innerPair156Input
    leaf2790InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2790LowerChecked :
    lowerCheck 24 leaf2790Box leaf2790Inputs = true := by
  rfl'

private theorem leaf2790CoversExact : CoversExact 8
    leaf2790Box leaf2790Certificate leaf2790InnerLog leaf2790Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk228RoundedFacts chi176RoundedFacts
    innerPair156RoundedFacts leaf2790RoundedFacts (by rfl)

private theorem leaf2790FlatSound : Sound leaf2790Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2790CertificateValid
    leaf2790InnerLogValid leaf2790CoversExact leaf2790LowerChecked

private noncomputable def leaf2791Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (241/64), chiLo := (19/128), chiHi := (39/256) }

private noncomputable def leaf2791Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742383/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434141184) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1671360339/1073741824) }, upper := { exponent := 0, mantissa := (25783/16384) } }, logOuter := sk225LogOuterCertificate, logK := sk225LogKCertificate, logChi := chi177LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871063039/274868282368) } }, logDArg := sk225LogDArgCertificate }

private noncomputable def leaf2791InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf2791LocalValidity :
    LeafFacts leaf2791Box leaf2791Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2791Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434141184) }) = true
      norm_num [leaf2791Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2791CertificateValid :
    WideCertificateValid leaf2791Box leaf2791Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk225ValidityFacts chi177ValidityFacts
    leaf2791LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2791CoverageChecked :
    coverageCheck (innerAD leaf2791Box) leaf2791InnerLog = true := by
  rfl'

private theorem leaf2791InnerLogValid :
    leaf2791InnerLog.Valid 8 (innerAD leaf2791Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf2791CoverageChecked

private noncomputable def leaf2791InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814625/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2791InputLogOnePlusV_eq :
    leaf2791InputLogOnePlusV = outerEnclosure 24
      (leaf2791Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2791RoundedFacts : LeafRoundedFacts 8
    leaf2791Certificate.logOnePlusV leaf2791InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2791InputLogOnePlusV_eq }

private noncomputable def leaf2791Inputs : Inputs :=
  inputsOfCaches globalInput sk225RoundedInputs
    chi177InputQChi innerPair41Input
    leaf2791InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2791LowerChecked :
    lowerCheck 24 leaf2791Box leaf2791Inputs = true := by
  rfl'

private theorem leaf2791CoversExact : CoversExact 8
    leaf2791Box leaf2791Certificate leaf2791InnerLog leaf2791Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk225RoundedFacts chi177RoundedFacts
    innerPair41RoundedFacts leaf2791RoundedFacts (by rfl)

private theorem leaf2791FlatSound : Sound leaf2791Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2791CertificateValid
    leaf2791InnerLogValid leaf2791CoversExact leaf2791LowerChecked

private noncomputable def leaf2792Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (241/64), kHi := (121/32), chiLo := (19/128), chiHi := (39/256) }

private noncomputable def leaf2792Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742385/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434121216) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1673850553/1073741824) }, upper := { exponent := 0, mantissa := (12911/8192) } }, logOuter := sk226LogOuterCertificate, logK := sk226LogKCertificate, logChi := chi177LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871043071/274868242432) } }, logDArg := sk226LogDArgCertificate }

private noncomputable def leaf2792InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf2792LocalValidity :
    LeafFacts leaf2792Box leaf2792Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2792Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434121216) }) = true
      norm_num [leaf2792Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2792CertificateValid :
    WideCertificateValid leaf2792Box leaf2792Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk226ValidityFacts chi177ValidityFacts
    leaf2792LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2792CoverageChecked :
    coverageCheck (innerAD leaf2792Box) leaf2792InnerLog = true := by
  rfl'

private theorem leaf2792InnerLogValid :
    leaf2792InnerLog.Valid 8 (innerAD leaf2792Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf2792CoverageChecked

private noncomputable def leaf2792InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907313/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2792InputLogOnePlusV_eq :
    leaf2792InputLogOnePlusV = outerEnclosure 24
      (leaf2792Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2792RoundedFacts : LeafRoundedFacts 8
    leaf2792Certificate.logOnePlusV leaf2792InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2792InputLogOnePlusV_eq }

private noncomputable def leaf2792Inputs : Inputs :=
  inputsOfCaches globalInput sk226RoundedInputs
    chi177InputQChi innerPair41Input
    leaf2792InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2792LowerChecked :
    lowerCheck 24 leaf2792Box leaf2792Inputs = true := by
  rfl'

private theorem leaf2792CoversExact : CoversExact 8
    leaf2792Box leaf2792Certificate leaf2792InnerLog leaf2792Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk226RoundedFacts chi177RoundedFacts
    innerPair41RoundedFacts leaf2792RoundedFacts (by rfl)

private theorem leaf2792FlatSound : Sound leaf2792Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2792CertificateValid
    leaf2792InnerLogValid leaf2792CoversExact leaf2792LowerChecked

private noncomputable def leaf2793Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (241/64), chiLo := (39/256), chiHi := (5/32) }

private noncomputable def leaf2793Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742385/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45811339264) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1687088017/1073741824) }, upper := { exponent := 0, mantissa := (3253/2048) } }, logOuter := sk225LogOuterCertificate, logK := sk225LogKCertificate, logChi := chi178LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623646549/91622678528) } }, logDArg := sk225LogDArgCertificate }

private noncomputable def leaf2793InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2793LocalValidity :
    LeafFacts leaf2793Box leaf2793Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2793Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45811339264) }) = true
      norm_num [leaf2793Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2793CertificateValid :
    WideCertificateValid leaf2793Box leaf2793Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk225ValidityFacts chi178ValidityFacts
    leaf2793LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2793CoverageChecked :
    coverageCheck (innerAD leaf2793Box) leaf2793InnerLog = true := by
  rfl'

private theorem leaf2793InnerLogValid :
    leaf2793InnerLog.Valid 8 (innerAD leaf2793Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2793CoverageChecked

private noncomputable def leaf2793InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814629/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2793InputLogOnePlusV_eq :
    leaf2793InputLogOnePlusV = outerEnclosure 24
      (leaf2793Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2793RoundedFacts : LeafRoundedFacts 8
    leaf2793Certificate.logOnePlusV leaf2793InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2793InputLogOnePlusV_eq }

private noncomputable def leaf2793Inputs : Inputs :=
  inputsOfCaches globalInput sk225RoundedInputs
    chi178InputQChi innerPair50Input
    leaf2793InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2793LowerChecked :
    lowerCheck 24 leaf2793Box leaf2793Inputs = true := by
  rfl'

private theorem leaf2793CoversExact : CoversExact 8
    leaf2793Box leaf2793Certificate leaf2793InnerLog leaf2793Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk225RoundedFacts chi178RoundedFacts
    innerPair50RoundedFacts leaf2793RoundedFacts (by rfl)

private theorem leaf2793FlatSound : Sound leaf2793Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2793CertificateValid
    leaf2793InnerLogValid leaf2793CoversExact leaf2793LowerChecked

private noncomputable def leaf2794Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (241/64), kHi := (121/32), chiLo := (39/256), chiHi := (5/32) }

private noncomputable def leaf2794Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742387/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433997312) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1689643763/1073741824) }, upper := { exponent := 0, mantissa := (1629/1024) } }, logOuter := sk226LogOuterCertificate, logK := sk226LogKCertificate, logChi := chi178LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870919167/274867994624) } }, logDArg := sk226LogDArgCertificate }

private noncomputable def leaf2794InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2794LocalValidity :
    LeafFacts leaf2794Box leaf2794Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2794Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433997312) }) = true
      norm_num [leaf2794Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2794CertificateValid :
    WideCertificateValid leaf2794Box leaf2794Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk226ValidityFacts chi178ValidityFacts
    leaf2794LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2794CoverageChecked :
    coverageCheck (innerAD leaf2794Box) leaf2794InnerLog = true := by
  rfl'

private theorem leaf2794InnerLogValid :
    leaf2794InnerLog.Valid 8 (innerAD leaf2794Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2794CoverageChecked

private noncomputable def leaf2794InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629259/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2794InputLogOnePlusV_eq :
    leaf2794InputLogOnePlusV = outerEnclosure 24
      (leaf2794Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2794RoundedFacts : LeafRoundedFacts 8
    leaf2794Certificate.logOnePlusV leaf2794InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2794InputLogOnePlusV_eq }

private noncomputable def leaf2794Inputs : Inputs :=
  inputsOfCaches globalInput sk226RoundedInputs
    chi178InputQChi innerPair50Input
    leaf2794InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2794LowerChecked :
    lowerCheck 24 leaf2794Box leaf2794Inputs = true := by
  rfl'

private theorem leaf2794CoversExact : CoversExact 8
    leaf2794Box leaf2794Certificate leaf2794InnerLog leaf2794Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk226RoundedFacts chi178RoundedFacts
    innerPair50RoundedFacts leaf2794RoundedFacts (by rfl)

private theorem leaf2794FlatSound : Sound leaf2794Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2794CertificateValid
    leaf2794InnerLogValid leaf2794CoversExact leaf2794LowerChecked

private noncomputable def leaf2795Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (243/64), chiLo := (19/128), chiHi := (39/256) }

private noncomputable def leaf2795Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742387/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434101248) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1676340767/1073741824) }, upper := { exponent := 0, mantissa := (25861/16384) } }, logOuter := sk227LogOuterCertificate, logK := sk227LogKCertificate, logChi := chi177LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871023103/274868202496) } }, logDArg := sk227LogDArgCertificate }

private noncomputable def leaf2795InnerLog : WideLogData :=
  innerPair154Data

set_option maxRecDepth 1000000 in
private theorem leaf2795LocalValidity :
    LeafFacts leaf2795Box leaf2795Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2795Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434101248) }) = true
      norm_num [leaf2795Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2795CertificateValid :
    WideCertificateValid leaf2795Box leaf2795Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk227ValidityFacts chi177ValidityFacts
    leaf2795LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2795CoverageChecked :
    coverageCheck (innerAD leaf2795Box) leaf2795InnerLog = true := by
  rfl'

private theorem leaf2795InnerLogValid :
    leaf2795InnerLog.Valid 8 (innerAD leaf2795Box) :=
  wideLogDataValid_of_cachedCheck endpoint43PositiveFacts
    endpoint44PositiveFacts.valid leaf2795CoverageChecked

private noncomputable def leaf2795InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629253/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2795InputLogOnePlusV_eq :
    leaf2795InputLogOnePlusV = outerEnclosure 24
      (leaf2795Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2795RoundedFacts : LeafRoundedFacts 8
    leaf2795Certificate.logOnePlusV leaf2795InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2795InputLogOnePlusV_eq }

private noncomputable def leaf2795Inputs : Inputs :=
  inputsOfCaches globalInput sk227RoundedInputs
    chi177InputQChi innerPair154Input
    leaf2795InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2795LowerChecked :
    lowerCheck 24 leaf2795Box leaf2795Inputs = true := by
  rfl'

private theorem leaf2795CoversExact : CoversExact 8
    leaf2795Box leaf2795Certificate leaf2795InnerLog leaf2795Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk227RoundedFacts chi177RoundedFacts
    innerPair154RoundedFacts leaf2795RoundedFacts (by rfl)

private theorem leaf2795FlatSound : Sound leaf2795Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2795CertificateValid
    leaf2795InnerLogValid leaf2795CoversExact leaf2795LowerChecked

private noncomputable def leaf2796Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (243/64), kHi := (61/16), chiLo := (19/128), chiHi := (39/256) }

private noncomputable def leaf2796Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742389/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486816256) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1678830981/1073741824) }, upper := { exponent := 0, mantissa := (6475/4096) } }, logOuter := sk228LogOuterCertificate, logK := sk228LogKCertificate, logChi := chi177LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54974200627/54973632512) } }, logDArg := sk228LogDArgCertificate }

private noncomputable def leaf2796InnerLog : WideLogData :=
  innerPair54Data

set_option maxRecDepth 1000000 in
private theorem leaf2796LocalValidity :
    LeafFacts leaf2796Box leaf2796Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2796Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486816256) }) = true
      norm_num [leaf2796Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2796CertificateValid :
    WideCertificateValid leaf2796Box leaf2796Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk228ValidityFacts chi177ValidityFacts
    leaf2796LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2796CoverageChecked :
    coverageCheck (innerAD leaf2796Box) leaf2796InnerLog = true := by
  rfl'

private theorem leaf2796InnerLogValid :
    leaf2796InnerLog.Valid 8 (innerAD leaf2796Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint44PositiveFacts.valid leaf2796CoverageChecked

private noncomputable def leaf2796InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814627/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2796InputLogOnePlusV_eq :
    leaf2796InputLogOnePlusV = outerEnclosure 24
      (leaf2796Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2796RoundedFacts : LeafRoundedFacts 8
    leaf2796Certificate.logOnePlusV leaf2796InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2796InputLogOnePlusV_eq }

private noncomputable def leaf2796Inputs : Inputs :=
  inputsOfCaches globalInput sk228RoundedInputs
    chi177InputQChi innerPair54Input
    leaf2796InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2796LowerChecked :
    lowerCheck 24 leaf2796Box leaf2796Inputs = true := by
  rfl'

private theorem leaf2796CoversExact : CoversExact 8
    leaf2796Box leaf2796Certificate leaf2796InnerLog leaf2796Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk228RoundedFacts chi177RoundedFacts
    innerPair54RoundedFacts leaf2796RoundedFacts (by rfl)

private theorem leaf2796FlatSound : Sound leaf2796Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2796CertificateValid
    leaf2796InnerLogValid leaf2796CoversExact leaf2796LowerChecked

private noncomputable def leaf2797Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (243/64), chiLo := (39/256), chiHi := (5/32) }

private noncomputable def leaf2797Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742389/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433976832) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1692199509/1073741824) }, upper := { exponent := 0, mantissa := (3263/2048) } }, logOuter := sk227LogOuterCertificate, logK := sk227LogKCertificate, logChi := chi178LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870898687/274867953664) } }, logDArg := sk227LogDArgCertificate }

private noncomputable def leaf2797InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2797LocalValidity :
    LeafFacts leaf2797Box leaf2797Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2797Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433976832) }) = true
      norm_num [leaf2797Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2797CertificateValid :
    WideCertificateValid leaf2797Box leaf2797Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk227ValidityFacts chi178ValidityFacts
    leaf2797LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2797CoverageChecked :
    coverageCheck (innerAD leaf2797Box) leaf2797InnerLog = true := by
  rfl'

private theorem leaf2797InnerLogValid :
    leaf2797InnerLog.Valid 8 (innerAD leaf2797Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2797CoverageChecked

private noncomputable def leaf2797InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907315/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2797InputLogOnePlusV_eq :
    leaf2797InputLogOnePlusV = outerEnclosure 24
      (leaf2797Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2797RoundedFacts : LeafRoundedFacts 8
    leaf2797Certificate.logOnePlusV leaf2797InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2797InputLogOnePlusV_eq }

private noncomputable def leaf2797Inputs : Inputs :=
  inputsOfCaches globalInput sk227RoundedInputs
    chi178InputQChi innerPair50Input
    leaf2797InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2797LowerChecked :
    lowerCheck 24 leaf2797Box leaf2797Inputs = true := by
  rfl'

private theorem leaf2797CoversExact : CoversExact 8
    leaf2797Box leaf2797Certificate leaf2797InnerLog leaf2797Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk227RoundedFacts chi178RoundedFacts
    innerPair50RoundedFacts leaf2797RoundedFacts (by rfl)

private theorem leaf2797FlatSound : Sound leaf2797Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2797CertificateValid
    leaf2797InnerLogValid leaf2797CoversExact leaf2797LowerChecked

private noncomputable def leaf2798Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (243/64), kHi := (61/16), chiLo := (39/256), chiHi := (5/32) }

private noncomputable def leaf2798Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742391/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45811318784) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1694755255/1073741824) }, upper := { exponent := 0, mantissa := (817/512) } }, logOuter := sk228LogOuterCertificate, logK := sk228LogKCertificate, logChi := chi178LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623626069/91622637568) } }, logDArg := sk228LogDArgCertificate }

private noncomputable def leaf2798InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2798LocalValidity :
    LeafFacts leaf2798Box leaf2798Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2798Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45811318784) }) = true
      norm_num [leaf2798Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2798CertificateValid :
    WideCertificateValid leaf2798Box leaf2798Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk228ValidityFacts chi178ValidityFacts
    leaf2798LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2798CoverageChecked :
    coverageCheck (innerAD leaf2798Box) leaf2798InnerLog = true := by
  rfl'

private theorem leaf2798InnerLogValid :
    leaf2798InnerLog.Valid 8 (innerAD leaf2798Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2798CoverageChecked

private noncomputable def leaf2798InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814631/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2798InputLogOnePlusV_eq :
    leaf2798InputLogOnePlusV = outerEnclosure 24
      (leaf2798Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2798RoundedFacts : LeafRoundedFacts 8
    leaf2798Certificate.logOnePlusV leaf2798InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2798InputLogOnePlusV_eq }

private noncomputable def leaf2798Inputs : Inputs :=
  inputsOfCaches globalInput sk228RoundedInputs
    chi178InputQChi innerPair50Input
    leaf2798InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2798LowerChecked :
    lowerCheck 24 leaf2798Box leaf2798Inputs = true := by
  rfl'

private theorem leaf2798CoversExact : CoversExact 8
    leaf2798Box leaf2798Certificate leaf2798InnerLog leaf2798Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk228RoundedFacts chi178RoundedFacts
    innerPair50RoundedFacts leaf2798RoundedFacts (by rfl)

private theorem leaf2798FlatSound : Sound leaf2798Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2798CertificateValid
    leaf2798InnerLogValid leaf2798CoversExact leaf2798LowerChecked

private noncomputable def leaf2799Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (245/64), chiLo := (9/64), chiHi := (37/256) }

private noncomputable def leaf2799Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742387/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434312192) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1649341583/1073741824) }, upper := { exponent := 0, mantissa := (25449/16384) } }, logOuter := sk229LogOuterCertificate, logK := sk229LogKCertificate, logChi := chi175LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871234047/274868624384) } }, logDArg := sk229LogDArgCertificate }

private noncomputable def leaf2799InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2799LocalValidity :
    LeafFacts leaf2799Box leaf2799Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2799Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434312192) }) = true
      norm_num [leaf2799Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2799CertificateValid :
    WideCertificateValid leaf2799Box leaf2799Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk229ValidityFacts chi175ValidityFacts
    leaf2799LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2799CoverageChecked :
    coverageCheck (innerAD leaf2799Box) leaf2799InnerLog = true := by
  rfl'

private theorem leaf2799InnerLogValid :
    leaf2799InnerLog.Valid 8 (innerAD leaf2799Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2799CoverageChecked

private noncomputable def leaf2799InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453655/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf2799InputLogOnePlusV_eq :
    leaf2799InputLogOnePlusV = outerEnclosure 24
      (leaf2799Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2799RoundedFacts : LeafRoundedFacts 8
    leaf2799Certificate.logOnePlusV leaf2799InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2799InputLogOnePlusV_eq }

private noncomputable def leaf2799Inputs : Inputs :=
  inputsOfCaches globalInput sk229RoundedInputs
    chi175InputQChi innerPair40Input
    leaf2799InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2799LowerChecked :
    lowerCheck 24 leaf2799Box leaf2799Inputs = true := by
  rfl'

private theorem leaf2799CoversExact : CoversExact 8
    leaf2799Box leaf2799Certificate leaf2799InnerLog leaf2799Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk229RoundedFacts chi175RoundedFacts
    innerPair40RoundedFacts leaf2799RoundedFacts (by rfl)

private theorem leaf2799FlatSound : Sound leaf2799Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2799CertificateValid
    leaf2799InnerLogValid leaf2799CoversExact leaf2799LowerChecked

private noncomputable def leaf2800Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (245/64), kHi := (123/32), chiLo := (9/64), chiHi := (37/256) }

private noncomputable def leaf2800Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742389/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434293248) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1651700733/1073741824) }, upper := { exponent := 0, mantissa := (12743/8192) } }, logOuter := sk230LogOuterCertificate, logK := sk230LogKCertificate, logChi := chi175LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871215103/274868586496) } }, logDArg := sk230LogDArgCertificate }

private noncomputable def leaf2800InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2800LocalValidity :
    LeafFacts leaf2800Box leaf2800Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2800Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434293248) }) = true
      norm_num [leaf2800Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2800CertificateValid :
    WideCertificateValid leaf2800Box leaf2800Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk230ValidityFacts chi175ValidityFacts
    leaf2800LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2800CoverageChecked :
    coverageCheck (innerAD leaf2800Box) leaf2800InnerLog = true := by
  rfl'

private theorem leaf2800InnerLogValid :
    leaf2800InnerLog.Valid 8 (innerAD leaf2800Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2800CoverageChecked

private noncomputable def leaf2800InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629241/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2800InputLogOnePlusV_eq :
    leaf2800InputLogOnePlusV = outerEnclosure 24
      (leaf2800Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2800RoundedFacts : LeafRoundedFacts 8
    leaf2800Certificate.logOnePlusV leaf2800InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2800InputLogOnePlusV_eq }

private noncomputable def leaf2800Inputs : Inputs :=
  inputsOfCaches globalInput sk230RoundedInputs
    chi175InputQChi innerPair40Input
    leaf2800InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2800LowerChecked :
    lowerCheck 24 leaf2800Box leaf2800Inputs = true := by
  rfl'

private theorem leaf2800CoversExact : CoversExact 8
    leaf2800Box leaf2800Certificate leaf2800InnerLog leaf2800Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk230RoundedFacts chi175RoundedFacts
    innerPair40RoundedFacts leaf2800RoundedFacts (by rfl)

private theorem leaf2800FlatSound : Sound leaf2800Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2800CertificateValid
    leaf2800InnerLogValid leaf2800CoversExact leaf2800LowerChecked

private noncomputable def leaf2801Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (245/64), chiLo := (37/256), chiHi := (19/128) }

private noncomputable def leaf2801Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742389/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45811395584) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1665331389/1073741824) }, upper := { exponent := 0, mantissa := (12847/8192) } }, logOuter := sk229LogOuterCertificate, logK := sk229LogKCertificate, logChi := chi176LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623702869/91622791168) } }, logDArg := sk229LogDArgCertificate }

private noncomputable def leaf2801InnerLog : WideLogData :=
  innerPair156Data

set_option maxRecDepth 1000000 in
private theorem leaf2801LocalValidity :
    LeafFacts leaf2801Box leaf2801Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2801Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45811395584) }) = true
      norm_num [leaf2801Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2801CertificateValid :
    WideCertificateValid leaf2801Box leaf2801Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk229ValidityFacts chi176ValidityFacts
    leaf2801LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2801CoverageChecked :
    coverageCheck (innerAD leaf2801Box) leaf2801InnerLog = true := by
  rfl'

private theorem leaf2801InnerLogValid :
    leaf2801InnerLog.Valid 8 (innerAD leaf2801Box) :=
  wideLogDataValid_of_cachedCheck endpoint43PositiveFacts
    endpoint47PositiveFacts.valid leaf2801CoverageChecked

private noncomputable def leaf2801InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (181707/262144) }

set_option maxRecDepth 1000000 in
private theorem leaf2801InputLogOnePlusV_eq :
    leaf2801InputLogOnePlusV = outerEnclosure 24
      (leaf2801Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2801RoundedFacts : LeafRoundedFacts 8
    leaf2801Certificate.logOnePlusV leaf2801InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2801InputLogOnePlusV_eq }

private noncomputable def leaf2801Inputs : Inputs :=
  inputsOfCaches globalInput sk229RoundedInputs
    chi176InputQChi innerPair156Input
    leaf2801InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2801LowerChecked :
    lowerCheck 24 leaf2801Box leaf2801Inputs = true := by
  rfl'

private theorem leaf2801CoversExact : CoversExact 8
    leaf2801Box leaf2801Certificate leaf2801InnerLog leaf2801Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk229RoundedFacts chi176RoundedFacts
    innerPair156RoundedFacts leaf2801RoundedFacts (by rfl)

private theorem leaf2801FlatSound : Sound leaf2801Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2801CertificateValid
    leaf2801InnerLogValid leaf2801CoversExact leaf2801LowerChecked

private noncomputable def leaf2802Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (245/64), kHi := (123/32), chiLo := (37/256), chiHi := (19/128) }

private noncomputable def leaf2802Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742391/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434167296) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1667756071/1073741824) }, upper := { exponent := 0, mantissa := (6433/4096) } }, logOuter := sk230LogOuterCertificate, logK := sk230LogKCertificate, logChi := chi176LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871089151/274868334592) } }, logDArg := sk230LogDArgCertificate }

private noncomputable def leaf2802InnerLog : WideLogData :=
  innerPair156Data

set_option maxRecDepth 1000000 in
private theorem leaf2802LocalValidity :
    LeafFacts leaf2802Box leaf2802Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2802Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434167296) }) = true
      norm_num [leaf2802Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2802CertificateValid :
    WideCertificateValid leaf2802Box leaf2802Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk230ValidityFacts chi176ValidityFacts
    leaf2802LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2802CoverageChecked :
    coverageCheck (innerAD leaf2802Box) leaf2802InnerLog = true := by
  rfl'

private theorem leaf2802InnerLogValid :
    leaf2802InnerLog.Valid 8 (innerAD leaf2802Box) :=
  wideLogDataValid_of_cachedCheck endpoint43PositiveFacts
    endpoint47PositiveFacts.valid leaf2802CoverageChecked

private noncomputable def leaf2802InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629249/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2802InputLogOnePlusV_eq :
    leaf2802InputLogOnePlusV = outerEnclosure 24
      (leaf2802Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2802RoundedFacts : LeafRoundedFacts 8
    leaf2802Certificate.logOnePlusV leaf2802InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2802InputLogOnePlusV_eq }

private noncomputable def leaf2802Inputs : Inputs :=
  inputsOfCaches globalInput sk230RoundedInputs
    chi176InputQChi innerPair156Input
    leaf2802InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2802LowerChecked :
    lowerCheck 24 leaf2802Box leaf2802Inputs = true := by
  rfl'

private theorem leaf2802CoversExact : CoversExact 8
    leaf2802Box leaf2802Certificate leaf2802InnerLog leaf2802Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk230RoundedFacts chi176RoundedFacts
    innerPair156RoundedFacts leaf2802RoundedFacts (by rfl)

private theorem leaf2802FlatSound : Sound leaf2802Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2802CertificateValid
    leaf2802InnerLogValid leaf2802CoversExact leaf2802LowerChecked

private noncomputable def leaf2803Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (247/64), chiLo := (9/64), chiHi := (37/256) }

private noncomputable def leaf2803Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742391/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45811424768) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1654059883/1073741824) }, upper := { exponent := 0, mantissa := (25523/16384) } }, logOuter := sk231LogOuterCertificate, logK := sk231LogKCertificate, logChi := chi175LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623732053/91622849536) } }, logDArg := sk231LogDArgCertificate }

private noncomputable def leaf2803InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2803LocalValidity :
    LeafFacts leaf2803Box leaf2803Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2803Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45811424768) }) = true
      norm_num [leaf2803Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2803CertificateValid :
    WideCertificateValid leaf2803Box leaf2803Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk231ValidityFacts chi175ValidityFacts
    leaf2803LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2803CoverageChecked :
    coverageCheck (innerAD leaf2803Box) leaf2803InnerLog = true := by
  rfl'

private theorem leaf2803InnerLogValid :
    leaf2803InnerLog.Valid 8 (innerAD leaf2803Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2803CoverageChecked

private noncomputable def leaf2803InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814621/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2803InputLogOnePlusV_eq :
    leaf2803InputLogOnePlusV = outerEnclosure 24
      (leaf2803Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2803RoundedFacts : LeafRoundedFacts 8
    leaf2803Certificate.logOnePlusV leaf2803InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2803InputLogOnePlusV_eq }

private noncomputable def leaf2803Inputs : Inputs :=
  inputsOfCaches globalInput sk231RoundedInputs
    chi175InputQChi innerPair40Input
    leaf2803InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2803LowerChecked :
    lowerCheck 24 leaf2803Box leaf2803Inputs = true := by
  rfl'

private theorem leaf2803CoversExact : CoversExact 8
    leaf2803Box leaf2803Certificate leaf2803InnerLog leaf2803Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk231RoundedFacts chi175RoundedFacts
    innerPair40RoundedFacts leaf2803RoundedFacts (by rfl)

private theorem leaf2803FlatSound : Sound leaf2803Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2803CertificateValid
    leaf2803InnerLogValid leaf2803CoversExact leaf2803LowerChecked

private noncomputable def leaf2804Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (247/64), kHi := (31/8), chiLo := (9/64), chiHi := (37/256) }

private noncomputable def leaf2804Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742393/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486851072) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1656419033/1073741824) }, upper := { exponent := 0, mantissa := (3195/2048) } }, logOuter := sk232LogOuterCertificate, logK := sk232LogKCertificate, logChi := chi175LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54974235443/54973702144) } }, logDArg := sk232LogDArgCertificate }

private noncomputable def leaf2804InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2804LocalValidity :
    LeafFacts leaf2804Box leaf2804Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2804Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486851072) }) = true
      norm_num [leaf2804Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2804CertificateValid :
    WideCertificateValid leaf2804Box leaf2804Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk232ValidityFacts chi175ValidityFacts
    leaf2804LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2804CoverageChecked :
    coverageCheck (innerAD leaf2804Box) leaf2804InnerLog = true := by
  rfl'

private theorem leaf2804InnerLogValid :
    leaf2804InnerLog.Valid 8 (innerAD leaf2804Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2804CoverageChecked

private noncomputable def leaf2804InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629243/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2804InputLogOnePlusV_eq :
    leaf2804InputLogOnePlusV = outerEnclosure 24
      (leaf2804Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2804RoundedFacts : LeafRoundedFacts 8
    leaf2804Certificate.logOnePlusV leaf2804InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2804InputLogOnePlusV_eq }

private noncomputable def leaf2804Inputs : Inputs :=
  inputsOfCaches globalInput sk232RoundedInputs
    chi175InputQChi innerPair40Input
    leaf2804InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2804LowerChecked :
    lowerCheck 24 leaf2804Box leaf2804Inputs = true := by
  rfl'

private theorem leaf2804CoversExact : CoversExact 8
    leaf2804Box leaf2804Certificate leaf2804InnerLog leaf2804Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk232RoundedFacts chi175RoundedFacts
    innerPair40RoundedFacts leaf2804RoundedFacts (by rfl)

private theorem leaf2804FlatSound : Sound leaf2804Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2804CertificateValid
    leaf2804InnerLogValid leaf2804CoversExact leaf2804LowerChecked

private noncomputable def leaf2805Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (247/64), chiLo := (37/256), chiHi := (19/128) }

private noncomputable def leaf2805Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742393/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486829568) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1670180753/1073741824) }, upper := { exponent := 0, mantissa := (12885/8192) } }, logOuter := sk231LogOuterCertificate, logK := sk231LogKCertificate, logChi := chi176LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54974213939/54973659136) } }, logDArg := sk231LogDArgCertificate }

private noncomputable def leaf2805InnerLog : WideLogData :=
  innerPair156Data

set_option maxRecDepth 1000000 in
private theorem leaf2805LocalValidity :
    LeafFacts leaf2805Box leaf2805Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2805Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486829568) }) = true
      norm_num [leaf2805Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2805CertificateValid :
    WideCertificateValid leaf2805Box leaf2805Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk231ValidityFacts chi176ValidityFacts
    leaf2805LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2805CoverageChecked :
    coverageCheck (innerAD leaf2805Box) leaf2805InnerLog = true := by
  rfl'

private theorem leaf2805InnerLogValid :
    leaf2805InnerLog.Valid 8 (innerAD leaf2805Box) :=
  wideLogDataValid_of_cachedCheck endpoint43PositiveFacts
    endpoint47PositiveFacts.valid leaf2805CoverageChecked

private noncomputable def leaf2805InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814625/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2805InputLogOnePlusV_eq :
    leaf2805InputLogOnePlusV = outerEnclosure 24
      (leaf2805Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2805RoundedFacts : LeafRoundedFacts 8
    leaf2805Certificate.logOnePlusV leaf2805InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2805InputLogOnePlusV_eq }

private noncomputable def leaf2805Inputs : Inputs :=
  inputsOfCaches globalInput sk231RoundedInputs
    chi176InputQChi innerPair156Input
    leaf2805InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2805LowerChecked :
    lowerCheck 24 leaf2805Box leaf2805Inputs = true := by
  rfl'

private theorem leaf2805CoversExact : CoversExact 8
    leaf2805Box leaf2805Certificate leaf2805InnerLog leaf2805Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk231RoundedFacts chi176RoundedFacts
    innerPair156RoundedFacts leaf2805RoundedFacts (by rfl)

private theorem leaf2805FlatSound : Sound leaf2805Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2805CertificateValid
    leaf2805InnerLogValid leaf2805CoversExact leaf2805LowerChecked

private noncomputable def leaf2806Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (247/64), kHi := (31/8), chiLo := (37/256), chiHi := (19/128) }

private noncomputable def leaf2806Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742395/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45811376128) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1672605435/1073741824) }, upper := { exponent := 0, mantissa := (1613/1024) } }, logOuter := sk232LogOuterCertificate, logK := sk232LogKCertificate, logChi := chi176LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623683413/91622752256) } }, logDArg := sk232LogDArgCertificate }

private noncomputable def leaf2806InnerLog : WideLogData :=
  innerPair156Data

set_option maxRecDepth 1000000 in
private theorem leaf2806LocalValidity :
    LeafFacts leaf2806Box leaf2806Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2806Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45811376128) }) = true
      norm_num [leaf2806Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2806CertificateValid :
    WideCertificateValid leaf2806Box leaf2806Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk232ValidityFacts chi176ValidityFacts
    leaf2806LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2806CoverageChecked :
    coverageCheck (innerAD leaf2806Box) leaf2806InnerLog = true := by
  rfl'

private theorem leaf2806InnerLogValid :
    leaf2806InnerLog.Valid 8 (innerAD leaf2806Box) :=
  wideLogDataValid_of_cachedCheck endpoint43PositiveFacts
    endpoint47PositiveFacts.valid leaf2806CoverageChecked

private noncomputable def leaf2806InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629251/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2806InputLogOnePlusV_eq :
    leaf2806InputLogOnePlusV = outerEnclosure 24
      (leaf2806Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2806RoundedFacts : LeafRoundedFacts 8
    leaf2806Certificate.logOnePlusV leaf2806InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2806InputLogOnePlusV_eq }

private noncomputable def leaf2806Inputs : Inputs :=
  inputsOfCaches globalInput sk232RoundedInputs
    chi176InputQChi innerPair156Input
    leaf2806InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2806LowerChecked :
    lowerCheck 24 leaf2806Box leaf2806Inputs = true := by
  rfl'

private theorem leaf2806CoversExact : CoversExact 8
    leaf2806Box leaf2806Certificate leaf2806InnerLog leaf2806Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk232RoundedFacts chi176RoundedFacts
    innerPair156RoundedFacts leaf2806RoundedFacts (by rfl)

private theorem leaf2806FlatSound : Sound leaf2806Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2806CertificateValid
    leaf2806InnerLogValid leaf2806CoversExact leaf2806LowerChecked

private noncomputable def leaf2807Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (245/64), chiLo := (19/128), chiHi := (39/256) }

private noncomputable def leaf2807Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742391/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434061312) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1681321195/1073741824) }, upper := { exponent := 0, mantissa := (25939/16384) } }, logOuter := sk229LogOuterCertificate, logK := sk229LogKCertificate, logChi := chi177LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870983167/274868122624) } }, logDArg := sk229LogDArgCertificate }

private noncomputable def leaf2807InnerLog : WideLogData :=
  innerPair54Data

set_option maxRecDepth 1000000 in
private theorem leaf2807LocalValidity :
    LeafFacts leaf2807Box leaf2807Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2807Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434061312) }) = true
      norm_num [leaf2807Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2807CertificateValid :
    WideCertificateValid leaf2807Box leaf2807Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk229ValidityFacts chi177ValidityFacts
    leaf2807LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2807CoverageChecked :
    coverageCheck (innerAD leaf2807Box) leaf2807InnerLog = true := by
  rfl'

private theorem leaf2807InnerLogValid :
    leaf2807InnerLog.Valid 8 (innerAD leaf2807Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint44PositiveFacts.valid leaf2807CoverageChecked

private noncomputable def leaf2807InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629255/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2807InputLogOnePlusV_eq :
    leaf2807InputLogOnePlusV = outerEnclosure 24
      (leaf2807Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2807RoundedFacts : LeafRoundedFacts 8
    leaf2807Certificate.logOnePlusV leaf2807InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2807InputLogOnePlusV_eq }

private noncomputable def leaf2807Inputs : Inputs :=
  inputsOfCaches globalInput sk229RoundedInputs
    chi177InputQChi innerPair54Input
    leaf2807InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2807LowerChecked :
    lowerCheck 24 leaf2807Box leaf2807Inputs = true := by
  rfl'

private theorem leaf2807CoversExact : CoversExact 8
    leaf2807Box leaf2807Certificate leaf2807InnerLog leaf2807Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk229RoundedFacts chi177RoundedFacts
    innerPair54RoundedFacts leaf2807RoundedFacts (by rfl)

private theorem leaf2807FlatSound : Sound leaf2807Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2807CertificateValid
    leaf2807InnerLogValid leaf2807CoversExact leaf2807LowerChecked

private noncomputable def leaf2808Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (245/64), kHi := (123/32), chiLo := (19/128), chiHi := (39/256) }

private noncomputable def leaf2808Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742393/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434041344) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1683811409/1073741824) }, upper := { exponent := 0, mantissa := (12989/8192) } }, logOuter := sk230LogOuterCertificate, logK := sk230LogKCertificate, logChi := chi177LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870963199/274868082688) } }, logDArg := sk230LogDArgCertificate }

private noncomputable def leaf2808InnerLog : WideLogData :=
  innerPair54Data

set_option maxRecDepth 1000000 in
private theorem leaf2808LocalValidity :
    LeafFacts leaf2808Box leaf2808Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2808Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434041344) }) = true
      norm_num [leaf2808Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2808CertificateValid :
    WideCertificateValid leaf2808Box leaf2808Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk230ValidityFacts chi177ValidityFacts
    leaf2808LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2808CoverageChecked :
    coverageCheck (innerAD leaf2808Box) leaf2808InnerLog = true := by
  rfl'

private theorem leaf2808InnerLogValid :
    leaf2808InnerLog.Valid 8 (innerAD leaf2808Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint44PositiveFacts.valid leaf2808CoverageChecked

private noncomputable def leaf2808InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629257/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2808InputLogOnePlusV_eq :
    leaf2808InputLogOnePlusV = outerEnclosure 24
      (leaf2808Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2808RoundedFacts : LeafRoundedFacts 8
    leaf2808Certificate.logOnePlusV leaf2808InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2808InputLogOnePlusV_eq }

private noncomputable def leaf2808Inputs : Inputs :=
  inputsOfCaches globalInput sk230RoundedInputs
    chi177InputQChi innerPair54Input
    leaf2808InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2808LowerChecked :
    lowerCheck 24 leaf2808Box leaf2808Inputs = true := by
  rfl'

private theorem leaf2808CoversExact : CoversExact 8
    leaf2808Box leaf2808Certificate leaf2808InnerLog leaf2808Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk230RoundedFacts chi177RoundedFacts
    innerPair54RoundedFacts leaf2808RoundedFacts (by rfl)

private theorem leaf2808FlatSound : Sound leaf2808Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2808CertificateValid
    leaf2808InnerLogValid leaf2808CoversExact leaf2808LowerChecked

private noncomputable def leaf2809Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (245/64), chiLo := (39/256), chiHi := (5/32) }

private noncomputable def leaf2809Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742393/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433935872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1697311001/1073741824) }, upper := { exponent := 0, mantissa := (3273/2048) } }, logOuter := sk229LogOuterCertificate, logK := sk229LogKCertificate, logChi := chi178LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870857727/274867871744) } }, logDArg := sk229LogDArgCertificate }

private noncomputable def leaf2809InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2809LocalValidity :
    LeafFacts leaf2809Box leaf2809Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2809Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433935872) }) = true
      norm_num [leaf2809Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2809CertificateValid :
    WideCertificateValid leaf2809Box leaf2809Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk229ValidityFacts chi178ValidityFacts
    leaf2809LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2809CoverageChecked :
    coverageCheck (innerAD leaf2809Box) leaf2809InnerLog = true := by
  rfl'

private theorem leaf2809InnerLogValid :
    leaf2809InnerLog.Valid 8 (innerAD leaf2809Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2809CoverageChecked

private noncomputable def leaf2809InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629263/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2809InputLogOnePlusV_eq :
    leaf2809InputLogOnePlusV = outerEnclosure 24
      (leaf2809Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2809RoundedFacts : LeafRoundedFacts 8
    leaf2809Certificate.logOnePlusV leaf2809InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2809InputLogOnePlusV_eq }

private noncomputable def leaf2809Inputs : Inputs :=
  inputsOfCaches globalInput sk229RoundedInputs
    chi178InputQChi innerPair50Input
    leaf2809InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2809LowerChecked :
    lowerCheck 24 leaf2809Box leaf2809Inputs = true := by
  rfl'

private theorem leaf2809CoversExact : CoversExact 8
    leaf2809Box leaf2809Certificate leaf2809InnerLog leaf2809Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk229RoundedFacts chi178RoundedFacts
    innerPair50RoundedFacts leaf2809RoundedFacts (by rfl)

private theorem leaf2809FlatSound : Sound leaf2809Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2809CertificateValid
    leaf2809InnerLogValid leaf2809CoversExact leaf2809LowerChecked

private noncomputable def leaf2810Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (245/64), kHi := (123/32), chiLo := (39/256), chiHi := (5/32) }

private noncomputable def leaf2810Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742395/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433915392) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1699866747/1073741824) }, upper := { exponent := 0, mantissa := (1639/1024) } }, logOuter := sk230LogOuterCertificate, logK := sk230LogKCertificate, logChi := chi178LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870837247/274867830784) } }, logDArg := sk230LogDArgCertificate }

private noncomputable def leaf2810InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2810LocalValidity :
    LeafFacts leaf2810Box leaf2810Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2810Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433915392) }) = true
      norm_num [leaf2810Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2810CertificateValid :
    WideCertificateValid leaf2810Box leaf2810Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk230ValidityFacts chi178ValidityFacts
    leaf2810LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2810CoverageChecked :
    coverageCheck (innerAD leaf2810Box) leaf2810InnerLog = true := by
  rfl'

private theorem leaf2810InnerLogValid :
    leaf2810InnerLog.Valid 8 (innerAD leaf2810Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2810CoverageChecked

private noncomputable def leaf2810InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726829/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf2810InputLogOnePlusV_eq :
    leaf2810InputLogOnePlusV = outerEnclosure 24
      (leaf2810Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2810RoundedFacts : LeafRoundedFacts 8
    leaf2810Certificate.logOnePlusV leaf2810InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2810InputLogOnePlusV_eq }

private noncomputable def leaf2810Inputs : Inputs :=
  inputsOfCaches globalInput sk230RoundedInputs
    chi178InputQChi innerPair50Input
    leaf2810InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2810LowerChecked :
    lowerCheck 24 leaf2810Box leaf2810Inputs = true := by
  rfl'

private theorem leaf2810CoversExact : CoversExact 8
    leaf2810Box leaf2810Certificate leaf2810InnerLog leaf2810Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk230RoundedFacts chi178RoundedFacts
    innerPair50RoundedFacts leaf2810RoundedFacts (by rfl)

private theorem leaf2810FlatSound : Sound leaf2810Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2810CertificateValid
    leaf2810InnerLogValid leaf2810CoversExact leaf2810LowerChecked

private noncomputable def leaf2811Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (247/64), chiLo := (19/128), chiHi := (39/256) }

private noncomputable def leaf2811Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742395/1073741824) }, vSqrt := { lower := (8191/8192), upper := (3196207485/3196140032) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1686301623/1073741824) }, upper := { exponent := 0, mantissa := (26017/16384) } }, logOuter := sk231LogOuterCertificate, logK := sk231LogKCertificate, logChi := chi177LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (6392347517/6392280064) } }, logDArg := sk231LogDArgCertificate }

private noncomputable def leaf2811InnerLog : WideLogData :=
  innerPair54Data

set_option maxRecDepth 1000000 in
private theorem leaf2811LocalValidity :
    LeafFacts leaf2811Box leaf2811Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2811Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (3196207485/3196140032) }) = true
      norm_num [leaf2811Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2811CertificateValid :
    WideCertificateValid leaf2811Box leaf2811Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk231ValidityFacts chi177ValidityFacts
    leaf2811LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2811CoverageChecked :
    coverageCheck (innerAD leaf2811Box) leaf2811InnerLog = true := by
  rfl'

private theorem leaf2811InnerLogValid :
    leaf2811InnerLog.Valid 8 (innerAD leaf2811Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint44PositiveFacts.valid leaf2811CoverageChecked

private noncomputable def leaf2811InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814629/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2811InputLogOnePlusV_eq :
    leaf2811InputLogOnePlusV = outerEnclosure 24
      (leaf2811Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2811RoundedFacts : LeafRoundedFacts 8
    leaf2811Certificate.logOnePlusV leaf2811InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2811InputLogOnePlusV_eq }

private noncomputable def leaf2811Inputs : Inputs :=
  inputsOfCaches globalInput sk231RoundedInputs
    chi177InputQChi innerPair54Input
    leaf2811InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2811LowerChecked :
    lowerCheck 24 leaf2811Box leaf2811Inputs = true := by
  rfl'

private theorem leaf2811CoversExact : CoversExact 8
    leaf2811Box leaf2811Certificate leaf2811InnerLog leaf2811Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk231RoundedFacts chi177RoundedFacts
    innerPair54RoundedFacts leaf2811RoundedFacts (by rfl)

private theorem leaf2811FlatSound : Sound leaf2811Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2811CertificateValid
    leaf2811InnerLogValid leaf2811CoversExact leaf2811LowerChecked

private noncomputable def leaf2812Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (247/64), kHi := (31/8), chiLo := (19/128), chiHi := (39/256) }

private noncomputable def leaf2812Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742397/1073741824) }, vSqrt := { lower := (8191/8192), upper := (8084524815/8084353024) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1688791837/1073741824) }, upper := { exponent := 0, mantissa := (3257/2048) } }, logOuter := sk232LogOuterCertificate, logK := sk232LogKCertificate, logChi := chi177LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16168877839/16168706048) } }, logDArg := sk232LogDArgCertificate }

private noncomputable def leaf2812InnerLog : WideLogData :=
  innerPair54Data

set_option maxRecDepth 1000000 in
private theorem leaf2812LocalValidity :
    LeafFacts leaf2812Box leaf2812Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2812Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8084524815/8084353024) }) = true
      norm_num [leaf2812Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2812CertificateValid :
    WideCertificateValid leaf2812Box leaf2812Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk232ValidityFacts chi177ValidityFacts
    leaf2812LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2812CoverageChecked :
    coverageCheck (innerAD leaf2812Box) leaf2812InnerLog = true := by
  rfl'

private theorem leaf2812InnerLogValid :
    leaf2812InnerLog.Valid 8 (innerAD leaf2812Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint44PositiveFacts.valid leaf2812CoverageChecked

private noncomputable def leaf2812InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629259/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2812InputLogOnePlusV_eq :
    leaf2812InputLogOnePlusV = outerEnclosure 24
      (leaf2812Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2812RoundedFacts : LeafRoundedFacts 8
    leaf2812Certificate.logOnePlusV leaf2812InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2812InputLogOnePlusV_eq }

private noncomputable def leaf2812Inputs : Inputs :=
  inputsOfCaches globalInput sk232RoundedInputs
    chi177InputQChi innerPair54Input
    leaf2812InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2812LowerChecked :
    lowerCheck 24 leaf2812Box leaf2812Inputs = true := by
  rfl'

private theorem leaf2812CoversExact : CoversExact 8
    leaf2812Box leaf2812Certificate leaf2812InnerLog leaf2812Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk232RoundedFacts chi177RoundedFacts
    innerPair54RoundedFacts leaf2812RoundedFacts (by rfl)

private theorem leaf2812FlatSound : Sound leaf2812Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2812CertificateValid
    leaf2812InnerLogValid leaf2812CoversExact leaf2812LowerChecked

private noncomputable def leaf2813Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (247/64), chiLo := (39/256), chiHi := (5/32) }

private noncomputable def leaf2813Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742397/1073741824) }, vSqrt := { lower := (8191/8192), upper := (5090256365/5090144256) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1702422493/1073741824) }, upper := { exponent := 0, mantissa := (3283/2048) } }, logOuter := sk231LogOuterCertificate, logK := sk231LogKCertificate, logChi := chi178LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (10180400621/10180288512) } }, logDArg := sk231LogDArgCertificate }

private noncomputable def leaf2813InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2813LocalValidity :
    LeafFacts leaf2813Box leaf2813Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2813Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5090256365/5090144256) }) = true
      norm_num [leaf2813Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2813CertificateValid :
    WideCertificateValid leaf2813Box leaf2813Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk231ValidityFacts chi178ValidityFacts
    leaf2813LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2813CoverageChecked :
    coverageCheck (innerAD leaf2813Box) leaf2813InnerLog = true := by
  rfl'

private theorem leaf2813InnerLogValid :
    leaf2813InnerLog.Valid 8 (innerAD leaf2813Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2813CoverageChecked

private noncomputable def leaf2813InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629265/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2813InputLogOnePlusV_eq :
    leaf2813InputLogOnePlusV = outerEnclosure 24
      (leaf2813Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2813RoundedFacts : LeafRoundedFacts 8
    leaf2813Certificate.logOnePlusV leaf2813InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2813InputLogOnePlusV_eq }

private noncomputable def leaf2813Inputs : Inputs :=
  inputsOfCaches globalInput sk231RoundedInputs
    chi178InputQChi innerPair50Input
    leaf2813InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2813LowerChecked :
    lowerCheck 24 leaf2813Box leaf2813Inputs = true := by
  rfl'

private theorem leaf2813CoversExact : CoversExact 8
    leaf2813Box leaf2813Certificate leaf2813InnerLog leaf2813Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk231RoundedFacts chi178RoundedFacts
    innerPair50RoundedFacts leaf2813RoundedFacts (by rfl)

private theorem leaf2813FlatSound : Sound leaf2813Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2813CertificateValid
    leaf2813InnerLogValid leaf2813CoversExact leaf2813LowerChecked

private noncomputable def leaf2814Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (247/64), kHi := (31/8), chiLo := (39/256), chiHi := (5/32) }

private noncomputable def leaf2814Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742399/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433874432) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1704978239/1073741824) }, upper := { exponent := 0, mantissa := (411/256) } }, logOuter := sk232LogOuterCertificate, logK := sk232LogKCertificate, logChi := chi178LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870796287/274867748864) } }, logDArg := sk232LogDArgCertificate }

private noncomputable def leaf2814InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2814LocalValidity :
    LeafFacts leaf2814Box leaf2814Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2814Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433874432) }) = true
      norm_num [leaf2814Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2814CertificateValid :
    WideCertificateValid leaf2814Box leaf2814Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk232ValidityFacts chi178ValidityFacts
    leaf2814LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2814CoverageChecked :
    coverageCheck (innerAD leaf2814Box) leaf2814InnerLog = true := by
  rfl'

private theorem leaf2814InnerLogValid :
    leaf2814InnerLog.Valid 8 (innerAD leaf2814Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2814CoverageChecked

private noncomputable def leaf2814InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629267/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2814InputLogOnePlusV_eq :
    leaf2814InputLogOnePlusV = outerEnclosure 24
      (leaf2814Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2814RoundedFacts : LeafRoundedFacts 8
    leaf2814Certificate.logOnePlusV leaf2814InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2814InputLogOnePlusV_eq }

private noncomputable def leaf2814Inputs : Inputs :=
  inputsOfCaches globalInput sk232RoundedInputs
    chi178InputQChi innerPair50Input
    leaf2814InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2814LowerChecked :
    lowerCheck 24 leaf2814Box leaf2814Inputs = true := by
  rfl'

private theorem leaf2814CoversExact : CoversExact 8
    leaf2814Box leaf2814Certificate leaf2814InnerLog leaf2814Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk232RoundedFacts chi178RoundedFacts
    innerPair50RoundedFacts leaf2814RoundedFacts (by rfl)

private theorem leaf2814FlatSound : Sound leaf2814Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2814CertificateValid
    leaf2814InnerLogValid leaf2814CoversExact leaf2814LowerChecked

private noncomputable def component58Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (1/8), chiHi := (33/256) }

set_option maxRecDepth 1000000 in
private theorem component58Node0_sound : Sound component58Node0Box :=
  sound_of_literal_split component58Node0Box leaf2751Box leaf2752Box
    .chi (65/512) (by rfl) (by rfl)
    leaf2751FlatSound leaf2752FlatSound

private noncomputable def component58Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (33/256), chiHi := (17/128) }

set_option maxRecDepth 1000000 in
private theorem component58Node1_sound : Sound component58Node1Box :=
  sound_of_literal_split component58Node1Box leaf2753Box leaf2754Box
    .chi (67/512) (by rfl) (by rfl)
    leaf2753FlatSound leaf2754FlatSound

private noncomputable def component58Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (1/8), chiHi := (17/128) }

set_option maxRecDepth 1000000 in
private theorem component58Node2_sound : Sound component58Node2Box :=
  sound_of_literal_split component58Node2Box component58Node0Box component58Node1Box
    .chi (33/256) (by rfl) (by rfl)
    component58Node0_sound component58Node1_sound

private noncomputable def component58Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (1/8), chiHi := (33/256) }

set_option maxRecDepth 1000000 in
private theorem component58Node3_sound : Sound component58Node3Box :=
  sound_of_literal_split component58Node3Box leaf2755Box leaf2756Box
    .chi (65/512) (by rfl) (by rfl)
    leaf2755FlatSound leaf2756FlatSound

private noncomputable def component58Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (33/256), chiHi := (17/128) }

set_option maxRecDepth 1000000 in
private theorem component58Node4_sound : Sound component58Node4Box :=
  sound_of_literal_split component58Node4Box leaf2757Box leaf2758Box
    .chi (67/512) (by rfl) (by rfl)
    leaf2757FlatSound leaf2758FlatSound

private noncomputable def component58Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (1/8), chiHi := (17/128) }

set_option maxRecDepth 1000000 in
private theorem component58Node5_sound : Sound component58Node5Box :=
  sound_of_literal_split component58Node5Box component58Node3Box component58Node4Box
    .chi (33/256) (by rfl) (by rfl)
    component58Node3_sound component58Node4_sound

private noncomputable def component58Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (1/8), chiHi := (17/128) }

set_option maxRecDepth 1000000 in
private theorem component58Node6_sound : Sound component58Node6Box :=
  sound_of_literal_split component58Node6Box component58Node2Box component58Node5Box
    .k (121/32) (by rfl) (by rfl)
    component58Node2_sound component58Node5_sound

private noncomputable def component58Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (17/128), chiHi := (35/256) }

set_option maxRecDepth 1000000 in
private theorem component58Node7_sound : Sound component58Node7Box :=
  sound_of_literal_split component58Node7Box leaf2759Box leaf2760Box
    .k (241/64) (by rfl) (by rfl)
    leaf2759FlatSound leaf2760FlatSound

private noncomputable def component58Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (35/256), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component58Node8_sound : Sound component58Node8Box :=
  sound_of_literal_split component58Node8Box leaf2761Box leaf2762Box
    .k (241/64) (by rfl) (by rfl)
    leaf2761FlatSound leaf2762FlatSound

private noncomputable def component58Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (17/128), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component58Node9_sound : Sound component58Node9Box :=
  sound_of_literal_split component58Node9Box component58Node7Box component58Node8Box
    .chi (35/256) (by rfl) (by rfl)
    component58Node7_sound component58Node8_sound

private noncomputable def component58Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (17/128), chiHi := (35/256) }

set_option maxRecDepth 1000000 in
private theorem component58Node10_sound : Sound component58Node10Box :=
  sound_of_literal_split component58Node10Box leaf2763Box leaf2764Box
    .k (243/64) (by rfl) (by rfl)
    leaf2763FlatSound leaf2764FlatSound

private noncomputable def component58Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (35/256), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component58Node11_sound : Sound component58Node11Box :=
  sound_of_literal_split component58Node11Box leaf2765Box leaf2766Box
    .k (243/64) (by rfl) (by rfl)
    leaf2765FlatSound leaf2766FlatSound

private noncomputable def component58Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (17/128), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component58Node12_sound : Sound component58Node12Box :=
  sound_of_literal_split component58Node12Box component58Node10Box component58Node11Box
    .chi (35/256) (by rfl) (by rfl)
    component58Node10_sound component58Node11_sound

private noncomputable def component58Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (17/128), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component58Node13_sound : Sound component58Node13Box :=
  sound_of_literal_split component58Node13Box component58Node9Box component58Node12Box
    .k (121/32) (by rfl) (by rfl)
    component58Node9_sound component58Node12_sound

private noncomputable def component58Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (1/8), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component58Node14_sound : Sound component58Node14Box :=
  sound_of_literal_split component58Node14Box component58Node6Box component58Node13Box
    .chi (17/128) (by rfl) (by rfl)
    component58Node6_sound component58Node13_sound

private noncomputable def component58Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (1/8), chiHi := (33/256) }

set_option maxRecDepth 1000000 in
private theorem component58Node15_sound : Sound component58Node15Box :=
  sound_of_literal_split component58Node15Box leaf2767Box leaf2768Box
    .chi (65/512) (by rfl) (by rfl)
    leaf2767FlatSound leaf2768FlatSound

private noncomputable def component58Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (33/256), chiHi := (17/128) }

set_option maxRecDepth 1000000 in
private theorem component58Node16_sound : Sound component58Node16Box :=
  sound_of_literal_split component58Node16Box leaf2769Box leaf2770Box
    .chi (67/512) (by rfl) (by rfl)
    leaf2769FlatSound leaf2770FlatSound

private noncomputable def component58Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (1/8), chiHi := (17/128) }

set_option maxRecDepth 1000000 in
private theorem component58Node17_sound : Sound component58Node17Box :=
  sound_of_literal_split component58Node17Box component58Node15Box component58Node16Box
    .chi (33/256) (by rfl) (by rfl)
    component58Node15_sound component58Node16_sound

private noncomputable def component58Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (1/8), chiHi := (33/256) }

set_option maxRecDepth 1000000 in
private theorem component58Node18_sound : Sound component58Node18Box :=
  sound_of_literal_split component58Node18Box leaf2771Box leaf2772Box
    .chi (65/512) (by rfl) (by rfl)
    leaf2771FlatSound leaf2772FlatSound

private noncomputable def component58Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (33/256), chiHi := (17/128) }

set_option maxRecDepth 1000000 in
private theorem component58Node19_sound : Sound component58Node19Box :=
  sound_of_literal_split component58Node19Box leaf2773Box leaf2774Box
    .chi (67/512) (by rfl) (by rfl)
    leaf2773FlatSound leaf2774FlatSound

private noncomputable def component58Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (1/8), chiHi := (17/128) }

set_option maxRecDepth 1000000 in
private theorem component58Node20_sound : Sound component58Node20Box :=
  sound_of_literal_split component58Node20Box component58Node18Box component58Node19Box
    .chi (33/256) (by rfl) (by rfl)
    component58Node18_sound component58Node19_sound

private noncomputable def component58Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (1/8), chiHi := (17/128) }

set_option maxRecDepth 1000000 in
private theorem component58Node21_sound : Sound component58Node21Box :=
  sound_of_literal_split component58Node21Box component58Node17Box component58Node20Box
    .k (123/32) (by rfl) (by rfl)
    component58Node17_sound component58Node20_sound

private noncomputable def component58Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (17/128), chiHi := (35/256) }

set_option maxRecDepth 1000000 in
private theorem component58Node22_sound : Sound component58Node22Box :=
  sound_of_literal_split component58Node22Box leaf2775Box leaf2776Box
    .k (245/64) (by rfl) (by rfl)
    leaf2775FlatSound leaf2776FlatSound

private noncomputable def component58Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (35/256), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component58Node23_sound : Sound component58Node23Box :=
  sound_of_literal_split component58Node23Box leaf2777Box leaf2778Box
    .k (245/64) (by rfl) (by rfl)
    leaf2777FlatSound leaf2778FlatSound

private noncomputable def component58Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (17/128), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component58Node24_sound : Sound component58Node24Box :=
  sound_of_literal_split component58Node24Box component58Node22Box component58Node23Box
    .chi (35/256) (by rfl) (by rfl)
    component58Node22_sound component58Node23_sound

private noncomputable def component58Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (17/128), chiHi := (35/256) }

set_option maxRecDepth 1000000 in
private theorem component58Node25_sound : Sound component58Node25Box :=
  sound_of_literal_split component58Node25Box leaf2779Box leaf2780Box
    .chi (69/512) (by rfl) (by rfl)
    leaf2779FlatSound leaf2780FlatSound

private noncomputable def component58Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (35/256), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component58Node26_sound : Sound component58Node26Box :=
  sound_of_literal_split component58Node26Box leaf2781Box leaf2782Box
    .k (247/64) (by rfl) (by rfl)
    leaf2781FlatSound leaf2782FlatSound

private noncomputable def component58Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (17/128), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component58Node27_sound : Sound component58Node27Box :=
  sound_of_literal_split component58Node27Box component58Node25Box component58Node26Box
    .chi (35/256) (by rfl) (by rfl)
    component58Node25_sound component58Node26_sound

private noncomputable def component58Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (17/128), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component58Node28_sound : Sound component58Node28Box :=
  sound_of_literal_split component58Node28Box component58Node24Box component58Node27Box
    .k (123/32) (by rfl) (by rfl)
    component58Node24_sound component58Node27_sound

private noncomputable def component58Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (1/8), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component58Node29_sound : Sound component58Node29Box :=
  sound_of_literal_split component58Node29Box component58Node21Box component58Node28Box
    .chi (17/128) (by rfl) (by rfl)
    component58Node21_sound component58Node28_sound

private noncomputable def component58Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (1/8), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component58Node30_sound : Sound component58Node30Box :=
  sound_of_literal_split component58Node30Box component58Node14Box component58Node29Box
    .k (61/16) (by rfl) (by rfl)
    component58Node14_sound component58Node29_sound

private noncomputable def component58Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (9/64), chiHi := (37/256) }

set_option maxRecDepth 1000000 in
private theorem component58Node31_sound : Sound component58Node31Box :=
  sound_of_literal_split component58Node31Box leaf2783Box leaf2784Box
    .k (241/64) (by rfl) (by rfl)
    leaf2783FlatSound leaf2784FlatSound

private noncomputable def component58Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (37/256), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component58Node32_sound : Sound component58Node32Box :=
  sound_of_literal_split component58Node32Box leaf2785Box leaf2786Box
    .k (241/64) (by rfl) (by rfl)
    leaf2785FlatSound leaf2786FlatSound

private noncomputable def component58Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (9/64), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component58Node33_sound : Sound component58Node33Box :=
  sound_of_literal_split component58Node33Box component58Node31Box component58Node32Box
    .chi (37/256) (by rfl) (by rfl)
    component58Node31_sound component58Node32_sound

private noncomputable def component58Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (9/64), chiHi := (37/256) }

set_option maxRecDepth 1000000 in
private theorem component58Node34_sound : Sound component58Node34Box :=
  sound_of_literal_split component58Node34Box leaf2787Box leaf2788Box
    .k (243/64) (by rfl) (by rfl)
    leaf2787FlatSound leaf2788FlatSound

private noncomputable def component58Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (37/256), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component58Node35_sound : Sound component58Node35Box :=
  sound_of_literal_split component58Node35Box leaf2789Box leaf2790Box
    .k (243/64) (by rfl) (by rfl)
    leaf2789FlatSound leaf2790FlatSound

private noncomputable def component58Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (9/64), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component58Node36_sound : Sound component58Node36Box :=
  sound_of_literal_split component58Node36Box component58Node34Box component58Node35Box
    .chi (37/256) (by rfl) (by rfl)
    component58Node34_sound component58Node35_sound

private noncomputable def component58Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (9/64), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component58Node37_sound : Sound component58Node37Box :=
  sound_of_literal_split component58Node37Box component58Node33Box component58Node36Box
    .k (121/32) (by rfl) (by rfl)
    component58Node33_sound component58Node36_sound

private noncomputable def component58Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (19/128), chiHi := (39/256) }

set_option maxRecDepth 1000000 in
private theorem component58Node38_sound : Sound component58Node38Box :=
  sound_of_literal_split component58Node38Box leaf2791Box leaf2792Box
    .k (241/64) (by rfl) (by rfl)
    leaf2791FlatSound leaf2792FlatSound

private noncomputable def component58Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (39/256), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component58Node39_sound : Sound component58Node39Box :=
  sound_of_literal_split component58Node39Box leaf2793Box leaf2794Box
    .k (241/64) (by rfl) (by rfl)
    leaf2793FlatSound leaf2794FlatSound

private noncomputable def component58Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (19/128), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component58Node40_sound : Sound component58Node40Box :=
  sound_of_literal_split component58Node40Box component58Node38Box component58Node39Box
    .chi (39/256) (by rfl) (by rfl)
    component58Node38_sound component58Node39_sound

private noncomputable def component58Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (19/128), chiHi := (39/256) }

set_option maxRecDepth 1000000 in
private theorem component58Node41_sound : Sound component58Node41Box :=
  sound_of_literal_split component58Node41Box leaf2795Box leaf2796Box
    .k (243/64) (by rfl) (by rfl)
    leaf2795FlatSound leaf2796FlatSound

private noncomputable def component58Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (39/256), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component58Node42_sound : Sound component58Node42Box :=
  sound_of_literal_split component58Node42Box leaf2797Box leaf2798Box
    .k (243/64) (by rfl) (by rfl)
    leaf2797FlatSound leaf2798FlatSound

private noncomputable def component58Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (19/128), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component58Node43_sound : Sound component58Node43Box :=
  sound_of_literal_split component58Node43Box component58Node41Box component58Node42Box
    .chi (39/256) (by rfl) (by rfl)
    component58Node41_sound component58Node42_sound

private noncomputable def component58Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (19/128), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component58Node44_sound : Sound component58Node44Box :=
  sound_of_literal_split component58Node44Box component58Node40Box component58Node43Box
    .k (121/32) (by rfl) (by rfl)
    component58Node40_sound component58Node43_sound

private noncomputable def component58Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (9/64), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component58Node45_sound : Sound component58Node45Box :=
  sound_of_literal_split component58Node45Box component58Node37Box component58Node44Box
    .chi (19/128) (by rfl) (by rfl)
    component58Node37_sound component58Node44_sound

private noncomputable def component58Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (9/64), chiHi := (37/256) }

set_option maxRecDepth 1000000 in
private theorem component58Node46_sound : Sound component58Node46Box :=
  sound_of_literal_split component58Node46Box leaf2799Box leaf2800Box
    .k (245/64) (by rfl) (by rfl)
    leaf2799FlatSound leaf2800FlatSound

private noncomputable def component58Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (37/256), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component58Node47_sound : Sound component58Node47Box :=
  sound_of_literal_split component58Node47Box leaf2801Box leaf2802Box
    .k (245/64) (by rfl) (by rfl)
    leaf2801FlatSound leaf2802FlatSound

private noncomputable def component58Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (9/64), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component58Node48_sound : Sound component58Node48Box :=
  sound_of_literal_split component58Node48Box component58Node46Box component58Node47Box
    .chi (37/256) (by rfl) (by rfl)
    component58Node46_sound component58Node47_sound

private noncomputable def component58Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (9/64), chiHi := (37/256) }

set_option maxRecDepth 1000000 in
private theorem component58Node49_sound : Sound component58Node49Box :=
  sound_of_literal_split component58Node49Box leaf2803Box leaf2804Box
    .k (247/64) (by rfl) (by rfl)
    leaf2803FlatSound leaf2804FlatSound

private noncomputable def component58Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (37/256), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component58Node50_sound : Sound component58Node50Box :=
  sound_of_literal_split component58Node50Box leaf2805Box leaf2806Box
    .k (247/64) (by rfl) (by rfl)
    leaf2805FlatSound leaf2806FlatSound

private noncomputable def component58Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (9/64), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component58Node51_sound : Sound component58Node51Box :=
  sound_of_literal_split component58Node51Box component58Node49Box component58Node50Box
    .chi (37/256) (by rfl) (by rfl)
    component58Node49_sound component58Node50_sound

private noncomputable def component58Node52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (9/64), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component58Node52_sound : Sound component58Node52Box :=
  sound_of_literal_split component58Node52Box component58Node48Box component58Node51Box
    .k (123/32) (by rfl) (by rfl)
    component58Node48_sound component58Node51_sound

private noncomputable def component58Node53Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (19/128), chiHi := (39/256) }

set_option maxRecDepth 1000000 in
private theorem component58Node53_sound : Sound component58Node53Box :=
  sound_of_literal_split component58Node53Box leaf2807Box leaf2808Box
    .k (245/64) (by rfl) (by rfl)
    leaf2807FlatSound leaf2808FlatSound

private noncomputable def component58Node54Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (39/256), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component58Node54_sound : Sound component58Node54Box :=
  sound_of_literal_split component58Node54Box leaf2809Box leaf2810Box
    .k (245/64) (by rfl) (by rfl)
    leaf2809FlatSound leaf2810FlatSound

private noncomputable def component58Node55Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (19/128), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component58Node55_sound : Sound component58Node55Box :=
  sound_of_literal_split component58Node55Box component58Node53Box component58Node54Box
    .chi (39/256) (by rfl) (by rfl)
    component58Node53_sound component58Node54_sound

private noncomputable def component58Node56Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (19/128), chiHi := (39/256) }

set_option maxRecDepth 1000000 in
private theorem component58Node56_sound : Sound component58Node56Box :=
  sound_of_literal_split component58Node56Box leaf2811Box leaf2812Box
    .k (247/64) (by rfl) (by rfl)
    leaf2811FlatSound leaf2812FlatSound

private noncomputable def component58Node57Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (39/256), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component58Node57_sound : Sound component58Node57Box :=
  sound_of_literal_split component58Node57Box leaf2813Box leaf2814Box
    .k (247/64) (by rfl) (by rfl)
    leaf2813FlatSound leaf2814FlatSound

private noncomputable def component58Node58Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (19/128), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component58Node58_sound : Sound component58Node58Box :=
  sound_of_literal_split component58Node58Box component58Node56Box component58Node57Box
    .chi (39/256) (by rfl) (by rfl)
    component58Node56_sound component58Node57_sound

private noncomputable def component58Node59Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (19/128), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component58Node59_sound : Sound component58Node59Box :=
  sound_of_literal_split component58Node59Box component58Node55Box component58Node58Box
    .k (123/32) (by rfl) (by rfl)
    component58Node55_sound component58Node58_sound

private noncomputable def component58Node60Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (9/64), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component58Node60_sound : Sound component58Node60Box :=
  sound_of_literal_split component58Node60Box component58Node52Box component58Node59Box
    .chi (19/128) (by rfl) (by rfl)
    component58Node52_sound component58Node59_sound

private noncomputable def component58Node61Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (9/64), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component58Node61_sound : Sound component58Node61Box :=
  sound_of_literal_split component58Node61Box component58Node45Box component58Node60Box
    .k (61/16) (by rfl) (by rfl)
    component58Node45_sound component58Node60_sound

noncomputable def component58Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (1/8), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
theorem component58_sound : Sound component58Box :=
  sound_of_literal_split component58Box component58Node30Box component58Node61Box
    .chi (9/64) (by rfl) (by rfl)
    component58Node30_sound component58Node61_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
