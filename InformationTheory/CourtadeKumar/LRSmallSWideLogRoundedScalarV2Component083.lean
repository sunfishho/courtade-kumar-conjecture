import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch5
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch8
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheSKBatch1

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

private noncomputable def leaf4032Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (89/32), chiLo := (5/16), chiHi := (41/128) }

private noncomputable def leaf4032Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435715/268435456) }, vSqrt := { lower := (32765/32768), upper := (4581232913/4581049344) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (499075071/268435456) }, upper := { exponent := 0, mantissa := (7745/4096) } }, logOuter := sk107LogOuterCertificate, logK := sk107LogKCertificate, logChi := chi249LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (9162282257/9162098688) } }, logDArg := sk107LogDArgCertificate }

private noncomputable def leaf4032InnerLog : WideLogData :=
  innerPair92Data

set_option maxRecDepth 1000000 in
private theorem leaf4032LocalValidity :
    LeafFacts leaf4032Box leaf4032Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4032Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4581232913/4581049344) }) = true
      norm_num [leaf4032Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4032CertificateValid :
    WideCertificateValid leaf4032Box leaf4032Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk107ValidityFacts chi249ValidityFacts
    leaf4032LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4032CoverageChecked :
    coverageCheck (innerAD leaf4032Box) leaf4032InnerLog = true := by
  rfl'

private theorem leaf4032InnerLogValid :
    leaf4032InnerLog.Valid 8 (innerAD leaf4032Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint23PositiveFacts.valid leaf4032CoverageChecked

private noncomputable def leaf4032InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629417/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4032InputLogOnePlusV_eq :
    leaf4032InputLogOnePlusV = outerEnclosure 24
      (leaf4032Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4032RoundedFacts : LeafRoundedFacts 8
    leaf4032Certificate.logOnePlusV leaf4032InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4032InputLogOnePlusV_eq }

private noncomputable def leaf4032Inputs : Inputs :=
  inputsOfCaches globalInput sk107RoundedInputs
    chi249InputQChi innerPair92Input
    leaf4032InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4032LowerChecked :
    lowerCheck 24 leaf4032Box leaf4032Inputs = true := by
  rfl'

private theorem leaf4032CoversExact : CoversExact 8
    leaf4032Box leaf4032Certificate leaf4032InnerLog leaf4032Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk107RoundedFacts chi249RoundedFacts
    innerPair92RoundedFacts leaf4032RoundedFacts (by rfl)

private theorem leaf4032FlatSound : Sound leaf4032Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4032CertificateValid
    leaf4032InnerLogValid leaf4032CoversExact leaf4032LowerChecked

private noncomputable def leaf4033Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (89/32), chiLo := (41/128), chiHi := (21/64) }

private noncomputable def leaf4033Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435717/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68715649024) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (504841885/268435456) }, upper := { exponent := 0, mantissa := (3917/2048) } }, logOuter := sk107LogOuterCertificate, logK := sk107LogKCertificate, logChi := chi250LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434142719/137431298048) } }, logDArg := sk107LogDArgCertificate }

private noncomputable def leaf4033InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4033LocalValidity :
    LeafFacts leaf4033Box leaf4033Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4033Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68715649024) }) = true
      norm_num [leaf4033Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4033CertificateValid :
    WideCertificateValid leaf4033Box leaf4033Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk107ValidityFacts chi250ValidityFacts
    leaf4033LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4033CoverageChecked :
    coverageCheck (innerAD leaf4033Box) leaf4033InnerLog = true := by
  rfl'

private theorem leaf4033InnerLogValid :
    leaf4033InnerLog.Valid 8 (innerAD leaf4033Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4033CoverageChecked

private noncomputable def leaf4033InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907357/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4033InputLogOnePlusV_eq :
    leaf4033InputLogOnePlusV = outerEnclosure 24
      (leaf4033Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4033RoundedFacts : LeafRoundedFacts 8
    leaf4033Certificate.logOnePlusV leaf4033InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4033InputLogOnePlusV_eq }

private noncomputable def leaf4033Inputs : Inputs :=
  inputsOfCaches globalInput sk107RoundedInputs
    chi250InputQChi innerPair100Input
    leaf4033InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4033LowerChecked :
    lowerCheck 24 leaf4033Box leaf4033Inputs = true := by
  rfl'

private theorem leaf4033CoversExact : CoversExact 8
    leaf4033Box leaf4033Certificate leaf4033InnerLog leaf4033Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk107RoundedFacts chi250RoundedFacts
    innerPair100RoundedFacts leaf4033RoundedFacts (by rfl)

private theorem leaf4033FlatSound : Sound leaf4033Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4033CertificateValid
    leaf4033InnerLogValid leaf4033CoversExact leaf4033LowerChecked

private noncomputable def leaf4034Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (89/32), kHi := (45/16), chiLo := (5/16), chiHi := (41/128) }

private noncomputable def leaf4034Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435717/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68715698176) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (501696349/268435456) }, upper := { exponent := 0, mantissa := (3893/2048) } }, logOuter := sk108LogOuterCertificate, logK := sk108LogKCertificate, logChi := chi249LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434191871/137431396352) } }, logDArg := sk108LogDArgCertificate }

private noncomputable def leaf4034InnerLog : WideLogData :=
  innerPair92Data

set_option maxRecDepth 1000000 in
private theorem leaf4034LocalValidity :
    LeafFacts leaf4034Box leaf4034Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4034Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68715698176) }) = true
      norm_num [leaf4034Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4034CertificateValid :
    WideCertificateValid leaf4034Box leaf4034Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk108ValidityFacts chi249ValidityFacts
    leaf4034LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4034CoverageChecked :
    coverageCheck (innerAD leaf4034Box) leaf4034InnerLog = true := by
  rfl'

private theorem leaf4034InnerLogValid :
    leaf4034InnerLog.Valid 8 (innerAD leaf4034Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint23PositiveFacts.valid leaf4034CoverageChecked

private noncomputable def leaf4034InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814711/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4034InputLogOnePlusV_eq :
    leaf4034InputLogOnePlusV = outerEnclosure 24
      (leaf4034Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4034RoundedFacts : LeafRoundedFacts 8
    leaf4034Certificate.logOnePlusV leaf4034InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4034InputLogOnePlusV_eq }

private noncomputable def leaf4034Inputs : Inputs :=
  inputsOfCaches globalInput sk108RoundedInputs
    chi249InputQChi innerPair92Input
    leaf4034InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4034LowerChecked :
    lowerCheck 24 leaf4034Box leaf4034Inputs = true := by
  rfl'

private theorem leaf4034CoversExact : CoversExact 8
    leaf4034Box leaf4034Certificate leaf4034InnerLog leaf4034Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk108RoundedFacts chi249RoundedFacts
    innerPair92RoundedFacts leaf4034RoundedFacts (by rfl)

private theorem leaf4034FlatSound : Sound leaf4034Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4034CertificateValid
    leaf4034InnerLogValid leaf4034CoversExact leaf4034LowerChecked

private noncomputable def leaf4035Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (89/32), kHi := (45/16), chiLo := (41/128), chiHi := (21/64) }

private noncomputable def leaf4035Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435719/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68715606016) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (507528695/268435456) }, upper := { exponent := 0, mantissa := (1969/1024) } }, logOuter := sk108LogOuterCertificate, logK := sk108LogKCertificate, logChi := chi250LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434099711/137431212032) } }, logDArg := sk108LogDArgCertificate }

private noncomputable def leaf4035InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4035LocalValidity :
    LeafFacts leaf4035Box leaf4035Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4035Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68715606016) }) = true
      norm_num [leaf4035Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4035CertificateValid :
    WideCertificateValid leaf4035Box leaf4035Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk108ValidityFacts chi250ValidityFacts
    leaf4035LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4035CoverageChecked :
    coverageCheck (innerAD leaf4035Box) leaf4035InnerLog = true := by
  rfl'

private theorem leaf4035InnerLogValid :
    leaf4035InnerLog.Valid 8 (innerAD leaf4035Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4035CoverageChecked

private noncomputable def leaf4035InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629433/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4035InputLogOnePlusV_eq :
    leaf4035InputLogOnePlusV = outerEnclosure 24
      (leaf4035Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4035RoundedFacts : LeafRoundedFacts 8
    leaf4035Certificate.logOnePlusV leaf4035InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4035InputLogOnePlusV_eq }

private noncomputable def leaf4035Inputs : Inputs :=
  inputsOfCaches globalInput sk108RoundedInputs
    chi250InputQChi innerPair100Input
    leaf4035InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4035LowerChecked :
    lowerCheck 24 leaf4035Box leaf4035Inputs = true := by
  rfl'

private theorem leaf4035CoversExact : CoversExact 8
    leaf4035Box leaf4035Certificate leaf4035InnerLog leaf4035Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk108RoundedFacts chi250RoundedFacts
    innerPair100RoundedFacts leaf4035RoundedFacts (by rfl)

private theorem leaf4035FlatSound : Sound leaf4035Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4035CertificateValid
    leaf4035InnerLogValid leaf4035CoversExact leaf4035LowerChecked

private noncomputable def leaf4036Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (89/32), chiLo := (21/64), chiHi := (43/128) }

private noncomputable def leaf4036Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435719/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68715557888) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (510608699/268435456) }, upper := { exponent := 0, mantissa := (7923/4096) } }, logOuter := sk107LogOuterCertificate, logK := sk107LogKCertificate, logChi := chi251LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434051583/137431115776) } }, logDArg := sk107LogDArgCertificate }

private noncomputable def leaf4036InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4036LocalValidity :
    LeafFacts leaf4036Box leaf4036Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4036Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68715557888) }) = true
      norm_num [leaf4036Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4036CertificateValid :
    WideCertificateValid leaf4036Box leaf4036Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk107ValidityFacts chi251ValidityFacts
    leaf4036LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4036CoverageChecked :
    coverageCheck (innerAD leaf4036Box) leaf4036InnerLog = true := by
  rfl'

private theorem leaf4036InnerLogValid :
    leaf4036InnerLog.Valid 8 (innerAD leaf4036Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4036CoverageChecked

private noncomputable def leaf4036InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629439/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4036InputLogOnePlusV_eq :
    leaf4036InputLogOnePlusV = outerEnclosure 24
      (leaf4036Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4036RoundedFacts : LeafRoundedFacts 8
    leaf4036Certificate.logOnePlusV leaf4036InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4036InputLogOnePlusV_eq }

private noncomputable def leaf4036Inputs : Inputs :=
  inputsOfCaches globalInput sk107RoundedInputs
    chi251InputQChi innerPair100Input
    leaf4036InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4036LowerChecked :
    lowerCheck 24 leaf4036Box leaf4036Inputs = true := by
  rfl'

private theorem leaf4036CoversExact : CoversExact 8
    leaf4036Box leaf4036Certificate leaf4036InnerLog leaf4036Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk107RoundedFacts chi251RoundedFacts
    innerPair100RoundedFacts leaf4036RoundedFacts (by rfl)

private theorem leaf4036FlatSound : Sound leaf4036Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4036CertificateValid
    leaf4036InnerLogValid leaf4036CoversExact leaf4036LowerChecked

private noncomputable def leaf4037Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (89/32), chiLo := (43/128), chiHi := (11/32) }

private noncomputable def leaf4037Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435721/268435456) }, vSqrt := { lower := (32765/32768), upper := (22906164565/22905155584) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (516375513/268435456) }, upper := { exponent := 0, mantissa := (2003/1024) } }, logOuter := sk107LogOuterCertificate, logK := sk107LogKCertificate, logChi := chi252LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (45811320149/45810311168) } }, logDArg := sk107LogDArgCertificate }

private noncomputable def leaf4037InnerLog : WideLogData :=
  innerPair101Data

set_option maxRecDepth 1000000 in
private theorem leaf4037LocalValidity :
    LeafFacts leaf4037Box leaf4037Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4037Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (22906164565/22905155584) }) = true
      norm_num [leaf4037Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4037CertificateValid :
    WideCertificateValid leaf4037Box leaf4037Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk107ValidityFacts chi252ValidityFacts
    leaf4037LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4037CoverageChecked :
    coverageCheck (innerAD leaf4037Box) leaf4037InnerLog = true := by
  rfl'

private theorem leaf4037InnerLogValid :
    leaf4037InnerLog.Valid 8 (innerAD leaf4037Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint24PositiveFacts.valid leaf4037CoverageChecked

private noncomputable def leaf4037InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814725/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4037InputLogOnePlusV_eq :
    leaf4037InputLogOnePlusV = outerEnclosure 24
      (leaf4037Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4037RoundedFacts : LeafRoundedFacts 8
    leaf4037Certificate.logOnePlusV leaf4037InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4037InputLogOnePlusV_eq }

private noncomputable def leaf4037Inputs : Inputs :=
  inputsOfCaches globalInput sk107RoundedInputs
    chi252InputQChi innerPair101Input
    leaf4037InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4037LowerChecked :
    lowerCheck 24 leaf4037Box leaf4037Inputs = true := by
  rfl'

private theorem leaf4037CoversExact : CoversExact 8
    leaf4037Box leaf4037Certificate leaf4037InnerLog leaf4037Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk107RoundedFacts chi252RoundedFacts
    innerPair101RoundedFacts leaf4037RoundedFacts (by rfl)

private theorem leaf4037FlatSound : Sound leaf4037Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4037CertificateValid
    leaf4037InnerLogValid leaf4037CoversExact leaf4037LowerChecked

private noncomputable def leaf4038Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (89/32), kHi := (45/16), chiLo := (21/64), chiHi := (43/128) }

private noncomputable def leaf4038Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435721/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68715513856) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (513361041/268435456) }, upper := { exponent := 0, mantissa := (3983/2048) } }, logOuter := sk108LogOuterCertificate, logK := sk108LogKCertificate, logChi := chi251LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434007551/137431027712) } }, logDArg := sk108LogDArgCertificate }

private noncomputable def leaf4038InnerLog : WideLogData :=
  innerPair101Data

set_option maxRecDepth 1000000 in
private theorem leaf4038LocalValidity :
    LeafFacts leaf4038Box leaf4038Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4038Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68715513856) }) = true
      norm_num [leaf4038Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4038CertificateValid :
    WideCertificateValid leaf4038Box leaf4038Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk108ValidityFacts chi251ValidityFacts
    leaf4038LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4038CoverageChecked :
    coverageCheck (innerAD leaf4038Box) leaf4038InnerLog = true := by
  rfl'

private theorem leaf4038InnerLogValid :
    leaf4038InnerLog.Valid 8 (innerAD leaf4038Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint24PositiveFacts.valid leaf4038CoverageChecked

private noncomputable def leaf4038InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629445/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4038InputLogOnePlusV_eq :
    leaf4038InputLogOnePlusV = outerEnclosure 24
      (leaf4038Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4038RoundedFacts : LeafRoundedFacts 8
    leaf4038Certificate.logOnePlusV leaf4038InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4038InputLogOnePlusV_eq }

private noncomputable def leaf4038Inputs : Inputs :=
  inputsOfCaches globalInput sk108RoundedInputs
    chi251InputQChi innerPair101Input
    leaf4038InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4038LowerChecked :
    lowerCheck 24 leaf4038Box leaf4038Inputs = true := by
  rfl'

private theorem leaf4038CoversExact : CoversExact 8
    leaf4038Box leaf4038Certificate leaf4038InnerLog leaf4038Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk108RoundedFacts chi251RoundedFacts
    innerPair101RoundedFacts leaf4038RoundedFacts (by rfl)

private theorem leaf4038FlatSound : Sound leaf4038Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4038CertificateValid
    leaf4038InnerLogValid leaf4038CoversExact leaf4038LowerChecked

private noncomputable def leaf4039Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (89/32), kHi := (45/16), chiLo := (43/128), chiHi := (11/32) }

private noncomputable def leaf4039Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435723/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68715421696) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (519193387/268435456) }, upper := { exponent := 0, mantissa := (1007/512) } }, logOuter := sk108LogOuterCertificate, logK := sk108LogKCertificate, logChi := chi252LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137433915391/137430843392) } }, logDArg := sk108LogDArgCertificate }

private noncomputable def leaf4039InnerLog : WideLogData :=
  innerPair101Data

set_option maxRecDepth 1000000 in
private theorem leaf4039LocalValidity :
    LeafFacts leaf4039Box leaf4039Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4039Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68715421696) }) = true
      norm_num [leaf4039Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4039CertificateValid :
    WideCertificateValid leaf4039Box leaf4039Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk108ValidityFacts chi252ValidityFacts
    leaf4039LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4039CoverageChecked :
    coverageCheck (innerAD leaf4039Box) leaf4039InnerLog = true := by
  rfl'

private theorem leaf4039InnerLogValid :
    leaf4039InnerLog.Valid 8 (innerAD leaf4039Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint24PositiveFacts.valid leaf4039CoverageChecked

private noncomputable def leaf4039InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (726841/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf4039InputLogOnePlusV_eq :
    leaf4039InputLogOnePlusV = outerEnclosure 24
      (leaf4039Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4039RoundedFacts : LeafRoundedFacts 8
    leaf4039Certificate.logOnePlusV leaf4039InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4039InputLogOnePlusV_eq }

private noncomputable def leaf4039Inputs : Inputs :=
  inputsOfCaches globalInput sk108RoundedInputs
    chi252InputQChi innerPair101Input
    leaf4039InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4039LowerChecked :
    lowerCheck 24 leaf4039Box leaf4039Inputs = true := by
  rfl'

private theorem leaf4039CoversExact : CoversExact 8
    leaf4039Box leaf4039Certificate leaf4039InnerLog leaf4039Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk108RoundedFacts chi252RoundedFacts
    innerPair101RoundedFacts leaf4039RoundedFacts (by rfl)

private theorem leaf4039FlatSound : Sound leaf4039Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4039CertificateValid
    leaf4039InnerLogValid leaf4039CoversExact leaf4039LowerChecked

private noncomputable def leaf4040Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (91/32), chiLo := (5/16), chiHi := (41/128) }

private noncomputable def leaf4040Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435719/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68715656192) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (504317627/268435456) }, upper := { exponent := 0, mantissa := (7827/4096) } }, logOuter := sk109LogOuterCertificate, logK := sk109LogKCertificate, logChi := chi249LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434149887/137431312384) } }, logDArg := sk109LogDArgCertificate }

private noncomputable def leaf4040InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4040LocalValidity :
    LeafFacts leaf4040Box leaf4040Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4040Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68715656192) }) = true
      norm_num [leaf4040Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4040CertificateValid :
    WideCertificateValid leaf4040Box leaf4040Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk109ValidityFacts chi249ValidityFacts
    leaf4040LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4040CoverageChecked :
    coverageCheck (innerAD leaf4040Box) leaf4040InnerLog = true := by
  rfl'

private theorem leaf4040InnerLogValid :
    leaf4040InnerLog.Valid 8 (innerAD leaf4040Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4040CoverageChecked

private noncomputable def leaf4040InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629427/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4040InputLogOnePlusV_eq :
    leaf4040InputLogOnePlusV = outerEnclosure 24
      (leaf4040Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4040RoundedFacts : LeafRoundedFacts 8
    leaf4040Certificate.logOnePlusV leaf4040InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4040InputLogOnePlusV_eq }

private noncomputable def leaf4040Inputs : Inputs :=
  inputsOfCaches globalInput sk109RoundedInputs
    chi249InputQChi innerPair100Input
    leaf4040InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4040LowerChecked :
    lowerCheck 24 leaf4040Box leaf4040Inputs = true := by
  rfl'

private theorem leaf4040CoversExact : CoversExact 8
    leaf4040Box leaf4040Certificate leaf4040InnerLog leaf4040Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk109RoundedFacts chi249RoundedFacts
    innerPair100RoundedFacts leaf4040RoundedFacts (by rfl)

private theorem leaf4040FlatSound : Sound leaf4040Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4040CertificateValid
    leaf4040InnerLogValid leaf4040CoversExact leaf4040LowerChecked

private noncomputable def leaf4041Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (91/32), kHi := (23/8), chiLo := (5/16), chiHi := (41/128) }

private noncomputable def leaf4041Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435721/268435456) }, vSqrt := { lower := (32765/32768), upper := (22906164565/22905204736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (506938905/268435456) }, upper := { exponent := 0, mantissa := (1967/1024) } }, logOuter := sk110LogOuterCertificate, logK := sk110LogKCertificate, logChi := chi249LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (45811369301/45810409472) } }, logDArg := sk110LogDArgCertificate }

private noncomputable def leaf4041InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4041LocalValidity :
    LeafFacts leaf4041Box leaf4041Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4041Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (22906164565/22905204736) }) = true
      norm_num [leaf4041Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4041CertificateValid :
    WideCertificateValid leaf4041Box leaf4041Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk110ValidityFacts chi249ValidityFacts
    leaf4041LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4041CoverageChecked :
    coverageCheck (innerAD leaf4041Box) leaf4041InnerLog = true := by
  rfl'

private theorem leaf4041InnerLogValid :
    leaf4041InnerLog.Valid 8 (innerAD leaf4041Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4041CoverageChecked

private noncomputable def leaf4041InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (1453679/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf4041InputLogOnePlusV_eq :
    leaf4041InputLogOnePlusV = outerEnclosure 24
      (leaf4041Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4041RoundedFacts : LeafRoundedFacts 8
    leaf4041Certificate.logOnePlusV leaf4041InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4041InputLogOnePlusV_eq }

private noncomputable def leaf4041Inputs : Inputs :=
  inputsOfCaches globalInput sk110RoundedInputs
    chi249InputQChi innerPair100Input
    leaf4041InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4041LowerChecked :
    lowerCheck 24 leaf4041Box leaf4041Inputs = true := by
  rfl'

private theorem leaf4041CoversExact : CoversExact 8
    leaf4041Box leaf4041Certificate leaf4041InnerLog leaf4041Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk110RoundedFacts chi249RoundedFacts
    innerPair100RoundedFacts leaf4041RoundedFacts (by rfl)

private theorem leaf4041FlatSound : Sound leaf4041Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4041CertificateValid
    leaf4041InnerLogValid leaf4041CoversExact leaf4041LowerChecked

private noncomputable def leaf4042Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (91/32), chiLo := (41/128), chiHi := (21/64) }

private noncomputable def leaf4042Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435721/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68715563008) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (510215505/268435456) }, upper := { exponent := 0, mantissa := (3959/2048) } }, logOuter := sk109LogOuterCertificate, logK := sk109LogKCertificate, logChi := chi250LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434056703/137431126016) } }, logDArg := sk109LogDArgCertificate }

private noncomputable def leaf4042InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4042LocalValidity :
    LeafFacts leaf4042Box leaf4042Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4042Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68715563008) }) = true
      norm_num [leaf4042Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4042CertificateValid :
    WideCertificateValid leaf4042Box leaf4042Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk109ValidityFacts chi250ValidityFacts
    leaf4042LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4042CoverageChecked :
    coverageCheck (innerAD leaf4042Box) leaf4042InnerLog = true := by
  rfl'

private theorem leaf4042InnerLogValid :
    leaf4042InnerLog.Valid 8 (innerAD leaf4042Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4042CoverageChecked

private noncomputable def leaf4042InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629439/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4042InputLogOnePlusV_eq :
    leaf4042InputLogOnePlusV = outerEnclosure 24
      (leaf4042Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4042RoundedFacts : LeafRoundedFacts 8
    leaf4042Certificate.logOnePlusV leaf4042InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4042InputLogOnePlusV_eq }

private noncomputable def leaf4042Inputs : Inputs :=
  inputsOfCaches globalInput sk109RoundedInputs
    chi250InputQChi innerPair100Input
    leaf4042InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4042LowerChecked :
    lowerCheck 24 leaf4042Box leaf4042Inputs = true := by
  rfl'

private theorem leaf4042CoversExact : CoversExact 8
    leaf4042Box leaf4042Certificate leaf4042InnerLog leaf4042Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk109RoundedFacts chi250RoundedFacts
    innerPair100RoundedFacts leaf4042RoundedFacts (by rfl)

private theorem leaf4042FlatSound : Sound leaf4042Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4042CertificateValid
    leaf4042InnerLogValid leaf4042CoversExact leaf4042LowerChecked

private noncomputable def leaf4043Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (91/32), kHi := (23/8), chiLo := (41/128), chiHi := (21/64) }

private noncomputable def leaf4043Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435723/268435456) }, vSqrt := { lower := (32765/32768), upper := (13743698739/13743104000) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (512902315/268435456) }, upper := { exponent := 0, mantissa := (995/512) } }, logOuter := sk110LogOuterCertificate, logK := sk110LogKCertificate, logChi := chi250LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (27486802739/27486208000) } }, logDArg := sk110LogDArgCertificate }

private noncomputable def leaf4043InnerLog : WideLogData :=
  innerPair233Data

set_option maxRecDepth 1000000 in
private theorem leaf4043LocalValidity :
    LeafFacts leaf4043Box leaf4043Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4043Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (13743698739/13743104000) }) = true
      norm_num [leaf4043Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4043CertificateValid :
    WideCertificateValid leaf4043Box leaf4043Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk110ValidityFacts chi250ValidityFacts
    leaf4043LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4043CoverageChecked :
    coverageCheck (innerAD leaf4043Box) leaf4043InnerLog = true := by
  rfl'

private theorem leaf4043InnerLogValid :
    leaf4043InnerLog.Valid 8 (innerAD leaf4043Box) :=
  wideLogDataValid_of_cachedCheck endpoint70PositiveFacts
    endpoint71PositiveFacts.valid leaf4043CoverageChecked

private noncomputable def leaf4043InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907361/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4043InputLogOnePlusV_eq :
    leaf4043InputLogOnePlusV = outerEnclosure 24
      (leaf4043Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4043RoundedFacts : LeafRoundedFacts 8
    leaf4043Certificate.logOnePlusV leaf4043InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4043InputLogOnePlusV_eq }

private noncomputable def leaf4043Inputs : Inputs :=
  inputsOfCaches globalInput sk110RoundedInputs
    chi250InputQChi innerPair233Input
    leaf4043InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4043LowerChecked :
    lowerCheck 24 leaf4043Box leaf4043Inputs = true := by
  rfl'

private theorem leaf4043CoversExact : CoversExact 8
    leaf4043Box leaf4043Certificate leaf4043InnerLog leaf4043Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk110RoundedFacts chi250RoundedFacts
    innerPair233RoundedFacts leaf4043RoundedFacts (by rfl)

private theorem leaf4043FlatSound : Sound leaf4043Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4043CertificateValid
    leaf4043InnerLogValid leaf4043CoversExact leaf4043LowerChecked

private noncomputable def leaf4044Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (91/32), chiLo := (21/64), chiHi := (43/128) }

private noncomputable def leaf4044Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435723/268435456) }, vSqrt := { lower := (32765/32768), upper := (22906164565/22905156608) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (516113383/268435456) }, upper := { exponent := 0, mantissa := (8009/4096) } }, logOuter := sk109LogOuterCertificate, logK := sk109LogKCertificate, logChi := chi251LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (45811321173/45810313216) } }, logDArg := sk109LogDArgCertificate }

private noncomputable def leaf4044InnerLog : WideLogData :=
  innerPair101Data

set_option maxRecDepth 1000000 in
private theorem leaf4044LocalValidity :
    LeafFacts leaf4044Box leaf4044Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4044Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (22906164565/22905156608) }) = true
      norm_num [leaf4044Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4044CertificateValid :
    WideCertificateValid leaf4044Box leaf4044Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk109ValidityFacts chi251ValidityFacts
    leaf4044LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4044CoverageChecked :
    coverageCheck (innerAD leaf4044Box) leaf4044InnerLog = true := by
  rfl'

private theorem leaf4044InnerLogValid :
    leaf4044InnerLog.Valid 8 (innerAD leaf4044Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint24PositiveFacts.valid leaf4044CoverageChecked

private noncomputable def leaf4044InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814725/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4044InputLogOnePlusV_eq :
    leaf4044InputLogOnePlusV = outerEnclosure 24
      (leaf4044Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4044RoundedFacts : LeafRoundedFacts 8
    leaf4044Certificate.logOnePlusV leaf4044InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4044InputLogOnePlusV_eq }

private noncomputable def leaf4044Inputs : Inputs :=
  inputsOfCaches globalInput sk109RoundedInputs
    chi251InputQChi innerPair101Input
    leaf4044InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4044LowerChecked :
    lowerCheck 24 leaf4044Box leaf4044Inputs = true := by
  rfl'

private theorem leaf4044CoversExact : CoversExact 8
    leaf4044Box leaf4044Certificate leaf4044InnerLog leaf4044Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk109RoundedFacts chi251RoundedFacts
    innerPair101RoundedFacts leaf4044RoundedFacts (by rfl)

private theorem leaf4044FlatSound : Sound leaf4044Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4044CertificateValid
    leaf4044InnerLogValid leaf4044CoversExact leaf4044LowerChecked

private noncomputable def leaf4045Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (91/32), kHi := (23/8), chiLo := (21/64), chiHi := (43/128) }

private noncomputable def leaf4045Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435725/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68715425792) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (518865725/268435456) }, upper := { exponent := 0, mantissa := (2013/1024) } }, logOuter := sk110LogOuterCertificate, logK := sk110LogKCertificate, logChi := chi251LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137433919487/137430851584) } }, logDArg := sk110LogDArgCertificate }

private noncomputable def leaf4045InnerLog : WideLogData :=
  innerPair101Data

set_option maxRecDepth 1000000 in
private theorem leaf4045LocalValidity :
    LeafFacts leaf4045Box leaf4045Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4045Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68715425792) }) = true
      norm_num [leaf4045Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4045CertificateValid :
    WideCertificateValid leaf4045Box leaf4045Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk110ValidityFacts chi251ValidityFacts
    leaf4045LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4045CoverageChecked :
    coverageCheck (innerAD leaf4045Box) leaf4045InnerLog = true := by
  rfl'

private theorem leaf4045InnerLogValid :
    leaf4045InnerLog.Valid 8 (innerAD leaf4045Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint24PositiveFacts.valid leaf4045CoverageChecked

private noncomputable def leaf4045InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629455/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4045InputLogOnePlusV_eq :
    leaf4045InputLogOnePlusV = outerEnclosure 24
      (leaf4045Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4045RoundedFacts : LeafRoundedFacts 8
    leaf4045Certificate.logOnePlusV leaf4045InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4045InputLogOnePlusV_eq }

private noncomputable def leaf4045Inputs : Inputs :=
  inputsOfCaches globalInput sk110RoundedInputs
    chi251InputQChi innerPair101Input
    leaf4045InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4045LowerChecked :
    lowerCheck 24 leaf4045Box leaf4045Inputs = true := by
  rfl'

private theorem leaf4045CoversExact : CoversExact 8
    leaf4045Box leaf4045Certificate leaf4045InnerLog leaf4045Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk110RoundedFacts chi251RoundedFacts
    innerPair101RoundedFacts leaf4045RoundedFacts (by rfl)

private theorem leaf4045FlatSound : Sound leaf4045Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4045CertificateValid
    leaf4045InnerLogValid leaf4045CoversExact leaf4045LowerChecked

private noncomputable def leaf4046Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (91/32), chiLo := (43/128), chiHi := (11/32) }

private noncomputable def leaf4046Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435725/268435456) }, vSqrt := { lower := (32765/32768), upper := (13743698739/13743075328) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (522011261/268435456) }, upper := { exponent := 0, mantissa := (2025/1024) } }, logOuter := sk109LogOuterCertificate, logK := sk109LogKCertificate, logChi := chi252LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (27486774067/27486150656) } }, logDArg := sk109LogDArgCertificate }

private noncomputable def leaf4046InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4046LocalValidity :
    LeafFacts leaf4046Box leaf4046Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4046Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (13743698739/13743075328) }) = true
      norm_num [leaf4046Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4046CertificateValid :
    WideCertificateValid leaf4046Box leaf4046Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk109ValidityFacts chi252ValidityFacts
    leaf4046LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4046CoverageChecked :
    coverageCheck (innerAD leaf4046Box) leaf4046InnerLog = true := by
  rfl'

private theorem leaf4046InnerLogValid :
    leaf4046InnerLog.Valid 8 (innerAD leaf4046Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4046CoverageChecked

private noncomputable def leaf4046InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629461/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4046InputLogOnePlusV_eq :
    leaf4046InputLogOnePlusV = outerEnclosure 24
      (leaf4046Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4046RoundedFacts : LeafRoundedFacts 8
    leaf4046Certificate.logOnePlusV leaf4046InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4046InputLogOnePlusV_eq }

private noncomputable def leaf4046Inputs : Inputs :=
  inputsOfCaches globalInput sk109RoundedInputs
    chi252InputQChi innerPair108Input
    leaf4046InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4046LowerChecked :
    lowerCheck 24 leaf4046Box leaf4046Inputs = true := by
  rfl'

private theorem leaf4046CoversExact : CoversExact 8
    leaf4046Box leaf4046Certificate leaf4046InnerLog leaf4046Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk109RoundedFacts chi252RoundedFacts
    innerPair108RoundedFacts leaf4046RoundedFacts (by rfl)

private theorem leaf4046FlatSound : Sound leaf4046Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4046CertificateValid
    leaf4046InnerLogValid leaf4046CoversExact leaf4046LowerChecked

private noncomputable def leaf4047Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (91/32), kHi := (23/8), chiLo := (43/128), chiHi := (11/32) }

private noncomputable def leaf4047Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435727/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357665792) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (524829135/268435456) }, upper := { exponent := 0, mantissa := (509/256) } }, logOuter := sk110LogOuterCertificate, logK := sk110LogKCertificate, logChi := chi252LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716388351/68715331584) } }, logDArg := sk110LogDArgCertificate }

private noncomputable def leaf4047InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4047LocalValidity :
    LeafFacts leaf4047Box leaf4047Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4047Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357665792) }) = true
      norm_num [leaf4047Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4047CertificateValid :
    WideCertificateValid leaf4047Box leaf4047Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk110ValidityFacts chi252ValidityFacts
    leaf4047LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4047CoverageChecked :
    coverageCheck (innerAD leaf4047Box) leaf4047InnerLog = true := by
  rfl'

private theorem leaf4047InnerLogValid :
    leaf4047InnerLog.Valid 8 (innerAD leaf4047Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4047CoverageChecked

private noncomputable def leaf4047InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629339/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4047InputLogOnePlusV_eq :
    leaf4047InputLogOnePlusV = outerEnclosure 24
      (leaf4047Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4047RoundedFacts : LeafRoundedFacts 8
    leaf4047Certificate.logOnePlusV leaf4047InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4047InputLogOnePlusV_eq }

private noncomputable def leaf4047Inputs : Inputs :=
  inputsOfCaches globalInput sk110RoundedInputs
    chi252InputQChi innerPair108Input
    leaf4047InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4047LowerChecked :
    lowerCheck 24 leaf4047Box leaf4047Inputs = true := by
  rfl'

private theorem leaf4047CoversExact : CoversExact 8
    leaf4047Box leaf4047Certificate leaf4047InnerLog leaf4047Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk110RoundedFacts chi252RoundedFacts
    innerPair108RoundedFacts leaf4047RoundedFacts (by rfl)

private theorem leaf4047FlatSound : Sound leaf4047Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4047CertificateValid
    leaf4047InnerLogValid leaf4047CoversExact leaf4047LowerChecked

private noncomputable def leaf4048Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (89/32), chiLo := (11/32), chiHi := (45/128) }

private noncomputable def leaf4048Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435723/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68715375616) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (522142327/268435456) }, upper := { exponent := 0, mantissa := (8101/4096) } }, logOuter := sk107LogOuterCertificate, logK := sk107LogKCertificate, logChi := chi253LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137433869311/137430751232) } }, logDArg := sk107LogDArgCertificate }

private noncomputable def leaf4048InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4048LocalValidity :
    LeafFacts leaf4048Box leaf4048Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4048Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68715375616) }) = true
      norm_num [leaf4048Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4048CertificateValid :
    WideCertificateValid leaf4048Box leaf4048Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk107ValidityFacts chi253ValidityFacts
    leaf4048LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4048CoverageChecked :
    coverageCheck (innerAD leaf4048Box) leaf4048InnerLog = true := by
  rfl'

private theorem leaf4048InnerLogValid :
    leaf4048InnerLog.Valid 8 (innerAD leaf4048Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4048CoverageChecked

private noncomputable def leaf4048InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629461/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4048InputLogOnePlusV_eq :
    leaf4048InputLogOnePlusV = outerEnclosure 24
      (leaf4048Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4048RoundedFacts : LeafRoundedFacts 8
    leaf4048Certificate.logOnePlusV leaf4048InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4048InputLogOnePlusV_eq }

private noncomputable def leaf4048Inputs : Inputs :=
  inputsOfCaches globalInput sk107RoundedInputs
    chi253InputQChi innerPair108Input
    leaf4048InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4048LowerChecked :
    lowerCheck 24 leaf4048Box leaf4048Inputs = true := by
  rfl'

private theorem leaf4048CoversExact : CoversExact 8
    leaf4048Box leaf4048Certificate leaf4048InnerLog leaf4048Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk107RoundedFacts chi253RoundedFacts
    innerPair108RoundedFacts leaf4048RoundedFacts (by rfl)

private theorem leaf4048FlatSound : Sound leaf4048Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4048CertificateValid
    leaf4048InnerLogValid leaf4048CoversExact leaf4048LowerChecked

private noncomputable def leaf4049Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (89/32), kHi := (45/16), chiLo := (11/32), chiHi := (45/128) }

private noncomputable def leaf4049Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435725/268435456) }, vSqrt := { lower := (32765/32768), upper := (288728761/288719872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (525025733/268435456) }, upper := { exponent := 0, mantissa := (4073/2048) } }, logOuter := sk108LogOuterCertificate, logK := sk108LogKCertificate, logChi := chi253LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (577448633/577439744) } }, logDArg := sk108LogDArgCertificate }

private noncomputable def leaf4049InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4049LocalValidity :
    LeafFacts leaf4049Box leaf4049Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4049Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (288728761/288719872) }) = true
      norm_num [leaf4049Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4049CertificateValid :
    WideCertificateValid leaf4049Box leaf4049Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk108ValidityFacts chi253ValidityFacts
    leaf4049LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4049CoverageChecked :
    coverageCheck (innerAD leaf4049Box) leaf4049InnerLog = true := by
  rfl'

private theorem leaf4049InnerLogValid :
    leaf4049InnerLog.Valid 8 (innerAD leaf4049Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4049CoverageChecked

private noncomputable def leaf4049InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629339/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4049InputLogOnePlusV_eq :
    leaf4049InputLogOnePlusV = outerEnclosure 24
      (leaf4049Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4049RoundedFacts : LeafRoundedFacts 8
    leaf4049Certificate.logOnePlusV leaf4049InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4049InputLogOnePlusV_eq }

private noncomputable def leaf4049Inputs : Inputs :=
  inputsOfCaches globalInput sk108RoundedInputs
    chi253InputQChi innerPair108Input
    leaf4049InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4049LowerChecked :
    lowerCheck 24 leaf4049Box leaf4049Inputs = true := by
  rfl'

private theorem leaf4049CoversExact : CoversExact 8
    leaf4049Box leaf4049Certificate leaf4049InnerLog leaf4049Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk108RoundedFacts chi253RoundedFacts
    innerPair108RoundedFacts leaf4049RoundedFacts (by rfl)

private theorem leaf4049FlatSound : Sound leaf4049Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4049CertificateValid
    leaf4049InnerLogValid leaf4049CoversExact leaf4049LowerChecked

private noncomputable def leaf4050Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (89/32), chiLo := (45/128), chiHi := (23/64) }

private noncomputable def leaf4050Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435725/268435456) }, vSqrt := { lower := (32765/32768), upper := (1108345889/1108311040) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (527909141/268435456) }, upper := { exponent := 0, mantissa := (4095/2048) } }, logOuter := sk107LogOuterCertificate, logK := sk107LogKCertificate, logChi := chi254LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (2216656929/2216622080) } }, logDArg := sk107LogDArgCertificate }

private noncomputable def leaf4050InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4050LocalValidity :
    LeafFacts leaf4050Box leaf4050Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4050Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (1108345889/1108311040) }) = true
      norm_num [leaf4050Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4050CertificateValid :
    WideCertificateValid leaf4050Box leaf4050Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk107ValidityFacts chi254ValidityFacts
    leaf4050LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4050CoverageChecked :
    coverageCheck (innerAD leaf4050Box) leaf4050InnerLog = true := by
  rfl'

private theorem leaf4050InnerLogValid :
    leaf4050InnerLog.Valid 8 (innerAD leaf4050Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4050CoverageChecked

private noncomputable def leaf4050InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629345/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4050InputLogOnePlusV_eq :
    leaf4050InputLogOnePlusV = outerEnclosure 24
      (leaf4050Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4050RoundedFacts : LeafRoundedFacts 8
    leaf4050Certificate.logOnePlusV leaf4050InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4050InputLogOnePlusV_eq }

private noncomputable def leaf4050Inputs : Inputs :=
  inputsOfCaches globalInput sk107RoundedInputs
    chi254InputQChi innerPair108Input
    leaf4050InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4050LowerChecked :
    lowerCheck 24 leaf4050Box leaf4050Inputs = true := by
  rfl'

private theorem leaf4050CoversExact : CoversExact 8
    leaf4050Box leaf4050Certificate leaf4050InnerLog leaf4050Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk107RoundedFacts chi254RoundedFacts
    innerPair108RoundedFacts leaf4050RoundedFacts (by rfl)

private theorem leaf4050FlatSound : Sound leaf4050Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4050CertificateValid
    leaf4050InnerLogValid leaf4050CoversExact leaf4050LowerChecked

private noncomputable def leaf4051Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (89/32), kHi := (45/16), chiLo := (45/128), chiHi := (23/64) }

private noncomputable def leaf4051Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435727/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357618688) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (530858079/268435456) }, upper := { exponent := 1, mantissa := (2059/2048) } }, logOuter := sk108LogOuterCertificate, logK := sk108LogKCertificate, logChi := chi254LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716341247/68715237376) } }, logDArg := sk108LogDArgCertificate }

private noncomputable def leaf4051InnerLog : WideLogData :=
  innerPair110Data

set_option maxRecDepth 1000000 in
private theorem leaf4051LocalValidity :
    LeafFacts leaf4051Box leaf4051Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4051Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357618688) }) = true
      norm_num [leaf4051Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4051CertificateValid :
    WideCertificateValid leaf4051Box leaf4051Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk108ValidityFacts chi254ValidityFacts
    leaf4051LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4051CoverageChecked :
    coverageCheck (innerAD leaf4051Box) leaf4051InnerLog = true := by
  rfl'

private theorem leaf4051InnerLogValid :
    leaf4051InnerLog.Valid 8 (innerAD leaf4051Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint72PositiveFacts.valid leaf4051CoverageChecked

private noncomputable def leaf4051InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814675/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4051InputLogOnePlusV_eq :
    leaf4051InputLogOnePlusV = outerEnclosure 24
      (leaf4051Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4051RoundedFacts : LeafRoundedFacts 8
    leaf4051Certificate.logOnePlusV leaf4051InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4051InputLogOnePlusV_eq }

private noncomputable def leaf4051Inputs : Inputs :=
  inputsOfCaches globalInput sk108RoundedInputs
    chi254InputQChi innerPair110Input
    leaf4051InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4051LowerChecked :
    lowerCheck 24 leaf4051Box leaf4051Inputs = true := by
  rfl'

private theorem leaf4051CoversExact : CoversExact 8
    leaf4051Box leaf4051Certificate leaf4051InnerLog leaf4051Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk108RoundedFacts chi254RoundedFacts
    innerPair110RoundedFacts leaf4051RoundedFacts (by rfl)

private theorem leaf4051FlatSound : Sound leaf4051Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4051CertificateValid
    leaf4051InnerLogValid leaf4051CoversExact leaf4051LowerChecked

private noncomputable def leaf4052Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (89/32), chiLo := (23/64), chiHi := (47/128) }

private noncomputable def leaf4052Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435727/268435456) }, vSqrt := { lower := (32765/32768), upper := (4908388937/4908228096) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (533675955/268435456) }, upper := { exponent := 1, mantissa := (8279/8192) } }, logOuter := sk107LogOuterCertificate, logK := sk107LogKCertificate, logChi := chi255LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (9816617033/9816456192) } }, logDArg := sk107LogDArgCertificate }

private noncomputable def leaf4052InnerLog : WideLogData :=
  innerPair110Data

set_option maxRecDepth 1000000 in
private theorem leaf4052LocalValidity :
    LeafFacts leaf4052Box leaf4052Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4052Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4908388937/4908228096) }) = true
      norm_num [leaf4052Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4052CertificateValid :
    WideCertificateValid leaf4052Box leaf4052Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk107ValidityFacts chi255ValidityFacts
    leaf4052LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4052CoverageChecked :
    coverageCheck (innerAD leaf4052Box) leaf4052InnerLog = true := by
  rfl'

private theorem leaf4052InnerLogValid :
    leaf4052InnerLog.Valid 8 (innerAD leaf4052Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint72PositiveFacts.valid leaf4052CoverageChecked

private noncomputable def leaf4052InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907339/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4052InputLogOnePlusV_eq :
    leaf4052InputLogOnePlusV = outerEnclosure 24
      (leaf4052Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4052RoundedFacts : LeafRoundedFacts 8
    leaf4052Certificate.logOnePlusV leaf4052InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4052InputLogOnePlusV_eq }

private noncomputable def leaf4052Inputs : Inputs :=
  inputsOfCaches globalInput sk107RoundedInputs
    chi255InputQChi innerPair110Input
    leaf4052InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4052LowerChecked :
    lowerCheck 24 leaf4052Box leaf4052Inputs = true := by
  rfl'

private theorem leaf4052CoversExact : CoversExact 8
    leaf4052Box leaf4052Certificate leaf4052InnerLog leaf4052Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk107RoundedFacts chi255RoundedFacts
    innerPair110RoundedFacts leaf4052RoundedFacts (by rfl)

private theorem leaf4052FlatSound : Sound leaf4052Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4052CertificateValid
    leaf4052InnerLogValid leaf4052CoversExact leaf4052LowerChecked

private noncomputable def leaf4053Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (89/32), kHi := (45/16), chiLo := (23/64), chiHi := (47/128) }

private noncomputable def leaf4053Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435729/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357572608) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (536690425/268435456) }, upper := { exponent := 1, mantissa := (4163/4096) } }, logOuter := sk108LogOuterCertificate, logK := sk108LogKCertificate, logChi := chi255LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716295167/68715145216) } }, logDArg := sk108LogDArgCertificate }

private noncomputable def leaf4053InnerLog : WideLogData :=
  innerPair110Data

set_option maxRecDepth 1000000 in
private theorem leaf4053LocalValidity :
    LeafFacts leaf4053Box leaf4053Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4053Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357572608) }) = true
      norm_num [leaf4053Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4053CertificateValid :
    WideCertificateValid leaf4053Box leaf4053Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk108ValidityFacts chi255ValidityFacts
    leaf4053LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4053CoverageChecked :
    coverageCheck (innerAD leaf4053Box) leaf4053InnerLog = true := by
  rfl'

private theorem leaf4053InnerLogValid :
    leaf4053InnerLog.Valid 8 (innerAD leaf4053Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint72PositiveFacts.valid leaf4053CoverageChecked

private noncomputable def leaf4053InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814681/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4053InputLogOnePlusV_eq :
    leaf4053InputLogOnePlusV = outerEnclosure 24
      (leaf4053Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4053RoundedFacts : LeafRoundedFacts 8
    leaf4053Certificate.logOnePlusV leaf4053InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4053InputLogOnePlusV_eq }

private noncomputable def leaf4053Inputs : Inputs :=
  inputsOfCaches globalInput sk108RoundedInputs
    chi255InputQChi innerPair110Input
    leaf4053InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4053LowerChecked :
    lowerCheck 24 leaf4053Box leaf4053Inputs = true := by
  rfl'

private theorem leaf4053CoversExact : CoversExact 8
    leaf4053Box leaf4053Certificate leaf4053InnerLog leaf4053Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk108RoundedFacts chi255RoundedFacts
    innerPair110RoundedFacts leaf4053RoundedFacts (by rfl)

private theorem leaf4053FlatSound : Sound leaf4053Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4053CertificateValid
    leaf4053InnerLogValid leaf4053CoversExact leaf4053LowerChecked

private noncomputable def leaf4054Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (89/32), chiLo := (47/128), chiHi := (3/8) }

private noncomputable def leaf4054Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435729/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357551104) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (539442769/536870912) }, upper := { exponent := 1, mantissa := (523/512) } }, logOuter := sk107LogOuterCertificate, logK := sk107LogKCertificate, logChi := chi256LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716273663/68715102208) } }, logDArg := sk107LogDArgCertificate }

private noncomputable def leaf4054InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4054LocalValidity :
    LeafFacts leaf4054Box leaf4054Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4054Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357551104) }) = true
      norm_num [leaf4054Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4054CertificateValid :
    WideCertificateValid leaf4054Box leaf4054Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk107ValidityFacts chi256ValidityFacts
    leaf4054LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4054CoverageChecked :
    coverageCheck (innerAD leaf4054Box) leaf4054InnerLog = true := by
  rfl'

private theorem leaf4054InnerLogValid :
    leaf4054InnerLog.Valid 8 (innerAD leaf4054Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4054CoverageChecked

private noncomputable def leaf4054InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629367/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4054InputLogOnePlusV_eq :
    leaf4054InputLogOnePlusV = outerEnclosure 24
      (leaf4054Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4054RoundedFacts : LeafRoundedFacts 8
    leaf4054Certificate.logOnePlusV leaf4054InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4054InputLogOnePlusV_eq }

private noncomputable def leaf4054Inputs : Inputs :=
  inputsOfCaches globalInput sk107RoundedInputs
    chi256InputQChi innerPair116Input
    leaf4054InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4054LowerChecked :
    lowerCheck 24 leaf4054Box leaf4054Inputs = true := by
  rfl'

private theorem leaf4054CoversExact : CoversExact 8
    leaf4054Box leaf4054Certificate leaf4054InnerLog leaf4054Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk107RoundedFacts chi256RoundedFacts
    innerPair116RoundedFacts leaf4054RoundedFacts (by rfl)

private theorem leaf4054FlatSound : Sound leaf4054Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4054CertificateValid
    leaf4054InnerLogValid leaf4054CoversExact leaf4054LowerChecked

private noncomputable def leaf4055Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (89/32), kHi := (45/16), chiLo := (47/128), chiHi := (3/8) }

private noncomputable def leaf4055Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435731/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357526528) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (542522771/536870912) }, upper := { exponent := 1, mantissa := (263/256) } }, logOuter := sk108LogOuterCertificate, logK := sk108LogKCertificate, logChi := chi256LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716249087/68715053056) } }, logDArg := sk108LogDArgCertificate }

private noncomputable def leaf4055InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4055LocalValidity :
    LeafFacts leaf4055Box leaf4055Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4055Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357526528) }) = true
      norm_num [leaf4055Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4055CertificateValid :
    WideCertificateValid leaf4055Box leaf4055Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk108ValidityFacts chi256ValidityFacts
    leaf4055LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4055CoverageChecked :
    coverageCheck (innerAD leaf4055Box) leaf4055InnerLog = true := by
  rfl'

private theorem leaf4055InnerLogValid :
    leaf4055InnerLog.Valid 8 (innerAD leaf4055Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4055CoverageChecked

private noncomputable def leaf4055InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629373/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4055InputLogOnePlusV_eq :
    leaf4055InputLogOnePlusV = outerEnclosure 24
      (leaf4055Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4055RoundedFacts : LeafRoundedFacts 8
    leaf4055Certificate.logOnePlusV leaf4055InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4055InputLogOnePlusV_eq }

private noncomputable def leaf4055Inputs : Inputs :=
  inputsOfCaches globalInput sk108RoundedInputs
    chi256InputQChi innerPair116Input
    leaf4055InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4055LowerChecked :
    lowerCheck 24 leaf4055Box leaf4055Inputs = true := by
  rfl'

private theorem leaf4055CoversExact : CoversExact 8
    leaf4055Box leaf4055Certificate leaf4055InnerLog leaf4055Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk108RoundedFacts chi256RoundedFacts
    innerPair116RoundedFacts leaf4055RoundedFacts (by rfl)

private theorem leaf4055FlatSound : Sound leaf4055Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4055CertificateValid
    leaf4055InnerLogValid leaf4055CoversExact leaf4055LowerChecked

private noncomputable def leaf4056Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (91/32), chiLo := (11/32), chiHi := (45/128) }

private noncomputable def leaf4056Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435727/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357641728) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (527909139/268435456) }, upper := { exponent := 0, mantissa := (8191/4096) } }, logOuter := sk109LogOuterCertificate, logK := sk109LogKCertificate, logChi := chi253LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716364287/68715283456) } }, logDArg := sk109LogDArgCertificate }

private noncomputable def leaf4056InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4056LocalValidity :
    LeafFacts leaf4056Box leaf4056Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4056Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357641728) }) = true
      norm_num [leaf4056Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4056CertificateValid :
    WideCertificateValid leaf4056Box leaf4056Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk109ValidityFacts chi253ValidityFacts
    leaf4056LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4056CoverageChecked :
    coverageCheck (innerAD leaf4056Box) leaf4056InnerLog = true := by
  rfl'

private theorem leaf4056InnerLogValid :
    leaf4056InnerLog.Valid 8 (innerAD leaf4056Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4056CoverageChecked

private noncomputable def leaf4056InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629345/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4056InputLogOnePlusV_eq :
    leaf4056InputLogOnePlusV = outerEnclosure 24
      (leaf4056Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4056RoundedFacts : LeafRoundedFacts 8
    leaf4056Certificate.logOnePlusV leaf4056InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4056InputLogOnePlusV_eq }

private noncomputable def leaf4056Inputs : Inputs :=
  inputsOfCaches globalInput sk109RoundedInputs
    chi253InputQChi innerPair108Input
    leaf4056InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4056LowerChecked :
    lowerCheck 24 leaf4056Box leaf4056Inputs = true := by
  rfl'

private theorem leaf4056CoversExact : CoversExact 8
    leaf4056Box leaf4056Certificate leaf4056InnerLog leaf4056Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk109RoundedFacts chi253RoundedFacts
    innerPair108RoundedFacts leaf4056RoundedFacts (by rfl)

private theorem leaf4056FlatSound : Sound leaf4056Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4056CertificateValid
    leaf4056InnerLogValid leaf4056CoversExact leaf4056LowerChecked

private noncomputable def leaf4057Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (91/32), kHi := (23/8), chiLo := (11/32), chiHi := (45/128) }

private noncomputable def leaf4057Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435729/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357618688) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (530792545/268435456) }, upper := { exponent := 1, mantissa := (2059/2048) } }, logOuter := sk110LogOuterCertificate, logK := sk110LogKCertificate, logChi := chi253LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716341247/68715237376) } }, logDArg := sk110LogDArgCertificate }

private noncomputable def leaf4057InnerLog : WideLogData :=
  innerPair110Data

set_option maxRecDepth 1000000 in
private theorem leaf4057LocalValidity :
    LeafFacts leaf4057Box leaf4057Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4057Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357618688) }) = true
      norm_num [leaf4057Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4057CertificateValid :
    WideCertificateValid leaf4057Box leaf4057Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk110ValidityFacts chi253ValidityFacts
    leaf4057LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4057CoverageChecked :
    coverageCheck (innerAD leaf4057Box) leaf4057InnerLog = true := by
  rfl'

private theorem leaf4057InnerLogValid :
    leaf4057InnerLog.Valid 8 (innerAD leaf4057Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint72PositiveFacts.valid leaf4057CoverageChecked

private noncomputable def leaf4057InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814675/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4057InputLogOnePlusV_eq :
    leaf4057InputLogOnePlusV = outerEnclosure 24
      (leaf4057Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4057RoundedFacts : LeafRoundedFacts 8
    leaf4057Certificate.logOnePlusV leaf4057InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4057InputLogOnePlusV_eq }

private noncomputable def leaf4057Inputs : Inputs :=
  inputsOfCaches globalInput sk110RoundedInputs
    chi253InputQChi innerPair110Input
    leaf4057InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4057LowerChecked :
    lowerCheck 24 leaf4057Box leaf4057Inputs = true := by
  rfl'

private theorem leaf4057CoversExact : CoversExact 8
    leaf4057Box leaf4057Certificate leaf4057InnerLog leaf4057Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk110RoundedFacts chi253RoundedFacts
    innerPair110RoundedFacts leaf4057RoundedFacts (by rfl)

private theorem leaf4057FlatSound : Sound leaf4057Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4057CertificateValid
    leaf4057InnerLogValid leaf4057CoversExact leaf4057LowerChecked

private noncomputable def leaf4058Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (91/32), chiLo := (45/128), chiHi := (23/64) }

private noncomputable def leaf4058Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435729/268435456) }, vSqrt := { lower := (32765/32768), upper := (2021101327/2021035008) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (533807017/268435456) }, upper := { exponent := 1, mantissa := (4141/4096) } }, logOuter := sk109LogOuterCertificate, logK := sk109LogKCertificate, logChi := chi254LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (4042136335/4042070016) } }, logDArg := sk109LogDArgCertificate }

private noncomputable def leaf4058InnerLog : WideLogData :=
  innerPair110Data

set_option maxRecDepth 1000000 in
private theorem leaf4058LocalValidity :
    LeafFacts leaf4058Box leaf4058Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4058Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (2021101327/2021035008) }) = true
      norm_num [leaf4058Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4058CertificateValid :
    WideCertificateValid leaf4058Box leaf4058Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk109ValidityFacts chi254ValidityFacts
    leaf4058LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4058CoverageChecked :
    coverageCheck (innerAD leaf4058Box) leaf4058InnerLog = true := by
  rfl'

private theorem leaf4058InnerLogValid :
    leaf4058InnerLog.Valid 8 (innerAD leaf4058Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint72PositiveFacts.valid leaf4058CoverageChecked

private noncomputable def leaf4058InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907339/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4058InputLogOnePlusV_eq :
    leaf4058InputLogOnePlusV = outerEnclosure 24
      (leaf4058Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4058RoundedFacts : LeafRoundedFacts 8
    leaf4058Certificate.logOnePlusV leaf4058InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4058InputLogOnePlusV_eq }

private noncomputable def leaf4058Inputs : Inputs :=
  inputsOfCaches globalInput sk109RoundedInputs
    chi254InputQChi innerPair110Input
    leaf4058InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4058LowerChecked :
    lowerCheck 24 leaf4058Box leaf4058Inputs = true := by
  rfl'

private theorem leaf4058CoversExact : CoversExact 8
    leaf4058Box leaf4058Certificate leaf4058InnerLog leaf4058Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk109RoundedFacts chi254RoundedFacts
    innerPair110RoundedFacts leaf4058RoundedFacts (by rfl)

private theorem leaf4058FlatSound : Sound leaf4058Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4058CertificateValid
    leaf4058InnerLogValid leaf4058CoversExact leaf4058LowerChecked

private noncomputable def leaf4059Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (91/32), kHi := (23/8), chiLo := (45/128), chiHi := (23/64) }

private noncomputable def leaf4059Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435731/268435456) }, vSqrt := { lower := (32765/32768), upper := (4908388937/4908224512) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (536755955/268435456) }, upper := { exponent := 1, mantissa := (1041/1024) } }, logOuter := sk110LogOuterCertificate, logK := sk110LogKCertificate, logChi := chi254LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (9816613449/9816449024) } }, logDArg := sk110LogDArgCertificate }

private noncomputable def leaf4059InnerLog : WideLogData :=
  innerPair110Data

set_option maxRecDepth 1000000 in
private theorem leaf4059LocalValidity :
    LeafFacts leaf4059Box leaf4059Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4059Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4908388937/4908224512) }) = true
      norm_num [leaf4059Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4059CertificateValid :
    WideCertificateValid leaf4059Box leaf4059Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk110ValidityFacts chi254ValidityFacts
    leaf4059LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4059CoverageChecked :
    coverageCheck (innerAD leaf4059Box) leaf4059InnerLog = true := by
  rfl'

private theorem leaf4059InnerLogValid :
    leaf4059InnerLog.Valid 8 (innerAD leaf4059Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint72PositiveFacts.valid leaf4059CoverageChecked

private noncomputable def leaf4059InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814681/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4059InputLogOnePlusV_eq :
    leaf4059InputLogOnePlusV = outerEnclosure 24
      (leaf4059Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4059RoundedFacts : LeafRoundedFacts 8
    leaf4059Certificate.logOnePlusV leaf4059InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4059InputLogOnePlusV_eq }

private noncomputable def leaf4059Inputs : Inputs :=
  inputsOfCaches globalInput sk110RoundedInputs
    chi254InputQChi innerPair110Input
    leaf4059InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4059LowerChecked :
    lowerCheck 24 leaf4059Box leaf4059Inputs = true := by
  rfl'

private theorem leaf4059CoversExact : CoversExact 8
    leaf4059Box leaf4059Certificate leaf4059InnerLog leaf4059Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk110RoundedFacts chi254RoundedFacts
    innerPair110RoundedFacts leaf4059RoundedFacts (by rfl)

private theorem leaf4059FlatSound : Sound leaf4059Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4059CertificateValid
    leaf4059InnerLogValid leaf4059CoversExact leaf4059LowerChecked

private noncomputable def leaf4060Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (91/32), chiLo := (23/64), chiHi := (47/128) }

private noncomputable def leaf4060Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435731/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357548544) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (539704895/536870912) }, upper := { exponent := 1, mantissa := (8373/8192) } }, logOuter := sk109LogOuterCertificate, logK := sk109LogKCertificate, logChi := chi255LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716271103/68715097088) } }, logDArg := sk109LogDArgCertificate }

private noncomputable def leaf4060InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4060LocalValidity :
    LeafFacts leaf4060Box leaf4060Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4060Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357548544) }) = true
      norm_num [leaf4060Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4060CertificateValid :
    WideCertificateValid leaf4060Box leaf4060Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk109ValidityFacts chi255ValidityFacts
    leaf4060LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4060CoverageChecked :
    coverageCheck (innerAD leaf4060Box) leaf4060InnerLog = true := by
  rfl'

private theorem leaf4060InnerLogValid :
    leaf4060InnerLog.Valid 8 (innerAD leaf4060Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4060CoverageChecked

private noncomputable def leaf4060InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629367/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4060InputLogOnePlusV_eq :
    leaf4060InputLogOnePlusV = outerEnclosure 24
      (leaf4060Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4060RoundedFacts : LeafRoundedFacts 8
    leaf4060Certificate.logOnePlusV leaf4060InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4060InputLogOnePlusV_eq }

private noncomputable def leaf4060Inputs : Inputs :=
  inputsOfCaches globalInput sk109RoundedInputs
    chi255InputQChi innerPair116Input
    leaf4060InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4060LowerChecked :
    lowerCheck 24 leaf4060Box leaf4060Inputs = true := by
  rfl'

private theorem leaf4060CoversExact : CoversExact 8
    leaf4060Box leaf4060Certificate leaf4060InnerLog leaf4060Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk109RoundedFacts chi255RoundedFacts
    innerPair116RoundedFacts leaf4060RoundedFacts (by rfl)

private theorem leaf4060FlatSound : Sound leaf4060Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4060CertificateValid
    leaf4060InnerLogValid leaf4060CoversExact leaf4060LowerChecked

private noncomputable def leaf4061Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (91/32), kHi := (23/8), chiLo := (23/64), chiHi := (47/128) }

private noncomputable def leaf4061Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435733/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357524480) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (542719365/536870912) }, upper := { exponent := 1, mantissa := (2105/2048) } }, logOuter := sk110LogOuterCertificate, logK := sk110LogKCertificate, logChi := chi255LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716247039/68715048960) } }, logDArg := sk110LogDArgCertificate }

private noncomputable def leaf4061InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4061LocalValidity :
    LeafFacts leaf4061Box leaf4061Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4061Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357524480) }) = true
      norm_num [leaf4061Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4061CertificateValid :
    WideCertificateValid leaf4061Box leaf4061Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk110ValidityFacts chi255ValidityFacts
    leaf4061LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4061CoverageChecked :
    coverageCheck (innerAD leaf4061Box) leaf4061InnerLog = true := by
  rfl'

private theorem leaf4061InnerLogValid :
    leaf4061InnerLog.Valid 8 (innerAD leaf4061Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4061CoverageChecked

private noncomputable def leaf4061InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629373/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4061InputLogOnePlusV_eq :
    leaf4061InputLogOnePlusV = outerEnclosure 24
      (leaf4061Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4061RoundedFacts : LeafRoundedFacts 8
    leaf4061Certificate.logOnePlusV leaf4061InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4061InputLogOnePlusV_eq }

private noncomputable def leaf4061Inputs : Inputs :=
  inputsOfCaches globalInput sk110RoundedInputs
    chi255InputQChi innerPair116Input
    leaf4061InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4061LowerChecked :
    lowerCheck 24 leaf4061Box leaf4061Inputs = true := by
  rfl'

private theorem leaf4061CoversExact : CoversExact 8
    leaf4061Box leaf4061Certificate leaf4061InnerLog leaf4061Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk110RoundedFacts chi255RoundedFacts
    innerPair116RoundedFacts leaf4061RoundedFacts (by rfl)

private theorem leaf4061FlatSound : Sound leaf4061Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4061CertificateValid
    leaf4061InnerLogValid leaf4061CoversExact leaf4061LowerChecked

private noncomputable def leaf4062Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (91/32), chiLo := (47/128), chiHi := (3/8) }

private noncomputable def leaf4062Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435733/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357501952) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (545602773/536870912) }, upper := { exponent := 1, mantissa := (529/512) } }, logOuter := sk109LogOuterCertificate, logK := sk109LogKCertificate, logChi := chi256LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716224511/68715003904) } }, logDArg := sk109LogDArgCertificate }

private noncomputable def leaf4062InnerLog : WideLogData :=
  innerPair117Data

set_option maxRecDepth 1000000 in
private theorem leaf4062LocalValidity :
    LeafFacts leaf4062Box leaf4062Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4062Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357501952) }) = true
      norm_num [leaf4062Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4062CertificateValid :
    WideCertificateValid leaf4062Box leaf4062Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk109ValidityFacts chi256ValidityFacts
    leaf4062LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4062CoverageChecked :
    coverageCheck (innerAD leaf4062Box) leaf4062InnerLog = true := by
  rfl'

private theorem leaf4062InnerLogValid :
    leaf4062InnerLog.Valid 8 (innerAD leaf4062Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint73PositiveFacts.valid leaf4062CoverageChecked

private noncomputable def leaf4062InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629379/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4062InputLogOnePlusV_eq :
    leaf4062InputLogOnePlusV = outerEnclosure 24
      (leaf4062Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4062RoundedFacts : LeafRoundedFacts 8
    leaf4062Certificate.logOnePlusV leaf4062InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4062InputLogOnePlusV_eq }

private noncomputable def leaf4062Inputs : Inputs :=
  inputsOfCaches globalInput sk109RoundedInputs
    chi256InputQChi innerPair117Input
    leaf4062InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4062LowerChecked :
    lowerCheck 24 leaf4062Box leaf4062Inputs = true := by
  rfl'

private theorem leaf4062CoversExact : CoversExact 8
    leaf4062Box leaf4062Certificate leaf4062InnerLog leaf4062Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk109RoundedFacts chi256RoundedFacts
    innerPair117RoundedFacts leaf4062RoundedFacts (by rfl)

private theorem leaf4062FlatSound : Sound leaf4062Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4062CertificateValid
    leaf4062InnerLogValid leaf4062CoversExact leaf4062LowerChecked

private noncomputable def leaf4063Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (91/32), kHi := (23/8), chiLo := (47/128), chiHi := (3/8) }

private noncomputable def leaf4063Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435735/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357477376) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (548682775/536870912) }, upper := { exponent := 1, mantissa := (133/128) } }, logOuter := sk110LogOuterCertificate, logK := sk110LogKCertificate, logChi := chi256LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716199935/68714954752) } }, logDArg := sk110LogDArgCertificate }

private noncomputable def leaf4063InnerLog : WideLogData :=
  innerPair117Data

set_option maxRecDepth 1000000 in
private theorem leaf4063LocalValidity :
    LeafFacts leaf4063Box leaf4063Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4063Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357477376) }) = true
      norm_num [leaf4063Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4063CertificateValid :
    WideCertificateValid leaf4063Box leaf4063Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk110ValidityFacts chi256ValidityFacts
    leaf4063LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4063CoverageChecked :
    coverageCheck (innerAD leaf4063Box) leaf4063InnerLog = true := by
  rfl'

private theorem leaf4063InnerLogValid :
    leaf4063InnerLog.Valid 8 (innerAD leaf4063Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint73PositiveFacts.valid leaf4063CoverageChecked

private noncomputable def leaf4063InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629385/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4063InputLogOnePlusV_eq :
    leaf4063InputLogOnePlusV = outerEnclosure 24
      (leaf4063Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4063RoundedFacts : LeafRoundedFacts 8
    leaf4063Certificate.logOnePlusV leaf4063InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4063InputLogOnePlusV_eq }

private noncomputable def leaf4063Inputs : Inputs :=
  inputsOfCaches globalInput sk110RoundedInputs
    chi256InputQChi innerPair117Input
    leaf4063InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4063LowerChecked :
    lowerCheck 24 leaf4063Box leaf4063Inputs = true := by
  rfl'

private theorem leaf4063CoversExact : CoversExact 8
    leaf4063Box leaf4063Certificate leaf4063InnerLog leaf4063Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk110RoundedFacts chi256RoundedFacts
    innerPair117RoundedFacts leaf4063RoundedFacts (by rfl)

private theorem leaf4063FlatSound : Sound leaf4063Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4063CertificateValid
    leaf4063InnerLogValid leaf4063CoversExact leaf4063LowerChecked

private noncomputable def leaf4064Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (93/32), chiLo := (5/16), chiHi := (41/128) }

private noncomputable def leaf4064Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435723/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68715572224) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (509560183/268435456) }, upper := { exponent := 0, mantissa := (7909/4096) } }, logOuter := sk111LogOuterCertificate, logK := sk111LogKCertificate, logChi := chi249LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434065919/137431144448) } }, logDArg := sk111LogDArgCertificate }

private noncomputable def leaf4064InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4064LocalValidity :
    LeafFacts leaf4064Box leaf4064Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4064Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68715572224) }) = true
      norm_num [leaf4064Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4064CertificateValid :
    WideCertificateValid leaf4064Box leaf4064Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk111ValidityFacts chi249ValidityFacts
    leaf4064LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4064CoverageChecked :
    coverageCheck (innerAD leaf4064Box) leaf4064InnerLog = true := by
  rfl'

private theorem leaf4064InnerLogValid :
    leaf4064InnerLog.Valid 8 (innerAD leaf4064Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4064CoverageChecked

private noncomputable def leaf4064InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629437/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4064InputLogOnePlusV_eq :
    leaf4064InputLogOnePlusV = outerEnclosure 24
      (leaf4064Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4064RoundedFacts : LeafRoundedFacts 8
    leaf4064Certificate.logOnePlusV leaf4064InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4064InputLogOnePlusV_eq }

private noncomputable def leaf4064Inputs : Inputs :=
  inputsOfCaches globalInput sk111RoundedInputs
    chi249InputQChi innerPair100Input
    leaf4064InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4064LowerChecked :
    lowerCheck 24 leaf4064Box leaf4064Inputs = true := by
  rfl'

private theorem leaf4064CoversExact : CoversExact 8
    leaf4064Box leaf4064Certificate leaf4064InnerLog leaf4064Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk111RoundedFacts chi249RoundedFacts
    innerPair100RoundedFacts leaf4064RoundedFacts (by rfl)

private theorem leaf4064FlatSound : Sound leaf4064Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4064CertificateValid
    leaf4064InnerLogValid leaf4064CoversExact leaf4064LowerChecked

private noncomputable def leaf4065Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (93/32), kHi := (47/16), chiLo := (5/16), chiHi := (41/128) }

private noncomputable def leaf4065Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435725/268435456) }, vSqrt := { lower := (32765/32768), upper := (13743698739/13743106048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (512181461/268435456) }, upper := { exponent := 0, mantissa := (3975/2048) } }, logOuter := sk112LogOuterCertificate, logK := sk112LogKCertificate, logChi := chi249LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (27486804787/27486212096) } }, logDArg := sk112LogDArgCertificate }

private noncomputable def leaf4065InnerLog : WideLogData :=
  innerPair233Data

set_option maxRecDepth 1000000 in
private theorem leaf4065LocalValidity :
    LeafFacts leaf4065Box leaf4065Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4065Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (13743698739/13743106048) }) = true
      norm_num [leaf4065Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4065CertificateValid :
    WideCertificateValid leaf4065Box leaf4065Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk112ValidityFacts chi249ValidityFacts
    leaf4065LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4065CoverageChecked :
    coverageCheck (innerAD leaf4065Box) leaf4065InnerLog = true := by
  rfl'

private theorem leaf4065InnerLogValid :
    leaf4065InnerLog.Valid 8 (innerAD leaf4065Box) :=
  wideLogDataValid_of_cachedCheck endpoint70PositiveFacts
    endpoint71PositiveFacts.valid leaf4065CoverageChecked

private noncomputable def leaf4065InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629443/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4065InputLogOnePlusV_eq :
    leaf4065InputLogOnePlusV = outerEnclosure 24
      (leaf4065Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4065RoundedFacts : LeafRoundedFacts 8
    leaf4065Certificate.logOnePlusV leaf4065InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4065InputLogOnePlusV_eq }

private noncomputable def leaf4065Inputs : Inputs :=
  inputsOfCaches globalInput sk112RoundedInputs
    chi249InputQChi innerPair233Input
    leaf4065InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4065LowerChecked :
    lowerCheck 24 leaf4065Box leaf4065Inputs = true := by
  rfl'

private theorem leaf4065CoversExact : CoversExact 8
    leaf4065Box leaf4065Certificate leaf4065InnerLog leaf4065Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk112RoundedFacts chi249RoundedFacts
    innerPair233RoundedFacts leaf4065RoundedFacts (by rfl)

private theorem leaf4065FlatSound : Sound leaf4065Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4065CertificateValid
    leaf4065InnerLogValid leaf4065CoversExact leaf4065LowerChecked

private noncomputable def leaf4066Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (93/32), chiLo := (41/128), chiHi := (21/64) }

private noncomputable def leaf4066Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435725/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68715476992) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (515589125/268435456) }, upper := { exponent := 0, mantissa := (4001/2048) } }, logOuter := sk111LogOuterCertificate, logK := sk111LogKCertificate, logChi := chi250LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137433970687/137430953984) } }, logDArg := sk111LogDArgCertificate }

private noncomputable def leaf4066InnerLog : WideLogData :=
  innerPair234Data

set_option maxRecDepth 1000000 in
private theorem leaf4066LocalValidity :
    LeafFacts leaf4066Box leaf4066Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4066Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68715476992) }) = true
      norm_num [leaf4066Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4066CertificateValid :
    WideCertificateValid leaf4066Box leaf4066Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk111ValidityFacts chi250ValidityFacts
    leaf4066LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4066CoverageChecked :
    coverageCheck (innerAD leaf4066Box) leaf4066InnerLog = true := by
  rfl'

private theorem leaf4066InnerLogValid :
    leaf4066InnerLog.Valid 8 (innerAD leaf4066Box) :=
  wideLogDataValid_of_cachedCheck endpoint70PositiveFacts
    endpoint85PositiveFacts.valid leaf4066CoverageChecked

private noncomputable def leaf4066InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629449/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4066InputLogOnePlusV_eq :
    leaf4066InputLogOnePlusV = outerEnclosure 24
      (leaf4066Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4066RoundedFacts : LeafRoundedFacts 8
    leaf4066Certificate.logOnePlusV leaf4066InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4066InputLogOnePlusV_eq }

private noncomputable def leaf4066Inputs : Inputs :=
  inputsOfCaches globalInput sk111RoundedInputs
    chi250InputQChi innerPair234Input
    leaf4066InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4066LowerChecked :
    lowerCheck 24 leaf4066Box leaf4066Inputs = true := by
  rfl'

private theorem leaf4066CoversExact : CoversExact 8
    leaf4066Box leaf4066Certificate leaf4066InnerLog leaf4066Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk111RoundedFacts chi250RoundedFacts
    innerPair234RoundedFacts leaf4066RoundedFacts (by rfl)

private theorem leaf4066FlatSound : Sound leaf4066Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4066CertificateValid
    leaf4066InnerLogValid leaf4066CoversExact leaf4066LowerChecked

private noncomputable def leaf4067Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (93/32), kHi := (47/16), chiLo := (41/128), chiHi := (21/64) }

private noncomputable def leaf4067Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435727/268435456) }, vSqrt := { lower := (32765/32768), upper := (4042264335/4042084352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (518275935/268435456) }, upper := { exponent := 0, mantissa := (2011/1024) } }, logOuter := sk112LogOuterCertificate, logK := sk112LogKCertificate, logChi := chi250LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (8084348687/8084168704) } }, logDArg := sk112LogDArgCertificate }

private noncomputable def leaf4067InnerLog : WideLogData :=
  innerPair306Data

set_option maxRecDepth 1000000 in
private theorem leaf4067LocalValidity :
    LeafFacts leaf4067Box leaf4067Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4067Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4042264335/4042084352) }) = true
      norm_num [leaf4067Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4067CertificateValid :
    WideCertificateValid leaf4067Box leaf4067Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk112ValidityFacts chi250ValidityFacts
    leaf4067LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4067CoverageChecked :
    coverageCheck (innerAD leaf4067Box) leaf4067InnerLog = true := by
  rfl'

private theorem leaf4067InnerLogValid :
    leaf4067InnerLog.Valid 8 (innerAD leaf4067Box) :=
  wideLogDataValid_of_cachedCheck endpoint81PositiveFacts
    endpoint85PositiveFacts.valid leaf4067CoverageChecked

private noncomputable def leaf4067InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814727/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4067InputLogOnePlusV_eq :
    leaf4067InputLogOnePlusV = outerEnclosure 24
      (leaf4067Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4067RoundedFacts : LeafRoundedFacts 8
    leaf4067Certificate.logOnePlusV leaf4067InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4067InputLogOnePlusV_eq }

private noncomputable def leaf4067Inputs : Inputs :=
  inputsOfCaches globalInput sk112RoundedInputs
    chi250InputQChi innerPair306Input
    leaf4067InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4067LowerChecked :
    lowerCheck 24 leaf4067Box leaf4067Inputs = true := by
  rfl'

private theorem leaf4067CoversExact : CoversExact 8
    leaf4067Box leaf4067Certificate leaf4067InnerLog leaf4067Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk112RoundedFacts chi250RoundedFacts
    innerPair306RoundedFacts leaf4067RoundedFacts (by rfl)

private theorem leaf4067FlatSound : Sound leaf4067Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4067CertificateValid
    leaf4067InnerLogValid leaf4067CoversExact leaf4067LowerChecked

private noncomputable def leaf4068Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (93/32), chiLo := (21/64), chiHi := (43/128) }

private noncomputable def leaf4068Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435727/268435456) }, vSqrt := { lower := (32765/32768), upper := (808452867/808416256) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (521618067/268435456) }, upper := { exponent := 0, mantissa := (8095/4096) } }, logOuter := sk111LogOuterCertificate, logK := sk111LogKCertificate, logChi := chi251LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (1616869123/1616832512) } }, logDArg := sk111LogDArgCertificate }

private noncomputable def leaf4068InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4068LocalValidity :
    LeafFacts leaf4068Box leaf4068Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4068Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (808452867/808416256) }) = true
      norm_num [leaf4068Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4068CertificateValid :
    WideCertificateValid leaf4068Box leaf4068Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk111ValidityFacts chi251ValidityFacts
    leaf4068LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4068CoverageChecked :
    coverageCheck (innerAD leaf4068Box) leaf4068InnerLog = true := by
  rfl'

private theorem leaf4068InnerLogValid :
    leaf4068InnerLog.Valid 8 (innerAD leaf4068Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4068CoverageChecked

private noncomputable def leaf4068InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629461/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4068InputLogOnePlusV_eq :
    leaf4068InputLogOnePlusV = outerEnclosure 24
      (leaf4068Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4068RoundedFacts : LeafRoundedFacts 8
    leaf4068Certificate.logOnePlusV leaf4068InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4068InputLogOnePlusV_eq }

private noncomputable def leaf4068Inputs : Inputs :=
  inputsOfCaches globalInput sk111RoundedInputs
    chi251InputQChi innerPair108Input
    leaf4068InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4068LowerChecked :
    lowerCheck 24 leaf4068Box leaf4068Inputs = true := by
  rfl'

private theorem leaf4068CoversExact : CoversExact 8
    leaf4068Box leaf4068Certificate leaf4068InnerLog leaf4068Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk111RoundedFacts chi251RoundedFacts
    innerPair108RoundedFacts leaf4068RoundedFacts (by rfl)

private theorem leaf4068FlatSound : Sound leaf4068Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4068CertificateValid
    leaf4068InnerLogValid leaf4068CoversExact leaf4068LowerChecked

private noncomputable def leaf4069Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (93/32), kHi := (47/16), chiLo := (21/64), chiHi := (43/128) }

private noncomputable def leaf4069Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435729/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357668864) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (524370409/268435456) }, upper := { exponent := 0, mantissa := (4069/2048) } }, logOuter := sk112LogOuterCertificate, logK := sk112LogKCertificate, logChi := chi251LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716391423/68715337728) } }, logDArg := sk112LogDArgCertificate }

private noncomputable def leaf4069InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4069LocalValidity :
    LeafFacts leaf4069Box leaf4069Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4069Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357668864) }) = true
      norm_num [leaf4069Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4069CertificateValid :
    WideCertificateValid leaf4069Box leaf4069Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk112ValidityFacts chi251ValidityFacts
    leaf4069LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4069CoverageChecked :
    coverageCheck (innerAD leaf4069Box) leaf4069InnerLog = true := by
  rfl'

private theorem leaf4069InnerLogValid :
    leaf4069InnerLog.Valid 8 (innerAD leaf4069Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4069CoverageChecked

private noncomputable def leaf4069InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814669/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4069InputLogOnePlusV_eq :
    leaf4069InputLogOnePlusV = outerEnclosure 24
      (leaf4069Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4069RoundedFacts : LeafRoundedFacts 8
    leaf4069Certificate.logOnePlusV leaf4069InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4069InputLogOnePlusV_eq }

private noncomputable def leaf4069Inputs : Inputs :=
  inputsOfCaches globalInput sk112RoundedInputs
    chi251InputQChi innerPair108Input
    leaf4069InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4069LowerChecked :
    lowerCheck 24 leaf4069Box leaf4069Inputs = true := by
  rfl'

private theorem leaf4069CoversExact : CoversExact 8
    leaf4069Box leaf4069Certificate leaf4069InnerLog leaf4069Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk112RoundedFacts chi251RoundedFacts
    innerPair108RoundedFacts leaf4069RoundedFacts (by rfl)

private theorem leaf4069FlatSound : Sound leaf4069Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4069CertificateValid
    leaf4069InnerLogValid leaf4069CoversExact leaf4069LowerChecked

private noncomputable def leaf4070Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (93/32), chiLo := (43/128), chiHi := (11/32) }

private noncomputable def leaf4070Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435729/268435456) }, vSqrt := { lower := (32765/32768), upper := (4908388937/4908234752) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (527647009/268435456) }, upper := { exponent := 0, mantissa := (2047/1024) } }, logOuter := sk111LogOuterCertificate, logK := sk111LogKCertificate, logChi := chi252LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (9816623689/9816469504) } }, logDArg := sk111LogDArgCertificate }

private noncomputable def leaf4070InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4070LocalValidity :
    LeafFacts leaf4070Box leaf4070Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4070Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4908388937/4908234752) }) = true
      norm_num [leaf4070Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4070CertificateValid :
    WideCertificateValid leaf4070Box leaf4070Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk111ValidityFacts chi252ValidityFacts
    leaf4070LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4070CoverageChecked :
    coverageCheck (innerAD leaf4070Box) leaf4070InnerLog = true := by
  rfl'

private theorem leaf4070InnerLogValid :
    leaf4070InnerLog.Valid 8 (innerAD leaf4070Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4070CoverageChecked

private noncomputable def leaf4070InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (363417/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf4070InputLogOnePlusV_eq :
    leaf4070InputLogOnePlusV = outerEnclosure 24
      (leaf4070Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4070RoundedFacts : LeafRoundedFacts 8
    leaf4070Certificate.logOnePlusV leaf4070InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4070InputLogOnePlusV_eq }

private noncomputable def leaf4070Inputs : Inputs :=
  inputsOfCaches globalInput sk111RoundedInputs
    chi252InputQChi innerPair108Input
    leaf4070InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4070LowerChecked :
    lowerCheck 24 leaf4070Box leaf4070Inputs = true := by
  rfl'

private theorem leaf4070CoversExact : CoversExact 8
    leaf4070Box leaf4070Certificate leaf4070InnerLog leaf4070Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk111RoundedFacts chi252RoundedFacts
    innerPair108RoundedFacts leaf4070RoundedFacts (by rfl)

private theorem leaf4070FlatSound : Sound leaf4070Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4070CertificateValid
    leaf4070InnerLogValid leaf4070CoversExact leaf4070LowerChecked

private noncomputable def leaf4071Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (93/32), kHi := (47/16), chiLo := (43/128), chiHi := (11/32) }

private noncomputable def leaf4071Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435731/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357620736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (530464883/268435456) }, upper := { exponent := 1, mantissa := (1029/1024) } }, logOuter := sk112LogOuterCertificate, logK := sk112LogKCertificate, logChi := chi252LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716343295/68715241472) } }, logDArg := sk112LogDArgCertificate }

private noncomputable def leaf4071InnerLog : WideLogData :=
  innerPair321Data

set_option maxRecDepth 1000000 in
private theorem leaf4071LocalValidity :
    LeafFacts leaf4071Box leaf4071Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4071Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357620736) }) = true
      norm_num [leaf4071Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4071CertificateValid :
    WideCertificateValid leaf4071Box leaf4071Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk112ValidityFacts chi252ValidityFacts
    leaf4071LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4071CoverageChecked :
    coverageCheck (innerAD leaf4071Box) leaf4071InnerLog = true := by
  rfl'

private theorem leaf4071InnerLogValid :
    leaf4071InnerLog.Valid 8 (innerAD leaf4071Box) :=
  wideLogDataValid_of_cachedCheck endpoint85PositiveFacts
    endpoint283PositiveFacts.valid leaf4071CoverageChecked

private noncomputable def leaf4071InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814675/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4071InputLogOnePlusV_eq :
    leaf4071InputLogOnePlusV = outerEnclosure 24
      (leaf4071Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4071RoundedFacts : LeafRoundedFacts 8
    leaf4071Certificate.logOnePlusV leaf4071InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4071InputLogOnePlusV_eq }

private noncomputable def leaf4071Inputs : Inputs :=
  inputsOfCaches globalInput sk112RoundedInputs
    chi252InputQChi innerPair321Input
    leaf4071InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4071LowerChecked :
    lowerCheck 24 leaf4071Box leaf4071Inputs = true := by
  rfl'

private theorem leaf4071CoversExact : CoversExact 8
    leaf4071Box leaf4071Certificate leaf4071InnerLog leaf4071Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk112RoundedFacts chi252RoundedFacts
    innerPair321RoundedFacts leaf4071RoundedFacts (by rfl)

private theorem leaf4071FlatSound : Sound leaf4071Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4071CertificateValid
    leaf4071InnerLogValid leaf4071CoversExact leaf4071LowerChecked

private noncomputable def leaf4072Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (95/32), chiLo := (5/16), chiHi := (41/128) }

private noncomputable def leaf4072Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435727/268435456) }, vSqrt := { lower := (32765/32768), upper := (22906164565/22905162752) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (514802739/268435456) }, upper := { exponent := 0, mantissa := (7991/4096) } }, logOuter := sk113LogOuterCertificate, logK := sk113LogKCertificate, logChi := chi249LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (45811327317/45810325504) } }, logDArg := sk113LogDArgCertificate }

private noncomputable def leaf4072InnerLog : WideLogData :=
  innerPair233Data

set_option maxRecDepth 1000000 in
private theorem leaf4072LocalValidity :
    LeafFacts leaf4072Box leaf4072Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4072Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (22906164565/22905162752) }) = true
      norm_num [leaf4072Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4072CertificateValid :
    WideCertificateValid leaf4072Box leaf4072Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk113ValidityFacts chi249ValidityFacts
    leaf4072LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4072CoverageChecked :
    coverageCheck (innerAD leaf4072Box) leaf4072InnerLog = true := by
  rfl'

private theorem leaf4072InnerLogValid :
    leaf4072InnerLog.Valid 8 (innerAD leaf4072Box) :=
  wideLogDataValid_of_cachedCheck endpoint70PositiveFacts
    endpoint71PositiveFacts.valid leaf4072CoverageChecked

private noncomputable def leaf4072InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (1453681/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf4072InputLogOnePlusV_eq :
    leaf4072InputLogOnePlusV = outerEnclosure 24
      (leaf4072Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4072RoundedFacts : LeafRoundedFacts 8
    leaf4072Certificate.logOnePlusV leaf4072InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4072InputLogOnePlusV_eq }

private noncomputable def leaf4072Inputs : Inputs :=
  inputsOfCaches globalInput sk113RoundedInputs
    chi249InputQChi innerPair233Input
    leaf4072InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4072LowerChecked :
    lowerCheck 24 leaf4072Box leaf4072Inputs = true := by
  rfl'

private theorem leaf4072CoversExact : CoversExact 8
    leaf4072Box leaf4072Certificate leaf4072InnerLog leaf4072Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk113RoundedFacts chi249RoundedFacts
    innerPair233RoundedFacts leaf4072RoundedFacts (by rfl)

private theorem leaf4072FlatSound : Sound leaf4072Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4072CertificateValid
    leaf4072InnerLogValid leaf4072CoversExact leaf4072LowerChecked

private noncomputable def leaf4073Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (3), chiLo := (5/16), chiHi := (41/128) }

private noncomputable def leaf4073Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435729/268435456) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715446272) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (517424017/268435456) }, upper := { exponent := 0, mantissa := (251/128) } }, logOuter := sk114LogOuterCertificate, logK := sk114LogKCertificate, logChi := chi249LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137433939967/137430892544) } }, logDArg := sk114LogDArgCertificate }

private noncomputable def leaf4073InnerLog : WideLogData :=
  innerPair306Data

set_option maxRecDepth 1000000 in
private theorem leaf4073LocalValidity :
    LeafFacts leaf4073Box leaf4073Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4073Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715446272) }) = true
      norm_num [leaf4073Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4073CertificateValid :
    WideCertificateValid leaf4073Box leaf4073Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk114ValidityFacts chi249ValidityFacts
    leaf4073LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4073CoverageChecked :
    coverageCheck (innerAD leaf4073Box) leaf4073InnerLog = true := by
  rfl'

private theorem leaf4073InnerLogValid :
    leaf4073InnerLog.Valid 8 (innerAD leaf4073Box) :=
  wideLogDataValid_of_cachedCheck endpoint81PositiveFacts
    endpoint85PositiveFacts.valid leaf4073CoverageChecked

private noncomputable def leaf4073InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629453/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4073InputLogOnePlusV_eq :
    leaf4073InputLogOnePlusV = outerEnclosure 24
      (leaf4073Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4073RoundedFacts : LeafRoundedFacts 8
    leaf4073Certificate.logOnePlusV leaf4073InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4073InputLogOnePlusV_eq }

private noncomputable def leaf4073Inputs : Inputs :=
  inputsOfCaches globalInput sk114RoundedInputs
    chi249InputQChi innerPair306Input
    leaf4073InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4073LowerChecked :
    lowerCheck 24 leaf4073Box leaf4073Inputs = true := by
  rfl'

private theorem leaf4073CoversExact : CoversExact 8
    leaf4073Box leaf4073Certificate leaf4073InnerLog leaf4073Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk114RoundedFacts chi249RoundedFacts
    innerPair306RoundedFacts leaf4073RoundedFacts (by rfl)

private theorem leaf4073FlatSound : Sound leaf4073Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4073CertificateValid
    leaf4073InnerLogValid leaf4073CoversExact leaf4073LowerChecked

private noncomputable def leaf4074Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (95/32), chiLo := (41/128), chiHi := (21/64) }

private noncomputable def leaf4074Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435729/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68715390976) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (520962745/268435456) }, upper := { exponent := 0, mantissa := (4043/2048) } }, logOuter := sk113LogOuterCertificate, logK := sk113LogKCertificate, logChi := chi250LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137433884671/137430781952) } }, logDArg := sk113LogDArgCertificate }

private noncomputable def leaf4074InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4074LocalValidity :
    LeafFacts leaf4074Box leaf4074Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4074Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68715390976) }) = true
      norm_num [leaf4074Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4074CertificateValid :
    WideCertificateValid leaf4074Box leaf4074Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk113ValidityFacts chi250ValidityFacts
    leaf4074LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4074CoverageChecked :
    coverageCheck (innerAD leaf4074Box) leaf4074InnerLog = true := by
  rfl'

private theorem leaf4074InnerLogValid :
    leaf4074InnerLog.Valid 8 (innerAD leaf4074Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4074CoverageChecked

private noncomputable def leaf4074InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907365/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4074InputLogOnePlusV_eq :
    leaf4074InputLogOnePlusV = outerEnclosure 24
      (leaf4074Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4074RoundedFacts : LeafRoundedFacts 8
    leaf4074Certificate.logOnePlusV leaf4074InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4074InputLogOnePlusV_eq }

private noncomputable def leaf4074Inputs : Inputs :=
  inputsOfCaches globalInput sk113RoundedInputs
    chi250InputQChi innerPair108Input
    leaf4074InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4074LowerChecked :
    lowerCheck 24 leaf4074Box leaf4074Inputs = true := by
  rfl'

private theorem leaf4074CoversExact : CoversExact 8
    leaf4074Box leaf4074Certificate leaf4074InnerLog leaf4074Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk113RoundedFacts chi250RoundedFacts
    innerPair108RoundedFacts leaf4074RoundedFacts (by rfl)

private theorem leaf4074FlatSound : Sound leaf4074Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4074CertificateValid
    leaf4074InnerLogValid leaf4074CoversExact leaf4074LowerChecked

private noncomputable def leaf4075Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (3), chiLo := (41/128), chiHi := (21/64) }

private noncomputable def leaf4075Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435731/268435456) }, vSqrt := { lower := (65529/65536), upper := (1108345889/1108312064) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (523649555/268435456) }, upper := { exponent := 0, mantissa := (127/64) } }, logOuter := sk114LogOuterCertificate, logK := sk114LogKCertificate, logChi := chi250LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (2216657953/2216624128) } }, logDArg := sk114LogDArgCertificate }

private noncomputable def leaf4075InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4075LocalValidity :
    LeafFacts leaf4075Box leaf4075Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4075Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (1108345889/1108312064) }) = true
      norm_num [leaf4075Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4075CertificateValid :
    WideCertificateValid leaf4075Box leaf4075Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk114ValidityFacts chi250ValidityFacts
    leaf4075LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4075CoverageChecked :
    coverageCheck (innerAD leaf4075Box) leaf4075InnerLog = true := by
  rfl'

private theorem leaf4075InnerLogValid :
    leaf4075InnerLog.Valid 8 (innerAD leaf4075Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4075CoverageChecked

private noncomputable def leaf4075InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629337/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4075InputLogOnePlusV_eq :
    leaf4075InputLogOnePlusV = outerEnclosure 24
      (leaf4075Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4075RoundedFacts : LeafRoundedFacts 8
    leaf4075Certificate.logOnePlusV leaf4075InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4075InputLogOnePlusV_eq }

private noncomputable def leaf4075Inputs : Inputs :=
  inputsOfCaches globalInput sk114RoundedInputs
    chi250InputQChi innerPair108Input
    leaf4075InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4075LowerChecked :
    lowerCheck 24 leaf4075Box leaf4075Inputs = true := by
  rfl'

private theorem leaf4075CoversExact : CoversExact 8
    leaf4075Box leaf4075Certificate leaf4075InnerLog leaf4075Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk114RoundedFacts chi250RoundedFacts
    innerPair108RoundedFacts leaf4075RoundedFacts (by rfl)

private theorem leaf4075FlatSound : Sound leaf4075Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4075CertificateValid
    leaf4075InnerLogValid leaf4075CoversExact leaf4075LowerChecked

private noncomputable def leaf4076Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (95/32), chiLo := (21/64), chiHi := (43/128) }

private noncomputable def leaf4076Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435731/268435456) }, vSqrt := { lower := (32765/32768), upper := (4908388937/4908235264) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (527122751/268435456) }, upper := { exponent := 0, mantissa := (8181/4096) } }, logOuter := sk113LogOuterCertificate, logK := sk113LogKCertificate, logChi := chi251LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (9816624201/9816470528) } }, logDArg := sk113LogDArgCertificate }

private noncomputable def leaf4076InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4076LocalValidity :
    LeafFacts leaf4076Box leaf4076Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4076Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4908388937/4908235264) }) = true
      norm_num [leaf4076Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4076CertificateValid :
    WideCertificateValid leaf4076Box leaf4076Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk113ValidityFacts chi251ValidityFacts
    leaf4076LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4076CoverageChecked :
    coverageCheck (innerAD leaf4076Box) leaf4076InnerLog = true := by
  rfl'

private theorem leaf4076InnerLogValid :
    leaf4076InnerLog.Valid 8 (innerAD leaf4076Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4076CoverageChecked

private noncomputable def leaf4076InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629343/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4076InputLogOnePlusV_eq :
    leaf4076InputLogOnePlusV = outerEnclosure 24
      (leaf4076Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4076RoundedFacts : LeafRoundedFacts 8
    leaf4076Certificate.logOnePlusV leaf4076InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4076InputLogOnePlusV_eq }

private noncomputable def leaf4076Inputs : Inputs :=
  inputsOfCaches globalInput sk113RoundedInputs
    chi251InputQChi innerPair108Input
    leaf4076InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4076LowerChecked :
    lowerCheck 24 leaf4076Box leaf4076Inputs = true := by
  rfl'

private theorem leaf4076CoversExact : CoversExact 8
    leaf4076Box leaf4076Certificate leaf4076InnerLog leaf4076Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk113RoundedFacts chi251RoundedFacts
    innerPair108RoundedFacts leaf4076RoundedFacts (by rfl)

private theorem leaf4076FlatSound : Sound leaf4076Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4076CertificateValid
    leaf4076InnerLogValid leaf4076CoversExact leaf4076LowerChecked

private noncomputable def leaf4077Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (3), chiLo := (21/64), chiHi := (43/128) }

private noncomputable def leaf4077Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435733/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357624832) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (529875093/268435456) }, upper := { exponent := 1, mantissa := (257/256) } }, logOuter := sk114LogOuterCertificate, logK := sk114LogKCertificate, logChi := chi251LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716347391/68715249664) } }, logDArg := sk114LogDArgCertificate }

private noncomputable def leaf4077InnerLog : WideLogData :=
  innerPair321Data

set_option maxRecDepth 1000000 in
private theorem leaf4077LocalValidity :
    LeafFacts leaf4077Box leaf4077Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4077Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357624832) }) = true
      norm_num [leaf4077Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4077CertificateValid :
    WideCertificateValid leaf4077Box leaf4077Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk114ValidityFacts chi251ValidityFacts
    leaf4077LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4077CoverageChecked :
    coverageCheck (innerAD leaf4077Box) leaf4077InnerLog = true := by
  rfl'

private theorem leaf4077InnerLogValid :
    leaf4077InnerLog.Valid 8 (innerAD leaf4077Box) :=
  wideLogDataValid_of_cachedCheck endpoint85PositiveFacts
    endpoint283PositiveFacts.valid leaf4077CoverageChecked

private noncomputable def leaf4077InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629349/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4077InputLogOnePlusV_eq :
    leaf4077InputLogOnePlusV = outerEnclosure 24
      (leaf4077Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4077RoundedFacts : LeafRoundedFacts 8
    leaf4077Certificate.logOnePlusV leaf4077InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4077InputLogOnePlusV_eq }

private noncomputable def leaf4077Inputs : Inputs :=
  inputsOfCaches globalInput sk114RoundedInputs
    chi251InputQChi innerPair321Input
    leaf4077InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4077LowerChecked :
    lowerCheck 24 leaf4077Box leaf4077Inputs = true := by
  rfl'

private theorem leaf4077CoversExact : CoversExact 8
    leaf4077Box leaf4077Certificate leaf4077InnerLog leaf4077Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk114RoundedFacts chi251RoundedFacts
    innerPair321RoundedFacts leaf4077RoundedFacts (by rfl)

private theorem leaf4077FlatSound : Sound leaf4077Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4077CertificateValid
    leaf4077InnerLogValid leaf4077CoversExact leaf4077LowerChecked

private noncomputable def leaf4078Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (95/32), chiLo := (43/128), chiHi := (11/32) }

private noncomputable def leaf4078Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435733/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357598208) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (533282757/268435456) }, upper := { exponent := 1, mantissa := (2069/2048) } }, logOuter := sk113LogOuterCertificate, logK := sk113LogKCertificate, logChi := chi252LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716320767/68715196416) } }, logDArg := sk113LogDArgCertificate }

private noncomputable def leaf4078InnerLog : WideLogData :=
  innerPair531Data

set_option maxRecDepth 1000000 in
private theorem leaf4078LocalValidity :
    LeafFacts leaf4078Box leaf4078Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4078Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357598208) }) = true
      norm_num [leaf4078Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4078CertificateValid :
    WideCertificateValid leaf4078Box leaf4078Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk113ValidityFacts chi252ValidityFacts
    leaf4078LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4078CoverageChecked :
    coverageCheck (innerAD leaf4078Box) leaf4078InnerLog = true := by
  rfl'

private theorem leaf4078InnerLogValid :
    leaf4078InnerLog.Valid 8 (innerAD leaf4078Box) :=
  wideLogDataValid_of_cachedCheck endpoint267PositiveFacts
    endpoint82PositiveFacts.valid leaf4078CoverageChecked

private noncomputable def leaf4078InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629355/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4078InputLogOnePlusV_eq :
    leaf4078InputLogOnePlusV = outerEnclosure 24
      (leaf4078Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4078RoundedFacts : LeafRoundedFacts 8
    leaf4078Certificate.logOnePlusV leaf4078InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4078InputLogOnePlusV_eq }

private noncomputable def leaf4078Inputs : Inputs :=
  inputsOfCaches globalInput sk113RoundedInputs
    chi252InputQChi innerPair531Input
    leaf4078InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4078LowerChecked :
    lowerCheck 24 leaf4078Box leaf4078Inputs = true := by
  rfl'

private theorem leaf4078CoversExact : CoversExact 8
    leaf4078Box leaf4078Certificate leaf4078InnerLog leaf4078Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk113RoundedFacts chi252RoundedFacts
    innerPair531RoundedFacts leaf4078RoundedFacts (by rfl)

private theorem leaf4078FlatSound : Sound leaf4078Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4078CertificateValid
    leaf4078InnerLogValid leaf4078CoversExact leaf4078LowerChecked

private noncomputable def leaf4079Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (3), chiLo := (43/128), chiHi := (11/32) }

private noncomputable def leaf4079Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435735/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357575680) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (536100631/268435456) }, upper := { exponent := 1, mantissa := (65/64) } }, logOuter := sk114LogOuterCertificate, logK := sk114LogKCertificate, logChi := chi252LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716298239/68715151360) } }, logDArg := sk114LogDArgCertificate }

private noncomputable def leaf4079InnerLog : WideLogData :=
  innerPair110Data

set_option maxRecDepth 1000000 in
private theorem leaf4079LocalValidity :
    LeafFacts leaf4079Box leaf4079Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4079Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357575680) }) = true
      norm_num [leaf4079Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4079CertificateValid :
    WideCertificateValid leaf4079Box leaf4079Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk114ValidityFacts chi252ValidityFacts
    leaf4079LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4079CoverageChecked :
    coverageCheck (innerAD leaf4079Box) leaf4079InnerLog = true := by
  rfl'

private theorem leaf4079InnerLogValid :
    leaf4079InnerLog.Valid 8 (innerAD leaf4079Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint72PositiveFacts.valid leaf4079CoverageChecked

private noncomputable def leaf4079InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629361/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4079InputLogOnePlusV_eq :
    leaf4079InputLogOnePlusV = outerEnclosure 24
      (leaf4079Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4079RoundedFacts : LeafRoundedFacts 8
    leaf4079Certificate.logOnePlusV leaf4079InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4079InputLogOnePlusV_eq }

private noncomputable def leaf4079Inputs : Inputs :=
  inputsOfCaches globalInput sk114RoundedInputs
    chi252InputQChi innerPair110Input
    leaf4079InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4079LowerChecked :
    lowerCheck 24 leaf4079Box leaf4079Inputs = true := by
  rfl'

private theorem leaf4079CoversExact : CoversExact 8
    leaf4079Box leaf4079Certificate leaf4079InnerLog leaf4079Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk114RoundedFacts chi252RoundedFacts
    innerPair110RoundedFacts leaf4079RoundedFacts (by rfl)

private theorem leaf4079FlatSound : Sound leaf4079Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4079CertificateValid
    leaf4079InnerLogValid leaf4079CoversExact leaf4079LowerChecked

private noncomputable def leaf4080Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (93/32), chiLo := (11/32), chiHi := (45/128) }

private noncomputable def leaf4080Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435731/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357595648) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (533675951/268435456) }, upper := { exponent := 1, mantissa := (8281/8192) } }, logOuter := sk111LogOuterCertificate, logK := sk111LogKCertificate, logChi := chi253LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716318207/68715191296) } }, logDArg := sk111LogDArgCertificate }

private noncomputable def leaf4080InnerLog : WideLogData :=
  innerPair110Data

set_option maxRecDepth 1000000 in
private theorem leaf4080LocalValidity :
    LeafFacts leaf4080Box leaf4080Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4080Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357595648) }) = true
      norm_num [leaf4080Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4080CertificateValid :
    WideCertificateValid leaf4080Box leaf4080Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk111ValidityFacts chi253ValidityFacts
    leaf4080LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4080CoverageChecked :
    coverageCheck (innerAD leaf4080Box) leaf4080InnerLog = true := by
  rfl'

private theorem leaf4080InnerLogValid :
    leaf4080InnerLog.Valid 8 (innerAD leaf4080Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint72PositiveFacts.valid leaf4080CoverageChecked

private noncomputable def leaf4080InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907339/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4080InputLogOnePlusV_eq :
    leaf4080InputLogOnePlusV = outerEnclosure 24
      (leaf4080Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4080RoundedFacts : LeafRoundedFacts 8
    leaf4080Certificate.logOnePlusV leaf4080InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4080InputLogOnePlusV_eq }

private noncomputable def leaf4080Inputs : Inputs :=
  inputsOfCaches globalInput sk111RoundedInputs
    chi253InputQChi innerPair110Input
    leaf4080InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4080LowerChecked :
    lowerCheck 24 leaf4080Box leaf4080Inputs = true := by
  rfl'

private theorem leaf4080CoversExact : CoversExact 8
    leaf4080Box leaf4080Certificate leaf4080InnerLog leaf4080Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk111RoundedFacts chi253RoundedFacts
    innerPair110RoundedFacts leaf4080RoundedFacts (by rfl)

private theorem leaf4080FlatSound : Sound leaf4080Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4080CertificateValid
    leaf4080InnerLogValid leaf4080CoversExact leaf4080LowerChecked

private noncomputable def leaf4081Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (93/32), kHi := (47/16), chiLo := (11/32), chiHi := (45/128) }

private noncomputable def leaf4081Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435733/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357572608) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (536559357/268435456) }, upper := { exponent := 1, mantissa := (4163/4096) } }, logOuter := sk112LogOuterCertificate, logK := sk112LogKCertificate, logChi := chi253LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716295167/68715145216) } }, logDArg := sk112LogDArgCertificate }

private noncomputable def leaf4081InnerLog : WideLogData :=
  innerPair110Data

set_option maxRecDepth 1000000 in
private theorem leaf4081LocalValidity :
    LeafFacts leaf4081Box leaf4081Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4081Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357572608) }) = true
      norm_num [leaf4081Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4081CertificateValid :
    WideCertificateValid leaf4081Box leaf4081Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk112ValidityFacts chi253ValidityFacts
    leaf4081LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4081CoverageChecked :
    coverageCheck (innerAD leaf4081Box) leaf4081InnerLog = true := by
  rfl'

private theorem leaf4081InnerLogValid :
    leaf4081InnerLog.Valid 8 (innerAD leaf4081Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint72PositiveFacts.valid leaf4081CoverageChecked

private noncomputable def leaf4081InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814681/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4081InputLogOnePlusV_eq :
    leaf4081InputLogOnePlusV = outerEnclosure 24
      (leaf4081Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4081RoundedFacts : LeafRoundedFacts 8
    leaf4081Certificate.logOnePlusV leaf4081InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4081InputLogOnePlusV_eq }

private noncomputable def leaf4081Inputs : Inputs :=
  inputsOfCaches globalInput sk112RoundedInputs
    chi253InputQChi innerPair110Input
    leaf4081InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4081LowerChecked :
    lowerCheck 24 leaf4081Box leaf4081Inputs = true := by
  rfl'

private theorem leaf4081CoversExact : CoversExact 8
    leaf4081Box leaf4081Certificate leaf4081InnerLog leaf4081Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk112RoundedFacts chi253RoundedFacts
    innerPair110RoundedFacts leaf4081RoundedFacts (by rfl)

private theorem leaf4081FlatSound : Sound leaf4081Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4081CertificateValid
    leaf4081InnerLogValid leaf4081CoversExact leaf4081LowerChecked

private noncomputable def leaf4082Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (93/32), chiLo := (45/128), chiHi := (23/64) }

private noncomputable def leaf4082Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435733/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357548032) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (539704893/536870912) }, upper := { exponent := 1, mantissa := (4187/4096) } }, logOuter := sk111LogOuterCertificate, logK := sk111LogKCertificate, logChi := chi254LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716270591/68715096064) } }, logDArg := sk111LogDArgCertificate }

private noncomputable def leaf4082InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4082LocalValidity :
    LeafFacts leaf4082Box leaf4082Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4082Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357548032) }) = true
      norm_num [leaf4082Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4082CertificateValid :
    WideCertificateValid leaf4082Box leaf4082Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk111ValidityFacts chi254ValidityFacts
    leaf4082LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4082CoverageChecked :
    coverageCheck (innerAD leaf4082Box) leaf4082InnerLog = true := by
  rfl'

private theorem leaf4082InnerLogValid :
    leaf4082InnerLog.Valid 8 (innerAD leaf4082Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4082CoverageChecked

private noncomputable def leaf4082InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (1453671/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf4082InputLogOnePlusV_eq :
    leaf4082InputLogOnePlusV = outerEnclosure 24
      (leaf4082Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4082RoundedFacts : LeafRoundedFacts 8
    leaf4082Certificate.logOnePlusV leaf4082InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4082InputLogOnePlusV_eq }

private noncomputable def leaf4082Inputs : Inputs :=
  inputsOfCaches globalInput sk111RoundedInputs
    chi254InputQChi innerPair116Input
    leaf4082InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4082LowerChecked :
    lowerCheck 24 leaf4082Box leaf4082Inputs = true := by
  rfl'

private theorem leaf4082CoversExact : CoversExact 8
    leaf4082Box leaf4082Certificate leaf4082InnerLog leaf4082Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk111RoundedFacts chi254RoundedFacts
    innerPair116RoundedFacts leaf4082RoundedFacts (by rfl)

private theorem leaf4082FlatSound : Sound leaf4082Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4082CertificateValid
    leaf4082InnerLogValid leaf4082CoversExact leaf4082LowerChecked

private noncomputable def leaf4083Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (93/32), kHi := (47/16), chiLo := (45/128), chiHi := (23/64) }

private noncomputable def leaf4083Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435735/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357524480) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (542653831/536870912) }, upper := { exponent := 1, mantissa := (2105/2048) } }, logOuter := sk112LogOuterCertificate, logK := sk112LogKCertificate, logChi := chi254LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716247039/68715048960) } }, logDArg := sk112LogDArgCertificate }

private noncomputable def leaf4083InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4083LocalValidity :
    LeafFacts leaf4083Box leaf4083Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4083Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357524480) }) = true
      norm_num [leaf4083Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4083CertificateValid :
    WideCertificateValid leaf4083Box leaf4083Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk112ValidityFacts chi254ValidityFacts
    leaf4083LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4083CoverageChecked :
    coverageCheck (innerAD leaf4083Box) leaf4083InnerLog = true := by
  rfl'

private theorem leaf4083InnerLogValid :
    leaf4083InnerLog.Valid 8 (innerAD leaf4083Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4083CoverageChecked

private noncomputable def leaf4083InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629373/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4083InputLogOnePlusV_eq :
    leaf4083InputLogOnePlusV = outerEnclosure 24
      (leaf4083Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4083RoundedFacts : LeafRoundedFacts 8
    leaf4083Certificate.logOnePlusV leaf4083InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4083InputLogOnePlusV_eq }

private noncomputable def leaf4083Inputs : Inputs :=
  inputsOfCaches globalInput sk112RoundedInputs
    chi254InputQChi innerPair116Input
    leaf4083InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4083LowerChecked :
    lowerCheck 24 leaf4083Box leaf4083Inputs = true := by
  rfl'

private theorem leaf4083CoversExact : CoversExact 8
    leaf4083Box leaf4083Certificate leaf4083InnerLog leaf4083Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk112RoundedFacts chi254RoundedFacts
    innerPair116RoundedFacts leaf4083RoundedFacts (by rfl)

private theorem leaf4083FlatSound : Sound leaf4083Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4083CertificateValid
    leaf4083InnerLogValid leaf4083CoversExact leaf4083LowerChecked

private noncomputable def leaf4084Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (93/32), chiLo := (23/64), chiHi := (47/128) }

private noncomputable def leaf4084Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435735/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357500416) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (545733835/536870912) }, upper := { exponent := 1, mantissa := (8467/8192) } }, logOuter := sk111LogOuterCertificate, logK := sk111LogKCertificate, logChi := chi255LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716222975/68715000832) } }, logDArg := sk111LogDArgCertificate }

private noncomputable def leaf4084InnerLog : WideLogData :=
  innerPair117Data

set_option maxRecDepth 1000000 in
private theorem leaf4084LocalValidity :
    LeafFacts leaf4084Box leaf4084Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4084Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357500416) }) = true
      norm_num [leaf4084Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4084CertificateValid :
    WideCertificateValid leaf4084Box leaf4084Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk111ValidityFacts chi255ValidityFacts
    leaf4084LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4084CoverageChecked :
    coverageCheck (innerAD leaf4084Box) leaf4084InnerLog = true := by
  rfl'

private theorem leaf4084InnerLogValid :
    leaf4084InnerLog.Valid 8 (innerAD leaf4084Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint73PositiveFacts.valid leaf4084CoverageChecked

private noncomputable def leaf4084InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629379/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4084InputLogOnePlusV_eq :
    leaf4084InputLogOnePlusV = outerEnclosure 24
      (leaf4084Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4084RoundedFacts : LeafRoundedFacts 8
    leaf4084Certificate.logOnePlusV leaf4084InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4084InputLogOnePlusV_eq }

private noncomputable def leaf4084Inputs : Inputs :=
  inputsOfCaches globalInput sk111RoundedInputs
    chi255InputQChi innerPair117Input
    leaf4084InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4084LowerChecked :
    lowerCheck 24 leaf4084Box leaf4084Inputs = true := by
  rfl'

private theorem leaf4084CoversExact : CoversExact 8
    leaf4084Box leaf4084Certificate leaf4084InnerLog leaf4084Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk111RoundedFacts chi255RoundedFacts
    innerPair117RoundedFacts leaf4084RoundedFacts (by rfl)

private theorem leaf4084FlatSound : Sound leaf4084Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4084CertificateValid
    leaf4084InnerLogValid leaf4084CoversExact leaf4084LowerChecked

private noncomputable def leaf4085Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (93/32), kHi := (47/16), chiLo := (23/64), chiHi := (47/128) }

private noncomputable def leaf4085Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435737/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357476352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (548748305/536870912) }, upper := { exponent := 1, mantissa := (4257/4096) } }, logOuter := sk112LogOuterCertificate, logK := sk112LogKCertificate, logChi := chi255LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716198911/68714952704) } }, logDArg := sk112LogDArgCertificate }

private noncomputable def leaf4085InnerLog : WideLogData :=
  innerPair117Data

set_option maxRecDepth 1000000 in
private theorem leaf4085LocalValidity :
    LeafFacts leaf4085Box leaf4085Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4085Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357476352) }) = true
      norm_num [leaf4085Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4085CertificateValid :
    WideCertificateValid leaf4085Box leaf4085Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk112ValidityFacts chi255ValidityFacts
    leaf4085LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4085CoverageChecked :
    coverageCheck (innerAD leaf4085Box) leaf4085InnerLog = true := by
  rfl'

private theorem leaf4085InnerLogValid :
    leaf4085InnerLog.Valid 8 (innerAD leaf4085Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint73PositiveFacts.valid leaf4085CoverageChecked

private noncomputable def leaf4085InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629385/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4085InputLogOnePlusV_eq :
    leaf4085InputLogOnePlusV = outerEnclosure 24
      (leaf4085Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4085RoundedFacts : LeafRoundedFacts 8
    leaf4085Certificate.logOnePlusV leaf4085InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4085InputLogOnePlusV_eq }

private noncomputable def leaf4085Inputs : Inputs :=
  inputsOfCaches globalInput sk112RoundedInputs
    chi255InputQChi innerPair117Input
    leaf4085InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4085LowerChecked :
    lowerCheck 24 leaf4085Box leaf4085Inputs = true := by
  rfl'

private theorem leaf4085CoversExact : CoversExact 8
    leaf4085Box leaf4085Certificate leaf4085InnerLog leaf4085Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk112RoundedFacts chi255RoundedFacts
    innerPair117RoundedFacts leaf4085RoundedFacts (by rfl)

private theorem leaf4085FlatSound : Sound leaf4085Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4085CertificateValid
    leaf4085InnerLogValid leaf4085CoversExact leaf4085LowerChecked

private noncomputable def leaf4086Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (93/32), chiLo := (47/128), chiHi := (3/8) }

private noncomputable def leaf4086Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435737/268435456) }, vSqrt := { lower := (32765/32768), upper := (227541209/227532800) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (551762777/536870912) }, upper := { exponent := 1, mantissa := (535/512) } }, logOuter := sk111LogOuterCertificate, logK := sk111LogKCertificate, logChi := chi256LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (455074009/455065600) } }, logDArg := sk111LogDArgCertificate }

private noncomputable def leaf4086InnerLog : WideLogData :=
  innerPair117Data

set_option maxRecDepth 1000000 in
private theorem leaf4086LocalValidity :
    LeafFacts leaf4086Box leaf4086Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4086Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (227541209/227532800) }) = true
      norm_num [leaf4086Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4086CertificateValid :
    WideCertificateValid leaf4086Box leaf4086Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk111ValidityFacts chi256ValidityFacts
    leaf4086LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4086CoverageChecked :
    coverageCheck (innerAD leaf4086Box) leaf4086InnerLog = true := by
  rfl'

private theorem leaf4086InnerLogValid :
    leaf4086InnerLog.Valid 8 (innerAD leaf4086Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint73PositiveFacts.valid leaf4086CoverageChecked

private noncomputable def leaf4086InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629391/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4086InputLogOnePlusV_eq :
    leaf4086InputLogOnePlusV = outerEnclosure 24
      (leaf4086Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4086RoundedFacts : LeafRoundedFacts 8
    leaf4086Certificate.logOnePlusV leaf4086InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4086InputLogOnePlusV_eq }

private noncomputable def leaf4086Inputs : Inputs :=
  inputsOfCaches globalInput sk111RoundedInputs
    chi256InputQChi innerPair117Input
    leaf4086InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4086LowerChecked :
    lowerCheck 24 leaf4086Box leaf4086Inputs = true := by
  rfl'

private theorem leaf4086CoversExact : CoversExact 8
    leaf4086Box leaf4086Certificate leaf4086InnerLog leaf4086Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk111RoundedFacts chi256RoundedFacts
    innerPair117RoundedFacts leaf4086RoundedFacts (by rfl)

private theorem leaf4086FlatSound : Sound leaf4086Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4086CertificateValid
    leaf4086InnerLogValid leaf4086CoversExact leaf4086LowerChecked

private noncomputable def leaf4087Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (93/32), kHi := (47/16), chiLo := (47/128), chiHi := (3/8) }

private noncomputable def leaf4087Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435739/268435456) }, vSqrt := { lower := (32765/32768), upper := (4908388937/4908204032) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (554842779/536870912) }, upper := { exponent := 1, mantissa := (269/256) } }, logOuter := sk112LogOuterCertificate, logK := sk112LogKCertificate, logChi := chi256LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (9816592969/9816408064) } }, logDArg := sk112LogDArgCertificate }

private noncomputable def leaf4087InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4087LocalValidity :
    LeafFacts leaf4087Box leaf4087Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4087Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4908388937/4908204032) }) = true
      norm_num [leaf4087Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4087CertificateValid :
    WideCertificateValid leaf4087Box leaf4087Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk112ValidityFacts chi256ValidityFacts
    leaf4087LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4087CoverageChecked :
    coverageCheck (innerAD leaf4087Box) leaf4087InnerLog = true := by
  rfl'

private theorem leaf4087InnerLogValid :
    leaf4087InnerLog.Valid 8 (innerAD leaf4087Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4087CoverageChecked

private noncomputable def leaf4087InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629397/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4087InputLogOnePlusV_eq :
    leaf4087InputLogOnePlusV = outerEnclosure 24
      (leaf4087Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4087RoundedFacts : LeafRoundedFacts 8
    leaf4087Certificate.logOnePlusV leaf4087InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4087InputLogOnePlusV_eq }

private noncomputable def leaf4087Inputs : Inputs :=
  inputsOfCaches globalInput sk112RoundedInputs
    chi256InputQChi innerPair242Input
    leaf4087InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4087LowerChecked :
    lowerCheck 24 leaf4087Box leaf4087Inputs = true := by
  rfl'

private theorem leaf4087CoversExact : CoversExact 8
    leaf4087Box leaf4087Certificate leaf4087InnerLog leaf4087Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk112RoundedFacts chi256RoundedFacts
    innerPair242RoundedFacts leaf4087RoundedFacts (by rfl)

private theorem leaf4087FlatSound : Sound leaf4087Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4087CertificateValid
    leaf4087InnerLogValid leaf4087CoversExact leaf4087LowerChecked

private noncomputable def leaf4088Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (95/32), chiLo := (11/32), chiHi := (45/128) }

private noncomputable def leaf4088Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435735/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357549568) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (539442763/536870912) }, upper := { exponent := 1, mantissa := (8371/8192) } }, logOuter := sk113LogOuterCertificate, logK := sk113LogKCertificate, logChi := chi253LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716272127/68715099136) } }, logDArg := sk113LogDArgCertificate }

private noncomputable def leaf4088InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4088LocalValidity :
    LeafFacts leaf4088Box leaf4088Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4088Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357549568) }) = true
      norm_num [leaf4088Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4088CertificateValid :
    WideCertificateValid leaf4088Box leaf4088Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk113ValidityFacts chi253ValidityFacts
    leaf4088LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4088CoverageChecked :
    coverageCheck (innerAD leaf4088Box) leaf4088InnerLog = true := by
  rfl'

private theorem leaf4088InnerLogValid :
    leaf4088InnerLog.Valid 8 (innerAD leaf4088Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4088CoverageChecked

private noncomputable def leaf4088InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629367/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4088InputLogOnePlusV_eq :
    leaf4088InputLogOnePlusV = outerEnclosure 24
      (leaf4088Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4088RoundedFacts : LeafRoundedFacts 8
    leaf4088Certificate.logOnePlusV leaf4088InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4088InputLogOnePlusV_eq }

private noncomputable def leaf4088Inputs : Inputs :=
  inputsOfCaches globalInput sk113RoundedInputs
    chi253InputQChi innerPair116Input
    leaf4088InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4088LowerChecked :
    lowerCheck 24 leaf4088Box leaf4088Inputs = true := by
  rfl'

private theorem leaf4088CoversExact : CoversExact 8
    leaf4088Box leaf4088Certificate leaf4088InnerLog leaf4088Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk113RoundedFacts chi253RoundedFacts
    innerPair116RoundedFacts leaf4088RoundedFacts (by rfl)

private theorem leaf4088FlatSound : Sound leaf4088Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4088CertificateValid
    leaf4088InnerLogValid leaf4088CoversExact leaf4088LowerChecked

private noncomputable def leaf4089Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (3), chiLo := (11/32), chiHi := (45/128) }

private noncomputable def leaf4089Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435737/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357526528) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (542326169/536870912) }, upper := { exponent := 1, mantissa := (263/256) } }, logOuter := sk114LogOuterCertificate, logK := sk114LogKCertificate, logChi := chi253LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716249087/68715053056) } }, logDArg := sk114LogDArgCertificate }

private noncomputable def leaf4089InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4089LocalValidity :
    LeafFacts leaf4089Box leaf4089Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4089Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357526528) }) = true
      norm_num [leaf4089Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4089CertificateValid :
    WideCertificateValid leaf4089Box leaf4089Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk114ValidityFacts chi253ValidityFacts
    leaf4089LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4089CoverageChecked :
    coverageCheck (innerAD leaf4089Box) leaf4089InnerLog = true := by
  rfl'

private theorem leaf4089InnerLogValid :
    leaf4089InnerLog.Valid 8 (innerAD leaf4089Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4089CoverageChecked

private noncomputable def leaf4089InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629373/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4089InputLogOnePlusV_eq :
    leaf4089InputLogOnePlusV = outerEnclosure 24
      (leaf4089Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4089RoundedFacts : LeafRoundedFacts 8
    leaf4089Certificate.logOnePlusV leaf4089InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4089InputLogOnePlusV_eq }

private noncomputable def leaf4089Inputs : Inputs :=
  inputsOfCaches globalInput sk114RoundedInputs
    chi253InputQChi innerPair116Input
    leaf4089InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4089LowerChecked :
    lowerCheck 24 leaf4089Box leaf4089Inputs = true := by
  rfl'

private theorem leaf4089CoversExact : CoversExact 8
    leaf4089Box leaf4089Certificate leaf4089InnerLog leaf4089Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk114RoundedFacts chi253RoundedFacts
    innerPair116RoundedFacts leaf4089RoundedFacts (by rfl)

private theorem leaf4089FlatSound : Sound leaf4089Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4089CertificateValid
    leaf4089InnerLogValid leaf4089CoversExact leaf4089LowerChecked

private noncomputable def leaf4090Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (95/32), chiLo := (45/128), chiHi := (23/64) }

private noncomputable def leaf4090Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435737/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357500928) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (545602769/536870912) }, upper := { exponent := 1, mantissa := (4233/4096) } }, logOuter := sk113LogOuterCertificate, logK := sk113LogKCertificate, logChi := chi254LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716223487/68715001856) } }, logDArg := sk113LogDArgCertificate }

private noncomputable def leaf4090InnerLog : WideLogData :=
  innerPair311Data

set_option maxRecDepth 1000000 in
private theorem leaf4090LocalValidity :
    LeafFacts leaf4090Box leaf4090Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4090Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357500928) }) = true
      norm_num [leaf4090Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4090CertificateValid :
    WideCertificateValid leaf4090Box leaf4090Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk113ValidityFacts chi254ValidityFacts
    leaf4090LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4090CoverageChecked :
    coverageCheck (innerAD leaf4090Box) leaf4090InnerLog = true := by
  rfl'

private theorem leaf4090InnerLogValid :
    leaf4090InnerLog.Valid 8 (innerAD leaf4090Box) :=
  wideLogDataValid_of_cachedCheck endpoint82PositiveFacts
    endpoint86PositiveFacts.valid leaf4090CoverageChecked

private noncomputable def leaf4090InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629379/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4090InputLogOnePlusV_eq :
    leaf4090InputLogOnePlusV = outerEnclosure 24
      (leaf4090Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4090RoundedFacts : LeafRoundedFacts 8
    leaf4090Certificate.logOnePlusV leaf4090InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4090InputLogOnePlusV_eq }

private noncomputable def leaf4090Inputs : Inputs :=
  inputsOfCaches globalInput sk113RoundedInputs
    chi254InputQChi innerPair311Input
    leaf4090InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4090LowerChecked :
    lowerCheck 24 leaf4090Box leaf4090Inputs = true := by
  rfl'

private theorem leaf4090CoversExact : CoversExact 8
    leaf4090Box leaf4090Certificate leaf4090InnerLog leaf4090Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk113RoundedFacts chi254RoundedFacts
    innerPair311RoundedFacts leaf4090RoundedFacts (by rfl)

private theorem leaf4090FlatSound : Sound leaf4090Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4090CertificateValid
    leaf4090InnerLogValid leaf4090CoversExact leaf4090LowerChecked

private noncomputable def leaf4091Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (3), chiLo := (45/128), chiHi := (23/64) }

private noncomputable def leaf4091Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435739/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357477376) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (548551707/536870912) }, upper := { exponent := 1, mantissa := (133/128) } }, logOuter := sk114LogOuterCertificate, logK := sk114LogKCertificate, logChi := chi254LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716199935/68714954752) } }, logDArg := sk114LogDArgCertificate }

private noncomputable def leaf4091InnerLog : WideLogData :=
  innerPair311Data

set_option maxRecDepth 1000000 in
private theorem leaf4091LocalValidity :
    LeafFacts leaf4091Box leaf4091Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4091Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357477376) }) = true
      norm_num [leaf4091Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4091CertificateValid :
    WideCertificateValid leaf4091Box leaf4091Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk114ValidityFacts chi254ValidityFacts
    leaf4091LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4091CoverageChecked :
    coverageCheck (innerAD leaf4091Box) leaf4091InnerLog = true := by
  rfl'

private theorem leaf4091InnerLogValid :
    leaf4091InnerLog.Valid 8 (innerAD leaf4091Box) :=
  wideLogDataValid_of_cachedCheck endpoint82PositiveFacts
    endpoint86PositiveFacts.valid leaf4091CoverageChecked

private noncomputable def leaf4091InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629385/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4091InputLogOnePlusV_eq :
    leaf4091InputLogOnePlusV = outerEnclosure 24
      (leaf4091Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4091RoundedFacts : LeafRoundedFacts 8
    leaf4091Certificate.logOnePlusV leaf4091InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4091InputLogOnePlusV_eq }

private noncomputable def leaf4091Inputs : Inputs :=
  inputsOfCaches globalInput sk114RoundedInputs
    chi254InputQChi innerPair311Input
    leaf4091InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4091LowerChecked :
    lowerCheck 24 leaf4091Box leaf4091Inputs = true := by
  rfl'

private theorem leaf4091CoversExact : CoversExact 8
    leaf4091Box leaf4091Certificate leaf4091InnerLog leaf4091Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk114RoundedFacts chi254RoundedFacts
    innerPair311RoundedFacts leaf4091RoundedFacts (by rfl)

private theorem leaf4091FlatSound : Sound leaf4091Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4091CertificateValid
    leaf4091InnerLogValid leaf4091CoversExact leaf4091LowerChecked

private noncomputable def leaf4092Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (95/32), chiLo := (23/64), chiHi := (47/128) }

private noncomputable def leaf4092Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435739/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357452288) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (551762775/536870912) }, upper := { exponent := 1, mantissa := (8561/8192) } }, logOuter := sk113LogOuterCertificate, logK := sk113LogKCertificate, logChi := chi255LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716174847/68714904576) } }, logDArg := sk113LogDArgCertificate }

private noncomputable def leaf4092InnerLog : WideLogData :=
  innerPair117Data

set_option maxRecDepth 1000000 in
private theorem leaf4092LocalValidity :
    LeafFacts leaf4092Box leaf4092Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4092Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357452288) }) = true
      norm_num [leaf4092Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4092CertificateValid :
    WideCertificateValid leaf4092Box leaf4092Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk113ValidityFacts chi255ValidityFacts
    leaf4092LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4092CoverageChecked :
    coverageCheck (innerAD leaf4092Box) leaf4092InnerLog = true := by
  rfl'

private theorem leaf4092InnerLogValid :
    leaf4092InnerLog.Valid 8 (innerAD leaf4092Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint73PositiveFacts.valid leaf4092CoverageChecked

private noncomputable def leaf4092InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629391/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4092InputLogOnePlusV_eq :
    leaf4092InputLogOnePlusV = outerEnclosure 24
      (leaf4092Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4092RoundedFacts : LeafRoundedFacts 8
    leaf4092Certificate.logOnePlusV leaf4092InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4092InputLogOnePlusV_eq }

private noncomputable def leaf4092Inputs : Inputs :=
  inputsOfCaches globalInput sk113RoundedInputs
    chi255InputQChi innerPair117Input
    leaf4092InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4092LowerChecked :
    lowerCheck 24 leaf4092Box leaf4092Inputs = true := by
  rfl'

private theorem leaf4092CoversExact : CoversExact 8
    leaf4092Box leaf4092Certificate leaf4092InnerLog leaf4092Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk113RoundedFacts chi255RoundedFacts
    innerPair117RoundedFacts leaf4092RoundedFacts (by rfl)

private theorem leaf4092FlatSound : Sound leaf4092Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4092CertificateValid
    leaf4092InnerLogValid leaf4092CoversExact leaf4092LowerChecked

private noncomputable def leaf4093Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (3), chiLo := (23/64), chiHi := (47/128) }

private noncomputable def leaf4093Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435741/268435456) }, vSqrt := { lower := (65529/65536), upper := (4908388937/4908204032) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (554777245/536870912) }, upper := { exponent := 1, mantissa := (269/256) } }, logOuter := sk114LogOuterCertificate, logK := sk114LogKCertificate, logChi := chi255LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (9816592969/9816408064) } }, logDArg := sk114LogDArgCertificate }

private noncomputable def leaf4093InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4093LocalValidity :
    LeafFacts leaf4093Box leaf4093Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4093Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4908388937/4908204032) }) = true
      norm_num [leaf4093Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4093CertificateValid :
    WideCertificateValid leaf4093Box leaf4093Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk114ValidityFacts chi255ValidityFacts
    leaf4093LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4093CoverageChecked :
    coverageCheck (innerAD leaf4093Box) leaf4093InnerLog = true := by
  rfl'

private theorem leaf4093InnerLogValid :
    leaf4093InnerLog.Valid 8 (innerAD leaf4093Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4093CoverageChecked

private noncomputable def leaf4093InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629397/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4093InputLogOnePlusV_eq :
    leaf4093InputLogOnePlusV = outerEnclosure 24
      (leaf4093Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4093RoundedFacts : LeafRoundedFacts 8
    leaf4093Certificate.logOnePlusV leaf4093InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4093InputLogOnePlusV_eq }

private noncomputable def leaf4093Inputs : Inputs :=
  inputsOfCaches globalInput sk114RoundedInputs
    chi255InputQChi innerPair242Input
    leaf4093InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4093LowerChecked :
    lowerCheck 24 leaf4093Box leaf4093Inputs = true := by
  rfl'

private theorem leaf4093CoversExact : CoversExact 8
    leaf4093Box leaf4093Certificate leaf4093InnerLog leaf4093Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk114RoundedFacts chi255RoundedFacts
    innerPair242RoundedFacts leaf4093RoundedFacts (by rfl)

private theorem leaf4093FlatSound : Sound leaf4093Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4093CertificateValid
    leaf4093InnerLogValid leaf4093CoversExact leaf4093LowerChecked

private noncomputable def leaf4094Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (95/32), chiLo := (47/128), chiHi := (3/8) }

private noncomputable def leaf4094Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435741/268435456) }, vSqrt := { lower := (32765/32768), upper := (2021101327/2021023744) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (557922781/536870912) }, upper := { exponent := 1, mantissa := (541/512) } }, logOuter := sk113LogOuterCertificate, logK := sk113LogKCertificate, logChi := chi256LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (4042125071/4042047488) } }, logDArg := sk113LogDArgCertificate }

private noncomputable def leaf4094InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4094LocalValidity :
    LeafFacts leaf4094Box leaf4094Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4094Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (2021101327/2021023744) }) = true
      norm_num [leaf4094Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4094CertificateValid :
    WideCertificateValid leaf4094Box leaf4094Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk113ValidityFacts chi256ValidityFacts
    leaf4094LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4094CoverageChecked :
    coverageCheck (innerAD leaf4094Box) leaf4094InnerLog = true := by
  rfl'

private theorem leaf4094InnerLogValid :
    leaf4094InnerLog.Valid 8 (innerAD leaf4094Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4094CoverageChecked

private noncomputable def leaf4094InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629403/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4094InputLogOnePlusV_eq :
    leaf4094InputLogOnePlusV = outerEnclosure 24
      (leaf4094Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4094RoundedFacts : LeafRoundedFacts 8
    leaf4094Certificate.logOnePlusV leaf4094InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4094InputLogOnePlusV_eq }

private noncomputable def leaf4094Inputs : Inputs :=
  inputsOfCaches globalInput sk113RoundedInputs
    chi256InputQChi innerPair242Input
    leaf4094InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4094LowerChecked :
    lowerCheck 24 leaf4094Box leaf4094Inputs = true := by
  rfl'

private theorem leaf4094CoversExact : CoversExact 8
    leaf4094Box leaf4094Certificate leaf4094InnerLog leaf4094Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk113RoundedFacts chi256RoundedFacts
    innerPair242RoundedFacts leaf4094RoundedFacts (by rfl)

private theorem leaf4094FlatSound : Sound leaf4094Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4094CertificateValid
    leaf4094InnerLogValid leaf4094CoversExact leaf4094LowerChecked

private noncomputable def leaf4095Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (3), chiLo := (47/128), chiHi := (3/8) }

private noncomputable def leaf4095Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435743/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357379072) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (561002783/536870912) }, upper := { exponent := 1, mantissa := (17/16) } }, logOuter := sk114LogOuterCertificate, logK := sk114LogKCertificate, logChi := chi256LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716101631/68714758144) } }, logDArg := sk114LogDArgCertificate }

private noncomputable def leaf4095InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4095LocalValidity :
    LeafFacts leaf4095Box leaf4095Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4095Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357379072) }) = true
      norm_num [leaf4095Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4095CertificateValid :
    WideCertificateValid leaf4095Box leaf4095Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk114ValidityFacts chi256ValidityFacts
    leaf4095LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4095CoverageChecked :
    coverageCheck (innerAD leaf4095Box) leaf4095InnerLog = true := by
  rfl'

private theorem leaf4095InnerLogValid :
    leaf4095InnerLog.Valid 8 (innerAD leaf4095Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4095CoverageChecked

private noncomputable def leaf4095InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629409/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4095InputLogOnePlusV_eq :
    leaf4095InputLogOnePlusV = outerEnclosure 24
      (leaf4095Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4095RoundedFacts : LeafRoundedFacts 8
    leaf4095Certificate.logOnePlusV leaf4095InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4095InputLogOnePlusV_eq }

private noncomputable def leaf4095Inputs : Inputs :=
  inputsOfCaches globalInput sk114RoundedInputs
    chi256InputQChi innerPair242Input
    leaf4095InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4095LowerChecked :
    lowerCheck 24 leaf4095Box leaf4095Inputs = true := by
  rfl'

private theorem leaf4095CoversExact : CoversExact 8
    leaf4095Box leaf4095Certificate leaf4095InnerLog leaf4095Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk114RoundedFacts chi256RoundedFacts
    innerPair242RoundedFacts leaf4095RoundedFacts (by rfl)

private theorem leaf4095FlatSound : Sound leaf4095Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4095CertificateValid
    leaf4095InnerLogValid leaf4095CoversExact leaf4095LowerChecked

private noncomputable def component83Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (89/32), chiLo := (5/16), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component83Node0_sound : Sound component83Node0Box :=
  sound_of_literal_split component83Node0Box leaf4032Box leaf4033Box
    .chi (41/128) (by rfl) (by rfl)
    leaf4032FlatSound leaf4033FlatSound

private noncomputable def component83Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (89/32), kHi := (45/16), chiLo := (5/16), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component83Node1_sound : Sound component83Node1Box :=
  sound_of_literal_split component83Node1Box leaf4034Box leaf4035Box
    .chi (41/128) (by rfl) (by rfl)
    leaf4034FlatSound leaf4035FlatSound

private noncomputable def component83Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (5/16), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component83Node2_sound : Sound component83Node2Box :=
  sound_of_literal_split component83Node2Box component83Node0Box component83Node1Box
    .k (89/32) (by rfl) (by rfl)
    component83Node0_sound component83Node1_sound

private noncomputable def component83Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (89/32), chiLo := (21/64), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component83Node3_sound : Sound component83Node3Box :=
  sound_of_literal_split component83Node3Box leaf4036Box leaf4037Box
    .chi (43/128) (by rfl) (by rfl)
    leaf4036FlatSound leaf4037FlatSound

private noncomputable def component83Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (89/32), kHi := (45/16), chiLo := (21/64), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component83Node4_sound : Sound component83Node4Box :=
  sound_of_literal_split component83Node4Box leaf4038Box leaf4039Box
    .chi (43/128) (by rfl) (by rfl)
    leaf4038FlatSound leaf4039FlatSound

private noncomputable def component83Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (21/64), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component83Node5_sound : Sound component83Node5Box :=
  sound_of_literal_split component83Node5Box component83Node3Box component83Node4Box
    .k (89/32) (by rfl) (by rfl)
    component83Node3_sound component83Node4_sound

private noncomputable def component83Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (5/16), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component83Node6_sound : Sound component83Node6Box :=
  sound_of_literal_split component83Node6Box component83Node2Box component83Node5Box
    .chi (21/64) (by rfl) (by rfl)
    component83Node2_sound component83Node5_sound

private noncomputable def component83Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (5/16), chiHi := (41/128) }

set_option maxRecDepth 1000000 in
private theorem component83Node7_sound : Sound component83Node7Box :=
  sound_of_literal_split component83Node7Box leaf4040Box leaf4041Box
    .k (91/32) (by rfl) (by rfl)
    leaf4040FlatSound leaf4041FlatSound

private noncomputable def component83Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (41/128), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component83Node8_sound : Sound component83Node8Box :=
  sound_of_literal_split component83Node8Box leaf4042Box leaf4043Box
    .k (91/32) (by rfl) (by rfl)
    leaf4042FlatSound leaf4043FlatSound

private noncomputable def component83Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (5/16), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component83Node9_sound : Sound component83Node9Box :=
  sound_of_literal_split component83Node9Box component83Node7Box component83Node8Box
    .chi (41/128) (by rfl) (by rfl)
    component83Node7_sound component83Node8_sound

private noncomputable def component83Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (21/64), chiHi := (43/128) }

set_option maxRecDepth 1000000 in
private theorem component83Node10_sound : Sound component83Node10Box :=
  sound_of_literal_split component83Node10Box leaf4044Box leaf4045Box
    .k (91/32) (by rfl) (by rfl)
    leaf4044FlatSound leaf4045FlatSound

private noncomputable def component83Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (43/128), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component83Node11_sound : Sound component83Node11Box :=
  sound_of_literal_split component83Node11Box leaf4046Box leaf4047Box
    .k (91/32) (by rfl) (by rfl)
    leaf4046FlatSound leaf4047FlatSound

private noncomputable def component83Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (21/64), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component83Node12_sound : Sound component83Node12Box :=
  sound_of_literal_split component83Node12Box component83Node10Box component83Node11Box
    .chi (43/128) (by rfl) (by rfl)
    component83Node10_sound component83Node11_sound

private noncomputable def component83Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (5/16), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component83Node13_sound : Sound component83Node13Box :=
  sound_of_literal_split component83Node13Box component83Node9Box component83Node12Box
    .chi (21/64) (by rfl) (by rfl)
    component83Node9_sound component83Node12_sound

private noncomputable def component83Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (23/8), chiLo := (5/16), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component83Node14_sound : Sound component83Node14Box :=
  sound_of_literal_split component83Node14Box component83Node6Box component83Node13Box
    .k (45/16) (by rfl) (by rfl)
    component83Node6_sound component83Node13_sound

private noncomputable def component83Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (11/32), chiHi := (45/128) }

set_option maxRecDepth 1000000 in
private theorem component83Node15_sound : Sound component83Node15Box :=
  sound_of_literal_split component83Node15Box leaf4048Box leaf4049Box
    .k (89/32) (by rfl) (by rfl)
    leaf4048FlatSound leaf4049FlatSound

private noncomputable def component83Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (45/128), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component83Node16_sound : Sound component83Node16Box :=
  sound_of_literal_split component83Node16Box leaf4050Box leaf4051Box
    .k (89/32) (by rfl) (by rfl)
    leaf4050FlatSound leaf4051FlatSound

private noncomputable def component83Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (11/32), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component83Node17_sound : Sound component83Node17Box :=
  sound_of_literal_split component83Node17Box component83Node15Box component83Node16Box
    .chi (45/128) (by rfl) (by rfl)
    component83Node15_sound component83Node16_sound

private noncomputable def component83Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (23/64), chiHi := (47/128) }

set_option maxRecDepth 1000000 in
private theorem component83Node18_sound : Sound component83Node18Box :=
  sound_of_literal_split component83Node18Box leaf4052Box leaf4053Box
    .k (89/32) (by rfl) (by rfl)
    leaf4052FlatSound leaf4053FlatSound

private noncomputable def component83Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (47/128), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component83Node19_sound : Sound component83Node19Box :=
  sound_of_literal_split component83Node19Box leaf4054Box leaf4055Box
    .k (89/32) (by rfl) (by rfl)
    leaf4054FlatSound leaf4055FlatSound

private noncomputable def component83Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (23/64), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component83Node20_sound : Sound component83Node20Box :=
  sound_of_literal_split component83Node20Box component83Node18Box component83Node19Box
    .chi (47/128) (by rfl) (by rfl)
    component83Node18_sound component83Node19_sound

private noncomputable def component83Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (11/32), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component83Node21_sound : Sound component83Node21Box :=
  sound_of_literal_split component83Node21Box component83Node17Box component83Node20Box
    .chi (23/64) (by rfl) (by rfl)
    component83Node17_sound component83Node20_sound

private noncomputable def component83Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (11/32), chiHi := (45/128) }

set_option maxRecDepth 1000000 in
private theorem component83Node22_sound : Sound component83Node22Box :=
  sound_of_literal_split component83Node22Box leaf4056Box leaf4057Box
    .k (91/32) (by rfl) (by rfl)
    leaf4056FlatSound leaf4057FlatSound

private noncomputable def component83Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (45/128), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component83Node23_sound : Sound component83Node23Box :=
  sound_of_literal_split component83Node23Box leaf4058Box leaf4059Box
    .k (91/32) (by rfl) (by rfl)
    leaf4058FlatSound leaf4059FlatSound

private noncomputable def component83Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (11/32), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component83Node24_sound : Sound component83Node24Box :=
  sound_of_literal_split component83Node24Box component83Node22Box component83Node23Box
    .chi (45/128) (by rfl) (by rfl)
    component83Node22_sound component83Node23_sound

private noncomputable def component83Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (23/64), chiHi := (47/128) }

set_option maxRecDepth 1000000 in
private theorem component83Node25_sound : Sound component83Node25Box :=
  sound_of_literal_split component83Node25Box leaf4060Box leaf4061Box
    .k (91/32) (by rfl) (by rfl)
    leaf4060FlatSound leaf4061FlatSound

private noncomputable def component83Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (47/128), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component83Node26_sound : Sound component83Node26Box :=
  sound_of_literal_split component83Node26Box leaf4062Box leaf4063Box
    .k (91/32) (by rfl) (by rfl)
    leaf4062FlatSound leaf4063FlatSound

private noncomputable def component83Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (23/64), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component83Node27_sound : Sound component83Node27Box :=
  sound_of_literal_split component83Node27Box component83Node25Box component83Node26Box
    .chi (47/128) (by rfl) (by rfl)
    component83Node25_sound component83Node26_sound

private noncomputable def component83Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (11/32), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component83Node28_sound : Sound component83Node28Box :=
  sound_of_literal_split component83Node28Box component83Node24Box component83Node27Box
    .chi (23/64) (by rfl) (by rfl)
    component83Node24_sound component83Node27_sound

private noncomputable def component83Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (23/8), chiLo := (11/32), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component83Node29_sound : Sound component83Node29Box :=
  sound_of_literal_split component83Node29Box component83Node21Box component83Node28Box
    .k (45/16) (by rfl) (by rfl)
    component83Node21_sound component83Node28_sound

private noncomputable def component83Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (23/8), chiLo := (5/16), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component83Node30_sound : Sound component83Node30Box :=
  sound_of_literal_split component83Node30Box component83Node14Box component83Node29Box
    .chi (11/32) (by rfl) (by rfl)
    component83Node14_sound component83Node29_sound

private noncomputable def component83Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (5/16), chiHi := (41/128) }

set_option maxRecDepth 1000000 in
private theorem component83Node31_sound : Sound component83Node31Box :=
  sound_of_literal_split component83Node31Box leaf4064Box leaf4065Box
    .k (93/32) (by rfl) (by rfl)
    leaf4064FlatSound leaf4065FlatSound

private noncomputable def component83Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (41/128), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component83Node32_sound : Sound component83Node32Box :=
  sound_of_literal_split component83Node32Box leaf4066Box leaf4067Box
    .k (93/32) (by rfl) (by rfl)
    leaf4066FlatSound leaf4067FlatSound

private noncomputable def component83Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (5/16), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component83Node33_sound : Sound component83Node33Box :=
  sound_of_literal_split component83Node33Box component83Node31Box component83Node32Box
    .chi (41/128) (by rfl) (by rfl)
    component83Node31_sound component83Node32_sound

private noncomputable def component83Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (21/64), chiHi := (43/128) }

set_option maxRecDepth 1000000 in
private theorem component83Node34_sound : Sound component83Node34Box :=
  sound_of_literal_split component83Node34Box leaf4068Box leaf4069Box
    .k (93/32) (by rfl) (by rfl)
    leaf4068FlatSound leaf4069FlatSound

private noncomputable def component83Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (43/128), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component83Node35_sound : Sound component83Node35Box :=
  sound_of_literal_split component83Node35Box leaf4070Box leaf4071Box
    .k (93/32) (by rfl) (by rfl)
    leaf4070FlatSound leaf4071FlatSound

private noncomputable def component83Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (21/64), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component83Node36_sound : Sound component83Node36Box :=
  sound_of_literal_split component83Node36Box component83Node34Box component83Node35Box
    .chi (43/128) (by rfl) (by rfl)
    component83Node34_sound component83Node35_sound

private noncomputable def component83Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (5/16), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component83Node37_sound : Sound component83Node37Box :=
  sound_of_literal_split component83Node37Box component83Node33Box component83Node36Box
    .chi (21/64) (by rfl) (by rfl)
    component83Node33_sound component83Node36_sound

private noncomputable def component83Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (5/16), chiHi := (41/128) }

set_option maxRecDepth 1000000 in
private theorem component83Node38_sound : Sound component83Node38Box :=
  sound_of_literal_split component83Node38Box leaf4072Box leaf4073Box
    .k (95/32) (by rfl) (by rfl)
    leaf4072FlatSound leaf4073FlatSound

private noncomputable def component83Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (41/128), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component83Node39_sound : Sound component83Node39Box :=
  sound_of_literal_split component83Node39Box leaf4074Box leaf4075Box
    .k (95/32) (by rfl) (by rfl)
    leaf4074FlatSound leaf4075FlatSound

private noncomputable def component83Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (5/16), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component83Node40_sound : Sound component83Node40Box :=
  sound_of_literal_split component83Node40Box component83Node38Box component83Node39Box
    .chi (41/128) (by rfl) (by rfl)
    component83Node38_sound component83Node39_sound

private noncomputable def component83Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (21/64), chiHi := (43/128) }

set_option maxRecDepth 1000000 in
private theorem component83Node41_sound : Sound component83Node41Box :=
  sound_of_literal_split component83Node41Box leaf4076Box leaf4077Box
    .k (95/32) (by rfl) (by rfl)
    leaf4076FlatSound leaf4077FlatSound

private noncomputable def component83Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (43/128), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component83Node42_sound : Sound component83Node42Box :=
  sound_of_literal_split component83Node42Box leaf4078Box leaf4079Box
    .k (95/32) (by rfl) (by rfl)
    leaf4078FlatSound leaf4079FlatSound

private noncomputable def component83Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (21/64), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component83Node43_sound : Sound component83Node43Box :=
  sound_of_literal_split component83Node43Box component83Node41Box component83Node42Box
    .chi (43/128) (by rfl) (by rfl)
    component83Node41_sound component83Node42_sound

private noncomputable def component83Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (5/16), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component83Node44_sound : Sound component83Node44Box :=
  sound_of_literal_split component83Node44Box component83Node40Box component83Node43Box
    .chi (21/64) (by rfl) (by rfl)
    component83Node40_sound component83Node43_sound

private noncomputable def component83Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (5/16), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component83Node45_sound : Sound component83Node45Box :=
  sound_of_literal_split component83Node45Box component83Node37Box component83Node44Box
    .k (47/16) (by rfl) (by rfl)
    component83Node37_sound component83Node44_sound

private noncomputable def component83Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (11/32), chiHi := (45/128) }

set_option maxRecDepth 1000000 in
private theorem component83Node46_sound : Sound component83Node46Box :=
  sound_of_literal_split component83Node46Box leaf4080Box leaf4081Box
    .k (93/32) (by rfl) (by rfl)
    leaf4080FlatSound leaf4081FlatSound

private noncomputable def component83Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (45/128), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component83Node47_sound : Sound component83Node47Box :=
  sound_of_literal_split component83Node47Box leaf4082Box leaf4083Box
    .k (93/32) (by rfl) (by rfl)
    leaf4082FlatSound leaf4083FlatSound

private noncomputable def component83Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (11/32), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component83Node48_sound : Sound component83Node48Box :=
  sound_of_literal_split component83Node48Box component83Node46Box component83Node47Box
    .chi (45/128) (by rfl) (by rfl)
    component83Node46_sound component83Node47_sound

private noncomputable def component83Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (23/64), chiHi := (47/128) }

set_option maxRecDepth 1000000 in
private theorem component83Node49_sound : Sound component83Node49Box :=
  sound_of_literal_split component83Node49Box leaf4084Box leaf4085Box
    .k (93/32) (by rfl) (by rfl)
    leaf4084FlatSound leaf4085FlatSound

private noncomputable def component83Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (47/128), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component83Node50_sound : Sound component83Node50Box :=
  sound_of_literal_split component83Node50Box leaf4086Box leaf4087Box
    .k (93/32) (by rfl) (by rfl)
    leaf4086FlatSound leaf4087FlatSound

private noncomputable def component83Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (23/64), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component83Node51_sound : Sound component83Node51Box :=
  sound_of_literal_split component83Node51Box component83Node49Box component83Node50Box
    .chi (47/128) (by rfl) (by rfl)
    component83Node49_sound component83Node50_sound

private noncomputable def component83Node52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (11/32), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component83Node52_sound : Sound component83Node52Box :=
  sound_of_literal_split component83Node52Box component83Node48Box component83Node51Box
    .chi (23/64) (by rfl) (by rfl)
    component83Node48_sound component83Node51_sound

private noncomputable def component83Node53Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (11/32), chiHi := (45/128) }

set_option maxRecDepth 1000000 in
private theorem component83Node53_sound : Sound component83Node53Box :=
  sound_of_literal_split component83Node53Box leaf4088Box leaf4089Box
    .k (95/32) (by rfl) (by rfl)
    leaf4088FlatSound leaf4089FlatSound

private noncomputable def component83Node54Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (45/128), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component83Node54_sound : Sound component83Node54Box :=
  sound_of_literal_split component83Node54Box leaf4090Box leaf4091Box
    .k (95/32) (by rfl) (by rfl)
    leaf4090FlatSound leaf4091FlatSound

private noncomputable def component83Node55Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (11/32), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component83Node55_sound : Sound component83Node55Box :=
  sound_of_literal_split component83Node55Box component83Node53Box component83Node54Box
    .chi (45/128) (by rfl) (by rfl)
    component83Node53_sound component83Node54_sound

private noncomputable def component83Node56Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (23/64), chiHi := (47/128) }

set_option maxRecDepth 1000000 in
private theorem component83Node56_sound : Sound component83Node56Box :=
  sound_of_literal_split component83Node56Box leaf4092Box leaf4093Box
    .k (95/32) (by rfl) (by rfl)
    leaf4092FlatSound leaf4093FlatSound

private noncomputable def component83Node57Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (47/128), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component83Node57_sound : Sound component83Node57Box :=
  sound_of_literal_split component83Node57Box leaf4094Box leaf4095Box
    .k (95/32) (by rfl) (by rfl)
    leaf4094FlatSound leaf4095FlatSound

private noncomputable def component83Node58Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (23/64), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component83Node58_sound : Sound component83Node58Box :=
  sound_of_literal_split component83Node58Box component83Node56Box component83Node57Box
    .chi (47/128) (by rfl) (by rfl)
    component83Node56_sound component83Node57_sound

private noncomputable def component83Node59Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (11/32), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component83Node59_sound : Sound component83Node59Box :=
  sound_of_literal_split component83Node59Box component83Node55Box component83Node58Box
    .chi (23/64) (by rfl) (by rfl)
    component83Node55_sound component83Node58_sound

private noncomputable def component83Node60Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (11/32), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component83Node60_sound : Sound component83Node60Box :=
  sound_of_literal_split component83Node60Box component83Node52Box component83Node59Box
    .k (47/16) (by rfl) (by rfl)
    component83Node52_sound component83Node59_sound

private noncomputable def component83Node61Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (5/16), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component83Node61_sound : Sound component83Node61Box :=
  sound_of_literal_split component83Node61Box component83Node45Box component83Node60Box
    .chi (11/32) (by rfl) (by rfl)
    component83Node45_sound component83Node60_sound

noncomputable def component83Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (3), chiLo := (5/16), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
theorem component83_sound : Sound component83Box :=
  sound_of_literal_split component83Box component83Node30Box component83Node61Box
    .k (23/8) (by rfl) (by rfl)
    component83Node30_sound component83Node61_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
