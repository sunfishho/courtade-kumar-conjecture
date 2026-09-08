import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch5
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch6
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch7
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch10
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch11
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch5
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch8
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch9
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

private noncomputable def leaf6256Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (81/32), chiLo := (1/2), chiHi := (33/64) }

private noncomputable def leaf6256Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217955/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357001216) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (301946655/268435456) }, upper := { exponent := 1, mantissa := (4721/4096) } }, logOuter := sk99LogOuterCertificate, logK := sk99LogKCertificate, logChi := chi82LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715723775/68714002432) } }, logDArg := sk99LogDArgCertificate }

private noncomputable def leaf6256InnerLog : WideLogData :=
  innerPair257Data

set_option maxRecDepth 1000000 in
private theorem leaf6256LocalValidity :
    LeafFacts leaf6256Box leaf6256Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6256Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357001216) }) = true
      norm_num [leaf6256Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6256CertificateValid :
    WideCertificateValid leaf6256Box leaf6256Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk99ValidityFacts chi82ValidityFacts
    leaf6256LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6256CoverageChecked :
    coverageCheck (innerAD leaf6256Box) leaf6256InnerLog = true := by
  rfl'

private theorem leaf6256InnerLogValid :
    leaf6256InnerLog.Valid 8 (innerAD leaf6256Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint76PositiveFacts.valid leaf6256CoverageChecked

private noncomputable def leaf6256InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629501/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6256InputLogOnePlusV_eq :
    leaf6256InputLogOnePlusV = outerEnclosure 24
      (leaf6256Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6256RoundedFacts : LeafRoundedFacts 8
    leaf6256Certificate.logOnePlusV leaf6256InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6256InputLogOnePlusV_eq }

private noncomputable def leaf6256Inputs : Inputs :=
  inputsOfCaches globalInput sk99RoundedInputs
    chi82InputQChi innerPair257Input
    leaf6256InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6256LowerChecked :
    lowerCheck 24 leaf6256Box leaf6256Inputs = true := by
  rfl'

private theorem leaf6256CoversExact : CoversExact 8
    leaf6256Box leaf6256Certificate leaf6256InnerLog leaf6256Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk99RoundedFacts chi82RoundedFacts
    innerPair257RoundedFacts leaf6256RoundedFacts (by rfl)

private theorem leaf6256FlatSound : Sound leaf6256Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6256CertificateValid
    leaf6256InnerLogValid leaf6256CoversExact leaf6256LowerChecked

private noncomputable def leaf6257Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (81/32), kHi := (41/16), chiLo := (1/2), chiHi := (33/64) }

private noncomputable def leaf6257Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217957/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34356967424) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (304043677/268435456) }, upper := { exponent := 1, mantissa := (2377/2048) } }, logOuter := sk100LogOuterCertificate, logK := sk100LogKCertificate, logChi := chi82LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715689983/68713934848) } }, logDArg := sk100LogDArgCertificate }

private noncomputable def leaf6257InnerLog : WideLogData :=
  innerPair265Data

set_option maxRecDepth 1000000 in
private theorem leaf6257LocalValidity :
    LeafFacts leaf6257Box leaf6257Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6257Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34356967424) }) = true
      norm_num [leaf6257Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6257CertificateValid :
    WideCertificateValid leaf6257Box leaf6257Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk100ValidityFacts chi82ValidityFacts
    leaf6257LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6257CoverageChecked :
    coverageCheck (innerAD leaf6257Box) leaf6257InnerLog = true := by
  rfl'

private theorem leaf6257InnerLogValid :
    leaf6257InnerLog.Valid 8 (innerAD leaf6257Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint77PositiveFacts.valid leaf6257CoverageChecked

private noncomputable def leaf6257InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629509/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6257InputLogOnePlusV_eq :
    leaf6257InputLogOnePlusV = outerEnclosure 24
      (leaf6257Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6257RoundedFacts : LeafRoundedFacts 8
    leaf6257Certificate.logOnePlusV leaf6257InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6257InputLogOnePlusV_eq }

private noncomputable def leaf6257Inputs : Inputs :=
  inputsOfCaches globalInput sk100RoundedInputs
    chi82InputQChi innerPair265Input
    leaf6257InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6257LowerChecked :
    lowerCheck 24 leaf6257Box leaf6257Inputs = true := by
  rfl'

private theorem leaf6257CoversExact : CoversExact 8
    leaf6257Box leaf6257Certificate leaf6257InnerLog leaf6257Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk100RoundedFacts chi82RoundedFacts
    innerPair265RoundedFacts leaf6257RoundedFacts (by rfl)

private theorem leaf6257FlatSound : Sound leaf6257Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6257CertificateValid
    leaf6257InnerLogValid leaf6257CoversExact leaf6257LowerChecked

private noncomputable def leaf6258Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (81/32), chiLo := (33/64), chiHi := (17/32) }

private noncomputable def leaf6258Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217957/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34356918272) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (307189213/268435456) }, upper := { exponent := 1, mantissa := (2401/2048) } }, logOuter := sk99LogOuterCertificate, logK := sk99LogKCertificate, logChi := chi83LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715640831/68713836544) } }, logDArg := sk99LogDArgCertificate }

private noncomputable def leaf6258InnerLog : WideLogData :=
  innerPair265Data

set_option maxRecDepth 1000000 in
private theorem leaf6258LocalValidity :
    LeafFacts leaf6258Box leaf6258Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6258Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34356918272) }) = true
      norm_num [leaf6258Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6258CertificateValid :
    WideCertificateValid leaf6258Box leaf6258Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk99ValidityFacts chi83ValidityFacts
    leaf6258LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6258CoverageChecked :
    coverageCheck (innerAD leaf6258Box) leaf6258InnerLog = true := by
  rfl'

private theorem leaf6258InnerLogValid :
    leaf6258InnerLog.Valid 8 (innerAD leaf6258Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint77PositiveFacts.valid leaf6258CoverageChecked

private noncomputable def leaf6258InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629521/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6258InputLogOnePlusV_eq :
    leaf6258InputLogOnePlusV = outerEnclosure 24
      (leaf6258Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6258RoundedFacts : LeafRoundedFacts 8
    leaf6258Certificate.logOnePlusV leaf6258InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6258InputLogOnePlusV_eq }

private noncomputable def leaf6258Inputs : Inputs :=
  inputsOfCaches globalInput sk99RoundedInputs
    chi83InputQChi innerPair265Input
    leaf6258InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6258LowerChecked :
    lowerCheck 24 leaf6258Box leaf6258Inputs = true := by
  rfl'

private theorem leaf6258CoversExact : CoversExact 8
    leaf6258Box leaf6258Certificate leaf6258InnerLog leaf6258Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk99RoundedFacts chi83RoundedFacts
    innerPair265RoundedFacts leaf6258RoundedFacts (by rfl)

private theorem leaf6258FlatSound : Sound leaf6258Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6258CertificateValid
    leaf6258InnerLogValid leaf6258CoversExact leaf6258LowerChecked

private noncomputable def leaf6259Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (81/32), kHi := (41/16), chiLo := (33/64), chiHi := (17/32) }

private noncomputable def leaf6259Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217959/134217728) }, vSqrt := { lower := (32765/32768), upper := (4908388937/4908126208) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (309351767/268435456) }, upper := { exponent := 1, mantissa := (1209/1024) } }, logOuter := sk100LogOuterCertificate, logK := sk100LogKCertificate, logChi := chi83LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (9816515145/9816252416) } }, logDArg := sk100LogDArgCertificate }

private noncomputable def leaf6259InnerLog : WideLogData :=
  innerPair265Data

set_option maxRecDepth 1000000 in
private theorem leaf6259LocalValidity :
    LeafFacts leaf6259Box leaf6259Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6259Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4908388937/4908126208) }) = true
      norm_num [leaf6259Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6259CertificateValid :
    WideCertificateValid leaf6259Box leaf6259Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk100ValidityFacts chi83ValidityFacts
    leaf6259LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6259CoverageChecked :
    coverageCheck (innerAD leaf6259Box) leaf6259InnerLog = true := by
  rfl'

private theorem leaf6259InnerLogValid :
    leaf6259InnerLog.Valid 8 (innerAD leaf6259Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint77PositiveFacts.valid leaf6259CoverageChecked

private noncomputable def leaf6259InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814765/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6259InputLogOnePlusV_eq :
    leaf6259InputLogOnePlusV = outerEnclosure 24
      (leaf6259Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6259RoundedFacts : LeafRoundedFacts 8
    leaf6259Certificate.logOnePlusV leaf6259InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6259InputLogOnePlusV_eq }

private noncomputable def leaf6259Inputs : Inputs :=
  inputsOfCaches globalInput sk100RoundedInputs
    chi83InputQChi innerPair265Input
    leaf6259InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6259LowerChecked :
    lowerCheck 24 leaf6259Box leaf6259Inputs = true := by
  rfl'

private theorem leaf6259CoversExact : CoversExact 8
    leaf6259Box leaf6259Certificate leaf6259InnerLog leaf6259Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk100RoundedFacts chi83RoundedFacts
    innerPair265RoundedFacts leaf6259RoundedFacts (by rfl)

private theorem leaf6259FlatSound : Sound leaf6259Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6259CertificateValid
    leaf6259InnerLogValid leaf6259CoversExact leaf6259LowerChecked

private noncomputable def leaf6260Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (83/32), chiLo := (1/2), chiHi := (33/64) }

private noncomputable def leaf6260Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217959/134217728) }, vSqrt := { lower := (32765/32768), upper := (288728761/288713728) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (306140699/268435456) }, upper := { exponent := 1, mantissa := (4787/4096) } }, logOuter := sk101LogOuterCertificate, logK := sk101LogKCertificate, logChi := chi82LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (577442489/577427456) } }, logDArg := sk101LogDArgCertificate }

private noncomputable def leaf6260InnerLog : WideLogData :=
  innerPair265Data

set_option maxRecDepth 1000000 in
private theorem leaf6260LocalValidity :
    LeafFacts leaf6260Box leaf6260Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6260Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (288728761/288713728) }) = true
      norm_num [leaf6260Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6260CertificateValid :
    WideCertificateValid leaf6260Box leaf6260Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk101ValidityFacts chi82ValidityFacts
    leaf6260LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6260CoverageChecked :
    coverageCheck (innerAD leaf6260Box) leaf6260InnerLog = true := by
  rfl'

private theorem leaf6260InnerLogValid :
    leaf6260InnerLog.Valid 8 (innerAD leaf6260Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint77PositiveFacts.valid leaf6260CoverageChecked

private noncomputable def leaf6260InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814759/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6260InputLogOnePlusV_eq :
    leaf6260InputLogOnePlusV = outerEnclosure 24
      (leaf6260Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6260RoundedFacts : LeafRoundedFacts 8
    leaf6260Certificate.logOnePlusV leaf6260InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6260InputLogOnePlusV_eq }

private noncomputable def leaf6260Inputs : Inputs :=
  inputsOfCaches globalInput sk101RoundedInputs
    chi82InputQChi innerPair265Input
    leaf6260InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6260LowerChecked :
    lowerCheck 24 leaf6260Box leaf6260Inputs = true := by
  rfl'

private theorem leaf6260CoversExact : CoversExact 8
    leaf6260Box leaf6260Certificate leaf6260InnerLog leaf6260Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk101RoundedFacts chi82RoundedFacts
    innerPair265RoundedFacts leaf6260RoundedFacts (by rfl)

private theorem leaf6260FlatSound : Sound leaf6260Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6260CertificateValid
    leaf6260InnerLogValid leaf6260CoversExact leaf6260LowerChecked

private noncomputable def leaf6261Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (83/32), kHi := (21/8), chiLo := (1/2), chiHi := (33/64) }

private noncomputable def leaf6261Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217961/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34356899840) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (308237721/268435456) }, upper := { exponent := 1, mantissa := (1205/1024) } }, logOuter := sk102LogOuterCertificate, logK := sk102LogKCertificate, logChi := chi82LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715622399/68713799680) } }, logDArg := sk102LogDArgCertificate }

private noncomputable def leaf6261InnerLog : WideLogData :=
  innerPair265Data

set_option maxRecDepth 1000000 in
private theorem leaf6261LocalValidity :
    LeafFacts leaf6261Box leaf6261Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6261Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34356899840) }) = true
      norm_num [leaf6261Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6261CertificateValid :
    WideCertificateValid leaf6261Box leaf6261Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk102ValidityFacts chi82ValidityFacts
    leaf6261LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6261CoverageChecked :
    coverageCheck (innerAD leaf6261Box) leaf6261InnerLog = true := by
  rfl'

private theorem leaf6261InnerLogValid :
    leaf6261InnerLog.Valid 8 (innerAD leaf6261Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint77PositiveFacts.valid leaf6261CoverageChecked

private noncomputable def leaf6261InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814763/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6261InputLogOnePlusV_eq :
    leaf6261InputLogOnePlusV = outerEnclosure 24
      (leaf6261Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6261RoundedFacts : LeafRoundedFacts 8
    leaf6261Certificate.logOnePlusV leaf6261InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6261InputLogOnePlusV_eq }

private noncomputable def leaf6261Inputs : Inputs :=
  inputsOfCaches globalInput sk102RoundedInputs
    chi82InputQChi innerPair265Input
    leaf6261InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6261LowerChecked :
    lowerCheck 24 leaf6261Box leaf6261Inputs = true := by
  rfl'

private theorem leaf6261CoversExact : CoversExact 8
    leaf6261Box leaf6261Certificate leaf6261InnerLog leaf6261Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk102RoundedFacts chi82RoundedFacts
    innerPair265RoundedFacts leaf6261RoundedFacts (by rfl)

private theorem leaf6261FlatSound : Sound leaf6261Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6261CertificateValid
    leaf6261InnerLogValid leaf6261CoversExact leaf6261LowerChecked

private noncomputable def leaf6262Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (83/32), chiLo := (33/64), chiHi := (17/32) }

private noncomputable def leaf6262Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217961/134217728) }, vSqrt := { lower := (32765/32768), upper := (1108345889/1108285440) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (311514321/268435456) }, upper := { exponent := 1, mantissa := (2435/2048) } }, logOuter := sk101LogOuterCertificate, logK := sk101LogKCertificate, logChi := chi83LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (2216631329/2216570880) } }, logDArg := sk101LogDArgCertificate }

private noncomputable def leaf6262InnerLog : WideLogData :=
  innerPair273Data

set_option maxRecDepth 1000000 in
private theorem leaf6262LocalValidity :
    LeafFacts leaf6262Box leaf6262Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6262Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (1108345889/1108285440) }) = true
      norm_num [leaf6262Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6262CertificateValid :
    WideCertificateValid leaf6262Box leaf6262Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk101ValidityFacts chi83ValidityFacts
    leaf6262LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6262CoverageChecked :
    coverageCheck (innerAD leaf6262Box) leaf6262InnerLog = true := by
  rfl'

private theorem leaf6262InnerLogValid :
    leaf6262InnerLog.Valid 8 (innerAD leaf6262Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint78PositiveFacts.valid leaf6262CoverageChecked

private noncomputable def leaf6262InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814769/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6262InputLogOnePlusV_eq :
    leaf6262InputLogOnePlusV = outerEnclosure 24
      (leaf6262Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6262RoundedFacts : LeafRoundedFacts 8
    leaf6262Certificate.logOnePlusV leaf6262InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6262InputLogOnePlusV_eq }

private noncomputable def leaf6262Inputs : Inputs :=
  inputsOfCaches globalInput sk101RoundedInputs
    chi83InputQChi innerPair273Input
    leaf6262InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6262LowerChecked :
    lowerCheck 24 leaf6262Box leaf6262Inputs = true := by
  rfl'

private theorem leaf6262CoversExact : CoversExact 8
    leaf6262Box leaf6262Certificate leaf6262InnerLog leaf6262Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk101RoundedFacts chi83RoundedFacts
    innerPair273RoundedFacts leaf6262RoundedFacts (by rfl)

private theorem leaf6262FlatSound : Sound leaf6262Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6262CertificateValid
    leaf6262InnerLogValid leaf6262CoversExact leaf6262LowerChecked

private noncomputable def leaf6263Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (83/32), kHi := (21/8), chiLo := (33/64), chiHi := (17/32) }

private noncomputable def leaf6263Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217963/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34356813824) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (313676875/268435456) }, upper := { exponent := 1, mantissa := (613/512) } }, logOuter := sk102LogOuterCertificate, logK := sk102LogKCertificate, logChi := chi83LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715536383/68713627648) } }, logDArg := sk102LogDArgCertificate }

private noncomputable def leaf6263InnerLog : WideLogData :=
  innerPair273Data

set_option maxRecDepth 1000000 in
private theorem leaf6263LocalValidity :
    LeafFacts leaf6263Box leaf6263Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6263Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34356813824) }) = true
      norm_num [leaf6263Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6263CertificateValid :
    WideCertificateValid leaf6263Box leaf6263Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk102ValidityFacts chi83ValidityFacts
    leaf6263LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6263CoverageChecked :
    coverageCheck (innerAD leaf6263Box) leaf6263InnerLog = true := by
  rfl'

private theorem leaf6263InnerLogValid :
    leaf6263InnerLog.Valid 8 (innerAD leaf6263Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint78PositiveFacts.valid leaf6263CoverageChecked

private noncomputable def leaf6263InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629547/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6263InputLogOnePlusV_eq :
    leaf6263InputLogOnePlusV = outerEnclosure 24
      (leaf6263Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6263RoundedFacts : LeafRoundedFacts 8
    leaf6263Certificate.logOnePlusV leaf6263InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6263InputLogOnePlusV_eq }

private noncomputable def leaf6263Inputs : Inputs :=
  inputsOfCaches globalInput sk102RoundedInputs
    chi83InputQChi innerPair273Input
    leaf6263InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6263LowerChecked :
    lowerCheck 24 leaf6263Box leaf6263Inputs = true := by
  rfl'

private theorem leaf6263CoversExact : CoversExact 8
    leaf6263Box leaf6263Certificate leaf6263InnerLog leaf6263Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk102RoundedFacts chi83RoundedFacts
    innerPair273RoundedFacts leaf6263RoundedFacts (by rfl)

private theorem leaf6263FlatSound : Sound leaf6263Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6263CertificateValid
    leaf6263InnerLogValid leaf6263CoversExact leaf6263LowerChecked

private noncomputable def leaf6264Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (17/32), chiHi := (35/64) }

private noncomputable def leaf6264Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67109015/67108864) }, vSqrt := { lower := (32765/32768), upper := (5726459221/5726133248) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (156199467/134217728) }, upper := { exponent := 1, mantissa := (2459/2048) } }, logOuter := sk89LogOuterCertificate, logK := sk89LogKCertificate, logChi := chi84LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (11452592469/11452266496) } }, logDArg := sk89LogDArgCertificate }

private noncomputable def leaf6264InnerLog : WideLogData :=
  innerPair651Data

set_option maxRecDepth 1000000 in
private theorem leaf6264LocalValidity :
    LeafFacts leaf6264Box leaf6264Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6264Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (5726459221/5726133248) }) = true
      norm_num [leaf6264Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6264CertificateValid :
    WideCertificateValid leaf6264Box leaf6264Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk89ValidityFacts chi84ValidityFacts
    leaf6264LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6264CoverageChecked :
    coverageCheck (innerAD leaf6264Box) leaf6264InnerLog = true := by
  rfl'

private theorem leaf6264InnerLogValid :
    leaf6264InnerLog.Valid 8 (innerAD leaf6264Box) :=
  wideLogDataValid_of_cachedCheck endpoint394PositiveFacts
    endpoint409PositiveFacts.valid leaf6264CoverageChecked

private noncomputable def leaf6264InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814779/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6264InputLogOnePlusV_eq :
    leaf6264InputLogOnePlusV = outerEnclosure 24
      (leaf6264Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6264RoundedFacts : LeafRoundedFacts 8
    leaf6264Certificate.logOnePlusV leaf6264InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6264InputLogOnePlusV_eq }

private noncomputable def leaf6264Inputs : Inputs :=
  inputsOfCaches globalInput sk89RoundedInputs
    chi84InputQChi innerPair651Input
    leaf6264InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6264LowerChecked :
    lowerCheck 24 leaf6264Box leaf6264Inputs = true := by
  rfl'

private theorem leaf6264CoversExact : CoversExact 8
    leaf6264Box leaf6264Certificate leaf6264InnerLog leaf6264Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk89RoundedFacts chi84RoundedFacts
    innerPair651RoundedFacts leaf6264RoundedFacts (by rfl)

private theorem leaf6264FlatSound : Sound leaf6264Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6264CertificateValid
    leaf6264InnerLogValid leaf6264CoversExact leaf6264LowerChecked

private noncomputable def leaf6265Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (35/64), chiHi := (9/16) }

private noncomputable def leaf6265Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67109017/67108864) }, vSqrt := { lower := (32765/32768), upper := (17179377663/17178357760) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (158820745/134217728) }, upper := { exponent := 1, mantissa := (625/512) } }, logOuter := sk89LogOuterCertificate, logK := sk89LogKCertificate, logChi := chi85LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (34357735423/34356715520) } }, logDArg := sk89LogDArgCertificate }

private noncomputable def leaf6265InnerLog : WideLogData :=
  innerPair578Data

set_option maxRecDepth 1000000 in
private theorem leaf6265LocalValidity :
    LeafFacts leaf6265Box leaf6265Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6265Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (17179377663/17178357760) }) = true
      norm_num [leaf6265Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6265CertificateValid :
    WideCertificateValid leaf6265Box leaf6265Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk89ValidityFacts chi85ValidityFacts
    leaf6265LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6265CoverageChecked :
    coverageCheck (innerAD leaf6265Box) leaf6265InnerLog = true := by
  rfl'

private theorem leaf6265InnerLogValid :
    leaf6265InnerLog.Valid 8 (innerAD leaf6265Box) :=
  wideLogDataValid_of_cachedCheck endpoint299PositiveFacts
    endpoint403PositiveFacts.valid leaf6265CoverageChecked

private noncomputable def leaf6265InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629579/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6265InputLogOnePlusV_eq :
    leaf6265InputLogOnePlusV = outerEnclosure 24
      (leaf6265Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6265RoundedFacts : LeafRoundedFacts 8
    leaf6265Certificate.logOnePlusV leaf6265InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6265InputLogOnePlusV_eq }

private noncomputable def leaf6265Inputs : Inputs :=
  inputsOfCaches globalInput sk89RoundedInputs
    chi85InputQChi innerPair578Input
    leaf6265InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6265LowerChecked :
    lowerCheck 24 leaf6265Box leaf6265Inputs = true := by
  rfl'

private theorem leaf6265CoversExact : CoversExact 8
    leaf6265Box leaf6265Certificate leaf6265InnerLog leaf6265Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk89RoundedFacts chi85RoundedFacts
    innerPair578RoundedFacts leaf6265RoundedFacts (by rfl)

private theorem leaf6265FlatSound : Sound leaf6265Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6265CertificateValid
    leaf6265InnerLogValid leaf6265CoversExact leaf6265LowerChecked

private noncomputable def leaf6266Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (17/32), chiHi := (69/128) }

private noncomputable def leaf6266Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217949/134217728) }, vSqrt := { lower := (32765/32768), upper := (17179377663/17178385408) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (316887957/268435456) }, upper := { exponent := 1, mantissa := (2473/2048) } }, logOuter := sk90LogOuterCertificate, logK := sk90LogKCertificate, logChi := chi327LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (34357763071/34356770816) } }, logDArg := sk90LogDArgCertificate }

private noncomputable def leaf6266InnerLog : WideLogData :=
  innerPair273Data

set_option maxRecDepth 1000000 in
private theorem leaf6266LocalValidity :
    LeafFacts leaf6266Box leaf6266Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6266Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (17179377663/17178385408) }) = true
      norm_num [leaf6266Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6266CertificateValid :
    WideCertificateValid leaf6266Box leaf6266Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk90ValidityFacts chi327ValidityFacts
    leaf6266LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6266CoverageChecked :
    coverageCheck (innerAD leaf6266Box) leaf6266InnerLog = true := by
  rfl'

private theorem leaf6266InnerLogValid :
    leaf6266InnerLog.Valid 8 (innerAD leaf6266Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint78PositiveFacts.valid leaf6266CoverageChecked

private noncomputable def leaf6266InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629565/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6266InputLogOnePlusV_eq :
    leaf6266InputLogOnePlusV = outerEnclosure 24
      (leaf6266Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6266RoundedFacts : LeafRoundedFacts 8
    leaf6266Certificate.logOnePlusV leaf6266InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6266InputLogOnePlusV_eq }

private noncomputable def leaf6266Inputs : Inputs :=
  inputsOfCaches globalInput sk90RoundedInputs
    chi327InputQChi innerPair273Input
    leaf6266InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6266LowerChecked :
    lowerCheck 24 leaf6266Box leaf6266Inputs = true := by
  rfl'

private theorem leaf6266CoversExact : CoversExact 8
    leaf6266Box leaf6266Certificate leaf6266InnerLog leaf6266Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk90RoundedFacts chi327RoundedFacts
    innerPair273RoundedFacts leaf6266RoundedFacts (by rfl)

private theorem leaf6266FlatSound : Sound leaf6266Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6266CertificateValid
    leaf6266InnerLogValid leaf6266CoversExact leaf6266LowerChecked

private noncomputable def leaf6267Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (69/128), chiHi := (35/64) }

private noncomputable def leaf6267Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217951/134217728) }, vSqrt := { lower := (32765/32768), upper := (17179377663/17178363904) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (319574767/268435456) }, upper := { exponent := 1, mantissa := (1247/1024) } }, logOuter := sk90LogOuterCertificate, logK := sk90LogKCertificate, logChi := chi328LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (34357741567/34356727808) } }, logDArg := sk90LogDArgCertificate }

private noncomputable def leaf6267InnerLog : WideLogData :=
  innerPair278Data

set_option maxRecDepth 1000000 in
private theorem leaf6267LocalValidity :
    LeafFacts leaf6267Box leaf6267Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6267Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (17179377663/17178363904) }) = true
      norm_num [leaf6267Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6267CertificateValid :
    WideCertificateValid leaf6267Box leaf6267Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk90ValidityFacts chi328ValidityFacts
    leaf6267LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6267CoverageChecked :
    coverageCheck (innerAD leaf6267Box) leaf6267InnerLog = true := by
  rfl'

private theorem leaf6267InnerLogValid :
    leaf6267InnerLog.Valid 8 (innerAD leaf6267Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint78PositiveFacts.valid leaf6267CoverageChecked

private noncomputable def leaf6267InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (1453697/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf6267InputLogOnePlusV_eq :
    leaf6267InputLogOnePlusV = outerEnclosure 24
      (leaf6267Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6267RoundedFacts : LeafRoundedFacts 8
    leaf6267Certificate.logOnePlusV leaf6267InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6267InputLogOnePlusV_eq }

private noncomputable def leaf6267Inputs : Inputs :=
  inputsOfCaches globalInput sk90RoundedInputs
    chi328InputQChi innerPair278Input
    leaf6267InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6267LowerChecked :
    lowerCheck 24 leaf6267Box leaf6267Inputs = true := by
  rfl'

private theorem leaf6267CoversExact : CoversExact 8
    leaf6267Box leaf6267Certificate leaf6267InnerLog leaf6267Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk90RoundedFacts chi328RoundedFacts
    innerPair278RoundedFacts leaf6267RoundedFacts (by rfl)

private theorem leaf6267FlatSound : Sound leaf6267Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6267CertificateValid
    leaf6267InnerLogValid leaf6267CoversExact leaf6267LowerChecked

private noncomputable def leaf6268Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (35/64), chiHi := (9/16) }

private noncomputable def leaf6268Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67109019/67108864) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34356641792) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (161114363/134217728) }, upper := { exponent := 1, mantissa := (317/256) } }, logOuter := sk90LogOuterCertificate, logK := sk90LogKCertificate, logChi := chi85LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714872829/68713283584) } }, logDArg := sk90LogDArgCertificate }

private noncomputable def leaf6268InnerLog : WideLogData :=
  innerPair664Data

set_option maxRecDepth 1000000 in
private theorem leaf6268LocalValidity :
    LeafFacts leaf6268Box leaf6268Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6268Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34356641792) }) = true
      norm_num [leaf6268Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6268CertificateValid :
    WideCertificateValid leaf6268Box leaf6268Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk90ValidityFacts chi85ValidityFacts
    leaf6268LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6268CoverageChecked :
    coverageCheck (innerAD leaf6268Box) leaf6268InnerLog = true := by
  rfl'

private theorem leaf6268InnerLogValid :
    leaf6268InnerLog.Valid 8 (innerAD leaf6268Box) :=
  wideLogDataValid_of_cachedCheck endpoint412PositiveFacts
    endpoint474PositiveFacts.valid leaf6268CoverageChecked

private noncomputable def leaf6268InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629469/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6268InputLogOnePlusV_eq :
    leaf6268InputLogOnePlusV = outerEnclosure 24
      (leaf6268Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6268RoundedFacts : LeafRoundedFacts 8
    leaf6268Certificate.logOnePlusV leaf6268InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6268InputLogOnePlusV_eq }

private noncomputable def leaf6268Inputs : Inputs :=
  inputsOfCaches globalInput sk90RoundedInputs
    chi85InputQChi innerPair664Input
    leaf6268InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6268LowerChecked :
    lowerCheck 24 leaf6268Box leaf6268Inputs = true := by
  rfl'

private theorem leaf6268CoversExact : CoversExact 8
    leaf6268Box leaf6268Certificate leaf6268InnerLog leaf6268Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk90RoundedFacts chi85RoundedFacts
    innerPair664RoundedFacts leaf6268RoundedFacts (by rfl)

private theorem leaf6268FlatSound : Sound leaf6268Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6268CertificateValid
    leaf6268InnerLogValid leaf6268CoversExact leaf6268LowerChecked

private noncomputable def leaf6269Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (1/2), chiHi := (65/128) }

private noncomputable def leaf6269Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217943/134217728) }, vSqrt := { lower := (32765/32768), upper := (818065603/818020864) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (310334763/268435456) }, upper := { exponent := 1, mantissa := (4843/4096) } }, logOuter := sk91LogOuterCertificate, logK := sk91LogKCertificate, logChi := chi329LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (1636086467/1636041728) } }, logDArg := sk91LogDArgCertificate }

private noncomputable def leaf6269InnerLog : WideLogData :=
  innerPair265Data

set_option maxRecDepth 1000000 in
private theorem leaf6269LocalValidity :
    LeafFacts leaf6269Box leaf6269Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6269Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (818065603/818020864) }) = true
      norm_num [leaf6269Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6269CertificateValid :
    WideCertificateValid leaf6269Box leaf6269Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk91ValidityFacts chi329ValidityFacts
    leaf6269LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6269CoverageChecked :
    coverageCheck (innerAD leaf6269Box) leaf6269InnerLog = true := by
  rfl'

private theorem leaf6269InnerLogValid :
    leaf6269InnerLog.Valid 8 (innerAD leaf6269Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint77PositiveFacts.valid leaf6269CoverageChecked

private noncomputable def leaf6269InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907385/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6269InputLogOnePlusV_eq :
    leaf6269InputLogOnePlusV = outerEnclosure 24
      (leaf6269Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6269RoundedFacts : LeafRoundedFacts 8
    leaf6269Certificate.logOnePlusV leaf6269InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6269InputLogOnePlusV_eq }

private noncomputable def leaf6269Inputs : Inputs :=
  inputsOfCaches globalInput sk91RoundedInputs
    chi329InputQChi innerPair265Input
    leaf6269InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6269LowerChecked :
    lowerCheck 24 leaf6269Box leaf6269Inputs = true := by
  rfl'

private theorem leaf6269CoversExact : CoversExact 8
    leaf6269Box leaf6269Certificate leaf6269InnerLog leaf6269Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk91RoundedFacts chi329RoundedFacts
    innerPair265RoundedFacts leaf6269RoundedFacts (by rfl)

private theorem leaf6269FlatSound : Sound leaf6269Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6269CertificateValid
    leaf6269InnerLogValid leaf6269CoversExact leaf6269LowerChecked

private noncomputable def leaf6270Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (65/128), chiHi := (33/64) }

private noncomputable def leaf6270Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217945/134217728) }, vSqrt := { lower := (32765/32768), upper := (17179377663/17178416128) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (313087105/268435456) }, upper := { exponent := 1, mantissa := (2443/2048) } }, logOuter := sk91LogOuterCertificate, logK := sk91LogKCertificate, logChi := chi330LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (34357793791/34356832256) } }, logDArg := sk91LogDArgCertificate }

private noncomputable def leaf6270InnerLog : WideLogData :=
  innerPair567Data

set_option maxRecDepth 1000000 in
private theorem leaf6270LocalValidity :
    LeafFacts leaf6270Box leaf6270Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6270Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (17179377663/17178416128) }) = true
      norm_num [leaf6270Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6270CertificateValid :
    WideCertificateValid leaf6270Box leaf6270Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk91ValidityFacts chi330ValidityFacts
    leaf6270LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6270CoverageChecked :
    coverageCheck (innerAD leaf6270Box) leaf6270InnerLog = true := by
  rfl'

private theorem leaf6270InnerLogValid :
    leaf6270InnerLog.Valid 8 (innerAD leaf6270Box) :=
  wideLogDataValid_of_cachedCheck endpoint296PositiveFacts
    endpoint304PositiveFacts.valid leaf6270CoverageChecked

private noncomputable def leaf6270InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814775/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6270InputLogOnePlusV_eq :
    leaf6270InputLogOnePlusV = outerEnclosure 24
      (leaf6270Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6270RoundedFacts : LeafRoundedFacts 8
    leaf6270Certificate.logOnePlusV leaf6270InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6270InputLogOnePlusV_eq }

private noncomputable def leaf6270Inputs : Inputs :=
  inputsOfCaches globalInput sk91RoundedInputs
    chi330InputQChi innerPair567Input
    leaf6270InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6270LowerChecked :
    lowerCheck 24 leaf6270Box leaf6270Inputs = true := by
  rfl'

private theorem leaf6270CoversExact : CoversExact 8
    leaf6270Box leaf6270Certificate leaf6270InnerLog leaf6270Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk91RoundedFacts chi330RoundedFacts
    innerPair567RoundedFacts leaf6270RoundedFacts (by rfl)

private theorem leaf6270FlatSound : Sound leaf6270Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6270CertificateValid
    leaf6270InnerLogValid leaf6270CoversExact leaf6270LowerChecked

private noncomputable def leaf6271Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (33/64), chiHi := (67/128) }

private noncomputable def leaf6271Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217947/134217728) }, vSqrt := { lower := (32765/32768), upper := (17179377663/17178394112) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (315839447/268435456) }, upper := { exponent := 1, mantissa := (4929/4096) } }, logOuter := sk91LogOuterCertificate, logK := sk91LogKCertificate, logChi := chi331LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (34357771775/34356788224) } }, logDArg := sk91LogDArgCertificate }

private noncomputable def leaf6271InnerLog : WideLogData :=
  innerPair273Data

set_option maxRecDepth 1000000 in
private theorem leaf6271LocalValidity :
    LeafFacts leaf6271Box leaf6271Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6271Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (17179377663/17178394112) }) = true
      norm_num [leaf6271Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6271CertificateValid :
    WideCertificateValid leaf6271Box leaf6271Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk91ValidityFacts chi331ValidityFacts
    leaf6271LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6271CoverageChecked :
    coverageCheck (innerAD leaf6271Box) leaf6271InnerLog = true := by
  rfl'

private theorem leaf6271InnerLogValid :
    leaf6271InnerLog.Valid 8 (innerAD leaf6271Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint78PositiveFacts.valid leaf6271CoverageChecked

private noncomputable def leaf6271InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629561/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6271InputLogOnePlusV_eq :
    leaf6271InputLogOnePlusV = outerEnclosure 24
      (leaf6271Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6271RoundedFacts : LeafRoundedFacts 8
    leaf6271Certificate.logOnePlusV leaf6271InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6271InputLogOnePlusV_eq }

private noncomputable def leaf6271Inputs : Inputs :=
  inputsOfCaches globalInput sk91RoundedInputs
    chi331InputQChi innerPair273Input
    leaf6271InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6271LowerChecked :
    lowerCheck 24 leaf6271Box leaf6271Inputs = true := by
  rfl'

private theorem leaf6271CoversExact : CoversExact 8
    leaf6271Box leaf6271Certificate leaf6271InnerLog leaf6271Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk91RoundedFacts chi331RoundedFacts
    innerPair273RoundedFacts leaf6271RoundedFacts (by rfl)

private theorem leaf6271FlatSound : Sound leaf6271Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6271CertificateValid
    leaf6271InnerLogValid leaf6271CoversExact leaf6271LowerChecked

private noncomputable def leaf6272Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (67/128), chiHi := (17/32) }

private noncomputable def leaf6272Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217949/134217728) }, vSqrt := { lower := (32765/32768), upper := (5726459221/5726124032) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (318591789/268435456) }, upper := { exponent := 1, mantissa := (1243/1024) } }, logOuter := sk91LogOuterCertificate, logK := sk91LogKCertificate, logChi := chi332LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (11452583253/11452248064) } }, logDArg := sk91LogDArgCertificate }

private noncomputable def leaf6272InnerLog : WideLogData :=
  innerPair273Data

set_option maxRecDepth 1000000 in
private theorem leaf6272LocalValidity :
    LeafFacts leaf6272Box leaf6272Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6272Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (5726459221/5726124032) }) = true
      norm_num [leaf6272Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6272CertificateValid :
    WideCertificateValid leaf6272Box leaf6272Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk91ValidityFacts chi332ValidityFacts
    leaf6272LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6272CoverageChecked :
    coverageCheck (innerAD leaf6272Box) leaf6272InnerLog = true := by
  rfl'

private theorem leaf6272InnerLogValid :
    leaf6272InnerLog.Valid 8 (innerAD leaf6272Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint78PositiveFacts.valid leaf6272CoverageChecked

private noncomputable def leaf6272InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907393/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6272InputLogOnePlusV_eq :
    leaf6272InputLogOnePlusV = outerEnclosure 24
      (leaf6272Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6272RoundedFacts : LeafRoundedFacts 8
    leaf6272Certificate.logOnePlusV leaf6272InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6272InputLogOnePlusV_eq }

private noncomputable def leaf6272Inputs : Inputs :=
  inputsOfCaches globalInput sk91RoundedInputs
    chi332InputQChi innerPair273Input
    leaf6272InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6272LowerChecked :
    lowerCheck 24 leaf6272Box leaf6272Inputs = true := by
  rfl'

private theorem leaf6272CoversExact : CoversExact 8
    leaf6272Box leaf6272Certificate leaf6272InnerLog leaf6272Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk91RoundedFacts chi332RoundedFacts
    innerPair273RoundedFacts leaf6272RoundedFacts (by rfl)

private theorem leaf6272FlatSound : Sound leaf6272Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6272CertificateValid
    leaf6272InnerLogValid leaf6272CoversExact leaf6272LowerChecked

private noncomputable def leaf6273Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (1/2), chiHi := (65/128) }

private noncomputable def leaf6273Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217945/134217728) }, vSqrt := { lower := (32765/32768), upper := (17179377663/17178404864) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (314528809/268435456) }, upper := { exponent := 1, mantissa := (1227/1024) } }, logOuter := sk92LogOuterCertificate, logK := sk92LogKCertificate, logChi := chi329LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (34357782527/34356809728) } }, logDArg := sk92LogDArgCertificate }

private noncomputable def leaf6273InnerLog : WideLogData :=
  innerPair568Data

set_option maxRecDepth 1000000 in
private theorem leaf6273LocalValidity :
    LeafFacts leaf6273Box leaf6273Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6273Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (17179377663/17178404864) }) = true
      norm_num [leaf6273Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6273CertificateValid :
    WideCertificateValid leaf6273Box leaf6273Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk92ValidityFacts chi329ValidityFacts
    leaf6273LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6273CoverageChecked :
    coverageCheck (innerAD leaf6273Box) leaf6273InnerLog = true := by
  rfl'

private theorem leaf6273InnerLogValid :
    leaf6273InnerLog.Valid 8 (innerAD leaf6273Box) :=
  wideLogDataValid_of_cachedCheck endpoint296PositiveFacts
    endpoint305PositiveFacts.valid leaf6273CoverageChecked

private noncomputable def leaf6273InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907389/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6273InputLogOnePlusV_eq :
    leaf6273InputLogOnePlusV = outerEnclosure 24
      (leaf6273Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6273RoundedFacts : LeafRoundedFacts 8
    leaf6273Certificate.logOnePlusV leaf6273InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6273InputLogOnePlusV_eq }

private noncomputable def leaf6273Inputs : Inputs :=
  inputsOfCaches globalInput sk92RoundedInputs
    chi329InputQChi innerPair568Input
    leaf6273InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6273LowerChecked :
    lowerCheck 24 leaf6273Box leaf6273Inputs = true := by
  rfl'

private theorem leaf6273CoversExact : CoversExact 8
    leaf6273Box leaf6273Certificate leaf6273InnerLog leaf6273Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk92RoundedFacts chi329RoundedFacts
    innerPair568RoundedFacts leaf6273RoundedFacts (by rfl)

private theorem leaf6273FlatSound : Sound leaf6273Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6273CertificateValid
    leaf6273InnerLogValid leaf6273CoversExact leaf6273LowerChecked

private noncomputable def leaf6274Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (65/128), chiHi := (33/64) }

private noncomputable def leaf6274Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217947/134217728) }, vSqrt := { lower := (32765/32768), upper := (17179377663/17178382336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (317346683/268435456) }, upper := { exponent := 1, mantissa := (619/512) } }, logOuter := sk92LogOuterCertificate, logK := sk92LogKCertificate, logChi := chi330LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (34357759999/34356764672) } }, logDArg := sk92LogDArgCertificate }

private noncomputable def leaf6274InnerLog : WideLogData :=
  innerPair273Data

set_option maxRecDepth 1000000 in
private theorem leaf6274LocalValidity :
    LeafFacts leaf6274Box leaf6274Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6274Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (17179377663/17178382336) }) = true
      norm_num [leaf6274Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6274CertificateValid :
    WideCertificateValid leaf6274Box leaf6274Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk92ValidityFacts chi330ValidityFacts
    leaf6274LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6274CoverageChecked :
    coverageCheck (innerAD leaf6274Box) leaf6274InnerLog = true := by
  rfl'

private theorem leaf6274InnerLogValid :
    leaf6274InnerLog.Valid 8 (innerAD leaf6274Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint78PositiveFacts.valid leaf6274CoverageChecked

private noncomputable def leaf6274InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629567/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6274InputLogOnePlusV_eq :
    leaf6274InputLogOnePlusV = outerEnclosure 24
      (leaf6274Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6274RoundedFacts : LeafRoundedFacts 8
    leaf6274Certificate.logOnePlusV leaf6274InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6274InputLogOnePlusV_eq }

private noncomputable def leaf6274Inputs : Inputs :=
  inputsOfCaches globalInput sk92RoundedInputs
    chi330InputQChi innerPair273Input
    leaf6274InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6274LowerChecked :
    lowerCheck 24 leaf6274Box leaf6274Inputs = true := by
  rfl'

private theorem leaf6274CoversExact : CoversExact 8
    leaf6274Box leaf6274Certificate leaf6274InnerLog leaf6274Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk92RoundedFacts chi330RoundedFacts
    innerPair273RoundedFacts leaf6274RoundedFacts (by rfl)

private theorem leaf6274FlatSound : Sound leaf6274Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6274CertificateValid
    leaf6274InnerLogValid leaf6274CoversExact leaf6274LowerChecked

private noncomputable def leaf6275Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (33/64), chiHi := (67/128) }

private noncomputable def leaf6275Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217949/134217728) }, vSqrt := { lower := (32765/32768), upper := (5726459221/5726119936) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (320164557/268435456) }, upper := { exponent := 1, mantissa := (1249/1024) } }, logOuter := sk92LogOuterCertificate, logK := sk92LogKCertificate, logChi := chi331LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (11452579157/11452239872) } }, logDArg := sk92LogDArgCertificate }

private noncomputable def leaf6275InnerLog : WideLogData :=
  innerPair284Data

set_option maxRecDepth 1000000 in
private theorem leaf6275LocalValidity :
    LeafFacts leaf6275Box leaf6275Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6275Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (5726459221/5726119936) }) = true
      norm_num [leaf6275Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6275CertificateValid :
    WideCertificateValid leaf6275Box leaf6275Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk92ValidityFacts chi331ValidityFacts
    leaf6275LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6275CoverageChecked :
    coverageCheck (innerAD leaf6275Box) leaf6275InnerLog = true := by
  rfl'

private theorem leaf6275InnerLogValid :
    leaf6275InnerLog.Valid 8 (innerAD leaf6275Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint403PositiveFacts.valid leaf6275CoverageChecked

private noncomputable def leaf6275InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814789/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6275InputLogOnePlusV_eq :
    leaf6275InputLogOnePlusV = outerEnclosure 24
      (leaf6275Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6275RoundedFacts : LeafRoundedFacts 8
    leaf6275Certificate.logOnePlusV leaf6275InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6275InputLogOnePlusV_eq }

private noncomputable def leaf6275Inputs : Inputs :=
  inputsOfCaches globalInput sk92RoundedInputs
    chi331InputQChi innerPair284Input
    leaf6275InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6275LowerChecked :
    lowerCheck 24 leaf6275Box leaf6275Inputs = true := by
  rfl'

private theorem leaf6275CoversExact : CoversExact 8
    leaf6275Box leaf6275Certificate leaf6275InnerLog leaf6275Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk92RoundedFacts chi331RoundedFacts
    innerPair284RoundedFacts leaf6275RoundedFacts (by rfl)

private theorem leaf6275FlatSound : Sound leaf6275Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6275CertificateValid
    leaf6275InnerLogValid leaf6275CoversExact leaf6275LowerChecked

private noncomputable def leaf6276Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (67/128), chiHi := (17/32) }

private noncomputable def leaf6276Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217951/134217728) }, vSqrt := { lower := (32765/32768), upper := (17179377663/17178337280) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (322982431/268435456) }, upper := { exponent := 1, mantissa := (315/256) } }, logOuter := sk92LogOuterCertificate, logK := sk92LogKCertificate, logChi := chi332LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (34357714943/34356674560) } }, logDArg := sk92LogDArgCertificate }

private noncomputable def leaf6276InnerLog : WideLogData :=
  innerPair279Data

set_option maxRecDepth 1000000 in
private theorem leaf6276LocalValidity :
    LeafFacts leaf6276Box leaf6276Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6276Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (17179377663/17178337280) }) = true
      norm_num [leaf6276Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6276CertificateValid :
    WideCertificateValid leaf6276Box leaf6276Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk92ValidityFacts chi332ValidityFacts
    leaf6276LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6276CoverageChecked :
    coverageCheck (innerAD leaf6276Box) leaf6276InnerLog = true := by
  rfl'

private theorem leaf6276InnerLogValid :
    leaf6276InnerLog.Valid 8 (innerAD leaf6276Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint79PositiveFacts.valid leaf6276CoverageChecked

private noncomputable def leaf6276InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629589/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6276InputLogOnePlusV_eq :
    leaf6276InputLogOnePlusV = outerEnclosure 24
      (leaf6276Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6276RoundedFacts : LeafRoundedFacts 8
    leaf6276Certificate.logOnePlusV leaf6276InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6276InputLogOnePlusV_eq }

private noncomputable def leaf6276Inputs : Inputs :=
  inputsOfCaches globalInput sk92RoundedInputs
    chi332InputQChi innerPair279Input
    leaf6276InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6276LowerChecked :
    lowerCheck 24 leaf6276Box leaf6276Inputs = true := by
  rfl'

private theorem leaf6276CoversExact : CoversExact 8
    leaf6276Box leaf6276Certificate leaf6276InnerLog leaf6276Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk92RoundedFacts chi332RoundedFacts
    innerPair279RoundedFacts leaf6276RoundedFacts (by rfl)

private theorem leaf6276FlatSound : Sound leaf6276Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6276CertificateValid
    leaf6276InnerLogValid leaf6276CoversExact leaf6276LowerChecked

private noncomputable def leaf6277Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (17/32), chiHi := (69/128) }

private noncomputable def leaf6277Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217951/134217728) }, vSqrt := { lower := (32765/32768), upper := (17179377663/17178350080) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (321344131/268435456) }, upper := { exponent := 1, mantissa := (5015/4096) } }, logOuter := sk91LogOuterCertificate, logK := sk91LogKCertificate, logChi := chi327LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (34357727743/34356700160) } }, logDArg := sk91LogDArgCertificate }

private noncomputable def leaf6277InnerLog : WideLogData :=
  innerPair279Data

set_option maxRecDepth 1000000 in
private theorem leaf6277LocalValidity :
    LeafFacts leaf6277Box leaf6277Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6277Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (17179377663/17178350080) }) = true
      norm_num [leaf6277Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6277CertificateValid :
    WideCertificateValid leaf6277Box leaf6277Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk91ValidityFacts chi327ValidityFacts
    leaf6277LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6277CoverageChecked :
    coverageCheck (innerAD leaf6277Box) leaf6277InnerLog = true := by
  rfl'

private theorem leaf6277InnerLogValid :
    leaf6277InnerLog.Valid 8 (innerAD leaf6277Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint79PositiveFacts.valid leaf6277CoverageChecked

private noncomputable def leaf6277InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629583/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6277InputLogOnePlusV_eq :
    leaf6277InputLogOnePlusV = outerEnclosure 24
      (leaf6277Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6277RoundedFacts : LeafRoundedFacts 8
    leaf6277Certificate.logOnePlusV leaf6277InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6277InputLogOnePlusV_eq }

private noncomputable def leaf6277Inputs : Inputs :=
  inputsOfCaches globalInput sk91RoundedInputs
    chi327InputQChi innerPair279Input
    leaf6277InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6277LowerChecked :
    lowerCheck 24 leaf6277Box leaf6277Inputs = true := by
  rfl'

private theorem leaf6277CoversExact : CoversExact 8
    leaf6277Box leaf6277Certificate leaf6277InnerLog leaf6277Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk91RoundedFacts chi327RoundedFacts
    innerPair279RoundedFacts leaf6277RoundedFacts (by rfl)

private theorem leaf6277FlatSound : Sound leaf6277Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6277CertificateValid
    leaf6277InnerLogValid leaf6277CoversExact leaf6277LowerChecked

private noncomputable def leaf6278Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (69/128), chiHi := (35/64) }

private noncomputable def leaf6278Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217953/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34356656128) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (324096473/268435456) }, upper := { exponent := 1, mantissa := (2529/2048) } }, logOuter := sk91LogOuterCertificate, logK := sk91LogKCertificate, logChi := chi328LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714887165/68713312256) } }, logDArg := sk91LogDArgCertificate }

private noncomputable def leaf6278InnerLog : WideLogData :=
  innerPair279Data

set_option maxRecDepth 1000000 in
private theorem leaf6278LocalValidity :
    LeafFacts leaf6278Box leaf6278Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6278Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34356656128) }) = true
      norm_num [leaf6278Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6278CertificateValid :
    WideCertificateValid leaf6278Box leaf6278Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk91ValidityFacts chi328ValidityFacts
    leaf6278LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6278CoverageChecked :
    coverageCheck (innerAD leaf6278Box) leaf6278InnerLog = true := by
  rfl'

private theorem leaf6278InnerLogValid :
    leaf6278InnerLog.Valid 8 (innerAD leaf6278Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint79PositiveFacts.valid leaf6278CoverageChecked

private noncomputable def leaf6278InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629465/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6278InputLogOnePlusV_eq :
    leaf6278InputLogOnePlusV = outerEnclosure 24
      (leaf6278Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6278RoundedFacts : LeafRoundedFacts 8
    leaf6278Certificate.logOnePlusV leaf6278InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6278InputLogOnePlusV_eq }

private noncomputable def leaf6278Inputs : Inputs :=
  inputsOfCaches globalInput sk91RoundedInputs
    chi328InputQChi innerPair279Input
    leaf6278InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6278LowerChecked :
    lowerCheck 24 leaf6278Box leaf6278Inputs = true := by
  rfl'

private theorem leaf6278CoversExact : CoversExact 8
    leaf6278Box leaf6278Certificate leaf6278InnerLog leaf6278Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk91RoundedFacts chi328RoundedFacts
    innerPair279RoundedFacts leaf6278RoundedFacts (by rfl)

private theorem leaf6278FlatSound : Sound leaf6278Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6278CertificateValid
    leaf6278InnerLogValid leaf6278CoversExact leaf6278LowerChecked

private noncomputable def leaf6279Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (35/64), chiHi := (71/128) }

private noncomputable def leaf6279Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217955/134217728) }, vSqrt := { lower := (32765/32768), upper := (11452743679/11452204032) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (326848815/268435456) }, upper := { exponent := 1, mantissa := (5101/4096) } }, logOuter := sk91LogOuterCertificate, logK := sk91LogKCertificate, logChi := chi333LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (22904947711/22904408064) } }, logDArg := sk91LogDArgCertificate }

private noncomputable def leaf6279InnerLog : WideLogData :=
  innerPair279Data

set_option maxRecDepth 1000000 in
private theorem leaf6279LocalValidity :
    LeafFacts leaf6279Box leaf6279Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6279Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (11452743679/11452204032) }) = true
      norm_num [leaf6279Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6279CertificateValid :
    WideCertificateValid leaf6279Box leaf6279Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk91ValidityFacts chi333ValidityFacts
    leaf6279LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6279CoverageChecked :
    coverageCheck (innerAD leaf6279Box) leaf6279InnerLog = true := by
  rfl'

private theorem leaf6279InnerLogValid :
    leaf6279InnerLog.Valid 8 (innerAD leaf6279Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint79PositiveFacts.valid leaf6279CoverageChecked

private noncomputable def leaf6279InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907369/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6279InputLogOnePlusV_eq :
    leaf6279InputLogOnePlusV = outerEnclosure 24
      (leaf6279Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6279RoundedFacts : LeafRoundedFacts 8
    leaf6279Certificate.logOnePlusV leaf6279InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6279InputLogOnePlusV_eq }

private noncomputable def leaf6279Inputs : Inputs :=
  inputsOfCaches globalInput sk91RoundedInputs
    chi333InputQChi innerPair279Input
    leaf6279InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6279LowerChecked :
    lowerCheck 24 leaf6279Box leaf6279Inputs = true := by
  rfl'

private theorem leaf6279CoversExact : CoversExact 8
    leaf6279Box leaf6279Certificate leaf6279InnerLog leaf6279Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk91RoundedFacts chi333RoundedFacts
    innerPair279RoundedFacts leaf6279RoundedFacts (by rfl)

private theorem leaf6279FlatSound : Sound leaf6279Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6279CertificateValid
    leaf6279InnerLogValid leaf6279CoversExact leaf6279LowerChecked

private noncomputable def leaf6280Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (71/128), chiHi := (9/16) }

private noncomputable def leaf6280Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217957/134217728) }, vSqrt := { lower := (32765/32768), upper := (2642940849/2642812928) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (329601157/268435456) }, upper := { exponent := 1, mantissa := (643/512) } }, logOuter := sk91LogOuterCertificate, logK := sk91LogKCertificate, logChi := chi334LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (5285753777/5285625856) } }, logDArg := sk91LogDArgCertificate }

private noncomputable def leaf6280InnerLog : WideLogData :=
  innerPair286Data

set_option maxRecDepth 1000000 in
private theorem leaf6280LocalValidity :
    LeafFacts leaf6280Box leaf6280Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6280Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (2642940849/2642812928) }) = true
      norm_num [leaf6280Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6280CertificateValid :
    WideCertificateValid leaf6280Box leaf6280Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk91ValidityFacts chi334ValidityFacts
    leaf6280LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6280CoverageChecked :
    coverageCheck (innerAD leaf6280Box) leaf6280InnerLog = true := by
  rfl'

private theorem leaf6280InnerLogValid :
    leaf6280InnerLog.Valid 8 (innerAD leaf6280Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint90PositiveFacts.valid leaf6280CoverageChecked

private noncomputable def leaf6280InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629487/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6280InputLogOnePlusV_eq :
    leaf6280InputLogOnePlusV = outerEnclosure 24
      (leaf6280Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6280RoundedFacts : LeafRoundedFacts 8
    leaf6280Certificate.logOnePlusV leaf6280InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6280InputLogOnePlusV_eq }

private noncomputable def leaf6280Inputs : Inputs :=
  inputsOfCaches globalInput sk91RoundedInputs
    chi334InputQChi innerPair286Input
    leaf6280InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6280LowerChecked :
    lowerCheck 24 leaf6280Box leaf6280Inputs = true := by
  rfl'

private theorem leaf6280CoversExact : CoversExact 8
    leaf6280Box leaf6280Certificate leaf6280InnerLog leaf6280Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk91RoundedFacts chi334RoundedFacts
    innerPair286RoundedFacts leaf6280RoundedFacts (by rfl)

private theorem leaf6280FlatSound : Sound leaf6280Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6280CertificateValid
    leaf6280InnerLogValid leaf6280CoversExact leaf6280LowerChecked

private noncomputable def leaf6281Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (17/32), chiHi := (69/128) }

private noncomputable def leaf6281Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217953/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34356629504) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (325800305/268435456) }, upper := { exponent := 1, mantissa := (1271/1024) } }, logOuter := sk92LogOuterCertificate, logK := sk92LogKCertificate, logChi := chi327LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714860541/68713259008) } }, logDArg := sk92LogDArgCertificate }

private noncomputable def leaf6281InnerLog : WideLogData :=
  innerPair279Data

set_option maxRecDepth 1000000 in
private theorem leaf6281LocalValidity :
    LeafFacts leaf6281Box leaf6281Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6281Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34356629504) }) = true
      norm_num [leaf6281Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6281CertificateValid :
    WideCertificateValid leaf6281Box leaf6281Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk92ValidityFacts chi327ValidityFacts
    leaf6281LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6281CoverageChecked :
    coverageCheck (innerAD leaf6281Box) leaf6281InnerLog = true := by
  rfl'

private theorem leaf6281InnerLogValid :
    leaf6281InnerLog.Valid 8 (innerAD leaf6281Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint79PositiveFacts.valid leaf6281CoverageChecked

private noncomputable def leaf6281InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (363421/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf6281InputLogOnePlusV_eq :
    leaf6281InputLogOnePlusV = outerEnclosure 24
      (leaf6281Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6281RoundedFacts : LeafRoundedFacts 8
    leaf6281Certificate.logOnePlusV leaf6281InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6281InputLogOnePlusV_eq }

private noncomputable def leaf6281Inputs : Inputs :=
  inputsOfCaches globalInput sk92RoundedInputs
    chi327InputQChi innerPair279Input
    leaf6281InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6281LowerChecked :
    lowerCheck 24 leaf6281Box leaf6281Inputs = true := by
  rfl'

private theorem leaf6281CoversExact : CoversExact 8
    leaf6281Box leaf6281Certificate leaf6281InnerLog leaf6281Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk92RoundedFacts chi327RoundedFacts
    innerPair279RoundedFacts leaf6281RoundedFacts (by rfl)

private theorem leaf6281FlatSound : Sound leaf6281Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6281CertificateValid
    leaf6281InnerLogValid leaf6281CoversExact leaf6281LowerChecked

private noncomputable def leaf6282Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (69/128), chiHi := (35/64) }

private noncomputable def leaf6282Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217955/134217728) }, vSqrt := { lower := (32765/32768), upper := (11452743679/11452194816) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (328618179/268435456) }, upper := { exponent := 1, mantissa := (641/512) } }, logOuter := sk92LogOuterCertificate, logK := sk92LogKCertificate, logChi := chi328LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (22904938495/22904389632) } }, logDArg := sk92LogDArgCertificate }

private noncomputable def leaf6282InnerLog : WideLogData :=
  innerPair286Data

set_option maxRecDepth 1000000 in
private theorem leaf6282LocalValidity :
    LeafFacts leaf6282Box leaf6282Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6282Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (11452743679/11452194816) }) = true
      norm_num [leaf6282Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6282CertificateValid :
    WideCertificateValid leaf6282Box leaf6282Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk92ValidityFacts chi328ValidityFacts
    leaf6282LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6282CoverageChecked :
    coverageCheck (innerAD leaf6282Box) leaf6282InnerLog = true := by
  rfl'

private theorem leaf6282InnerLogValid :
    leaf6282InnerLog.Valid 8 (innerAD leaf6282Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint90PositiveFacts.valid leaf6282CoverageChecked

private noncomputable def leaf6282InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629483/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6282InputLogOnePlusV_eq :
    leaf6282InputLogOnePlusV = outerEnclosure 24
      (leaf6282Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6282RoundedFacts : LeafRoundedFacts 8
    leaf6282Certificate.logOnePlusV leaf6282InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6282InputLogOnePlusV_eq }

private noncomputable def leaf6282Inputs : Inputs :=
  inputsOfCaches globalInput sk92RoundedInputs
    chi328InputQChi innerPair286Input
    leaf6282InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6282LowerChecked :
    lowerCheck 24 leaf6282Box leaf6282Inputs = true := by
  rfl'

private theorem leaf6282CoversExact : CoversExact 8
    leaf6282Box leaf6282Certificate leaf6282InnerLog leaf6282Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk92RoundedFacts chi328RoundedFacts
    innerPair286RoundedFacts leaf6282RoundedFacts (by rfl)

private theorem leaf6282FlatSound : Sound leaf6282Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6282CertificateValid
    leaf6282InnerLogValid leaf6282CoversExact leaf6282LowerChecked

private noncomputable def leaf6283Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (35/64), chiHi := (71/128) }

private noncomputable def leaf6283Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217957/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34356539392) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (331436053/268435456) }, upper := { exponent := 1, mantissa := (1293/1024) } }, logOuter := sk92LogOuterCertificate, logK := sk92LogKCertificate, logChi := chi333LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714770429/68713078784) } }, logDArg := sk92LogDArgCertificate }

private noncomputable def leaf6283InnerLog : WideLogData :=
  innerPair286Data

set_option maxRecDepth 1000000 in
private theorem leaf6283LocalValidity :
    LeafFacts leaf6283Box leaf6283Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6283Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34356539392) }) = true
      norm_num [leaf6283Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6283CertificateValid :
    WideCertificateValid leaf6283Box leaf6283Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk92ValidityFacts chi333ValidityFacts
    leaf6283LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6283CoverageChecked :
    coverageCheck (innerAD leaf6283Box) leaf6283InnerLog = true := by
  rfl'

private theorem leaf6283InnerLogValid :
    leaf6283InnerLog.Valid 8 (innerAD leaf6283Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint90PositiveFacts.valid leaf6283CoverageChecked

private noncomputable def leaf6283InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814747/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6283InputLogOnePlusV_eq :
    leaf6283InputLogOnePlusV = outerEnclosure 24
      (leaf6283Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6283RoundedFacts : LeafRoundedFacts 8
    leaf6283Certificate.logOnePlusV leaf6283InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6283InputLogOnePlusV_eq }

private noncomputable def leaf6283Inputs : Inputs :=
  inputsOfCaches globalInput sk92RoundedInputs
    chi333InputQChi innerPair286Input
    leaf6283InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6283LowerChecked :
    lowerCheck 24 leaf6283Box leaf6283Inputs = true := by
  rfl'

private theorem leaf6283CoversExact : CoversExact 8
    leaf6283Box leaf6283Certificate leaf6283InnerLog leaf6283Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk92RoundedFacts chi333RoundedFacts
    innerPair286RoundedFacts leaf6283RoundedFacts (by rfl)

private theorem leaf6283FlatSound : Sound leaf6283Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6283CertificateValid
    leaf6283InnerLogValid leaf6283CoversExact leaf6283LowerChecked

private noncomputable def leaf6284Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (71/128), chiHi := (9/16) }

private noncomputable def leaf6284Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217959/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34356494336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (334253927/268435456) }, upper := { exponent := 1, mantissa := (163/128) } }, logOuter := sk92LogOuterCertificate, logK := sk92LogKCertificate, logChi := chi334LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714725373/68712988672) } }, logDArg := sk92LogDArgCertificate }

private noncomputable def leaf6284InnerLog : WideLogData :=
  innerPair286Data

set_option maxRecDepth 1000000 in
private theorem leaf6284LocalValidity :
    LeafFacts leaf6284Box leaf6284Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6284Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34356494336) }) = true
      norm_num [leaf6284Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6284CertificateValid :
    WideCertificateValid leaf6284Box leaf6284Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk92ValidityFacts chi334ValidityFacts
    leaf6284LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6284CoverageChecked :
    coverageCheck (innerAD leaf6284Box) leaf6284InnerLog = true := by
  rfl'

private theorem leaf6284InnerLogValid :
    leaf6284InnerLog.Valid 8 (innerAD leaf6284Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint90PositiveFacts.valid leaf6284CoverageChecked

private noncomputable def leaf6284InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629505/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6284InputLogOnePlusV_eq :
    leaf6284InputLogOnePlusV = outerEnclosure 24
      (leaf6284Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6284RoundedFacts : LeafRoundedFacts 8
    leaf6284Certificate.logOnePlusV leaf6284InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6284InputLogOnePlusV_eq }

private noncomputable def leaf6284Inputs : Inputs :=
  inputsOfCaches globalInput sk92RoundedInputs
    chi334InputQChi innerPair286Input
    leaf6284InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6284LowerChecked :
    lowerCheck 24 leaf6284Box leaf6284Inputs = true := by
  rfl'

private theorem leaf6284CoversExact : CoversExact 8
    leaf6284Box leaf6284Certificate leaf6284InnerLog leaf6284Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk92RoundedFacts chi334RoundedFacts
    innerPair286RoundedFacts leaf6284RoundedFacts (by rfl)

private theorem leaf6284FlatSound : Sound leaf6284Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6284CertificateValid
    leaf6284InnerLogValid leaf6284CoversExact leaf6284LowerChecked

private noncomputable def leaf6285Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (9/16), chiHi := (37/64) }

private noncomputable def leaf6285Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67109019/67108864) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34356631552) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (161442023/134217728) }, upper := { exponent := 1, mantissa := (2541/2048) } }, logOuter := sk89LogOuterCertificate, logK := sk89LogKCertificate, logChi := chi86LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714862589/68713263104) } }, logDArg := sk89LogDArgCertificate }

private noncomputable def leaf6285InnerLog : WideLogData :=
  innerPair279Data

set_option maxRecDepth 1000000 in
private theorem leaf6285LocalValidity :
    LeafFacts leaf6285Box leaf6285Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6285Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34356631552) }) = true
      norm_num [leaf6285Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6285CertificateValid :
    WideCertificateValid leaf6285Box leaf6285Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk89ValidityFacts chi86ValidityFacts
    leaf6285LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6285CoverageChecked :
    coverageCheck (innerAD leaf6285Box) leaf6285InnerLog = true := by
  rfl'

private theorem leaf6285InnerLogValid :
    leaf6285InnerLog.Valid 8 (innerAD leaf6285Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint79PositiveFacts.valid leaf6285CoverageChecked

private noncomputable def leaf6285InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629471/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6285InputLogOnePlusV_eq :
    leaf6285InputLogOnePlusV = outerEnclosure 24
      (leaf6285Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6285RoundedFacts : LeafRoundedFacts 8
    leaf6285Certificate.logOnePlusV leaf6285InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6285InputLogOnePlusV_eq }

private noncomputable def leaf6285Inputs : Inputs :=
  inputsOfCaches globalInput sk89RoundedInputs
    chi86InputQChi innerPair279Input
    leaf6285InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6285LowerChecked :
    lowerCheck 24 leaf6285Box leaf6285Inputs = true := by
  rfl'

private theorem leaf6285CoversExact : CoversExact 8
    leaf6285Box leaf6285Certificate leaf6285InnerLog leaf6285Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk89RoundedFacts chi86RoundedFacts
    innerPair279RoundedFacts leaf6285RoundedFacts (by rfl)

private theorem leaf6285FlatSound : Sound leaf6285Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6285CertificateValid
    leaf6285InnerLogValid leaf6285CoversExact leaf6285LowerChecked

private noncomputable def leaf6286Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (37/64), chiHi := (19/32) }

private noncomputable def leaf6286Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109021/67108864) }, vSqrt := { lower := (32765/32768), upper := (11452743679/11452182528) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (164063301/134217728) }, upper := { exponent := 1, mantissa := (1291/1024) } }, logOuter := sk89LogOuterCertificate, logK := sk89LogKCertificate, logChi := chi87LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (22904926207/22904365056) } }, logDArg := sk89LogDArgCertificate }

private noncomputable def leaf6286InnerLog : WideLogData :=
  innerPair292Data

set_option maxRecDepth 1000000 in
private theorem leaf6286LocalValidity :
    LeafFacts leaf6286Box leaf6286Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6286Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (11452743679/11452182528) }) = true
      norm_num [leaf6286Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6286CertificateValid :
    WideCertificateValid leaf6286Box leaf6286Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk89ValidityFacts chi87ValidityFacts
    leaf6286LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6286CoverageChecked :
    coverageCheck (innerAD leaf6286Box) leaf6286InnerLog = true := by
  rfl'

private theorem leaf6286InnerLogValid :
    leaf6286InnerLog.Valid 8 (innerAD leaf6286Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint434PositiveFacts.valid leaf6286CoverageChecked

private noncomputable def leaf6286InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907373/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6286InputLogOnePlusV_eq :
    leaf6286InputLogOnePlusV = outerEnclosure 24
      (leaf6286Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6286RoundedFacts : LeafRoundedFacts 8
    leaf6286Certificate.logOnePlusV leaf6286InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6286InputLogOnePlusV_eq }

private noncomputable def leaf6286Inputs : Inputs :=
  inputsOfCaches globalInput sk89RoundedInputs
    chi87InputQChi innerPair292Input
    leaf6286InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6286LowerChecked :
    lowerCheck 24 leaf6286Box leaf6286Inputs = true := by
  rfl'

private theorem leaf6286CoversExact : CoversExact 8
    leaf6286Box leaf6286Certificate leaf6286InnerLog leaf6286Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk89RoundedFacts chi87RoundedFacts
    innerPair292RoundedFacts leaf6286RoundedFacts (by rfl)

private theorem leaf6286FlatSound : Sound leaf6286Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6286CertificateValid
    leaf6286InnerLogValid leaf6286CoversExact leaf6286LowerChecked

private noncomputable def leaf6287Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (9/16), chiHi := (37/64) }

private noncomputable def leaf6287Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109021/67108864) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34356555776) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (163801173/134217728) }, upper := { exponent := 1, mantissa := (1289/1024) } }, logOuter := sk90LogOuterCertificate, logK := sk90LogKCertificate, logChi := chi86LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714786813/68713111552) } }, logDArg := sk90LogDArgCertificate }

private noncomputable def leaf6287InnerLog : WideLogData :=
  innerPair292Data

set_option maxRecDepth 1000000 in
private theorem leaf6287LocalValidity :
    LeafFacts leaf6287Box leaf6287Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6287Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34356555776) }) = true
      norm_num [leaf6287Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6287CertificateValid :
    WideCertificateValid leaf6287Box leaf6287Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk90ValidityFacts chi86ValidityFacts
    leaf6287LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6287CoverageChecked :
    coverageCheck (innerAD leaf6287Box) leaf6287InnerLog = true := by
  rfl'

private theorem leaf6287InnerLogValid :
    leaf6287InnerLog.Valid 8 (innerAD leaf6287Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint434PositiveFacts.valid leaf6287CoverageChecked

private noncomputable def leaf6287InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814745/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6287InputLogOnePlusV_eq :
    leaf6287InputLogOnePlusV = outerEnclosure 24
      (leaf6287Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6287RoundedFacts : LeafRoundedFacts 8
    leaf6287Certificate.logOnePlusV leaf6287InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6287InputLogOnePlusV_eq }

private noncomputable def leaf6287Inputs : Inputs :=
  inputsOfCaches globalInput sk90RoundedInputs
    chi86InputQChi innerPair292Input
    leaf6287InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6287LowerChecked :
    lowerCheck 24 leaf6287Box leaf6287Inputs = true := by
  rfl'

private theorem leaf6287CoversExact : CoversExact 8
    leaf6287Box leaf6287Certificate leaf6287InnerLog leaf6287Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk90RoundedFacts chi86RoundedFacts
    innerPair292RoundedFacts leaf6287RoundedFacts (by rfl)

private theorem leaf6287FlatSound : Sound leaf6287Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6287CertificateValid
    leaf6287InnerLogValid leaf6287CoversExact leaf6287LowerChecked

private noncomputable def leaf6288Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (37/64), chiHi := (19/32) }

private noncomputable def leaf6288Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109023/67108864) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34356469760) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (166487983/134217728) }, upper := { exponent := 1, mantissa := (655/512) } }, logOuter := sk90LogOuterCertificate, logK := sk90LogKCertificate, logChi := chi87LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714700797/68712939520) } }, logDArg := sk90LogDArgCertificate }

private noncomputable def leaf6288InnerLog : WideLogData :=
  innerPair286Data

set_option maxRecDepth 1000000 in
private theorem leaf6288LocalValidity :
    LeafFacts leaf6288Box leaf6288Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6288Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34356469760) }) = true
      norm_num [leaf6288Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6288CertificateValid :
    WideCertificateValid leaf6288Box leaf6288Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk90ValidityFacts chi87ValidityFacts
    leaf6288LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6288CoverageChecked :
    coverageCheck (innerAD leaf6288Box) leaf6288InnerLog = true := by
  rfl'

private theorem leaf6288InnerLogValid :
    leaf6288InnerLog.Valid 8 (innerAD leaf6288Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint90PositiveFacts.valid leaf6288CoverageChecked

private noncomputable def leaf6288InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629511/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6288InputLogOnePlusV_eq :
    leaf6288InputLogOnePlusV = outerEnclosure 24
      (leaf6288Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6288RoundedFacts : LeafRoundedFacts 8
    leaf6288Certificate.logOnePlusV leaf6288InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6288InputLogOnePlusV_eq }

private noncomputable def leaf6288Inputs : Inputs :=
  inputsOfCaches globalInput sk90RoundedInputs
    chi87InputQChi innerPair286Input
    leaf6288InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6288LowerChecked :
    lowerCheck 24 leaf6288Box leaf6288Inputs = true := by
  rfl'

private theorem leaf6288CoversExact : CoversExact 8
    leaf6288Box leaf6288Certificate leaf6288InnerLog leaf6288Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk90RoundedFacts chi87RoundedFacts
    innerPair286RoundedFacts leaf6288RoundedFacts (by rfl)

private theorem leaf6288FlatSound : Sound leaf6288Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6288CertificateValid
    leaf6288InnerLogValid leaf6288CoversExact leaf6288LowerChecked

private noncomputable def leaf6289Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (19/32), chiHi := (39/64) }

private noncomputable def leaf6289Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109023/67108864) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34356463616) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (166684579/134217728) }, upper := { exponent := 1, mantissa := (2623/2048) } }, logOuter := sk89LogOuterCertificate, logK := sk89LogKCertificate, logChi := chi321LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714694653/68712927232) } }, logDArg := sk89LogDArgCertificate }

private noncomputable def leaf6289InnerLog : WideLogData :=
  innerPair286Data

set_option maxRecDepth 1000000 in
private theorem leaf6289LocalValidity :
    LeafFacts leaf6289Box leaf6289Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6289Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34356463616) }) = true
      norm_num [leaf6289Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6289CertificateValid :
    WideCertificateValid leaf6289Box leaf6289Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk89ValidityFacts chi321ValidityFacts
    leaf6289LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6289CoverageChecked :
    coverageCheck (innerAD leaf6289Box) leaf6289InnerLog = true := by
  rfl'

private theorem leaf6289InnerLogValid :
    leaf6289InnerLog.Valid 8 (innerAD leaf6289Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint90PositiveFacts.valid leaf6289CoverageChecked

private noncomputable def leaf6289InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (1453689/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf6289InputLogOnePlusV_eq :
    leaf6289InputLogOnePlusV = outerEnclosure 24
      (leaf6289Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6289RoundedFacts : LeafRoundedFacts 8
    leaf6289Certificate.logOnePlusV leaf6289InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6289InputLogOnePlusV_eq }

private noncomputable def leaf6289Inputs : Inputs :=
  inputsOfCaches globalInput sk89RoundedInputs
    chi321InputQChi innerPair286Input
    leaf6289InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6289LowerChecked :
    lowerCheck 24 leaf6289Box leaf6289Inputs = true := by
  rfl'

private theorem leaf6289CoversExact : CoversExact 8
    leaf6289Box leaf6289Certificate leaf6289InnerLog leaf6289Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk89RoundedFacts chi321RoundedFacts
    innerPair286RoundedFacts leaf6289RoundedFacts (by rfl)

private theorem leaf6289FlatSound : Sound leaf6289Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6289CertificateValid
    leaf6289InnerLogValid leaf6289CoversExact leaf6289LowerChecked

private noncomputable def leaf6290Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (39/64), chiHi := (5/8) }

private noncomputable def leaf6290Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109025/67108864) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34356379648) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (169305857/134217728) }, upper := { exponent := 1, mantissa := (333/256) } }, logOuter := sk89LogOuterCertificate, logK := sk89LogKCertificate, logChi := chi322LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714610685/68712759296) } }, logDArg := sk89LogDArgCertificate }

private noncomputable def leaf6290InnerLog : WideLogData :=
  innerPair294Data

set_option maxRecDepth 1000000 in
private theorem leaf6290LocalValidity :
    LeafFacts leaf6290Box leaf6290Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6290Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34356379648) }) = true
      norm_num [leaf6290Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6290CertificateValid :
    WideCertificateValid leaf6290Box leaf6290Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk89ValidityFacts chi322ValidityFacts
    leaf6290LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6290CoverageChecked :
    coverageCheck (innerAD leaf6290Box) leaf6290InnerLog = true := by
  rfl'

private theorem leaf6290InnerLogValid :
    leaf6290InnerLog.Valid 8 (innerAD leaf6290Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint91PositiveFacts.valid leaf6290CoverageChecked

private noncomputable def leaf6290InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629533/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6290InputLogOnePlusV_eq :
    leaf6290InputLogOnePlusV = outerEnclosure 24
      (leaf6290Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6290RoundedFacts : LeafRoundedFacts 8
    leaf6290Certificate.logOnePlusV leaf6290InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6290InputLogOnePlusV_eq }

private noncomputable def leaf6290Inputs : Inputs :=
  inputsOfCaches globalInput sk89RoundedInputs
    chi322InputQChi innerPair294Input
    leaf6290InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6290LowerChecked :
    lowerCheck 24 leaf6290Box leaf6290Inputs = true := by
  rfl'

private theorem leaf6290CoversExact : CoversExact 8
    leaf6290Box leaf6290Certificate leaf6290InnerLog leaf6290Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk89RoundedFacts chi322RoundedFacts
    innerPair294RoundedFacts leaf6290RoundedFacts (by rfl)

private theorem leaf6290FlatSound : Sound leaf6290Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6290CertificateValid
    leaf6290InnerLogValid leaf6290CoversExact leaf6290LowerChecked

private noncomputable def leaf6291Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (19/32), chiHi := (39/64) }

private noncomputable def leaf6291Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109025/67108864) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34356383744) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (169174793/134217728) }, upper := { exponent := 1, mantissa := (1331/1024) } }, logOuter := sk90LogOuterCertificate, logK := sk90LogKCertificate, logChi := chi321LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714614781/68712767488) } }, logDArg := sk90LogDArgCertificate }

private noncomputable def leaf6291InnerLog : WideLogData :=
  innerPair294Data

set_option maxRecDepth 1000000 in
private theorem leaf6291LocalValidity :
    LeafFacts leaf6291Box leaf6291Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6291Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34356383744) }) = true
      norm_num [leaf6291Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6291CertificateValid :
    WideCertificateValid leaf6291Box leaf6291Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk90ValidityFacts chi321ValidityFacts
    leaf6291LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6291CoverageChecked :
    coverageCheck (innerAD leaf6291Box) leaf6291InnerLog = true := by
  rfl'

private theorem leaf6291InnerLogValid :
    leaf6291InnerLog.Valid 8 (innerAD leaf6291Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint91PositiveFacts.valid leaf6291CoverageChecked

private noncomputable def leaf6291InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907383/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6291InputLogOnePlusV_eq :
    leaf6291InputLogOnePlusV = outerEnclosure 24
      (leaf6291Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6291RoundedFacts : LeafRoundedFacts 8
    leaf6291Certificate.logOnePlusV leaf6291InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6291InputLogOnePlusV_eq }

private noncomputable def leaf6291Inputs : Inputs :=
  inputsOfCaches globalInput sk90RoundedInputs
    chi321InputQChi innerPair294Input
    leaf6291InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6291LowerChecked :
    lowerCheck 24 leaf6291Box leaf6291Inputs = true := by
  rfl'

private theorem leaf6291CoversExact : CoversExact 8
    leaf6291Box leaf6291Certificate leaf6291InnerLog leaf6291Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk90RoundedFacts chi321RoundedFacts
    innerPair294RoundedFacts leaf6291RoundedFacts (by rfl)

private theorem leaf6291FlatSound : Sound leaf6291Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6291CertificateValid
    leaf6291InnerLogValid leaf6291CoversExact leaf6291LowerChecked

private noncomputable def leaf6292Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (39/64), chiHi := (5/8) }

private noncomputable def leaf6292Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109027/67108864) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34356297728) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (171861603/134217728) }, upper := { exponent := 1, mantissa := (169/128) } }, logOuter := sk90LogOuterCertificate, logK := sk90LogKCertificate, logChi := chi322LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714528765/68712595456) } }, logDArg := sk90LogDArgCertificate }

private noncomputable def leaf6292InnerLog : WideLogData :=
  innerPair295Data

set_option maxRecDepth 1000000 in
private theorem leaf6292LocalValidity :
    LeafFacts leaf6292Box leaf6292Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6292Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34356297728) }) = true
      norm_num [leaf6292Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6292CertificateValid :
    WideCertificateValid leaf6292Box leaf6292Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk90ValidityFacts chi322ValidityFacts
    leaf6292LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6292CoverageChecked :
    coverageCheck (innerAD leaf6292Box) leaf6292InnerLog = true := by
  rfl'

private theorem leaf6292InnerLogValid :
    leaf6292InnerLog.Valid 8 (innerAD leaf6292Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint92PositiveFacts.valid leaf6292CoverageChecked

private noncomputable def leaf6292InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629553/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6292InputLogOnePlusV_eq :
    leaf6292InputLogOnePlusV = outerEnclosure 24
      (leaf6292Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6292RoundedFacts : LeafRoundedFacts 8
    leaf6292Certificate.logOnePlusV leaf6292InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6292InputLogOnePlusV_eq }

private noncomputable def leaf6292Inputs : Inputs :=
  inputsOfCaches globalInput sk90RoundedInputs
    chi322InputQChi innerPair295Input
    leaf6292InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6292LowerChecked :
    lowerCheck 24 leaf6292Box leaf6292Inputs = true := by
  rfl'

private theorem leaf6292CoversExact : CoversExact 8
    leaf6292Box leaf6292Certificate leaf6292InnerLog leaf6292Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk90RoundedFacts chi322RoundedFacts
    innerPair295RoundedFacts leaf6292RoundedFacts (by rfl)

private theorem leaf6292FlatSound : Sound leaf6292Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6292CertificateValid
    leaf6292InnerLogValid leaf6292CoversExact leaf6292LowerChecked

private noncomputable def leaf6293Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (9/16), chiHi := (37/64) }

private noncomputable def leaf6293Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109023/67108864) }, vSqrt := { lower := (32765/32768), upper := (11452743679/11452160000) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (166160323/134217728) }, upper := { exponent := 1, mantissa := (2615/2048) } }, logOuter := sk91LogOuterCertificate, logK := sk91LogKCertificate, logChi := chi86LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (22904903679/22904320000) } }, logDArg := sk91LogDArgCertificate }

private noncomputable def leaf6293InnerLog : WideLogData :=
  innerPair286Data

set_option maxRecDepth 1000000 in
private theorem leaf6293LocalValidity :
    LeafFacts leaf6293Box leaf6293Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6293Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (11452743679/11452160000) }) = true
      norm_num [leaf6293Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6293CertificateValid :
    WideCertificateValid leaf6293Box leaf6293Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk91ValidityFacts chi86ValidityFacts
    leaf6293LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6293CoverageChecked :
    coverageCheck (innerAD leaf6293Box) leaf6293InnerLog = true := by
  rfl'

private theorem leaf6293InnerLogValid :
    leaf6293InnerLog.Valid 8 (innerAD leaf6293Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint90PositiveFacts.valid leaf6293CoverageChecked

private noncomputable def leaf6293InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907377/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6293InputLogOnePlusV_eq :
    leaf6293InputLogOnePlusV = outerEnclosure 24
      (leaf6293Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6293RoundedFacts : LeafRoundedFacts 8
    leaf6293Certificate.logOnePlusV leaf6293InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6293InputLogOnePlusV_eq }

private noncomputable def leaf6293Inputs : Inputs :=
  inputsOfCaches globalInput sk91RoundedInputs
    chi86InputQChi innerPair286Input
    leaf6293InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6293LowerChecked :
    lowerCheck 24 leaf6293Box leaf6293Inputs = true := by
  rfl'

private theorem leaf6293CoversExact : CoversExact 8
    leaf6293Box leaf6293Certificate leaf6293InnerLog leaf6293Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk91RoundedFacts chi86RoundedFacts
    innerPair286RoundedFacts leaf6293RoundedFacts (by rfl)

private theorem leaf6293FlatSound : Sound leaf6293Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6293CertificateValid
    leaf6293InnerLogValid leaf6293CoversExact leaf6293LowerChecked

private noncomputable def leaf6294Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (37/64), chiHi := (19/32) }

private noncomputable def leaf6294Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109025/67108864) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34356391936) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (168912665/134217728) }, upper := { exponent := 1, mantissa := (1329/1024) } }, logOuter := sk91LogOuterCertificate, logK := sk91LogKCertificate, logChi := chi87LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714622973/68712783872) } }, logDArg := sk91LogDArgCertificate }

private noncomputable def leaf6294InnerLog : WideLogData :=
  innerPair673Data

set_option maxRecDepth 1000000 in
private theorem leaf6294LocalValidity :
    LeafFacts leaf6294Box leaf6294Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6294Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34356391936) }) = true
      norm_num [leaf6294Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6294CertificateValid :
    WideCertificateValid leaf6294Box leaf6294Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk91ValidityFacts chi87ValidityFacts
    leaf6294LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6294CoverageChecked :
    coverageCheck (innerAD leaf6294Box) leaf6294InnerLog = true := by
  rfl'

private theorem leaf6294InnerLogValid :
    leaf6294InnerLog.Valid 8 (innerAD leaf6294Box) :=
  wideLogDataValid_of_cachedCheck endpoint419PositiveFacts
    endpoint444PositiveFacts.valid leaf6294CoverageChecked

private noncomputable def leaf6294InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814765/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6294InputLogOnePlusV_eq :
    leaf6294InputLogOnePlusV = outerEnclosure 24
      (leaf6294Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6294RoundedFacts : LeafRoundedFacts 8
    leaf6294Certificate.logOnePlusV leaf6294InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6294InputLogOnePlusV_eq }

private noncomputable def leaf6294Inputs : Inputs :=
  inputsOfCaches globalInput sk91RoundedInputs
    chi87InputQChi innerPair673Input
    leaf6294InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6294LowerChecked :
    lowerCheck 24 leaf6294Box leaf6294Inputs = true := by
  rfl'

private theorem leaf6294CoversExact : CoversExact 8
    leaf6294Box leaf6294Certificate leaf6294InnerLog leaf6294Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk91RoundedFacts chi87RoundedFacts
    innerPair673RoundedFacts leaf6294RoundedFacts (by rfl)

private theorem leaf6294FlatSound : Sound leaf6294Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6294CertificateValid
    leaf6294InnerLogValid leaf6294CoversExact leaf6294LowerChecked

private noncomputable def leaf6295Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (9/16), chiHi := (37/64) }

private noncomputable def leaf6295Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109025/67108864) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34356404224) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (168519473/134217728) }, upper := { exponent := 1, mantissa := (663/512) } }, logOuter := sk92LogOuterCertificate, logK := sk92LogKCertificate, logChi := chi86LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714635261/68712808448) } }, logDArg := sk92LogDArgCertificate }

private noncomputable def leaf6295InnerLog : WideLogData :=
  innerPair739Data

set_option maxRecDepth 1000000 in
private theorem leaf6295LocalValidity :
    LeafFacts leaf6295Box leaf6295Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6295Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34356404224) }) = true
      norm_num [leaf6295Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6295CertificateValid :
    WideCertificateValid leaf6295Box leaf6295Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk92ValidityFacts chi86ValidityFacts
    leaf6295LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6295CoverageChecked :
    coverageCheck (innerAD leaf6295Box) leaf6295InnerLog = true := by
  rfl'

private theorem leaf6295InnerLogValid :
    leaf6295InnerLog.Valid 8 (innerAD leaf6295Box) :=
  wideLogDataValid_of_cachedCheck endpoint475PositiveFacts
    endpoint476PositiveFacts.valid leaf6295CoverageChecked

private noncomputable def leaf6295InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629527/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6295InputLogOnePlusV_eq :
    leaf6295InputLogOnePlusV = outerEnclosure 24
      (leaf6295Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6295RoundedFacts : LeafRoundedFacts 8
    leaf6295Certificate.logOnePlusV leaf6295InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6295InputLogOnePlusV_eq }

private noncomputable def leaf6295Inputs : Inputs :=
  inputsOfCaches globalInput sk92RoundedInputs
    chi86InputQChi innerPair739Input
    leaf6295InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6295LowerChecked :
    lowerCheck 24 leaf6295Box leaf6295Inputs = true := by
  rfl'

private theorem leaf6295CoversExact : CoversExact 8
    leaf6295Box leaf6295Certificate leaf6295InnerLog leaf6295Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk92RoundedFacts chi86RoundedFacts
    innerPair739RoundedFacts leaf6295RoundedFacts (by rfl)

private theorem leaf6295FlatSound : Sound leaf6295Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6295CertificateValid
    leaf6295InnerLogValid leaf6295CoversExact leaf6295LowerChecked

private noncomputable def leaf6296Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (37/64), chiHi := (19/32) }

private noncomputable def leaf6296Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109027/67108864) }, vSqrt := { lower := (32765/32768), upper := (11452743679/11452104704) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (171337347/134217728) }, upper := { exponent := 1, mantissa := (337/256) } }, logOuter := sk92LogOuterCertificate, logK := sk92LogKCertificate, logChi := chi87LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (22904848383/22904209408) } }, logDArg := sk92LogDArgCertificate }

private noncomputable def leaf6296InnerLog : WideLogData :=
  innerPair691Data

set_option maxRecDepth 1000000 in
private theorem leaf6296LocalValidity :
    LeafFacts leaf6296Box leaf6296Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6296Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (11452743679/11452104704) }) = true
      norm_num [leaf6296Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6296CertificateValid :
    WideCertificateValid leaf6296Box leaf6296Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk92ValidityFacts chi87ValidityFacts
    leaf6296LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6296CoverageChecked :
    coverageCheck (innerAD leaf6296Box) leaf6296InnerLog = true := by
  rfl'

private theorem leaf6296InnerLogValid :
    leaf6296InnerLog.Valid 8 (innerAD leaf6296Box) :=
  wideLogDataValid_of_cachedCheck endpoint437PositiveFacts
    endpoint95PositiveFacts.valid leaf6296CoverageChecked

private noncomputable def leaf6296InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629549/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6296InputLogOnePlusV_eq :
    leaf6296InputLogOnePlusV = outerEnclosure 24
      (leaf6296Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6296RoundedFacts : LeafRoundedFacts 8
    leaf6296Certificate.logOnePlusV leaf6296InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6296InputLogOnePlusV_eq }

private noncomputable def leaf6296Inputs : Inputs :=
  inputsOfCaches globalInput sk92RoundedInputs
    chi87InputQChi innerPair691Input
    leaf6296InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6296LowerChecked :
    lowerCheck 24 leaf6296Box leaf6296Inputs = true := by
  rfl'

private theorem leaf6296CoversExact : CoversExact 8
    leaf6296Box leaf6296Certificate leaf6296InnerLog leaf6296Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk92RoundedFacts chi87RoundedFacts
    innerPair691RoundedFacts leaf6296RoundedFacts (by rfl)

private theorem leaf6296FlatSound : Sound leaf6296Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6296CertificateValid
    leaf6296InnerLogValid leaf6296CoversExact leaf6296LowerChecked

private noncomputable def leaf6297Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (19/32), chiHi := (39/64) }

private noncomputable def leaf6297Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109027/67108864) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34356303872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (171665007/134217728) }, upper := { exponent := 1, mantissa := (2701/2048) } }, logOuter := sk91LogOuterCertificate, logK := sk91LogKCertificate, logChi := chi321LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714534909/68712607744) } }, logDArg := sk91LogDArgCertificate }

private noncomputable def leaf6297InnerLog : WideLogData :=
  innerPair691Data

set_option maxRecDepth 1000000 in
private theorem leaf6297LocalValidity :
    LeafFacts leaf6297Box leaf6297Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6297Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34356303872) }) = true
      norm_num [leaf6297Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6297CertificateValid :
    WideCertificateValid leaf6297Box leaf6297Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk91ValidityFacts chi321ValidityFacts
    leaf6297LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6297CoverageChecked :
    coverageCheck (innerAD leaf6297Box) leaf6297InnerLog = true := by
  rfl'

private theorem leaf6297InnerLogValid :
    leaf6297InnerLog.Valid 8 (innerAD leaf6297Box) :=
  wideLogDataValid_of_cachedCheck endpoint437PositiveFacts
    endpoint95PositiveFacts.valid leaf6297CoverageChecked

private noncomputable def leaf6297InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629551/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6297InputLogOnePlusV_eq :
    leaf6297InputLogOnePlusV = outerEnclosure 24
      (leaf6297Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6297RoundedFacts : LeafRoundedFacts 8
    leaf6297Certificate.logOnePlusV leaf6297InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6297InputLogOnePlusV_eq }

private noncomputable def leaf6297Inputs : Inputs :=
  inputsOfCaches globalInput sk91RoundedInputs
    chi321InputQChi innerPair691Input
    leaf6297InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6297LowerChecked :
    lowerCheck 24 leaf6297Box leaf6297Inputs = true := by
  rfl'

private theorem leaf6297CoversExact : CoversExact 8
    leaf6297Box leaf6297Certificate leaf6297InnerLog leaf6297Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk91RoundedFacts chi321RoundedFacts
    innerPair691RoundedFacts leaf6297RoundedFacts (by rfl)

private theorem leaf6297FlatSound : Sound leaf6297Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6297CertificateValid
    leaf6297InnerLogValid leaf6297CoversExact leaf6297LowerChecked

private noncomputable def leaf6298Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (39/64), chiHi := (5/8) }

private noncomputable def leaf6298Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109029/67108864) }, vSqrt := { lower := (32765/32768), upper := (11452743679/11452071936) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (174417349/134217728) }, upper := { exponent := 1, mantissa := (343/256) } }, logOuter := sk91LogOuterCertificate, logK := sk91LogKCertificate, logChi := chi322LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (22904815615/22904143872) } }, logDArg := sk91LogDArgCertificate }

private noncomputable def leaf6298InnerLog : WideLogData :=
  innerPair340Data

set_option maxRecDepth 1000000 in
private theorem leaf6298LocalValidity :
    LeafFacts leaf6298Box leaf6298Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6298Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (11452743679/11452071936) }) = true
      norm_num [leaf6298Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6298CertificateValid :
    WideCertificateValid leaf6298Box leaf6298Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk91ValidityFacts chi322ValidityFacts
    leaf6298LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6298CoverageChecked :
    coverageCheck (innerAD leaf6298Box) leaf6298InnerLog = true := by
  rfl'

private theorem leaf6298InnerLogValid :
    leaf6298InnerLog.Valid 8 (innerAD leaf6298Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint92PositiveFacts.valid leaf6298CoverageChecked

private noncomputable def leaf6298InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629573/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6298InputLogOnePlusV_eq :
    leaf6298InputLogOnePlusV = outerEnclosure 24
      (leaf6298Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6298RoundedFacts : LeafRoundedFacts 8
    leaf6298Certificate.logOnePlusV leaf6298InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6298InputLogOnePlusV_eq }

private noncomputable def leaf6298Inputs : Inputs :=
  inputsOfCaches globalInput sk91RoundedInputs
    chi322InputQChi innerPair340Input
    leaf6298InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6298LowerChecked :
    lowerCheck 24 leaf6298Box leaf6298Inputs = true := by
  rfl'

private theorem leaf6298CoversExact : CoversExact 8
    leaf6298Box leaf6298Certificate leaf6298InnerLog leaf6298Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk91RoundedFacts chi322RoundedFacts
    innerPair340RoundedFacts leaf6298RoundedFacts (by rfl)

private theorem leaf6298FlatSound : Sound leaf6298Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6298CertificateValid
    leaf6298InnerLogValid leaf6298CoversExact leaf6298LowerChecked

private noncomputable def leaf6299Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (19/32), chiHi := (39/64) }

private noncomputable def leaf6299Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109029/67108864) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34356224000) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (174155221/134217728) }, upper := { exponent := 1, mantissa := (685/512) } }, logOuter := sk92LogOuterCertificate, logK := sk92LogKCertificate, logChi := chi321LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714455037/68712448000) } }, logDArg := sk92LogDArgCertificate }

private noncomputable def leaf6299InnerLog : WideLogData :=
  innerPair340Data

set_option maxRecDepth 1000000 in
private theorem leaf6299LocalValidity :
    LeafFacts leaf6299Box leaf6299Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6299Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34356224000) }) = true
      norm_num [leaf6299Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6299CertificateValid :
    WideCertificateValid leaf6299Box leaf6299Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk92ValidityFacts chi321ValidityFacts
    leaf6299LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6299CoverageChecked :
    coverageCheck (innerAD leaf6299Box) leaf6299InnerLog = true := by
  rfl'

private theorem leaf6299InnerLogValid :
    leaf6299InnerLog.Valid 8 (innerAD leaf6299Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint92PositiveFacts.valid leaf6299CoverageChecked

private noncomputable def leaf6299InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629571/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6299InputLogOnePlusV_eq :
    leaf6299InputLogOnePlusV = outerEnclosure 24
      (leaf6299Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6299RoundedFacts : LeafRoundedFacts 8
    leaf6299Certificate.logOnePlusV leaf6299InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6299InputLogOnePlusV_eq }

private noncomputable def leaf6299Inputs : Inputs :=
  inputsOfCaches globalInput sk92RoundedInputs
    chi321InputQChi innerPair340Input
    leaf6299InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6299LowerChecked :
    lowerCheck 24 leaf6299Box leaf6299Inputs = true := by
  rfl'

private theorem leaf6299CoversExact : CoversExact 8
    leaf6299Box leaf6299Certificate leaf6299InnerLog leaf6299Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk92RoundedFacts chi321RoundedFacts
    innerPair340RoundedFacts leaf6299RoundedFacts (by rfl)

private theorem leaf6299FlatSound : Sound leaf6299Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6299CertificateValid
    leaf6299InnerLogValid leaf6299CoversExact leaf6299LowerChecked

private noncomputable def leaf6300Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (39/64), chiHi := (5/8) }

private noncomputable def leaf6300Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109031/67108864) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34356133888) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (176973095/134217728) }, upper := { exponent := 1, mantissa := (87/64) } }, logOuter := sk92LogOuterCertificate, logK := sk92LogKCertificate, logChi := chi322LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714364925/68712267776) } }, logDArg := sk92LogDArgCertificate }

private noncomputable def leaf6300InnerLog : WideLogData :=
  innerPair346Data

set_option maxRecDepth 1000000 in
private theorem leaf6300LocalValidity :
    LeafFacts leaf6300Box leaf6300Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6300Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34356133888) }) = true
      norm_num [leaf6300Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6300CertificateValid :
    WideCertificateValid leaf6300Box leaf6300Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk92ValidityFacts chi322ValidityFacts
    leaf6300LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6300CoverageChecked :
    coverageCheck (innerAD leaf6300Box) leaf6300InnerLog = true := by
  rfl'

private theorem leaf6300InnerLogValid :
    leaf6300InnerLog.Valid 8 (innerAD leaf6300Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint93PositiveFacts.valid leaf6300CoverageChecked

private noncomputable def leaf6300InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629593/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6300InputLogOnePlusV_eq :
    leaf6300InputLogOnePlusV = outerEnclosure 24
      (leaf6300Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6300RoundedFacts : LeafRoundedFacts 8
    leaf6300Certificate.logOnePlusV leaf6300InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6300InputLogOnePlusV_eq }

private noncomputable def leaf6300Inputs : Inputs :=
  inputsOfCaches globalInput sk92RoundedInputs
    chi322InputQChi innerPair346Input
    leaf6300InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6300LowerChecked :
    lowerCheck 24 leaf6300Box leaf6300Inputs = true := by
  rfl'

private theorem leaf6300CoversExact : CoversExact 8
    leaf6300Box leaf6300Certificate leaf6300InnerLog leaf6300Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk92RoundedFacts chi322RoundedFacts
    innerPair346RoundedFacts leaf6300RoundedFacts (by rfl)

private theorem leaf6300FlatSound : Sound leaf6300Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6300CertificateValid
    leaf6300InnerLogValid leaf6300CoversExact leaf6300LowerChecked

private noncomputable def component126Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (1/2), chiHi := (33/64) }

set_option maxRecDepth 1000000 in
private theorem component126Node0_sound : Sound component126Node0Box :=
  sound_of_literal_split component126Node0Box leaf6256Box leaf6257Box
    .k (81/32) (by rfl) (by rfl)
    leaf6256FlatSound leaf6257FlatSound

private noncomputable def component126Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (33/64), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component126Node1_sound : Sound component126Node1Box :=
  sound_of_literal_split component126Node1Box leaf6258Box leaf6259Box
    .k (81/32) (by rfl) (by rfl)
    leaf6258FlatSound leaf6259FlatSound

private noncomputable def component126Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (1/2), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component126Node2_sound : Sound component126Node2Box :=
  sound_of_literal_split component126Node2Box component126Node0Box component126Node1Box
    .chi (33/64) (by rfl) (by rfl)
    component126Node0_sound component126Node1_sound

private noncomputable def component126Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (1/2), chiHi := (33/64) }

set_option maxRecDepth 1000000 in
private theorem component126Node3_sound : Sound component126Node3Box :=
  sound_of_literal_split component126Node3Box leaf6260Box leaf6261Box
    .k (83/32) (by rfl) (by rfl)
    leaf6260FlatSound leaf6261FlatSound

private noncomputable def component126Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (33/64), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component126Node4_sound : Sound component126Node4Box :=
  sound_of_literal_split component126Node4Box leaf6262Box leaf6263Box
    .k (83/32) (by rfl) (by rfl)
    leaf6262FlatSound leaf6263FlatSound

private noncomputable def component126Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (1/2), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component126Node5_sound : Sound component126Node5Box :=
  sound_of_literal_split component126Node5Box component126Node3Box component126Node4Box
    .chi (33/64) (by rfl) (by rfl)
    component126Node3_sound component126Node4_sound

private noncomputable def component126Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8), chiLo := (1/2), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component126Node6_sound : Sound component126Node6Box :=
  sound_of_literal_split component126Node6Box component126Node2Box component126Node5Box
    .k (41/16) (by rfl) (by rfl)
    component126Node2_sound component126Node5_sound

private noncomputable def component126Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (17/32), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component126Node7_sound : Sound component126Node7Box :=
  sound_of_literal_split component126Node7Box leaf6264Box leaf6265Box
    .chi (35/64) (by rfl) (by rfl)
    leaf6264FlatSound leaf6265FlatSound

private noncomputable def component126Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (17/32), chiHi := (35/64) }

set_option maxRecDepth 1000000 in
private theorem component126Node8_sound : Sound component126Node8Box :=
  sound_of_literal_split component126Node8Box leaf6266Box leaf6267Box
    .chi (69/128) (by rfl) (by rfl)
    leaf6266FlatSound leaf6267FlatSound

private noncomputable def component126Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (17/32), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component126Node9_sound : Sound component126Node9Box :=
  sound_of_literal_split component126Node9Box component126Node8Box leaf6268Box
    .chi (35/64) (by rfl) (by rfl)
    component126Node8_sound leaf6268FlatSound

private noncomputable def component126Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8), chiLo := (17/32), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component126Node10_sound : Sound component126Node10Box :=
  sound_of_literal_split component126Node10Box component126Node7Box component126Node9Box
    .k (41/16) (by rfl) (by rfl)
    component126Node7_sound component126Node9_sound

private noncomputable def component126Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8), chiLo := (1/2), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component126Node11_sound : Sound component126Node11Box :=
  sound_of_literal_split component126Node11Box component126Node6Box component126Node10Box
    .chi (17/32) (by rfl) (by rfl)
    component126Node6_sound component126Node10_sound

private noncomputable def component126Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (1/2), chiHi := (33/64) }

set_option maxRecDepth 1000000 in
private theorem component126Node12_sound : Sound component126Node12Box :=
  sound_of_literal_split component126Node12Box leaf6269Box leaf6270Box
    .chi (65/128) (by rfl) (by rfl)
    leaf6269FlatSound leaf6270FlatSound

private noncomputable def component126Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (33/64), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component126Node13_sound : Sound component126Node13Box :=
  sound_of_literal_split component126Node13Box leaf6271Box leaf6272Box
    .chi (67/128) (by rfl) (by rfl)
    leaf6271FlatSound leaf6272FlatSound

private noncomputable def component126Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (1/2), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component126Node14_sound : Sound component126Node14Box :=
  sound_of_literal_split component126Node14Box component126Node12Box component126Node13Box
    .chi (33/64) (by rfl) (by rfl)
    component126Node12_sound component126Node13_sound

private noncomputable def component126Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (1/2), chiHi := (33/64) }

set_option maxRecDepth 1000000 in
private theorem component126Node15_sound : Sound component126Node15Box :=
  sound_of_literal_split component126Node15Box leaf6273Box leaf6274Box
    .chi (65/128) (by rfl) (by rfl)
    leaf6273FlatSound leaf6274FlatSound

private noncomputable def component126Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (33/64), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component126Node16_sound : Sound component126Node16Box :=
  sound_of_literal_split component126Node16Box leaf6275Box leaf6276Box
    .chi (67/128) (by rfl) (by rfl)
    leaf6275FlatSound leaf6276FlatSound

private noncomputable def component126Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (1/2), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component126Node17_sound : Sound component126Node17Box :=
  sound_of_literal_split component126Node17Box component126Node15Box component126Node16Box
    .chi (33/64) (by rfl) (by rfl)
    component126Node15_sound component126Node16_sound

private noncomputable def component126Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4), chiLo := (1/2), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component126Node18_sound : Sound component126Node18Box :=
  sound_of_literal_split component126Node18Box component126Node14Box component126Node17Box
    .k (43/16) (by rfl) (by rfl)
    component126Node14_sound component126Node17_sound

private noncomputable def component126Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (17/32), chiHi := (35/64) }

set_option maxRecDepth 1000000 in
private theorem component126Node19_sound : Sound component126Node19Box :=
  sound_of_literal_split component126Node19Box leaf6277Box leaf6278Box
    .chi (69/128) (by rfl) (by rfl)
    leaf6277FlatSound leaf6278FlatSound

private noncomputable def component126Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (35/64), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component126Node20_sound : Sound component126Node20Box :=
  sound_of_literal_split component126Node20Box leaf6279Box leaf6280Box
    .chi (71/128) (by rfl) (by rfl)
    leaf6279FlatSound leaf6280FlatSound

private noncomputable def component126Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (17/32), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component126Node21_sound : Sound component126Node21Box :=
  sound_of_literal_split component126Node21Box component126Node19Box component126Node20Box
    .chi (35/64) (by rfl) (by rfl)
    component126Node19_sound component126Node20_sound

private noncomputable def component126Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (17/32), chiHi := (35/64) }

set_option maxRecDepth 1000000 in
private theorem component126Node22_sound : Sound component126Node22Box :=
  sound_of_literal_split component126Node22Box leaf6281Box leaf6282Box
    .chi (69/128) (by rfl) (by rfl)
    leaf6281FlatSound leaf6282FlatSound

private noncomputable def component126Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (35/64), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component126Node23_sound : Sound component126Node23Box :=
  sound_of_literal_split component126Node23Box leaf6283Box leaf6284Box
    .chi (71/128) (by rfl) (by rfl)
    leaf6283FlatSound leaf6284FlatSound

private noncomputable def component126Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (17/32), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component126Node24_sound : Sound component126Node24Box :=
  sound_of_literal_split component126Node24Box component126Node22Box component126Node23Box
    .chi (35/64) (by rfl) (by rfl)
    component126Node22_sound component126Node23_sound

private noncomputable def component126Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4), chiLo := (17/32), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component126Node25_sound : Sound component126Node25Box :=
  sound_of_literal_split component126Node25Box component126Node21Box component126Node24Box
    .k (43/16) (by rfl) (by rfl)
    component126Node21_sound component126Node24_sound

private noncomputable def component126Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4), chiLo := (1/2), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component126Node26_sound : Sound component126Node26Box :=
  sound_of_literal_split component126Node26Box component126Node18Box component126Node25Box
    .chi (17/32) (by rfl) (by rfl)
    component126Node18_sound component126Node25_sound

private noncomputable def component126Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (11/4), chiLo := (1/2), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component126Node27_sound : Sound component126Node27Box :=
  sound_of_literal_split component126Node27Box component126Node11Box component126Node26Box
    .k (21/8) (by rfl) (by rfl)
    component126Node11_sound component126Node26_sound

private noncomputable def component126Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (9/16), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component126Node28_sound : Sound component126Node28Box :=
  sound_of_literal_split component126Node28Box leaf6285Box leaf6286Box
    .chi (37/64) (by rfl) (by rfl)
    leaf6285FlatSound leaf6286FlatSound

private noncomputable def component126Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (9/16), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component126Node29_sound : Sound component126Node29Box :=
  sound_of_literal_split component126Node29Box leaf6287Box leaf6288Box
    .chi (37/64) (by rfl) (by rfl)
    leaf6287FlatSound leaf6288FlatSound

private noncomputable def component126Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8), chiLo := (9/16), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component126Node30_sound : Sound component126Node30Box :=
  sound_of_literal_split component126Node30Box component126Node28Box component126Node29Box
    .k (41/16) (by rfl) (by rfl)
    component126Node28_sound component126Node29_sound

private noncomputable def component126Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (19/32), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component126Node31_sound : Sound component126Node31Box :=
  sound_of_literal_split component126Node31Box leaf6289Box leaf6290Box
    .chi (39/64) (by rfl) (by rfl)
    leaf6289FlatSound leaf6290FlatSound

private noncomputable def component126Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (19/32), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component126Node32_sound : Sound component126Node32Box :=
  sound_of_literal_split component126Node32Box leaf6291Box leaf6292Box
    .chi (39/64) (by rfl) (by rfl)
    leaf6291FlatSound leaf6292FlatSound

private noncomputable def component126Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8), chiLo := (19/32), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component126Node33_sound : Sound component126Node33Box :=
  sound_of_literal_split component126Node33Box component126Node31Box component126Node32Box
    .k (41/16) (by rfl) (by rfl)
    component126Node31_sound component126Node32_sound

private noncomputable def component126Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8), chiLo := (9/16), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component126Node34_sound : Sound component126Node34Box :=
  sound_of_literal_split component126Node34Box component126Node30Box component126Node33Box
    .chi (19/32) (by rfl) (by rfl)
    component126Node30_sound component126Node33_sound

private noncomputable def component126Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (9/16), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component126Node35_sound : Sound component126Node35Box :=
  sound_of_literal_split component126Node35Box leaf6293Box leaf6294Box
    .chi (37/64) (by rfl) (by rfl)
    leaf6293FlatSound leaf6294FlatSound

private noncomputable def component126Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (9/16), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component126Node36_sound : Sound component126Node36Box :=
  sound_of_literal_split component126Node36Box leaf6295Box leaf6296Box
    .chi (37/64) (by rfl) (by rfl)
    leaf6295FlatSound leaf6296FlatSound

private noncomputable def component126Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4), chiLo := (9/16), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component126Node37_sound : Sound component126Node37Box :=
  sound_of_literal_split component126Node37Box component126Node35Box component126Node36Box
    .k (43/16) (by rfl) (by rfl)
    component126Node35_sound component126Node36_sound

private noncomputable def component126Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (19/32), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component126Node38_sound : Sound component126Node38Box :=
  sound_of_literal_split component126Node38Box leaf6297Box leaf6298Box
    .chi (39/64) (by rfl) (by rfl)
    leaf6297FlatSound leaf6298FlatSound

private noncomputable def component126Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (19/32), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component126Node39_sound : Sound component126Node39Box :=
  sound_of_literal_split component126Node39Box leaf6299Box leaf6300Box
    .chi (39/64) (by rfl) (by rfl)
    leaf6299FlatSound leaf6300FlatSound

private noncomputable def component126Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4), chiLo := (19/32), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component126Node40_sound : Sound component126Node40Box :=
  sound_of_literal_split component126Node40Box component126Node38Box component126Node39Box
    .k (43/16) (by rfl) (by rfl)
    component126Node38_sound component126Node39_sound

private noncomputable def component126Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4), chiLo := (9/16), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component126Node41_sound : Sound component126Node41Box :=
  sound_of_literal_split component126Node41Box component126Node37Box component126Node40Box
    .chi (19/32) (by rfl) (by rfl)
    component126Node37_sound component126Node40_sound

private noncomputable def component126Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (11/4), chiLo := (9/16), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component126Node42_sound : Sound component126Node42Box :=
  sound_of_literal_split component126Node42Box component126Node34Box component126Node41Box
    .k (21/8) (by rfl) (by rfl)
    component126Node34_sound component126Node41_sound

noncomputable def component126Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (11/4), chiLo := (1/2), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
theorem component126_sound : Sound component126Box :=
  sound_of_literal_split component126Box component126Node27Box component126Node42Box
    .chi (9/16) (by rfl) (by rfl)
    component126Node27_sound component126Node42_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
