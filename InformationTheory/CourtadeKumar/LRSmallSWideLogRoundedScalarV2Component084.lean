import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch1
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

private noncomputable def leaf4096Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (81/32), chiLo := (3/8), chiHi := (25/64) }

private noncomputable def leaf4096Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217939/134217728) }, vSqrt := { lower := (32765/32768), upper := (288728761/288719872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (260006191/134217728) }, upper := { exponent := 0, mantissa := (4073/2048) } }, logOuter := sk99LogOuterCertificate, logK := sk99LogKCertificate, logChi := chi62LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (577448633/577439744) } }, logDArg := sk99LogDArgCertificate }

private noncomputable def leaf4096InnerLog : WideLogData :=
  innerPair101Data

set_option maxRecDepth 1000000 in
private theorem leaf4096LocalValidity :
    LeafFacts leaf4096Box leaf4096Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4096Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (288728761/288719872) }) = true
      norm_num [leaf4096Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4096CertificateValid :
    WideCertificateValid leaf4096Box leaf4096Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk99ValidityFacts chi62ValidityFacts
    leaf4096LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4096CoverageChecked :
    coverageCheck (innerAD leaf4096Box) leaf4096InnerLog = true := by
  rfl'

private theorem leaf4096InnerLogValid :
    leaf4096InnerLog.Valid 8 (innerAD leaf4096Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint24PositiveFacts.valid leaf4096CoverageChecked

private noncomputable def leaf4096InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629339/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4096InputLogOnePlusV_eq :
    leaf4096InputLogOnePlusV = outerEnclosure 24
      (leaf4096Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4096RoundedFacts : LeafRoundedFacts 8
    leaf4096Certificate.logOnePlusV leaf4096InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4096InputLogOnePlusV_eq }

private noncomputable def leaf4096Inputs : Inputs :=
  inputsOfCaches globalInput sk99RoundedInputs
    chi62InputQChi innerPair101Input
    leaf4096InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4096LowerChecked :
    lowerCheck 24 leaf4096Box leaf4096Inputs = true := by
  rfl'

private theorem leaf4096CoversExact : CoversExact 8
    leaf4096Box leaf4096Certificate leaf4096InnerLog leaf4096Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk99RoundedFacts chi62RoundedFacts
    innerPair101RoundedFacts leaf4096RoundedFacts (by rfl)

private theorem leaf4096FlatSound : Sound leaf4096Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4096CertificateValid
    leaf4096InnerLogValid leaf4096CoversExact leaf4096LowerChecked

private noncomputable def leaf4097Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (81/32), kHi := (41/16), chiLo := (3/8), chiHi := (25/64) }

private noncomputable def leaf4097Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217941/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357639168) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (261578957/134217728) }, upper := { exponent := 1, mantissa := (2049/2048) } }, logOuter := sk100LogOuterCertificate, logK := sk100LogKCertificate, logChi := chi62LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716361727/68715278336) } }, logDArg := sk100LogDArgCertificate }

private noncomputable def leaf4097InnerLog : WideLogData :=
  innerPair115Data

set_option maxRecDepth 1000000 in
private theorem leaf4097LocalValidity :
    LeafFacts leaf4097Box leaf4097Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4097Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357639168) }) = true
      norm_num [leaf4097Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4097CertificateValid :
    WideCertificateValid leaf4097Box leaf4097Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk100ValidityFacts chi62ValidityFacts
    leaf4097LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4097CoverageChecked :
    coverageCheck (innerAD leaf4097Box) leaf4097InnerLog = true := by
  rfl'

private theorem leaf4097InnerLogValid :
    leaf4097InnerLog.Valid 8 (innerAD leaf4097Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint283PositiveFacts.valid leaf4097CoverageChecked

private noncomputable def leaf4097InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629345/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4097InputLogOnePlusV_eq :
    leaf4097InputLogOnePlusV = outerEnclosure 24
      (leaf4097Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4097RoundedFacts : LeafRoundedFacts 8
    leaf4097Certificate.logOnePlusV leaf4097InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4097InputLogOnePlusV_eq }

private noncomputable def leaf4097Inputs : Inputs :=
  inputsOfCaches globalInput sk100RoundedInputs
    chi62InputQChi innerPair115Input
    leaf4097InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4097LowerChecked :
    lowerCheck 24 leaf4097Box leaf4097Inputs = true := by
  rfl'

private theorem leaf4097CoversExact : CoversExact 8
    leaf4097Box leaf4097Certificate leaf4097InnerLog leaf4097Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk100RoundedFacts chi62RoundedFacts
    innerPair115RoundedFacts leaf4097RoundedFacts (by rfl)

private theorem leaf4097FlatSound : Sound leaf4097Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4097CertificateValid
    leaf4097InnerLogValid leaf4097CoversExact leaf4097LowerChecked

private noncomputable def leaf4098Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (81/32), chiLo := (25/64), chiHi := (13/32) }

private noncomputable def leaf4098Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217941/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357581824) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (265248749/134217728) }, upper := { exponent := 1, mantissa := (2077/2048) } }, logOuter := sk99LogOuterCertificate, logK := sk99LogKCertificate, logChi := chi63LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716304383/68715163648) } }, logDArg := sk99LogDArgCertificate }

private noncomputable def leaf4098InnerLog : WideLogData :=
  innerPair110Data

set_option maxRecDepth 1000000 in
private theorem leaf4098LocalValidity :
    LeafFacts leaf4098Box leaf4098Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4098Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357581824) }) = true
      norm_num [leaf4098Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4098CertificateValid :
    WideCertificateValid leaf4098Box leaf4098Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk99ValidityFacts chi63ValidityFacts
    leaf4098LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4098CoverageChecked :
    coverageCheck (innerAD leaf4098Box) leaf4098InnerLog = true := by
  rfl'

private theorem leaf4098InnerLogValid :
    leaf4098InnerLog.Valid 8 (innerAD leaf4098Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint72PositiveFacts.valid leaf4098CoverageChecked

private noncomputable def leaf4098InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629359/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4098InputLogOnePlusV_eq :
    leaf4098InputLogOnePlusV = outerEnclosure 24
      (leaf4098Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4098RoundedFacts : LeafRoundedFacts 8
    leaf4098Certificate.logOnePlusV leaf4098InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4098InputLogOnePlusV_eq }

private noncomputable def leaf4098Inputs : Inputs :=
  inputsOfCaches globalInput sk99RoundedInputs
    chi63InputQChi innerPair110Input
    leaf4098InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4098LowerChecked :
    lowerCheck 24 leaf4098Box leaf4098Inputs = true := by
  rfl'

private theorem leaf4098CoversExact : CoversExact 8
    leaf4098Box leaf4098Certificate leaf4098InnerLog leaf4098Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk99RoundedFacts chi63RoundedFacts
    innerPair110RoundedFacts leaf4098RoundedFacts (by rfl)

private theorem leaf4098FlatSound : Sound leaf4098Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4098CertificateValid
    leaf4098InnerLogValid leaf4098CoversExact leaf4098LowerChecked

private noncomputable def leaf4099Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (81/32), kHi := (41/16), chiLo := (25/64), chiHi := (13/32) }

private noncomputable def leaf4099Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217943/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357555200) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (266887047/134217728) }, upper := { exponent := 1, mantissa := (1045/1024) } }, logOuter := sk100LogOuterCertificate, logK := sk100LogKCertificate, logChi := chi63LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716277759/68715110400) } }, logDArg := sk100LogDArgCertificate }

private noncomputable def leaf4099InnerLog : WideLogData :=
  innerPair110Data

set_option maxRecDepth 1000000 in
private theorem leaf4099LocalValidity :
    LeafFacts leaf4099Box leaf4099Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4099Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357555200) }) = true
      norm_num [leaf4099Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4099CertificateValid :
    WideCertificateValid leaf4099Box leaf4099Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk100ValidityFacts chi63ValidityFacts
    leaf4099LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4099CoverageChecked :
    coverageCheck (innerAD leaf4099Box) leaf4099InnerLog = true := by
  rfl'

private theorem leaf4099InnerLogValid :
    leaf4099InnerLog.Valid 8 (innerAD leaf4099Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint72PositiveFacts.valid leaf4099CoverageChecked

private noncomputable def leaf4099InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814683/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4099InputLogOnePlusV_eq :
    leaf4099InputLogOnePlusV = outerEnclosure 24
      (leaf4099Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4099RoundedFacts : LeafRoundedFacts 8
    leaf4099Certificate.logOnePlusV leaf4099InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4099InputLogOnePlusV_eq }

private noncomputable def leaf4099Inputs : Inputs :=
  inputsOfCaches globalInput sk100RoundedInputs
    chi63InputQChi innerPair110Input
    leaf4099InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4099LowerChecked :
    lowerCheck 24 leaf4099Box leaf4099Inputs = true := by
  rfl'

private theorem leaf4099CoversExact : CoversExact 8
    leaf4099Box leaf4099Certificate leaf4099InnerLog leaf4099Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk100RoundedFacts chi63RoundedFacts
    innerPair110RoundedFacts leaf4099RoundedFacts (by rfl)

private theorem leaf4099FlatSound : Sound leaf4099Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4099CertificateValid
    leaf4099InnerLogValid leaf4099CoversExact leaf4099LowerChecked

private noncomputable def leaf4100Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (83/32), chiLo := (3/8), chiHi := (25/64) }

private noncomputable def leaf4100Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217943/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357613568) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (263151723/134217728) }, upper := { exponent := 1, mantissa := (4123/4096) } }, logOuter := sk101LogOuterCertificate, logK := sk101LogKCertificate, logChi := chi62LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716336127/68715227136) } }, logDArg := sk101LogDArgCertificate }

private noncomputable def leaf4100InnerLog : WideLogData :=
  innerPair241Data

set_option maxRecDepth 1000000 in
private theorem leaf4100LocalValidity :
    LeafFacts leaf4100Box leaf4100Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4100Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357613568) }) = true
      norm_num [leaf4100Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4100CertificateValid :
    WideCertificateValid leaf4100Box leaf4100Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk101ValidityFacts chi62ValidityFacts
    leaf4100LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4100CoverageChecked :
    coverageCheck (innerAD leaf4100Box) leaf4100InnerLog = true := by
  rfl'

private theorem leaf4100InnerLogValid :
    leaf4100InnerLog.Valid 8 (innerAD leaf4100Box) :=
  wideLogDataValid_of_cachedCheck endpoint71PositiveFacts
    endpoint283PositiveFacts.valid leaf4100CoverageChecked

private noncomputable def leaf4100InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (1453669/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf4100InputLogOnePlusV_eq :
    leaf4100InputLogOnePlusV = outerEnclosure 24
      (leaf4100Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4100RoundedFacts : LeafRoundedFacts 8
    leaf4100Certificate.logOnePlusV leaf4100InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4100InputLogOnePlusV_eq }

private noncomputable def leaf4100Inputs : Inputs :=
  inputsOfCaches globalInput sk101RoundedInputs
    chi62InputQChi innerPair241Input
    leaf4100InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4100LowerChecked :
    lowerCheck 24 leaf4100Box leaf4100Inputs = true := by
  rfl'

private theorem leaf4100CoversExact : CoversExact 8
    leaf4100Box leaf4100Certificate leaf4100InnerLog leaf4100Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk101RoundedFacts chi62RoundedFacts
    innerPair241RoundedFacts leaf4100RoundedFacts (by rfl)

private theorem leaf4100FlatSound : Sound leaf4100Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4100CertificateValid
    leaf4100InnerLogValid leaf4100CoversExact leaf4100LowerChecked

private noncomputable def leaf4101Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (83/32), kHi := (21/8), chiLo := (3/8), chiHi := (25/64) }

private noncomputable def leaf4101Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217945/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357587968) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (264724489/134217728) }, upper := { exponent := 1, mantissa := (1037/1024) } }, logOuter := sk102LogOuterCertificate, logK := sk102LogKCertificate, logChi := chi62LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716310527/68715175936) } }, logDArg := sk102LogDArgCertificate }

private noncomputable def leaf4101InnerLog : WideLogData :=
  innerPair317Data

set_option maxRecDepth 1000000 in
private theorem leaf4101LocalValidity :
    LeafFacts leaf4101Box leaf4101Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4101Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357587968) }) = true
      norm_num [leaf4101Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4101CertificateValid :
    WideCertificateValid leaf4101Box leaf4101Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk102ValidityFacts chi62ValidityFacts
    leaf4101LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4101CoverageChecked :
    coverageCheck (innerAD leaf4101Box) leaf4101InnerLog = true := by
  rfl'

private theorem leaf4101InnerLogValid :
    leaf4101InnerLog.Valid 8 (innerAD leaf4101Box) :=
  wideLogDataValid_of_cachedCheck endpoint85PositiveFacts
    endpoint82PositiveFacts.valid leaf4101CoverageChecked

private noncomputable def leaf4101InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814679/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4101InputLogOnePlusV_eq :
    leaf4101InputLogOnePlusV = outerEnclosure 24
      (leaf4101Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4101RoundedFacts : LeafRoundedFacts 8
    leaf4101Certificate.logOnePlusV leaf4101InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4101InputLogOnePlusV_eq }

private noncomputable def leaf4101Inputs : Inputs :=
  inputsOfCaches globalInput sk102RoundedInputs
    chi62InputQChi innerPair317Input
    leaf4101InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4101LowerChecked :
    lowerCheck 24 leaf4101Box leaf4101Inputs = true := by
  rfl'

private theorem leaf4101CoversExact : CoversExact 8
    leaf4101Box leaf4101Certificate leaf4101InnerLog leaf4101Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk102RoundedFacts chi62RoundedFacts
    innerPair317RoundedFacts leaf4101RoundedFacts (by rfl)

private theorem leaf4101FlatSound : Sound leaf4101Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4101CertificateValid
    leaf4101InnerLogValid leaf4101CoversExact leaf4101LowerChecked

private noncomputable def leaf4102Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (83/32), chiLo := (25/64), chiHi := (13/32) }

private noncomputable def leaf4102Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217945/134217728) }, vSqrt := { lower := (32765/32768), upper := (4908388937/4908218368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (268525345/268435456) }, upper := { exponent := 1, mantissa := (2103/2048) } }, logOuter := sk101LogOuterCertificate, logK := sk101LogKCertificate, logChi := chi63LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (9816607305/9816436736) } }, logDArg := sk101LogDArgCertificate }

private noncomputable def leaf4102InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4102LocalValidity :
    LeafFacts leaf4102Box leaf4102Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4102Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4908388937/4908218368) }) = true
      norm_num [leaf4102Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4102CertificateValid :
    WideCertificateValid leaf4102Box leaf4102Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk101ValidityFacts chi63ValidityFacts
    leaf4102LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4102CoverageChecked :
    coverageCheck (innerAD leaf4102Box) leaf4102InnerLog = true := by
  rfl'

private theorem leaf4102InnerLogValid :
    leaf4102InnerLog.Valid 8 (innerAD leaf4102Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4102CoverageChecked

private noncomputable def leaf4102InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907343/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4102InputLogOnePlusV_eq :
    leaf4102InputLogOnePlusV = outerEnclosure 24
      (leaf4102Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4102RoundedFacts : LeafRoundedFacts 8
    leaf4102Certificate.logOnePlusV leaf4102InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4102InputLogOnePlusV_eq }

private noncomputable def leaf4102Inputs : Inputs :=
  inputsOfCaches globalInput sk101RoundedInputs
    chi63InputQChi innerPair116Input
    leaf4102InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4102LowerChecked :
    lowerCheck 24 leaf4102Box leaf4102Inputs = true := by
  rfl'

private theorem leaf4102CoversExact : CoversExact 8
    leaf4102Box leaf4102Certificate leaf4102InnerLog leaf4102Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk101RoundedFacts chi63RoundedFacts
    innerPair116RoundedFacts leaf4102RoundedFacts (by rfl)

private theorem leaf4102FlatSound : Sound leaf4102Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4102CertificateValid
    leaf4102InnerLogValid leaf4102CoversExact leaf4102LowerChecked

private noncomputable def leaf4103Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (83/32), kHi := (21/8), chiLo := (25/64), chiHi := (13/32) }

private noncomputable def leaf4103Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217947/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357501952) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (270163643/268435456) }, upper := { exponent := 1, mantissa := (529/512) } }, logOuter := sk102LogOuterCertificate, logK := sk102LogKCertificate, logChi := chi63LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716224511/68715003904) } }, logDArg := sk102LogDArgCertificate }

private noncomputable def leaf4103InnerLog : WideLogData :=
  innerPair120Data

set_option maxRecDepth 1000000 in
private theorem leaf4103LocalValidity :
    LeafFacts leaf4103Box leaf4103Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4103Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357501952) }) = true
      norm_num [leaf4103Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4103CertificateValid :
    WideCertificateValid leaf4103Box leaf4103Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk102ValidityFacts chi63ValidityFacts
    leaf4103LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4103CoverageChecked :
    coverageCheck (innerAD leaf4103Box) leaf4103InnerLog = true := by
  rfl'

private theorem leaf4103InnerLogValid :
    leaf4103InnerLog.Valid 8 (innerAD leaf4103Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint86PositiveFacts.valid leaf4103CoverageChecked

private noncomputable def leaf4103InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629379/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4103InputLogOnePlusV_eq :
    leaf4103InputLogOnePlusV = outerEnclosure 24
      (leaf4103Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4103RoundedFacts : LeafRoundedFacts 8
    leaf4103Certificate.logOnePlusV leaf4103InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4103InputLogOnePlusV_eq }

private noncomputable def leaf4103Inputs : Inputs :=
  inputsOfCaches globalInput sk102RoundedInputs
    chi63InputQChi innerPair120Input
    leaf4103InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4103LowerChecked :
    lowerCheck 24 leaf4103Box leaf4103Inputs = true := by
  rfl'

private theorem leaf4103CoversExact : CoversExact 8
    leaf4103Box leaf4103Certificate leaf4103InnerLog leaf4103Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk102RoundedFacts chi63RoundedFacts
    innerPair120RoundedFacts leaf4103RoundedFacts (by rfl)

private theorem leaf4103FlatSound : Sound leaf4103Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4103CertificateValid
    leaf4103InnerLogValid leaf4103CoversExact leaf4103LowerChecked

private noncomputable def leaf4104Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (81/32), chiLo := (13/32), chiHi := (27/64) }

private noncomputable def leaf4104Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217943/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357498880) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (270491307/268435456) }, upper := { exponent := 1, mantissa := (4235/4096) } }, logOuter := sk99LogOuterCertificate, logK := sk99LogKCertificate, logChi := chi64LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716221439/68714997760) } }, logDArg := sk99LogDArgCertificate }

private noncomputable def leaf4104InnerLog : WideLogData :=
  innerPair117Data

set_option maxRecDepth 1000000 in
private theorem leaf4104LocalValidity :
    LeafFacts leaf4104Box leaf4104Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4104Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357498880) }) = true
      norm_num [leaf4104Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4104CertificateValid :
    WideCertificateValid leaf4104Box leaf4104Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk99ValidityFacts chi64ValidityFacts
    leaf4104LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4104CoverageChecked :
    coverageCheck (innerAD leaf4104Box) leaf4104InnerLog = true := by
  rfl'

private theorem leaf4104InnerLogValid :
    leaf4104InnerLog.Valid 8 (innerAD leaf4104Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint73PositiveFacts.valid leaf4104CoverageChecked

private noncomputable def leaf4104InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907345/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4104InputLogOnePlusV_eq :
    leaf4104InputLogOnePlusV = outerEnclosure 24
      (leaf4104Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4104RoundedFacts : LeafRoundedFacts 8
    leaf4104Certificate.logOnePlusV leaf4104InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4104InputLogOnePlusV_eq }

private noncomputable def leaf4104Inputs : Inputs :=
  inputsOfCaches globalInput sk99RoundedInputs
    chi64InputQChi innerPair117Input
    leaf4104InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4104LowerChecked :
    lowerCheck 24 leaf4104Box leaf4104Inputs = true := by
  rfl'

private theorem leaf4104CoversExact : CoversExact 8
    leaf4104Box leaf4104Certificate leaf4104InnerLog leaf4104Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk99RoundedFacts chi64RoundedFacts
    innerPair117RoundedFacts leaf4104RoundedFacts (by rfl)

private theorem leaf4104FlatSound : Sound leaf4104Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4104CertificateValid
    leaf4104InnerLogValid leaf4104CoversExact leaf4104LowerChecked

private noncomputable def leaf4105Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (81/32), kHi := (41/16), chiLo := (13/32), chiHi := (27/64) }

private noncomputable def leaf4105Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217945/134217728) }, vSqrt := { lower := (32765/32768), upper := (4908388937/4908210176) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (272195137/268435456) }, upper := { exponent := 1, mantissa := (2131/2048) } }, logOuter := sk100LogOuterCertificate, logK := sk100LogKCertificate, logChi := chi64LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (9816599113/9816420352) } }, logDArg := sk100LogDArgCertificate }

private noncomputable def leaf4105InnerLog : WideLogData :=
  innerPair117Data

set_option maxRecDepth 1000000 in
private theorem leaf4105LocalValidity :
    LeafFacts leaf4105Box leaf4105Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4105Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4908388937/4908210176) }) = true
      norm_num [leaf4105Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4105CertificateValid :
    WideCertificateValid leaf4105Box leaf4105Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk100ValidityFacts chi64ValidityFacts
    leaf4105LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4105CoverageChecked :
    coverageCheck (innerAD leaf4105Box) leaf4105InnerLog = true := by
  rfl'

private theorem leaf4105InnerLogValid :
    leaf4105InnerLog.Valid 8 (innerAD leaf4105Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint73PositiveFacts.valid leaf4105CoverageChecked

private noncomputable def leaf4105InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814693/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4105InputLogOnePlusV_eq :
    leaf4105InputLogOnePlusV = outerEnclosure 24
      (leaf4105Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4105RoundedFacts : LeafRoundedFacts 8
    leaf4105Certificate.logOnePlusV leaf4105InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4105InputLogOnePlusV_eq }

private noncomputable def leaf4105Inputs : Inputs :=
  inputsOfCaches globalInput sk100RoundedInputs
    chi64InputQChi innerPair117Input
    leaf4105InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4105LowerChecked :
    lowerCheck 24 leaf4105Box leaf4105Inputs = true := by
  rfl'

private theorem leaf4105CoversExact : CoversExact 8
    leaf4105Box leaf4105Certificate leaf4105InnerLog leaf4105Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk100RoundedFacts chi64RoundedFacts
    innerPair117RoundedFacts leaf4105RoundedFacts (by rfl)

private theorem leaf4105FlatSound : Sound leaf4105Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4105CertificateValid
    leaf4105InnerLogValid leaf4105CoversExact leaf4105LowerChecked

private noncomputable def leaf4106Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (81/32), chiLo := (27/64), chiHi := (7/16) }

private noncomputable def leaf4106Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217945/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357415936) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (275733865/268435456) }, upper := { exponent := 1, mantissa := (1079/1024) } }, logOuter := sk99LogOuterCertificate, logK := sk99LogKCertificate, logChi := chi65LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716138495/68714831872) } }, logDArg := sk99LogDArgCertificate }

private noncomputable def leaf4106InnerLog : WideLogData :=
  innerPair117Data

set_option maxRecDepth 1000000 in
private theorem leaf4106LocalValidity :
    LeafFacts leaf4106Box leaf4106Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4106Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357415936) }) = true
      norm_num [leaf4106Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4106CertificateValid :
    WideCertificateValid leaf4106Box leaf4106Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk99ValidityFacts chi65ValidityFacts
    leaf4106LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4106CoverageChecked :
    coverageCheck (innerAD leaf4106Box) leaf4106InnerLog = true := by
  rfl'

private theorem leaf4106InnerLogValid :
    leaf4106InnerLog.Valid 8 (innerAD leaf4106Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint73PositiveFacts.valid leaf4106CoverageChecked

private noncomputable def leaf4106InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (1453675/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf4106InputLogOnePlusV_eq :
    leaf4106InputLogOnePlusV = outerEnclosure 24
      (leaf4106Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4106RoundedFacts : LeafRoundedFacts 8
    leaf4106Certificate.logOnePlusV leaf4106InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4106InputLogOnePlusV_eq }

private noncomputable def leaf4106Inputs : Inputs :=
  inputsOfCaches globalInput sk99RoundedInputs
    chi65InputQChi innerPair117Input
    leaf4106InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4106LowerChecked :
    lowerCheck 24 leaf4106Box leaf4106Inputs = true := by
  rfl'

private theorem leaf4106CoversExact : CoversExact 8
    leaf4106Box leaf4106Certificate leaf4106InnerLog leaf4106Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk99RoundedFacts chi65RoundedFacts
    innerPair117RoundedFacts leaf4106RoundedFacts (by rfl)

private theorem leaf4106FlatSound : Sound leaf4106Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4106CertificateValid
    leaf4106InnerLogValid leaf4106CoversExact leaf4106LowerChecked

private noncomputable def leaf4107Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (81/32), kHi := (41/16), chiLo := (27/64), chiHi := (7/16) }

private noncomputable def leaf4107Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217947/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357387264) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (277503227/268435456) }, upper := { exponent := 1, mantissa := (543/512) } }, logOuter := sk100LogOuterCertificate, logK := sk100LogKCertificate, logChi := chi65LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716109823/68714774528) } }, logDArg := sk100LogDArgCertificate }

private noncomputable def leaf4107InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4107LocalValidity :
    LeafFacts leaf4107Box leaf4107Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4107Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357387264) }) = true
      norm_num [leaf4107Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4107CertificateValid :
    WideCertificateValid leaf4107Box leaf4107Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk100ValidityFacts chi65ValidityFacts
    leaf4107LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4107CoverageChecked :
    coverageCheck (innerAD leaf4107Box) leaf4107InnerLog = true := by
  rfl'

private theorem leaf4107InnerLogValid :
    leaf4107InnerLog.Valid 8 (innerAD leaf4107Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4107CoverageChecked

private noncomputable def leaf4107InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629407/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4107InputLogOnePlusV_eq :
    leaf4107InputLogOnePlusV = outerEnclosure 24
      (leaf4107Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4107RoundedFacts : LeafRoundedFacts 8
    leaf4107Certificate.logOnePlusV leaf4107InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4107InputLogOnePlusV_eq }

private noncomputable def leaf4107Inputs : Inputs :=
  inputsOfCaches globalInput sk100RoundedInputs
    chi65InputQChi innerPair242Input
    leaf4107InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4107LowerChecked :
    lowerCheck 24 leaf4107Box leaf4107Inputs = true := by
  rfl'

private theorem leaf4107CoversExact : CoversExact 8
    leaf4107Box leaf4107Certificate leaf4107InnerLog leaf4107Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk100RoundedFacts chi65RoundedFacts
    innerPair242RoundedFacts leaf4107RoundedFacts (by rfl)

private theorem leaf4107FlatSound : Sound leaf4107Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4107CertificateValid
    leaf4107InnerLogValid leaf4107CoversExact leaf4107LowerChecked

private noncomputable def leaf4108Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (83/32), chiLo := (13/32), chiHi := (27/64) }

private noncomputable def leaf4108Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217947/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357443584) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (273898967/268435456) }, upper := { exponent := 1, mantissa := (4289/4096) } }, logOuter := sk101LogOuterCertificate, logK := sk101LogKCertificate, logChi := chi64LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716166143/68714887168) } }, logDArg := sk101LogDArgCertificate }

private noncomputable def leaf4108InnerLog : WideLogData :=
  innerPair117Data

set_option maxRecDepth 1000000 in
private theorem leaf4108LocalValidity :
    LeafFacts leaf4108Box leaf4108Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4108Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357443584) }) = true
      norm_num [leaf4108Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4108CertificateValid :
    WideCertificateValid leaf4108Box leaf4108Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk101ValidityFacts chi64ValidityFacts
    leaf4108LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4108CoverageChecked :
    coverageCheck (innerAD leaf4108Box) leaf4108InnerLog = true := by
  rfl'

private theorem leaf4108InnerLogValid :
    leaf4108InnerLog.Valid 8 (innerAD leaf4108Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint73PositiveFacts.valid leaf4108CoverageChecked

private noncomputable def leaf4108InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629393/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4108InputLogOnePlusV_eq :
    leaf4108InputLogOnePlusV = outerEnclosure 24
      (leaf4108Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4108RoundedFacts : LeafRoundedFacts 8
    leaf4108Certificate.logOnePlusV leaf4108InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4108InputLogOnePlusV_eq }

private noncomputable def leaf4108Inputs : Inputs :=
  inputsOfCaches globalInput sk101RoundedInputs
    chi64InputQChi innerPair117Input
    leaf4108InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4108LowerChecked :
    lowerCheck 24 leaf4108Box leaf4108Inputs = true := by
  rfl'

private theorem leaf4108CoversExact : CoversExact 8
    leaf4108Box leaf4108Certificate leaf4108InnerLog leaf4108Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk101RoundedFacts chi64RoundedFacts
    innerPair117RoundedFacts leaf4108RoundedFacts (by rfl)

private theorem leaf4108FlatSound : Sound leaf4108Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4108CertificateValid
    leaf4108InnerLogValid leaf4108CoversExact leaf4108LowerChecked

private noncomputable def leaf4109Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (83/32), kHi := (21/8), chiLo := (13/32), chiHi := (27/64) }

private noncomputable def leaf4109Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217949/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357415936) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (275602797/268435456) }, upper := { exponent := 1, mantissa := (1079/1024) } }, logOuter := sk102LogOuterCertificate, logK := sk102LogKCertificate, logChi := chi64LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716138495/68714831872) } }, logDArg := sk102LogDArgCertificate }

private noncomputable def leaf4109InnerLog : WideLogData :=
  innerPair117Data

set_option maxRecDepth 1000000 in
private theorem leaf4109LocalValidity :
    LeafFacts leaf4109Box leaf4109Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4109Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357415936) }) = true
      norm_num [leaf4109Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4109CertificateValid :
    WideCertificateValid leaf4109Box leaf4109Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk102ValidityFacts chi64ValidityFacts
    leaf4109LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4109CoverageChecked :
    coverageCheck (innerAD leaf4109Box) leaf4109InnerLog = true := by
  rfl'

private theorem leaf4109InnerLogValid :
    leaf4109InnerLog.Valid 8 (innerAD leaf4109Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint73PositiveFacts.valid leaf4109CoverageChecked

private noncomputable def leaf4109InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (1453675/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf4109InputLogOnePlusV_eq :
    leaf4109InputLogOnePlusV = outerEnclosure 24
      (leaf4109Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4109RoundedFacts : LeafRoundedFacts 8
    leaf4109Certificate.logOnePlusV leaf4109InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4109InputLogOnePlusV_eq }

private noncomputable def leaf4109Inputs : Inputs :=
  inputsOfCaches globalInput sk102RoundedInputs
    chi64InputQChi innerPair117Input
    leaf4109InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4109LowerChecked :
    lowerCheck 24 leaf4109Box leaf4109Inputs = true := by
  rfl'

private theorem leaf4109CoversExact : CoversExact 8
    leaf4109Box leaf4109Certificate leaf4109InnerLog leaf4109Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk102RoundedFacts chi64RoundedFacts
    innerPair117RoundedFacts leaf4109RoundedFacts (by rfl)

private theorem leaf4109FlatSound : Sound leaf4109Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4109CertificateValid
    leaf4109InnerLogValid leaf4109CoversExact leaf4109LowerChecked

private noncomputable def leaf4110Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (83/32), chiLo := (27/64), chiHi := (7/16) }

private noncomputable def leaf4110Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217949/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357358592) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (279272589/268435456) }, upper := { exponent := 1, mantissa := (1093/1024) } }, logOuter := sk101LogOuterCertificate, logK := sk101LogKCertificate, logChi := chi65LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716081151/68714717184) } }, logDArg := sk101LogDArgCertificate }

private noncomputable def leaf4110InnerLog : WideLogData :=
  innerPair243Data

set_option maxRecDepth 1000000 in
private theorem leaf4110LocalValidity :
    LeafFacts leaf4110Box leaf4110Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4110Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357358592) }) = true
      norm_num [leaf4110Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4110CertificateValid :
    WideCertificateValid leaf4110Box leaf4110Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk101ValidityFacts chi65ValidityFacts
    leaf4110LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4110CoverageChecked :
    coverageCheck (innerAD leaf4110Box) leaf4110InnerLog = true := by
  rfl'

private theorem leaf4110InnerLogValid :
    leaf4110InnerLog.Valid 8 (innerAD leaf4110Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint74PositiveFacts.valid leaf4110CoverageChecked

private noncomputable def leaf4110InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814707/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4110InputLogOnePlusV_eq :
    leaf4110InputLogOnePlusV = outerEnclosure 24
      (leaf4110Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4110RoundedFacts : LeafRoundedFacts 8
    leaf4110Certificate.logOnePlusV leaf4110InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4110InputLogOnePlusV_eq }

private noncomputable def leaf4110Inputs : Inputs :=
  inputsOfCaches globalInput sk101RoundedInputs
    chi65InputQChi innerPair243Input
    leaf4110InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4110LowerChecked :
    lowerCheck 24 leaf4110Box leaf4110Inputs = true := by
  rfl'

private theorem leaf4110CoversExact : CoversExact 8
    leaf4110Box leaf4110Certificate leaf4110InnerLog leaf4110Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk101RoundedFacts chi65RoundedFacts
    innerPair243RoundedFacts leaf4110RoundedFacts (by rfl)

private theorem leaf4110FlatSound : Sound leaf4110Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4110CertificateValid
    leaf4110InnerLogValid leaf4110CoversExact leaf4110LowerChecked

private noncomputable def leaf4111Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (83/32), kHi := (21/8), chiLo := (27/64), chiHi := (7/16) }

private noncomputable def leaf4111Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217951/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357329920) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (281041951/268435456) }, upper := { exponent := 1, mantissa := (275/256) } }, logOuter := sk102LogOuterCertificate, logK := sk102LogKCertificate, logChi := chi65LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716052479/68714659840) } }, logDArg := sk102LogDArgCertificate }

private noncomputable def leaf4111InnerLog : WideLogData :=
  innerPair243Data

set_option maxRecDepth 1000000 in
private theorem leaf4111LocalValidity :
    LeafFacts leaf4111Box leaf4111Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4111Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357329920) }) = true
      norm_num [leaf4111Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4111CertificateValid :
    WideCertificateValid leaf4111Box leaf4111Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk102ValidityFacts chi65ValidityFacts
    leaf4111LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4111CoverageChecked :
    coverageCheck (innerAD leaf4111Box) leaf4111InnerLog = true := by
  rfl'

private theorem leaf4111InnerLogValid :
    leaf4111InnerLog.Valid 8 (innerAD leaf4111Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint74PositiveFacts.valid leaf4111CoverageChecked

private noncomputable def leaf4111InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629421/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4111InputLogOnePlusV_eq :
    leaf4111InputLogOnePlusV = outerEnclosure 24
      (leaf4111Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4111RoundedFacts : LeafRoundedFacts 8
    leaf4111Certificate.logOnePlusV leaf4111InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4111InputLogOnePlusV_eq }

private noncomputable def leaf4111Inputs : Inputs :=
  inputsOfCaches globalInput sk102RoundedInputs
    chi65InputQChi innerPair243Input
    leaf4111InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4111LowerChecked :
    lowerCheck 24 leaf4111Box leaf4111Inputs = true := by
  rfl'

private theorem leaf4111CoversExact : CoversExact 8
    leaf4111Box leaf4111Certificate leaf4111InnerLog leaf4111Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk102RoundedFacts chi65RoundedFacts
    innerPair243RoundedFacts leaf4111RoundedFacts (by rfl)

private theorem leaf4111FlatSound : Sound leaf4111Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4111CertificateValid
    leaf4111InnerLogValid leaf4111CoversExact leaf4111LowerChecked

private noncomputable def leaf4112Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (85/32), chiLo := (3/8), chiHi := (25/64) }

private noncomputable def leaf4112Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217947/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357562368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (266297255/134217728) }, upper := { exponent := 1, mantissa := (4173/4096) } }, logOuter := sk105LogOuterCertificate, logK := sk105LogKCertificate, logChi := chi62LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716284927/68715124736) } }, logDArg := sk105LogDArgCertificate }

private noncomputable def leaf4112InnerLog : WideLogData :=
  innerPair319Data

set_option maxRecDepth 1000000 in
private theorem leaf4112LocalValidity :
    LeafFacts leaf4112Box leaf4112Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4112Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357562368) }) = true
      norm_num [leaf4112Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4112CertificateValid :
    WideCertificateValid leaf4112Box leaf4112Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk105ValidityFacts chi62ValidityFacts
    leaf4112LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4112CoverageChecked :
    coverageCheck (innerAD leaf4112Box) leaf4112InnerLog = true := by
  rfl'

private theorem leaf4112InnerLogValid :
    leaf4112InnerLog.Valid 8 (innerAD leaf4112Box) :=
  wideLogDataValid_of_cachedCheck endpoint85PositiveFacts
    endpoint87PositiveFacts.valid leaf4112CoverageChecked

private noncomputable def leaf4112InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907341/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4112InputLogOnePlusV_eq :
    leaf4112InputLogOnePlusV = outerEnclosure 24
      (leaf4112Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4112RoundedFacts : LeafRoundedFacts 8
    leaf4112Certificate.logOnePlusV leaf4112InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4112InputLogOnePlusV_eq }

private noncomputable def leaf4112Inputs : Inputs :=
  inputsOfCaches globalInput sk105RoundedInputs
    chi62InputQChi innerPair319Input
    leaf4112InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4112LowerChecked :
    lowerCheck 24 leaf4112Box leaf4112Inputs = true := by
  rfl'

private theorem leaf4112CoversExact : CoversExact 8
    leaf4112Box leaf4112Certificate leaf4112InnerLog leaf4112Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk105RoundedFacts chi62RoundedFacts
    innerPair319RoundedFacts leaf4112RoundedFacts (by rfl)

private theorem leaf4112FlatSound : Sound leaf4112Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4112CertificateValid
    leaf4112InnerLogValid leaf4112CoversExact leaf4112LowerChecked

private noncomputable def leaf4113Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (85/32), kHi := (43/16), chiLo := (3/8), chiHi := (25/64) }

private noncomputable def leaf4113Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217949/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357536768) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (267870021/134217728) }, upper := { exponent := 1, mantissa := (2099/2048) } }, logOuter := sk106LogOuterCertificate, logK := sk106LogKCertificate, logChi := chi62LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716259327/68715073536) } }, logDArg := sk106LogDArgCertificate }

private noncomputable def leaf4113InnerLog : WideLogData :=
  innerPair544Data

set_option maxRecDepth 1000000 in
private theorem leaf4113LocalValidity :
    LeafFacts leaf4113Box leaf4113Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4113Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357536768) }) = true
      norm_num [leaf4113Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4113CertificateValid :
    WideCertificateValid leaf4113Box leaf4113Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk106ValidityFacts chi62ValidityFacts
    leaf4113LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4113CoverageChecked :
    coverageCheck (innerAD leaf4113Box) leaf4113InnerLog = true := by
  rfl'

private theorem leaf4113InnerLogValid :
    leaf4113InnerLog.Valid 8 (innerAD leaf4113Box) :=
  wideLogDataValid_of_cachedCheck endpoint278PositiveFacts
    endpoint288PositiveFacts.valid leaf4113CoverageChecked

private noncomputable def leaf4113InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814685/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4113InputLogOnePlusV_eq :
    leaf4113InputLogOnePlusV = outerEnclosure 24
      (leaf4113Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4113RoundedFacts : LeafRoundedFacts 8
    leaf4113Certificate.logOnePlusV leaf4113InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4113InputLogOnePlusV_eq }

private noncomputable def leaf4113Inputs : Inputs :=
  inputsOfCaches globalInput sk106RoundedInputs
    chi62InputQChi innerPair544Input
    leaf4113InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4113LowerChecked :
    lowerCheck 24 leaf4113Box leaf4113Inputs = true := by
  rfl'

private theorem leaf4113CoversExact : CoversExact 8
    leaf4113Box leaf4113Certificate leaf4113InnerLog leaf4113Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk106RoundedFacts chi62RoundedFacts
    innerPair544RoundedFacts leaf4113RoundedFacts (by rfl)

private theorem leaf4113FlatSound : Sound leaf4113Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4113CertificateValid
    leaf4113InnerLogValid leaf4113CoversExact leaf4113LowerChecked

private noncomputable def leaf4114Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (85/32), chiLo := (25/64), chiHi := (13/32) }

private noncomputable def leaf4114Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217949/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357475328) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (271801941/268435456) }, upper := { exponent := 1, mantissa := (2129/2048) } }, logOuter := sk105LogOuterCertificate, logK := sk105LogKCertificate, logChi := chi63LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716197887/68714950656) } }, logDArg := sk105LogDArgCertificate }

private noncomputable def leaf4114InnerLog : WideLogData :=
  innerPair549Data

set_option maxRecDepth 1000000 in
private theorem leaf4114LocalValidity :
    LeafFacts leaf4114Box leaf4114Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4114Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357475328) }) = true
      norm_num [leaf4114Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4114CertificateValid :
    WideCertificateValid leaf4114Box leaf4114Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk105ValidityFacts chi63ValidityFacts
    leaf4114LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4114CoverageChecked :
    coverageCheck (innerAD leaf4114Box) leaf4114InnerLog = true := by
  rfl'

private theorem leaf4114InnerLogValid :
    leaf4114InnerLog.Valid 8 (innerAD leaf4114Box) :=
  wideLogDataValid_of_cachedCheck endpoint283PositiveFacts
    endpoint284PositiveFacts.valid leaf4114CoverageChecked

private noncomputable def leaf4114InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629385/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4114InputLogOnePlusV_eq :
    leaf4114InputLogOnePlusV = outerEnclosure 24
      (leaf4114Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4114RoundedFacts : LeafRoundedFacts 8
    leaf4114Certificate.logOnePlusV leaf4114InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4114InputLogOnePlusV_eq }

private noncomputable def leaf4114Inputs : Inputs :=
  inputsOfCaches globalInput sk105RoundedInputs
    chi63InputQChi innerPair549Input
    leaf4114InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4114LowerChecked :
    lowerCheck 24 leaf4114Box leaf4114Inputs = true := by
  rfl'

private theorem leaf4114CoversExact : CoversExact 8
    leaf4114Box leaf4114Certificate leaf4114InnerLog leaf4114Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk105RoundedFacts chi63RoundedFacts
    innerPair549RoundedFacts leaf4114RoundedFacts (by rfl)

private theorem leaf4114FlatSound : Sound leaf4114Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4114CertificateValid
    leaf4114InnerLogValid leaf4114CoversExact leaf4114LowerChecked

private noncomputable def leaf4115Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (85/32), kHi := (43/16), chiLo := (25/64), chiHi := (13/32) }

private noncomputable def leaf4115Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217951/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357448704) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (273440239/268435456) }, upper := { exponent := 1, mantissa := (1071/1024) } }, logOuter := sk106LogOuterCertificate, logK := sk106LogKCertificate, logChi := chi63LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716171263/68714897408) } }, logDArg := sk106LogDArgCertificate }

private noncomputable def leaf4115InnerLog : WideLogData :=
  innerPair312Data

set_option maxRecDepth 1000000 in
private theorem leaf4115LocalValidity :
    LeafFacts leaf4115Box leaf4115Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4115Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357448704) }) = true
      norm_num [leaf4115Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4115CertificateValid :
    WideCertificateValid leaf4115Box leaf4115Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk106ValidityFacts chi63ValidityFacts
    leaf4115LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4115CoverageChecked :
    coverageCheck (innerAD leaf4115Box) leaf4115InnerLog = true := by
  rfl'

private theorem leaf4115InnerLogValid :
    leaf4115InnerLog.Valid 8 (innerAD leaf4115Box) :=
  wideLogDataValid_of_cachedCheck endpoint82PositiveFacts
    endpoint284PositiveFacts.valid leaf4115CoverageChecked

private noncomputable def leaf4115InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (726837/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf4115InputLogOnePlusV_eq :
    leaf4115InputLogOnePlusV = outerEnclosure 24
      (leaf4115Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4115RoundedFacts : LeafRoundedFacts 8
    leaf4115Certificate.logOnePlusV leaf4115InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4115InputLogOnePlusV_eq }

private noncomputable def leaf4115Inputs : Inputs :=
  inputsOfCaches globalInput sk106RoundedInputs
    chi63InputQChi innerPair312Input
    leaf4115InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4115LowerChecked :
    lowerCheck 24 leaf4115Box leaf4115Inputs = true := by
  rfl'

private theorem leaf4115CoversExact : CoversExact 8
    leaf4115Box leaf4115Certificate leaf4115InnerLog leaf4115Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk106RoundedFacts chi63RoundedFacts
    innerPair312RoundedFacts leaf4115RoundedFacts (by rfl)

private theorem leaf4115FlatSound : Sound leaf4115Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4115CertificateValid
    leaf4115InnerLogValid leaf4115CoversExact leaf4115LowerChecked

private noncomputable def leaf4116Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (87/32), chiLo := (3/8), chiHi := (25/64) }

private noncomputable def leaf4116Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217951/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357511168) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (269442787/268435456) }, upper := { exponent := 1, mantissa := (4223/4096) } }, logOuter := sk103LogOuterCertificate, logK := sk103LogKCertificate, logChi := chi62LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716233727/68715022336) } }, logDArg := sk103LogDArgCertificate }

private noncomputable def leaf4116InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4116LocalValidity :
    LeafFacts leaf4116Box leaf4116Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4116Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357511168) }) = true
      norm_num [leaf4116Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4116CertificateValid :
    WideCertificateValid leaf4116Box leaf4116Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk103ValidityFacts chi62ValidityFacts
    leaf4116LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4116CoverageChecked :
    coverageCheck (innerAD leaf4116Box) leaf4116InnerLog = true := by
  rfl'

private theorem leaf4116InnerLogValid :
    leaf4116InnerLog.Valid 8 (innerAD leaf4116Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4116CoverageChecked

private noncomputable def leaf4116InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629377/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4116InputLogOnePlusV_eq :
    leaf4116InputLogOnePlusV = outerEnclosure 24
      (leaf4116Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4116RoundedFacts : LeafRoundedFacts 8
    leaf4116Certificate.logOnePlusV leaf4116InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4116InputLogOnePlusV_eq }

private noncomputable def leaf4116Inputs : Inputs :=
  inputsOfCaches globalInput sk103RoundedInputs
    chi62InputQChi innerPair116Input
    leaf4116InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4116LowerChecked :
    lowerCheck 24 leaf4116Box leaf4116Inputs = true := by
  rfl'

private theorem leaf4116CoversExact : CoversExact 8
    leaf4116Box leaf4116Certificate leaf4116InnerLog leaf4116Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk103RoundedFacts chi62RoundedFacts
    innerPair116RoundedFacts leaf4116RoundedFacts (by rfl)

private theorem leaf4116FlatSound : Sound leaf4116Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4116CertificateValid
    leaf4116InnerLogValid leaf4116CoversExact leaf4116LowerChecked

private noncomputable def leaf4117Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (87/32), kHi := (11/4), chiLo := (3/8), chiHi := (49/128) }

private noncomputable def leaf4117Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435729/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357530624) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (542064049/536870912) }, upper := { exponent := 1, mantissa := (1051/1024) } }, logOuter := sk104LogOuterCertificate, logK := sk104LogKCertificate, logChi := chi259LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716253183/68715061248) } }, logDArg := sk104LogDArgCertificate }

private noncomputable def leaf4117InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4117LocalValidity :
    LeafFacts leaf4117Box leaf4117Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4117Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357530624) }) = true
      norm_num [leaf4117Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4117CertificateValid :
    WideCertificateValid leaf4117Box leaf4117Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk104ValidityFacts chi259ValidityFacts
    leaf4117LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4117CoverageChecked :
    coverageCheck (innerAD leaf4117Box) leaf4117InnerLog = true := by
  rfl'

private theorem leaf4117InnerLogValid :
    leaf4117InnerLog.Valid 8 (innerAD leaf4117Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4117CoverageChecked

private noncomputable def leaf4117InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907343/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4117InputLogOnePlusV_eq :
    leaf4117InputLogOnePlusV = outerEnclosure 24
      (leaf4117Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4117RoundedFacts : LeafRoundedFacts 8
    leaf4117Certificate.logOnePlusV leaf4117InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4117InputLogOnePlusV_eq }

private noncomputable def leaf4117Inputs : Inputs :=
  inputsOfCaches globalInput sk104RoundedInputs
    chi259InputQChi innerPair116Input
    leaf4117InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4117LowerChecked :
    lowerCheck 24 leaf4117Box leaf4117Inputs = true := by
  rfl'

private theorem leaf4117CoversExact : CoversExact 8
    leaf4117Box leaf4117Certificate leaf4117InnerLog leaf4117Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk104RoundedFacts chi259RoundedFacts
    innerPair116RoundedFacts leaf4117RoundedFacts (by rfl)

private theorem leaf4117FlatSound : Sound leaf4117Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4117CertificateValid
    leaf4117InnerLogValid leaf4117CoversExact leaf4117LowerChecked

private noncomputable def leaf4118Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (87/32), kHi := (11/4), chiLo := (49/128), chiHi := (25/64) }

private noncomputable def leaf4118Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435731/268435456) }, vSqrt := { lower := (32765/32768), upper := (4908388937/4908212224) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (547765331/536870912) }, upper := { exponent := 1, mantissa := (531/512) } }, logOuter := sk104LogOuterCertificate, logK := sk104LogKCertificate, logChi := chi260LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (9816601161/9816424448) } }, logDArg := sk104LogDArgCertificate }

private noncomputable def leaf4118InnerLog : WideLogData :=
  innerPair117Data

set_option maxRecDepth 1000000 in
private theorem leaf4118LocalValidity :
    LeafFacts leaf4118Box leaf4118Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4118Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4908388937/4908212224) }) = true
      norm_num [leaf4118Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4118CertificateValid :
    WideCertificateValid leaf4118Box leaf4118Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk104ValidityFacts chi260ValidityFacts
    leaf4118LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4118CoverageChecked :
    coverageCheck (innerAD leaf4118Box) leaf4118InnerLog = true := by
  rfl'

private theorem leaf4118InnerLogValid :
    leaf4118InnerLog.Valid 8 (innerAD leaf4118Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint73PositiveFacts.valid leaf4118CoverageChecked

private noncomputable def leaf4118InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629383/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4118InputLogOnePlusV_eq :
    leaf4118InputLogOnePlusV = outerEnclosure 24
      (leaf4118Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4118RoundedFacts : LeafRoundedFacts 8
    leaf4118Certificate.logOnePlusV leaf4118InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4118InputLogOnePlusV_eq }

private noncomputable def leaf4118Inputs : Inputs :=
  inputsOfCaches globalInput sk104RoundedInputs
    chi260InputQChi innerPair117Input
    leaf4118InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4118LowerChecked :
    lowerCheck 24 leaf4118Box leaf4118Inputs = true := by
  rfl'

private theorem leaf4118CoversExact : CoversExact 8
    leaf4118Box leaf4118Certificate leaf4118InnerLog leaf4118Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk104RoundedFacts chi260RoundedFacts
    innerPair117RoundedFacts leaf4118RoundedFacts (by rfl)

private theorem leaf4118FlatSound : Sound leaf4118Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4118CertificateValid
    leaf4118InnerLogValid leaf4118CoversExact leaf4118LowerChecked

private noncomputable def leaf4119Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (87/32), chiLo := (25/64), chiHi := (51/128) }

private noncomputable def leaf4119Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435731/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357466624) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (550190015/536870912) }, upper := { exponent := 1, mantissa := (8533/8192) } }, logOuter := sk103LogOuterCertificate, logK := sk103LogKCertificate, logChi := chi261LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716189183/68714933248) } }, logDArg := sk103LogDArgCertificate }

private noncomputable def leaf4119InnerLog : WideLogData :=
  innerPair117Data

set_option maxRecDepth 1000000 in
private theorem leaf4119LocalValidity :
    LeafFacts leaf4119Box leaf4119Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4119Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357466624) }) = true
      norm_num [leaf4119Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4119CertificateValid :
    WideCertificateValid leaf4119Box leaf4119Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk103ValidityFacts chi261ValidityFacts
    leaf4119LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4119CoverageChecked :
    coverageCheck (innerAD leaf4119Box) leaf4119InnerLog = true := by
  rfl'

private theorem leaf4119InnerLogValid :
    leaf4119InnerLog.Valid 8 (innerAD leaf4119Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint73PositiveFacts.valid leaf4119CoverageChecked

private noncomputable def leaf4119InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629387/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4119InputLogOnePlusV_eq :
    leaf4119InputLogOnePlusV = outerEnclosure 24
      (leaf4119Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4119RoundedFacts : LeafRoundedFacts 8
    leaf4119Certificate.logOnePlusV leaf4119InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4119InputLogOnePlusV_eq }

private noncomputable def leaf4119Inputs : Inputs :=
  inputsOfCaches globalInput sk103RoundedInputs
    chi261InputQChi innerPair117Input
    leaf4119InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4119LowerChecked :
    lowerCheck 24 leaf4119Box leaf4119Inputs = true := by
  rfl'

private theorem leaf4119CoversExact : CoversExact 8
    leaf4119Box leaf4119Certificate leaf4119InnerLog leaf4119Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk103RoundedFacts chi261RoundedFacts
    innerPair117RoundedFacts leaf4119RoundedFacts (by rfl)

private theorem leaf4119FlatSound : Sound leaf4119Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4119CertificateValid
    leaf4119InnerLogValid leaf4119CoversExact leaf4119LowerChecked

private noncomputable def leaf4120Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (87/32), kHi := (11/4), chiLo := (25/64), chiHi := (51/128) }

private noncomputable def leaf4120Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435733/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357440512) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (553466613/536870912) }, upper := { exponent := 1, mantissa := (1073/1024) } }, logOuter := sk104LogOuterCertificate, logK := sk104LogKCertificate, logChi := chi261LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716163071/68714881024) } }, logDArg := sk104LogDArgCertificate }

private noncomputable def leaf4120InnerLog : WideLogData :=
  innerPair117Data

set_option maxRecDepth 1000000 in
private theorem leaf4120LocalValidity :
    LeafFacts leaf4120Box leaf4120Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4120Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357440512) }) = true
      norm_num [leaf4120Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4120CertificateValid :
    WideCertificateValid leaf4120Box leaf4120Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk104ValidityFacts chi261ValidityFacts
    leaf4120LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4120CoverageChecked :
    coverageCheck (innerAD leaf4120Box) leaf4120InnerLog = true := by
  rfl'

private theorem leaf4120InnerLogValid :
    leaf4120InnerLog.Valid 8 (innerAD leaf4120Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint73PositiveFacts.valid leaf4120CoverageChecked

private noncomputable def leaf4120InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814697/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4120InputLogOnePlusV_eq :
    leaf4120InputLogOnePlusV = outerEnclosure 24
      (leaf4120Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4120RoundedFacts : LeafRoundedFacts 8
    leaf4120Certificate.logOnePlusV leaf4120InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4120InputLogOnePlusV_eq }

private noncomputable def leaf4120Inputs : Inputs :=
  inputsOfCaches globalInput sk104RoundedInputs
    chi261InputQChi innerPair117Input
    leaf4120InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4120LowerChecked :
    lowerCheck 24 leaf4120Box leaf4120Inputs = true := by
  rfl'

private theorem leaf4120CoversExact : CoversExact 8
    leaf4120Box leaf4120Certificate leaf4120InnerLog leaf4120Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk104RoundedFacts chi261RoundedFacts
    innerPair117RoundedFacts leaf4120RoundedFacts (by rfl)

private theorem leaf4120FlatSound : Sound leaf4120Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4120CertificateValid
    leaf4120InnerLogValid leaf4120CoversExact leaf4120LowerChecked

private noncomputable def leaf4121Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (87/32), chiLo := (51/128), chiHi := (13/32) }

private noncomputable def leaf4121Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435733/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357422080) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (555825765/536870912) }, upper := { exponent := 1, mantissa := (2155/2048) } }, logOuter := sk103LogOuterCertificate, logK := sk103LogKCertificate, logChi := chi262LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716144639/68714844160) } }, logDArg := sk103LogDArgCertificate }

private noncomputable def leaf4121InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4121LocalValidity :
    LeafFacts leaf4121Box leaf4121Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4121Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357422080) }) = true
      norm_num [leaf4121Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4121CertificateValid :
    WideCertificateValid leaf4121Box leaf4121Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk103ValidityFacts chi262ValidityFacts
    leaf4121LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4121CoverageChecked :
    coverageCheck (innerAD leaf4121Box) leaf4121InnerLog = true := by
  rfl'

private theorem leaf4121InnerLogValid :
    leaf4121InnerLog.Valid 8 (innerAD leaf4121Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4121CoverageChecked

private noncomputable def leaf4121InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814699/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4121InputLogOnePlusV_eq :
    leaf4121InputLogOnePlusV = outerEnclosure 24
      (leaf4121Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4121RoundedFacts : LeafRoundedFacts 8
    leaf4121Certificate.logOnePlusV leaf4121InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4121InputLogOnePlusV_eq }

private noncomputable def leaf4121Inputs : Inputs :=
  inputsOfCaches globalInput sk103RoundedInputs
    chi262InputQChi innerPair242Input
    leaf4121InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4121LowerChecked :
    lowerCheck 24 leaf4121Box leaf4121Inputs = true := by
  rfl'

private theorem leaf4121CoversExact : CoversExact 8
    leaf4121Box leaf4121Certificate leaf4121InnerLog leaf4121Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk103RoundedFacts chi262RoundedFacts
    innerPair242RoundedFacts leaf4121RoundedFacts (by rfl)

private theorem leaf4121FlatSound : Sound leaf4121Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4121CertificateValid
    leaf4121InnerLogValid leaf4121CoversExact leaf4121LowerChecked

private noncomputable def leaf4122Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (87/32), kHi := (11/4), chiLo := (51/128), chiHi := (13/32) }

private noncomputable def leaf4122Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435735/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357395456) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (559167895/536870912) }, upper := { exponent := 1, mantissa := (271/256) } }, logOuter := sk104LogOuterCertificate, logK := sk104LogKCertificate, logChi := chi262LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716118015/68714790912) } }, logDArg := sk104LogDArgCertificate }

private noncomputable def leaf4122InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4122LocalValidity :
    LeafFacts leaf4122Box leaf4122Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4122Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357395456) }) = true
      norm_num [leaf4122Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4122CertificateValid :
    WideCertificateValid leaf4122Box leaf4122Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk104ValidityFacts chi262ValidityFacts
    leaf4122LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4122CoverageChecked :
    coverageCheck (innerAD leaf4122Box) leaf4122InnerLog = true := by
  rfl'

private theorem leaf4122InnerLogValid :
    leaf4122InnerLog.Valid 8 (innerAD leaf4122Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4122CoverageChecked

private noncomputable def leaf4122InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629405/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4122InputLogOnePlusV_eq :
    leaf4122InputLogOnePlusV = outerEnclosure 24
      (leaf4122Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4122RoundedFacts : LeafRoundedFacts 8
    leaf4122Certificate.logOnePlusV leaf4122InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4122InputLogOnePlusV_eq }

private noncomputable def leaf4122Inputs : Inputs :=
  inputsOfCaches globalInput sk104RoundedInputs
    chi262InputQChi innerPair242Input
    leaf4122InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4122LowerChecked :
    lowerCheck 24 leaf4122Box leaf4122Inputs = true := by
  rfl'

private theorem leaf4122CoversExact : CoversExact 8
    leaf4122Box leaf4122Certificate leaf4122InnerLog leaf4122Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk104RoundedFacts chi262RoundedFacts
    innerPair242RoundedFacts leaf4122RoundedFacts (by rfl)

private theorem leaf4122FlatSound : Sound leaf4122Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4122CertificateValid
    leaf4122InnerLogValid leaf4122CoversExact leaf4122LowerChecked

private noncomputable def leaf4123Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (85/32), chiLo := (13/32), chiHi := (27/64) }

private noncomputable def leaf4123Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217951/134217728) }, vSqrt := { lower := (32765/32768), upper := (1108345889/1108302848) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (277306627/268435456) }, upper := { exponent := 1, mantissa := (4343/4096) } }, logOuter := sk105LogOuterCertificate, logK := sk105LogKCertificate, logChi := chi64LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (2216648737/2216605696) } }, logDArg := sk105LogDArgCertificate }

private noncomputable def leaf4123InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4123LocalValidity :
    LeafFacts leaf4123Box leaf4123Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4123Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (1108345889/1108302848) }) = true
      norm_num [leaf4123Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4123CertificateValid :
    WideCertificateValid leaf4123Box leaf4123Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk105ValidityFacts chi64ValidityFacts
    leaf4123LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4123CoverageChecked :
    coverageCheck (innerAD leaf4123Box) leaf4123InnerLog = true := by
  rfl'

private theorem leaf4123InnerLogValid :
    leaf4123InnerLog.Valid 8 (innerAD leaf4123Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4123CoverageChecked

private noncomputable def leaf4123InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629407/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4123InputLogOnePlusV_eq :
    leaf4123InputLogOnePlusV = outerEnclosure 24
      (leaf4123Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4123RoundedFacts : LeafRoundedFacts 8
    leaf4123Certificate.logOnePlusV leaf4123InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4123InputLogOnePlusV_eq }

private noncomputable def leaf4123Inputs : Inputs :=
  inputsOfCaches globalInput sk105RoundedInputs
    chi64InputQChi innerPair242Input
    leaf4123InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4123LowerChecked :
    lowerCheck 24 leaf4123Box leaf4123Inputs = true := by
  rfl'

private theorem leaf4123CoversExact : CoversExact 8
    leaf4123Box leaf4123Certificate leaf4123InnerLog leaf4123Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk105RoundedFacts chi64RoundedFacts
    innerPair242RoundedFacts leaf4123RoundedFacts (by rfl)

private theorem leaf4123FlatSound : Sound leaf4123Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4123CertificateValid
    leaf4123InnerLogValid leaf4123CoversExact leaf4123LowerChecked

private noncomputable def leaf4124Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (85/32), kHi := (43/16), chiLo := (13/32), chiHi := (27/64) }

private noncomputable def leaf4124Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217953/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357360640) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (279010457/268435456) }, upper := { exponent := 1, mantissa := (2185/2048) } }, logOuter := sk106LogOuterCertificate, logK := sk106LogKCertificate, logChi := chi64LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716083199/68714721280) } }, logDArg := sk106LogDArgCertificate }

private noncomputable def leaf4124InnerLog : WideLogData :=
  innerPair324Data

set_option maxRecDepth 1000000 in
private theorem leaf4124LocalValidity :
    LeafFacts leaf4124Box leaf4124Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4124Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357360640) }) = true
      norm_num [leaf4124Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4124CertificateValid :
    WideCertificateValid leaf4124Box leaf4124Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk106ValidityFacts chi64ValidityFacts
    leaf4124LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4124CoverageChecked :
    coverageCheck (innerAD leaf4124Box) leaf4124InnerLog = true := by
  rfl'

private theorem leaf4124InnerLogValid :
    leaf4124InnerLog.Valid 8 (innerAD leaf4124Box) :=
  wideLogDataValid_of_cachedCheck endpoint86PositiveFacts
    endpoint289PositiveFacts.valid leaf4124CoverageChecked

private noncomputable def leaf4124InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629413/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4124InputLogOnePlusV_eq :
    leaf4124InputLogOnePlusV = outerEnclosure 24
      (leaf4124Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4124RoundedFacts : LeafRoundedFacts 8
    leaf4124Certificate.logOnePlusV leaf4124InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4124InputLogOnePlusV_eq }

private noncomputable def leaf4124Inputs : Inputs :=
  inputsOfCaches globalInput sk106RoundedInputs
    chi64InputQChi innerPair324Input
    leaf4124InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4124LowerChecked :
    lowerCheck 24 leaf4124Box leaf4124Inputs = true := by
  rfl'

private theorem leaf4124CoversExact : CoversExact 8
    leaf4124Box leaf4124Certificate leaf4124InnerLog leaf4124Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk106RoundedFacts chi64RoundedFacts
    innerPair324RoundedFacts leaf4124RoundedFacts (by rfl)

private theorem leaf4124FlatSound : Sound leaf4124Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4124CertificateValid
    leaf4124InnerLogValid leaf4124CoversExact leaf4124LowerChecked

private noncomputable def leaf4125Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (85/32), chiLo := (27/64), chiHi := (7/16) }

private noncomputable def leaf4125Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217953/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357301248) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (282811313/268435456) }, upper := { exponent := 1, mantissa := (1107/1024) } }, logOuter := sk105LogOuterCertificate, logK := sk105LogKCertificate, logChi := chi65LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716023807/68714602496) } }, logDArg := sk105LogDArgCertificate }

private noncomputable def leaf4125InnerLog : WideLogData :=
  innerPair243Data

set_option maxRecDepth 1000000 in
private theorem leaf4125LocalValidity :
    LeafFacts leaf4125Box leaf4125Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4125Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357301248) }) = true
      norm_num [leaf4125Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4125CertificateValid :
    WideCertificateValid leaf4125Box leaf4125Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk105ValidityFacts chi65ValidityFacts
    leaf4125LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4125CoverageChecked :
    coverageCheck (innerAD leaf4125Box) leaf4125InnerLog = true := by
  rfl'

private theorem leaf4125InnerLogValid :
    leaf4125InnerLog.Valid 8 (innerAD leaf4125Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint74PositiveFacts.valid leaf4125CoverageChecked

private noncomputable def leaf4125InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907357/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4125InputLogOnePlusV_eq :
    leaf4125InputLogOnePlusV = outerEnclosure 24
      (leaf4125Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4125RoundedFacts : LeafRoundedFacts 8
    leaf4125Certificate.logOnePlusV leaf4125InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4125InputLogOnePlusV_eq }

private noncomputable def leaf4125Inputs : Inputs :=
  inputsOfCaches globalInput sk105RoundedInputs
    chi65InputQChi innerPair243Input
    leaf4125InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4125LowerChecked :
    lowerCheck 24 leaf4125Box leaf4125Inputs = true := by
  rfl'

private theorem leaf4125CoversExact : CoversExact 8
    leaf4125Box leaf4125Certificate leaf4125InnerLog leaf4125Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk105RoundedFacts chi65RoundedFacts
    innerPair243RoundedFacts leaf4125RoundedFacts (by rfl)

private theorem leaf4125FlatSound : Sound leaf4125Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4125CertificateValid
    leaf4125InnerLogValid leaf4125CoversExact leaf4125LowerChecked

private noncomputable def leaf4126Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (85/32), kHi := (43/16), chiLo := (27/64), chiHi := (7/16) }

private noncomputable def leaf4126Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217955/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357272576) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (284580675/268435456) }, upper := { exponent := 1, mantissa := (557/512) } }, logOuter := sk106LogOuterCertificate, logK := sk106LogKCertificate, logChi := chi65LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715995135/68714545152) } }, logDArg := sk106LogDArgCertificate }

private noncomputable def leaf4126InnerLog : WideLogData :=
  innerPair243Data

set_option maxRecDepth 1000000 in
private theorem leaf4126LocalValidity :
    LeafFacts leaf4126Box leaf4126Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4126Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357272576) }) = true
      norm_num [leaf4126Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4126CertificateValid :
    WideCertificateValid leaf4126Box leaf4126Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk106ValidityFacts chi65ValidityFacts
    leaf4126LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4126CoverageChecked :
    coverageCheck (innerAD leaf4126Box) leaf4126InnerLog = true := by
  rfl'

private theorem leaf4126InnerLogValid :
    leaf4126InnerLog.Valid 8 (innerAD leaf4126Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint74PositiveFacts.valid leaf4126CoverageChecked

private noncomputable def leaf4126InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629435/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4126InputLogOnePlusV_eq :
    leaf4126InputLogOnePlusV = outerEnclosure 24
      (leaf4126Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4126RoundedFacts : LeafRoundedFacts 8
    leaf4126Certificate.logOnePlusV leaf4126InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4126InputLogOnePlusV_eq }

private noncomputable def leaf4126Inputs : Inputs :=
  inputsOfCaches globalInput sk106RoundedInputs
    chi65InputQChi innerPair243Input
    leaf4126InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4126LowerChecked :
    lowerCheck 24 leaf4126Box leaf4126Inputs = true := by
  rfl'

private theorem leaf4126CoversExact : CoversExact 8
    leaf4126Box leaf4126Certificate leaf4126InnerLog leaf4126Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk106RoundedFacts chi65RoundedFacts
    innerPair243RoundedFacts leaf4126RoundedFacts (by rfl)

private theorem leaf4126FlatSound : Sound leaf4126Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4126CertificateValid
    leaf4126InnerLogValid leaf4126CoversExact leaf4126LowerChecked

private noncomputable def leaf4127Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (87/32), chiLo := (13/32), chiHi := (53/128) }

private noncomputable def leaf4127Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435735/268435456) }, vSqrt := { lower := (32765/32768), upper := (2021101327/2021022208) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (561461515/536870912) }, upper := { exponent := 1, mantissa := (8707/8192) } }, logOuter := sk103LogOuterCertificate, logK := sk103LogKCertificate, logChi := chi263LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (4042123535/4042044416) } }, logDArg := sk103LogDArgCertificate }

private noncomputable def leaf4127InnerLog : WideLogData :=
  innerPair243Data

set_option maxRecDepth 1000000 in
private theorem leaf4127LocalValidity :
    LeafFacts leaf4127Box leaf4127Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4127Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (2021101327/2021022208) }) = true
      norm_num [leaf4127Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4127CertificateValid :
    WideCertificateValid leaf4127Box leaf4127Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk103ValidityFacts chi263ValidityFacts
    leaf4127LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4127CoverageChecked :
    coverageCheck (innerAD leaf4127Box) leaf4127InnerLog = true := by
  rfl'

private theorem leaf4127InnerLogValid :
    leaf4127InnerLog.Valid 8 (innerAD leaf4127Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint74PositiveFacts.valid leaf4127CoverageChecked

private noncomputable def leaf4127InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629409/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4127InputLogOnePlusV_eq :
    leaf4127InputLogOnePlusV = outerEnclosure 24
      (leaf4127Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4127RoundedFacts : LeafRoundedFacts 8
    leaf4127Certificate.logOnePlusV leaf4127InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4127InputLogOnePlusV_eq }

private noncomputable def leaf4127Inputs : Inputs :=
  inputsOfCaches globalInput sk103RoundedInputs
    chi263InputQChi innerPair243Input
    leaf4127InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4127LowerChecked :
    lowerCheck 24 leaf4127Box leaf4127Inputs = true := by
  rfl'

private theorem leaf4127CoversExact : CoversExact 8
    leaf4127Box leaf4127Certificate leaf4127InnerLog leaf4127Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk103RoundedFacts chi263RoundedFacts
    innerPair243RoundedFacts leaf4127RoundedFacts (by rfl)

private theorem leaf4127FlatSound : Sound leaf4127Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4127CertificateValid
    leaf4127InnerLogValid leaf4127CoversExact leaf4127LowerChecked

private noncomputable def leaf4128Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (87/32), kHi := (11/4), chiLo := (13/32), chiHi := (53/128) }

private noncomputable def leaf4128Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435737/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357350400) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (564869177/536870912) }, upper := { exponent := 1, mantissa := (1095/1024) } }, logOuter := sk104LogOuterCertificate, logK := sk104LogKCertificate, logChi := chi263LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716072959/68714700800) } }, logDArg := sk104LogDArgCertificate }

private noncomputable def leaf4128InnerLog : WideLogData :=
  innerPair243Data

set_option maxRecDepth 1000000 in
private theorem leaf4128LocalValidity :
    LeafFacts leaf4128Box leaf4128Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4128Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357350400) }) = true
      norm_num [leaf4128Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4128CertificateValid :
    WideCertificateValid leaf4128Box leaf4128Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk104ValidityFacts chi263ValidityFacts
    leaf4128LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4128CoverageChecked :
    coverageCheck (innerAD leaf4128Box) leaf4128InnerLog = true := by
  rfl'

private theorem leaf4128InnerLogValid :
    leaf4128InnerLog.Valid 8 (innerAD leaf4128Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint74PositiveFacts.valid leaf4128CoverageChecked

private noncomputable def leaf4128InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (1453677/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf4128InputLogOnePlusV_eq :
    leaf4128InputLogOnePlusV = outerEnclosure 24
      (leaf4128Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4128RoundedFacts : LeafRoundedFacts 8
    leaf4128Certificate.logOnePlusV leaf4128InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4128InputLogOnePlusV_eq }

private noncomputable def leaf4128Inputs : Inputs :=
  inputsOfCaches globalInput sk104RoundedInputs
    chi263InputQChi innerPair243Input
    leaf4128InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4128LowerChecked :
    lowerCheck 24 leaf4128Box leaf4128Inputs = true := by
  rfl'

private theorem leaf4128CoversExact : CoversExact 8
    leaf4128Box leaf4128Certificate leaf4128InnerLog leaf4128Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk104RoundedFacts chi263RoundedFacts
    innerPair243RoundedFacts leaf4128RoundedFacts (by rfl)

private theorem leaf4128FlatSound : Sound leaf4128Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4128CertificateValid
    leaf4128InnerLogValid leaf4128CoversExact leaf4128LowerChecked

private noncomputable def leaf4129Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (87/32), chiLo := (53/128), chiHi := (27/64) }

private noncomputable def leaf4129Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435737/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357332992) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (567097265/536870912) }, upper := { exponent := 1, mantissa := (4397/4096) } }, logOuter := sk103LogOuterCertificate, logK := sk103LogKCertificate, logChi := chi264LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716055551/68714665984) } }, logDArg := sk103LogDArgCertificate }

private noncomputable def leaf4129InnerLog : WideLogData :=
  innerPair243Data

set_option maxRecDepth 1000000 in
private theorem leaf4129LocalValidity :
    LeafFacts leaf4129Box leaf4129Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4129Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357332992) }) = true
      norm_num [leaf4129Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4129CertificateValid :
    WideCertificateValid leaf4129Box leaf4129Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk103ValidityFacts chi264ValidityFacts
    leaf4129LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4129CoverageChecked :
    coverageCheck (innerAD leaf4129Box) leaf4129InnerLog = true := by
  rfl'

private theorem leaf4129InnerLogValid :
    leaf4129InnerLog.Valid 8 (innerAD leaf4129Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint74PositiveFacts.valid leaf4129CoverageChecked

private noncomputable def leaf4129InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907355/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4129InputLogOnePlusV_eq :
    leaf4129InputLogOnePlusV = outerEnclosure 24
      (leaf4129Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4129RoundedFacts : LeafRoundedFacts 8
    leaf4129Certificate.logOnePlusV leaf4129InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4129InputLogOnePlusV_eq }

private noncomputable def leaf4129Inputs : Inputs :=
  inputsOfCaches globalInput sk103RoundedInputs
    chi264InputQChi innerPair243Input
    leaf4129InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4129LowerChecked :
    lowerCheck 24 leaf4129Box leaf4129Inputs = true := by
  rfl'

private theorem leaf4129CoversExact : CoversExact 8
    leaf4129Box leaf4129Certificate leaf4129InnerLog leaf4129Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk103RoundedFacts chi264RoundedFacts
    innerPair243RoundedFacts leaf4129RoundedFacts (by rfl)

private theorem leaf4129FlatSound : Sound leaf4129Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4129CertificateValid
    leaf4129InnerLogValid leaf4129CoversExact leaf4129LowerChecked

private noncomputable def leaf4130Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (87/32), kHi := (11/4), chiLo := (53/128), chiHi := (27/64) }

private noncomputable def leaf4130Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435739/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357305344) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (570570459/536870912) }, upper := { exponent := 1, mantissa := (553/512) } }, logOuter := sk104LogOuterCertificate, logK := sk104LogKCertificate, logChi := chi264LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716027903/68714610688) } }, logDArg := sk104LogDArgCertificate }

private noncomputable def leaf4130InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf4130LocalValidity :
    LeafFacts leaf4130Box leaf4130Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4130Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357305344) }) = true
      norm_num [leaf4130Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4130CertificateValid :
    WideCertificateValid leaf4130Box leaf4130Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk104ValidityFacts chi264ValidityFacts
    leaf4130LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4130CoverageChecked :
    coverageCheck (innerAD leaf4130Box) leaf4130InnerLog = true := by
  rfl'

private theorem leaf4130InnerLogValid :
    leaf4130InnerLog.Valid 8 (innerAD leaf4130Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf4130CoverageChecked

private noncomputable def leaf4130InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629427/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4130InputLogOnePlusV_eq :
    leaf4130InputLogOnePlusV = outerEnclosure 24
      (leaf4130Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4130RoundedFacts : LeafRoundedFacts 8
    leaf4130Certificate.logOnePlusV leaf4130InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4130InputLogOnePlusV_eq }

private noncomputable def leaf4130Inputs : Inputs :=
  inputsOfCaches globalInput sk104RoundedInputs
    chi264InputQChi innerPair249Input
    leaf4130InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4130LowerChecked :
    lowerCheck 24 leaf4130Box leaf4130Inputs = true := by
  rfl'

private theorem leaf4130CoversExact : CoversExact 8
    leaf4130Box leaf4130Certificate leaf4130InnerLog leaf4130Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk104RoundedFacts chi264RoundedFacts
    innerPair249RoundedFacts leaf4130RoundedFacts (by rfl)

private theorem leaf4130FlatSound : Sound leaf4130Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4130CertificateValid
    leaf4130InnerLogValid leaf4130CoversExact leaf4130LowerChecked

private noncomputable def leaf4131Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (87/32), chiLo := (27/64), chiHi := (55/128) }

private noncomputable def leaf4131Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435739/268435456) }, vSqrt := { lower := (32765/32768), upper := (4908388937/4908184064) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (572733015/536870912) }, upper := { exponent := 1, mantissa := (8881/8192) } }, logOuter := sk103LogOuterCertificate, logK := sk103LogKCertificate, logChi := chi265LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (9816573001/9816368128) } }, logDArg := sk103LogDArgCertificate }

private noncomputable def leaf4131InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf4131LocalValidity :
    LeafFacts leaf4131Box leaf4131Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4131Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4908388937/4908184064) }) = true
      norm_num [leaf4131Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4131CertificateValid :
    WideCertificateValid leaf4131Box leaf4131Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk103ValidityFacts chi265ValidityFacts
    leaf4131LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4131CoverageChecked :
    coverageCheck (innerAD leaf4131Box) leaf4131InnerLog = true := by
  rfl'

private theorem leaf4131InnerLogValid :
    leaf4131InnerLog.Valid 8 (innerAD leaf4131Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf4131CoverageChecked

private noncomputable def leaf4131InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629431/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4131InputLogOnePlusV_eq :
    leaf4131InputLogOnePlusV = outerEnclosure 24
      (leaf4131Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4131RoundedFacts : LeafRoundedFacts 8
    leaf4131Certificate.logOnePlusV leaf4131InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4131InputLogOnePlusV_eq }

private noncomputable def leaf4131Inputs : Inputs :=
  inputsOfCaches globalInput sk103RoundedInputs
    chi265InputQChi innerPair249Input
    leaf4131InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4131LowerChecked :
    lowerCheck 24 leaf4131Box leaf4131Inputs = true := by
  rfl'

private theorem leaf4131CoversExact : CoversExact 8
    leaf4131Box leaf4131Certificate leaf4131InnerLog leaf4131Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk103RoundedFacts chi265RoundedFacts
    innerPair249RoundedFacts leaf4131RoundedFacts (by rfl)

private theorem leaf4131FlatSound : Sound leaf4131Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4131CertificateValid
    leaf4131InnerLogValid leaf4131CoversExact leaf4131LowerChecked

private noncomputable def leaf4132Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (87/32), kHi := (11/4), chiLo := (27/64), chiHi := (55/128) }

private noncomputable def leaf4132Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435741/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357260288) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (576271741/536870912) }, upper := { exponent := 1, mantissa := (1117/1024) } }, logOuter := sk104LogOuterCertificate, logK := sk104LogKCertificate, logChi := chi265LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715982847/68714520576) } }, logDArg := sk104LogDArgCertificate }

private noncomputable def leaf4132InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf4132LocalValidity :
    LeafFacts leaf4132Box leaf4132Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4132Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357260288) }) = true
      norm_num [leaf4132Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4132CertificateValid :
    WideCertificateValid leaf4132Box leaf4132Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk104ValidityFacts chi265ValidityFacts
    leaf4132LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4132CoverageChecked :
    coverageCheck (innerAD leaf4132Box) leaf4132InnerLog = true := by
  rfl'

private theorem leaf4132InnerLogValid :
    leaf4132InnerLog.Valid 8 (innerAD leaf4132Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf4132CoverageChecked

private noncomputable def leaf4132InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814719/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4132InputLogOnePlusV_eq :
    leaf4132InputLogOnePlusV = outerEnclosure 24
      (leaf4132Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4132RoundedFacts : LeafRoundedFacts 8
    leaf4132Certificate.logOnePlusV leaf4132InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4132InputLogOnePlusV_eq }

private noncomputable def leaf4132Inputs : Inputs :=
  inputsOfCaches globalInput sk104RoundedInputs
    chi265InputQChi innerPair249Input
    leaf4132InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4132LowerChecked :
    lowerCheck 24 leaf4132Box leaf4132Inputs = true := by
  rfl'

private theorem leaf4132CoversExact : CoversExact 8
    leaf4132Box leaf4132Certificate leaf4132InnerLog leaf4132Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk104RoundedFacts chi265RoundedFacts
    innerPair249RoundedFacts leaf4132RoundedFacts (by rfl)

private theorem leaf4132FlatSound : Sound leaf4132Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4132CertificateValid
    leaf4132InnerLogValid leaf4132CoversExact leaf4132LowerChecked

private noncomputable def leaf4133Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (87/32), chiLo := (55/128), chiHi := (7/16) }

private noncomputable def leaf4133Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435741/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357243904) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (578368765/536870912) }, upper := { exponent := 1, mantissa := (1121/1024) } }, logOuter := sk103LogOuterCertificate, logK := sk103LogKCertificate, logChi := chi266LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715966463/68714487808) } }, logDArg := sk103LogDArgCertificate }

private noncomputable def leaf4133InnerLog : WideLogData :=
  innerPair250Data

set_option maxRecDepth 1000000 in
private theorem leaf4133LocalValidity :
    LeafFacts leaf4133Box leaf4133Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4133Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357243904) }) = true
      norm_num [leaf4133Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4133CertificateValid :
    WideCertificateValid leaf4133Box leaf4133Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk103ValidityFacts chi266ValidityFacts
    leaf4133LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4133CoverageChecked :
    coverageCheck (innerAD leaf4133Box) leaf4133InnerLog = true := by
  rfl'

private theorem leaf4133InnerLogValid :
    leaf4133InnerLog.Valid 8 (innerAD leaf4133Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint75PositiveFacts.valid leaf4133CoverageChecked

private noncomputable def leaf4133InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814721/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4133InputLogOnePlusV_eq :
    leaf4133InputLogOnePlusV = outerEnclosure 24
      (leaf4133Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4133RoundedFacts : LeafRoundedFacts 8
    leaf4133Certificate.logOnePlusV leaf4133InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4133InputLogOnePlusV_eq }

private noncomputable def leaf4133Inputs : Inputs :=
  inputsOfCaches globalInput sk103RoundedInputs
    chi266InputQChi innerPair250Input
    leaf4133InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4133LowerChecked :
    lowerCheck 24 leaf4133Box leaf4133Inputs = true := by
  rfl'

private theorem leaf4133CoversExact : CoversExact 8
    leaf4133Box leaf4133Certificate leaf4133InnerLog leaf4133Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk103RoundedFacts chi266RoundedFacts
    innerPair250RoundedFacts leaf4133RoundedFacts (by rfl)

private theorem leaf4133FlatSound : Sound leaf4133Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4133CertificateValid
    leaf4133InnerLogValid leaf4133CoversExact leaf4133LowerChecked

private noncomputable def leaf4134Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (87/32), kHi := (11/4), chiLo := (55/128), chiHi := (7/16) }

private noncomputable def leaf4134Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435743/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357215232) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (581973023/536870912) }, upper := { exponent := 1, mantissa := (141/128) } }, logOuter := sk104LogOuterCertificate, logK := sk104LogKCertificate, logChi := chi266LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715937791/68714430464) } }, logDArg := sk104LogDArgCertificate }

private noncomputable def leaf4134InnerLog : WideLogData :=
  innerPair250Data

set_option maxRecDepth 1000000 in
private theorem leaf4134LocalValidity :
    LeafFacts leaf4134Box leaf4134Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4134Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357215232) }) = true
      norm_num [leaf4134Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4134CertificateValid :
    WideCertificateValid leaf4134Box leaf4134Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk104ValidityFacts chi266ValidityFacts
    leaf4134LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4134CoverageChecked :
    coverageCheck (innerAD leaf4134Box) leaf4134InnerLog = true := by
  rfl'

private theorem leaf4134InnerLogValid :
    leaf4134InnerLog.Valid 8 (innerAD leaf4134Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint75PositiveFacts.valid leaf4134CoverageChecked

private noncomputable def leaf4134InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629449/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4134InputLogOnePlusV_eq :
    leaf4134InputLogOnePlusV = outerEnclosure 24
      (leaf4134Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4134RoundedFacts : LeafRoundedFacts 8
    leaf4134Certificate.logOnePlusV leaf4134InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4134InputLogOnePlusV_eq }

private noncomputable def leaf4134Inputs : Inputs :=
  inputsOfCaches globalInput sk104RoundedInputs
    chi266InputQChi innerPair250Input
    leaf4134InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4134LowerChecked :
    lowerCheck 24 leaf4134Box leaf4134Inputs = true := by
  rfl'

private theorem leaf4134CoversExact : CoversExact 8
    leaf4134Box leaf4134Certificate leaf4134InnerLog leaf4134Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk104RoundedFacts chi266RoundedFacts
    innerPair250RoundedFacts leaf4134RoundedFacts (by rfl)

private theorem leaf4134FlatSound : Sound leaf4134Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4134CertificateValid
    leaf4134InnerLogValid leaf4134CoversExact leaf4134LowerChecked

private noncomputable def component84Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (3/8), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component84Node0_sound : Sound component84Node0Box :=
  sound_of_literal_split component84Node0Box leaf4096Box leaf4097Box
    .k (81/32) (by rfl) (by rfl)
    leaf4096FlatSound leaf4097FlatSound

private noncomputable def component84Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (25/64), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component84Node1_sound : Sound component84Node1Box :=
  sound_of_literal_split component84Node1Box leaf4098Box leaf4099Box
    .k (81/32) (by rfl) (by rfl)
    leaf4098FlatSound leaf4099FlatSound

private noncomputable def component84Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (3/8), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component84Node2_sound : Sound component84Node2Box :=
  sound_of_literal_split component84Node2Box component84Node0Box component84Node1Box
    .chi (25/64) (by rfl) (by rfl)
    component84Node0_sound component84Node1_sound

private noncomputable def component84Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (3/8), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component84Node3_sound : Sound component84Node3Box :=
  sound_of_literal_split component84Node3Box leaf4100Box leaf4101Box
    .k (83/32) (by rfl) (by rfl)
    leaf4100FlatSound leaf4101FlatSound

private noncomputable def component84Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (25/64), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component84Node4_sound : Sound component84Node4Box :=
  sound_of_literal_split component84Node4Box leaf4102Box leaf4103Box
    .k (83/32) (by rfl) (by rfl)
    leaf4102FlatSound leaf4103FlatSound

private noncomputable def component84Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (3/8), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component84Node5_sound : Sound component84Node5Box :=
  sound_of_literal_split component84Node5Box component84Node3Box component84Node4Box
    .chi (25/64) (by rfl) (by rfl)
    component84Node3_sound component84Node4_sound

private noncomputable def component84Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8), chiLo := (3/8), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component84Node6_sound : Sound component84Node6Box :=
  sound_of_literal_split component84Node6Box component84Node2Box component84Node5Box
    .k (41/16) (by rfl) (by rfl)
    component84Node2_sound component84Node5_sound

private noncomputable def component84Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (13/32), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component84Node7_sound : Sound component84Node7Box :=
  sound_of_literal_split component84Node7Box leaf4104Box leaf4105Box
    .k (81/32) (by rfl) (by rfl)
    leaf4104FlatSound leaf4105FlatSound

private noncomputable def component84Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (27/64), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component84Node8_sound : Sound component84Node8Box :=
  sound_of_literal_split component84Node8Box leaf4106Box leaf4107Box
    .k (81/32) (by rfl) (by rfl)
    leaf4106FlatSound leaf4107FlatSound

private noncomputable def component84Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (13/32), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component84Node9_sound : Sound component84Node9Box :=
  sound_of_literal_split component84Node9Box component84Node7Box component84Node8Box
    .chi (27/64) (by rfl) (by rfl)
    component84Node7_sound component84Node8_sound

private noncomputable def component84Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (13/32), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component84Node10_sound : Sound component84Node10Box :=
  sound_of_literal_split component84Node10Box leaf4108Box leaf4109Box
    .k (83/32) (by rfl) (by rfl)
    leaf4108FlatSound leaf4109FlatSound

private noncomputable def component84Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (27/64), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component84Node11_sound : Sound component84Node11Box :=
  sound_of_literal_split component84Node11Box leaf4110Box leaf4111Box
    .k (83/32) (by rfl) (by rfl)
    leaf4110FlatSound leaf4111FlatSound

private noncomputable def component84Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (13/32), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component84Node12_sound : Sound component84Node12Box :=
  sound_of_literal_split component84Node12Box component84Node10Box component84Node11Box
    .chi (27/64) (by rfl) (by rfl)
    component84Node10_sound component84Node11_sound

private noncomputable def component84Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8), chiLo := (13/32), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component84Node13_sound : Sound component84Node13Box :=
  sound_of_literal_split component84Node13Box component84Node9Box component84Node12Box
    .k (41/16) (by rfl) (by rfl)
    component84Node9_sound component84Node12_sound

private noncomputable def component84Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8), chiLo := (3/8), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component84Node14_sound : Sound component84Node14Box :=
  sound_of_literal_split component84Node14Box component84Node6Box component84Node13Box
    .chi (13/32) (by rfl) (by rfl)
    component84Node6_sound component84Node13_sound

private noncomputable def component84Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (3/8), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component84Node15_sound : Sound component84Node15Box :=
  sound_of_literal_split component84Node15Box leaf4112Box leaf4113Box
    .k (85/32) (by rfl) (by rfl)
    leaf4112FlatSound leaf4113FlatSound

private noncomputable def component84Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (25/64), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component84Node16_sound : Sound component84Node16Box :=
  sound_of_literal_split component84Node16Box leaf4114Box leaf4115Box
    .k (85/32) (by rfl) (by rfl)
    leaf4114FlatSound leaf4115FlatSound

private noncomputable def component84Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (3/8), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component84Node17_sound : Sound component84Node17Box :=
  sound_of_literal_split component84Node17Box component84Node15Box component84Node16Box
    .chi (25/64) (by rfl) (by rfl)
    component84Node15_sound component84Node16_sound

private noncomputable def component84Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (87/32), kHi := (11/4), chiLo := (3/8), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component84Node18_sound : Sound component84Node18Box :=
  sound_of_literal_split component84Node18Box leaf4117Box leaf4118Box
    .chi (49/128) (by rfl) (by rfl)
    leaf4117FlatSound leaf4118FlatSound

private noncomputable def component84Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (3/8), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component84Node19_sound : Sound component84Node19Box :=
  sound_of_literal_split component84Node19Box leaf4116Box component84Node18Box
    .k (87/32) (by rfl) (by rfl)
    leaf4116FlatSound component84Node18_sound

private noncomputable def component84Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (25/64), chiHi := (51/128) }

set_option maxRecDepth 1000000 in
private theorem component84Node20_sound : Sound component84Node20Box :=
  sound_of_literal_split component84Node20Box leaf4119Box leaf4120Box
    .k (87/32) (by rfl) (by rfl)
    leaf4119FlatSound leaf4120FlatSound

private noncomputable def component84Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (51/128), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component84Node21_sound : Sound component84Node21Box :=
  sound_of_literal_split component84Node21Box leaf4121Box leaf4122Box
    .k (87/32) (by rfl) (by rfl)
    leaf4121FlatSound leaf4122FlatSound

private noncomputable def component84Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (25/64), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component84Node22_sound : Sound component84Node22Box :=
  sound_of_literal_split component84Node22Box component84Node20Box component84Node21Box
    .chi (51/128) (by rfl) (by rfl)
    component84Node20_sound component84Node21_sound

private noncomputable def component84Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (3/8), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component84Node23_sound : Sound component84Node23Box :=
  sound_of_literal_split component84Node23Box component84Node19Box component84Node22Box
    .chi (25/64) (by rfl) (by rfl)
    component84Node19_sound component84Node22_sound

private noncomputable def component84Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4), chiLo := (3/8), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component84Node24_sound : Sound component84Node24Box :=
  sound_of_literal_split component84Node24Box component84Node17Box component84Node23Box
    .k (43/16) (by rfl) (by rfl)
    component84Node17_sound component84Node23_sound

private noncomputable def component84Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (13/32), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component84Node25_sound : Sound component84Node25Box :=
  sound_of_literal_split component84Node25Box leaf4123Box leaf4124Box
    .k (85/32) (by rfl) (by rfl)
    leaf4123FlatSound leaf4124FlatSound

private noncomputable def component84Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (27/64), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component84Node26_sound : Sound component84Node26Box :=
  sound_of_literal_split component84Node26Box leaf4125Box leaf4126Box
    .k (85/32) (by rfl) (by rfl)
    leaf4125FlatSound leaf4126FlatSound

private noncomputable def component84Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (13/32), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component84Node27_sound : Sound component84Node27Box :=
  sound_of_literal_split component84Node27Box component84Node25Box component84Node26Box
    .chi (27/64) (by rfl) (by rfl)
    component84Node25_sound component84Node26_sound

private noncomputable def component84Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (13/32), chiHi := (53/128) }

set_option maxRecDepth 1000000 in
private theorem component84Node28_sound : Sound component84Node28Box :=
  sound_of_literal_split component84Node28Box leaf4127Box leaf4128Box
    .k (87/32) (by rfl) (by rfl)
    leaf4127FlatSound leaf4128FlatSound

private noncomputable def component84Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (53/128), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component84Node29_sound : Sound component84Node29Box :=
  sound_of_literal_split component84Node29Box leaf4129Box leaf4130Box
    .k (87/32) (by rfl) (by rfl)
    leaf4129FlatSound leaf4130FlatSound

private noncomputable def component84Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (13/32), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component84Node30_sound : Sound component84Node30Box :=
  sound_of_literal_split component84Node30Box component84Node28Box component84Node29Box
    .chi (53/128) (by rfl) (by rfl)
    component84Node28_sound component84Node29_sound

private noncomputable def component84Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (27/64), chiHi := (55/128) }

set_option maxRecDepth 1000000 in
private theorem component84Node31_sound : Sound component84Node31Box :=
  sound_of_literal_split component84Node31Box leaf4131Box leaf4132Box
    .k (87/32) (by rfl) (by rfl)
    leaf4131FlatSound leaf4132FlatSound

private noncomputable def component84Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (55/128), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component84Node32_sound : Sound component84Node32Box :=
  sound_of_literal_split component84Node32Box leaf4133Box leaf4134Box
    .k (87/32) (by rfl) (by rfl)
    leaf4133FlatSound leaf4134FlatSound

private noncomputable def component84Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (27/64), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component84Node33_sound : Sound component84Node33Box :=
  sound_of_literal_split component84Node33Box component84Node31Box component84Node32Box
    .chi (55/128) (by rfl) (by rfl)
    component84Node31_sound component84Node32_sound

private noncomputable def component84Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (13/32), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component84Node34_sound : Sound component84Node34Box :=
  sound_of_literal_split component84Node34Box component84Node30Box component84Node33Box
    .chi (27/64) (by rfl) (by rfl)
    component84Node30_sound component84Node33_sound

private noncomputable def component84Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4), chiLo := (13/32), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component84Node35_sound : Sound component84Node35Box :=
  sound_of_literal_split component84Node35Box component84Node27Box component84Node34Box
    .k (43/16) (by rfl) (by rfl)
    component84Node27_sound component84Node34_sound

private noncomputable def component84Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4), chiLo := (3/8), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component84Node36_sound : Sound component84Node36Box :=
  sound_of_literal_split component84Node36Box component84Node24Box component84Node35Box
    .chi (13/32) (by rfl) (by rfl)
    component84Node24_sound component84Node35_sound

noncomputable def component84Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (11/4), chiLo := (3/8), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
theorem component84_sound : Sound component84Box :=
  sound_of_literal_split component84Box component84Node14Box component84Node36Box
    .k (21/8) (by rfl) (by rfl)
    component84Node14_sound component84Node36_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
