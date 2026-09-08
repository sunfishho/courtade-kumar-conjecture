import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch5
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch5
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

private noncomputable def leaf4529Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (9/32), chiHi := (73/256) }

private noncomputable def leaf4529Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871275/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715402752) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1046414615/536870912) }, upper := { exponent := 0, mantissa := (16149/8192) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi281LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137433896447/137430805504) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf4529InnerLog : WideLogData :=
  innerPair538Data

set_option maxRecDepth 1000000 in
private theorem leaf4529LocalValidity :
    LeafFacts leaf4529Box leaf4529Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4529Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715402752) }) = true
      norm_num [leaf4529Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4529CertificateValid :
    WideCertificateValid leaf4529Box leaf4529Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi281ValidityFacts
    leaf4529LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4529CoverageChecked :
    coverageCheck (innerAD leaf4529Box) leaf4529InnerLog = true := by
  rfl'

private theorem leaf4529InnerLogValid :
    leaf4529InnerLog.Valid 8 (innerAD leaf4529Box) :=
  wideLogDataValid_of_cachedCheck endpoint273PositiveFacts
    endpoint269PositiveFacts.valid leaf4529CoverageChecked

private noncomputable def leaf4529InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814729/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4529InputLogOnePlusV_eq :
    leaf4529InputLogOnePlusV = outerEnclosure 24
      (leaf4529Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4529RoundedFacts : LeafRoundedFacts 8
    leaf4529Certificate.logOnePlusV leaf4529InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4529InputLogOnePlusV_eq }

private noncomputable def leaf4529Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi281InputQChi innerPair538Input
    leaf4529InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4529LowerChecked :
    lowerCheck 24 leaf4529Box leaf4529Inputs = true := by
  rfl'

private theorem leaf4529CoversExact : CoversExact 8
    leaf4529Box leaf4529Certificate leaf4529InnerLog leaf4529Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi281RoundedFacts
    innerPair538RoundedFacts leaf4529RoundedFacts (by rfl)

private theorem leaf4529FlatSound : Sound leaf4529Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4529CertificateValid
    leaf4529InnerLogValid leaf4529CoversExact leaf4529LowerChecked

private noncomputable def leaf4530Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (73/256), chiHi := (37/128) }

private noncomputable def leaf4530Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871277/536870912) }, vSqrt := { lower := (65529/65536), upper := (2021101327/2021039616) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1053492069/536870912) }, upper := { exponent := 0, mantissa := (8129/4096) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi282LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (4042140943/4042079232) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf4530InnerLog : WideLogData :=
  innerPair314Data

set_option maxRecDepth 1000000 in
private theorem leaf4530LocalValidity :
    LeafFacts leaf4530Box leaf4530Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4530Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (2021101327/2021039616) }) = true
      norm_num [leaf4530Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4530CertificateValid :
    WideCertificateValid leaf4530Box leaf4530Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi282ValidityFacts
    leaf4530LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4530CoverageChecked :
    coverageCheck (innerAD leaf4530Box) leaf4530InnerLog = true := by
  rfl'

private theorem leaf4530InnerLogValid :
    leaf4530InnerLog.Valid 8 (innerAD leaf4530Box) :=
  wideLogDataValid_of_cachedCheck endpoint83PositiveFacts
    endpoint277PositiveFacts.valid leaf4530CoverageChecked

private noncomputable def leaf4530InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629337/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4530InputLogOnePlusV_eq :
    leaf4530InputLogOnePlusV = outerEnclosure 24
      (leaf4530Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4530RoundedFacts : LeafRoundedFacts 8
    leaf4530Certificate.logOnePlusV leaf4530InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4530InputLogOnePlusV_eq }

private noncomputable def leaf4530Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi282InputQChi innerPair314Input
    leaf4530InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4530LowerChecked :
    lowerCheck 24 leaf4530Box leaf4530Inputs = true := by
  rfl'

private theorem leaf4530CoversExact : CoversExact 8
    leaf4530Box leaf4530Certificate leaf4530InnerLog leaf4530Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi282RoundedFacts
    innerPair314RoundedFacts leaf4530RoundedFacts (by rfl)

private theorem leaf4530FlatSound : Sound leaf4530Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4530CertificateValid
    leaf4530InnerLogValid leaf4530CoversExact leaf4530LowerChecked

private noncomputable def leaf4531Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (9/32), chiHi := (73/256) }

private noncomputable def leaf4531Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871277/536870912) }, vSqrt := { lower := (65529/65536), upper := (22906164565/22905121792) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1051132917/536870912) }, upper := { exponent := 0, mantissa := (8111/4096) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi281LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (45811286357/45810243584) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf4531InnerLog : WideLogData :=
  innerPair238Data

set_option maxRecDepth 1000000 in
private theorem leaf4531LocalValidity :
    LeafFacts leaf4531Box leaf4531Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4531Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22906164565/22905121792) }) = true
      norm_num [leaf4531Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4531CertificateValid :
    WideCertificateValid leaf4531Box leaf4531Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi281ValidityFacts
    leaf4531LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4531CoverageChecked :
    coverageCheck (innerAD leaf4531Box) leaf4531InnerLog = true := by
  rfl'

private theorem leaf4531InnerLogValid :
    leaf4531InnerLog.Valid 8 (innerAD leaf4531Box) :=
  wideLogDataValid_of_cachedCheck endpoint71PositiveFacts
    endpoint267PositiveFacts.valid leaf4531CoverageChecked

private noncomputable def leaf4531InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629463/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4531InputLogOnePlusV_eq :
    leaf4531InputLogOnePlusV = outerEnclosure 24
      (leaf4531Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4531RoundedFacts : LeafRoundedFacts 8
    leaf4531Certificate.logOnePlusV leaf4531InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4531InputLogOnePlusV_eq }

private noncomputable def leaf4531Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi281InputQChi innerPair238Input
    leaf4531InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4531LowerChecked :
    lowerCheck 24 leaf4531Box leaf4531Inputs = true := by
  rfl'

private theorem leaf4531CoversExact : CoversExact 8
    leaf4531Box leaf4531Certificate leaf4531InnerLog leaf4531Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi281RoundedFacts
    innerPair238RoundedFacts leaf4531RoundedFacts (by rfl)

private theorem leaf4531FlatSound : Sound leaf4531Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4531CertificateValid
    leaf4531InnerLogValid leaf4531CoversExact leaf4531LowerChecked

private noncomputable def leaf4532Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (73/256), chiHi := (37/128) }

private noncomputable def leaf4532Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871279/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357654528) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1058275903/536870912) }, upper := { exponent := 0, mantissa := (4083/2048) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi282LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716377087/68715309056) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf4532InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4532LocalValidity :
    LeafFacts leaf4532Box leaf4532Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4532Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357654528) }) = true
      norm_num [leaf4532Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4532CertificateValid :
    WideCertificateValid leaf4532Box leaf4532Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi282ValidityFacts
    leaf4532LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4532CoverageChecked :
    coverageCheck (innerAD leaf4532Box) leaf4532InnerLog = true := by
  rfl'

private theorem leaf4532InnerLogValid :
    leaf4532InnerLog.Valid 8 (innerAD leaf4532Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4532CoverageChecked

private noncomputable def leaf4532InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814671/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4532InputLogOnePlusV_eq :
    leaf4532InputLogOnePlusV = outerEnclosure 24
      (leaf4532Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4532RoundedFacts : LeafRoundedFacts 8
    leaf4532Certificate.logOnePlusV leaf4532InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4532InputLogOnePlusV_eq }

private noncomputable def leaf4532Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi282InputQChi innerPair108Input
    leaf4532InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4532LowerChecked :
    lowerCheck 24 leaf4532Box leaf4532Inputs = true := by
  rfl'

private theorem leaf4532CoversExact : CoversExact 8
    leaf4532Box leaf4532Certificate leaf4532InnerLog leaf4532Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi282RoundedFacts
    innerPair108RoundedFacts leaf4532RoundedFacts (by rfl)

private theorem leaf4532FlatSound : Sound leaf4532Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4532CertificateValid
    leaf4532InnerLogValid leaf4532CoversExact leaf4532LowerChecked

private noncomputable def leaf4533Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (37/128), chiHi := (75/256) }

private noncomputable def leaf4533Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871279/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357645568) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1060569523/536870912) }, upper := { exponent := 0, mantissa := (16367/8192) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi283LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716368127/68715291136) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf4533InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4533LocalValidity :
    LeafFacts leaf4533Box leaf4533Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4533Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357645568) }) = true
      norm_num [leaf4533Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4533CertificateValid :
    WideCertificateValid leaf4533Box leaf4533Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi283ValidityFacts
    leaf4533LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4533CoverageChecked :
    coverageCheck (innerAD leaf4533Box) leaf4533InnerLog = true := by
  rfl'

private theorem leaf4533InnerLogValid :
    leaf4533InnerLog.Valid 8 (innerAD leaf4533Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4533CoverageChecked

private noncomputable def leaf4533InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (363417/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf4533InputLogOnePlusV_eq :
    leaf4533InputLogOnePlusV = outerEnclosure 24
      (leaf4533Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4533RoundedFacts : LeafRoundedFacts 8
    leaf4533Certificate.logOnePlusV leaf4533InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4533InputLogOnePlusV_eq }

private noncomputable def leaf4533Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi283InputQChi innerPair108Input
    leaf4533InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4533LowerChecked :
    lowerCheck 24 leaf4533Box leaf4533Inputs = true := by
  rfl'

private theorem leaf4533CoversExact : CoversExact 8
    leaf4533Box leaf4533Certificate leaf4533InnerLog leaf4533Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi283RoundedFacts
    innerPair108RoundedFacts leaf4533RoundedFacts (by rfl)

private theorem leaf4533FlatSound : Sound leaf4533Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4533CertificateValid
    leaf4533InnerLogValid leaf4533CoversExact leaf4533LowerChecked

private noncomputable def leaf4534Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (75/256), chiHi := (19/64) }

private noncomputable def leaf4534Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871281/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357617664) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1067646977/536870912) }, upper := { exponent := 1, mantissa := (4119/4096) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi284LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716340223/68715235328) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf4534InnerLog : WideLogData :=
  innerPair533Data

set_option maxRecDepth 1000000 in
private theorem leaf4534LocalValidity :
    LeafFacts leaf4534Box leaf4534Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4534Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357617664) }) = true
      norm_num [leaf4534Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4534CertificateValid :
    WideCertificateValid leaf4534Box leaf4534Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi284ValidityFacts
    leaf4534LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4534CoverageChecked :
    coverageCheck (innerAD leaf4534Box) leaf4534InnerLog = true := by
  rfl'

private theorem leaf4534InnerLogValid :
    leaf4534InnerLog.Valid 8 (innerAD leaf4534Box) :=
  wideLogDataValid_of_cachedCheck endpoint267PositiveFacts
    endpoint283PositiveFacts.valid leaf4534CoverageChecked

private noncomputable def leaf4534InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629351/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4534InputLogOnePlusV_eq :
    leaf4534InputLogOnePlusV = outerEnclosure 24
      (leaf4534Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4534RoundedFacts : LeafRoundedFacts 8
    leaf4534Certificate.logOnePlusV leaf4534InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4534InputLogOnePlusV_eq }

private noncomputable def leaf4534Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi284InputQChi innerPair533Input
    leaf4534InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4534LowerChecked :
    lowerCheck 24 leaf4534Box leaf4534Inputs = true := by
  rfl'

private theorem leaf4534CoversExact : CoversExact 8
    leaf4534Box leaf4534Certificate leaf4534InnerLog leaf4534Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi284RoundedFacts
    innerPair533RoundedFacts leaf4534RoundedFacts (by rfl)

private theorem leaf4534FlatSound : Sound leaf4534Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4534CertificateValid
    leaf4534InnerLogValid leaf4534CoversExact leaf4534LowerChecked

private noncomputable def leaf4535Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (37/128), chiHi := (75/256) }

private noncomputable def leaf4535Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871281/536870912) }, vSqrt := { lower := (65529/65536), upper := (1108345889/1108310528) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1065418889/536870912) }, upper := { exponent := 1, mantissa := (8221/8192) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi283LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (2216656417/2216621056) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf4535InnerLog : WideLogData :=
  innerPair533Data

set_option maxRecDepth 1000000 in
private theorem leaf4535LocalValidity :
    LeafFacts leaf4535Box leaf4535Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4535Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (1108345889/1108310528) }) = true
      norm_num [leaf4535Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4535CertificateValid :
    WideCertificateValid leaf4535Box leaf4535Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi283ValidityFacts
    leaf4535LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4535CoverageChecked :
    coverageCheck (innerAD leaf4535Box) leaf4535InnerLog = true := by
  rfl'

private theorem leaf4535InnerLogValid :
    leaf4535InnerLog.Valid 8 (innerAD leaf4535Box) :=
  wideLogDataValid_of_cachedCheck endpoint267PositiveFacts
    endpoint283PositiveFacts.valid leaf4535CoverageChecked

private noncomputable def leaf4535InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907337/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4535InputLogOnePlusV_eq :
    leaf4535InputLogOnePlusV = outerEnclosure 24
      (leaf4535Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4535RoundedFacts : LeafRoundedFacts 8
    leaf4535Certificate.logOnePlusV leaf4535InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4535InputLogOnePlusV_eq }

private noncomputable def leaf4535Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi283InputQChi innerPair533Input
    leaf4535InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4535LowerChecked :
    lowerCheck 24 leaf4535Box leaf4535Inputs = true := by
  rfl'

private theorem leaf4535CoversExact : CoversExact 8
    leaf4535Box leaf4535Certificate leaf4535InnerLog leaf4535Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi283RoundedFacts
    innerPair533RoundedFacts leaf4535RoundedFacts (by rfl)

private theorem leaf4535FlatSound : Sound leaf4535Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4535CertificateValid
    leaf4535InnerLogValid leaf4535CoversExact leaf4535LowerChecked

private noncomputable def leaf4536Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (75/256), chiHi := (19/64) }

private noncomputable def leaf4536Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871283/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357598208) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1072561875/536870912) }, upper := { exponent := 1, mantissa := (2069/2048) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi284LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716320767/68715196416) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf4536InnerLog : WideLogData :=
  innerPair531Data

set_option maxRecDepth 1000000 in
private theorem leaf4536LocalValidity :
    LeafFacts leaf4536Box leaf4536Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4536Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357598208) }) = true
      norm_num [leaf4536Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4536CertificateValid :
    WideCertificateValid leaf4536Box leaf4536Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi284ValidityFacts
    leaf4536LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4536CoverageChecked :
    coverageCheck (innerAD leaf4536Box) leaf4536InnerLog = true := by
  rfl'

private theorem leaf4536InnerLogValid :
    leaf4536InnerLog.Valid 8 (innerAD leaf4536Box) :=
  wideLogDataValid_of_cachedCheck endpoint267PositiveFacts
    endpoint82PositiveFacts.valid leaf4536CoverageChecked

private noncomputable def leaf4536InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629355/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4536InputLogOnePlusV_eq :
    leaf4536InputLogOnePlusV = outerEnclosure 24
      (leaf4536Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4536RoundedFacts : LeafRoundedFacts 8
    leaf4536Certificate.logOnePlusV leaf4536InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4536InputLogOnePlusV_eq }

private noncomputable def leaf4536Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi284InputQChi innerPair531Input
    leaf4536InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4536LowerChecked :
    lowerCheck 24 leaf4536Box leaf4536Inputs = true := by
  rfl'

private theorem leaf4536CoversExact : CoversExact 8
    leaf4536Box leaf4536Certificate leaf4536InnerLog leaf4536Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi284RoundedFacts
    innerPair531RoundedFacts leaf4536RoundedFacts (by rfl)

private theorem leaf4536FlatSound : Sound leaf4536Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4536CertificateValid
    leaf4536InnerLogValid leaf4536CoversExact leaf4536LowerChecked

private noncomputable def leaf4537Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (9/32), chiHi := (73/256) }

private noncomputable def leaf4537Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871279/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357664000) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1055851219/536870912) }, upper := { exponent := 0, mantissa := (16295/8192) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi281LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716386559/68715328000) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf4537InnerLog : WideLogData :=
  innerPair601Data

set_option maxRecDepth 1000000 in
private theorem leaf4537LocalValidity :
    LeafFacts leaf4537Box leaf4537Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4537Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357664000) }) = true
      norm_num [leaf4537Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4537CertificateValid :
    WideCertificateValid leaf4537Box leaf4537Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi281ValidityFacts
    leaf4537LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4537CoverageChecked :
    coverageCheck (innerAD leaf4537Box) leaf4537InnerLog = true := by
  rfl'

private theorem leaf4537InnerLogValid :
    leaf4537InnerLog.Valid 8 (innerAD leaf4537Box) :=
  wideLogDataValid_of_cachedCheck endpoint319PositiveFacts
    endpoint278PositiveFacts.valid leaf4537CoverageChecked

private noncomputable def leaf4537InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629339/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4537InputLogOnePlusV_eq :
    leaf4537InputLogOnePlusV = outerEnclosure 24
      (leaf4537Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4537RoundedFacts : LeafRoundedFacts 8
    leaf4537Certificate.logOnePlusV leaf4537InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4537InputLogOnePlusV_eq }

private noncomputable def leaf4537Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi281InputQChi innerPair601Input
    leaf4537InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4537LowerChecked :
    lowerCheck 24 leaf4537Box leaf4537Inputs = true := by
  rfl'

private theorem leaf4537CoversExact : CoversExact 8
    leaf4537Box leaf4537Certificate leaf4537InnerLog leaf4537Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi281RoundedFacts
    innerPair601RoundedFacts leaf4537RoundedFacts (by rfl)

private theorem leaf4537FlatSound : Sound leaf4537Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4537CertificateValid
    leaf4537InnerLogValid leaf4537CoversExact leaf4537LowerChecked

private noncomputable def leaf4538Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (73/256), chiHi := (37/128) }

private noncomputable def leaf4538Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871281/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357635584) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1063059737/536870912) }, upper := { exponent := 1, mantissa := (8203/8192) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi282LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716358143/68715271168) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf4538InnerLog : WideLogData :=
  innerPair541Data

set_option maxRecDepth 1000000 in
private theorem leaf4538LocalValidity :
    LeafFacts leaf4538Box leaf4538Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4538Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357635584) }) = true
      norm_num [leaf4538Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4538CertificateValid :
    WideCertificateValid leaf4538Box leaf4538Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi282ValidityFacts
    leaf4538LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4538CoverageChecked :
    coverageCheck (innerAD leaf4538Box) leaf4538InnerLog = true := by
  rfl'

private theorem leaf4538InnerLogValid :
    leaf4538InnerLog.Valid 8 (innerAD leaf4538Box) :=
  wideLogDataValid_of_cachedCheck endpoint275PositiveFacts
    endpoint320PositiveFacts.valid leaf4538CoverageChecked

private noncomputable def leaf4538InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814673/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4538InputLogOnePlusV_eq :
    leaf4538InputLogOnePlusV = outerEnclosure 24
      (leaf4538Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4538RoundedFacts : LeafRoundedFacts 8
    leaf4538Certificate.logOnePlusV leaf4538InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4538InputLogOnePlusV_eq }

private noncomputable def leaf4538Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi282InputQChi innerPair541Input
    leaf4538InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4538LowerChecked :
    lowerCheck 24 leaf4538Box leaf4538Inputs = true := by
  rfl'

private theorem leaf4538CoversExact : CoversExact 8
    leaf4538Box leaf4538Certificate leaf4538InnerLog leaf4538Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi282RoundedFacts
    innerPair541RoundedFacts leaf4538RoundedFacts (by rfl)

private theorem leaf4538FlatSound : Sound leaf4538Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4538CertificateValid
    leaf4538InnerLogValid leaf4538CoversExact leaf4538LowerChecked

private noncomputable def leaf4539Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (223/64), chiLo := (9/32), chiHi := (73/256) }

private noncomputable def leaf4539Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742415/1073741824) }, vSqrt := { lower := (65529/65536), upper := (7635268039/7635034368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2121171955/1073741824) }, upper := { exponent := 0, mantissa := (32663/16384) } }, logOuter := sk181LogOuterCertificate, logK := sk181LogKCertificate, logChi := chi281LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (15270302407/15270068736) } }, logDArg := sk181LogDArgCertificate }

private noncomputable def leaf4539InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4539LocalValidity :
    LeafFacts leaf4539Box leaf4539Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4539Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (7635268039/7635034368) }) = true
      norm_num [leaf4539Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4539CertificateValid :
    WideCertificateValid leaf4539Box leaf4539Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk181ValidityFacts chi281ValidityFacts
    leaf4539LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4539CoverageChecked :
    coverageCheck (innerAD leaf4539Box) leaf4539InnerLog = true := by
  rfl'

private theorem leaf4539InnerLogValid :
    leaf4539InnerLog.Valid 8 (innerAD leaf4539Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4539CoverageChecked

private noncomputable def leaf4539InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629337/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4539InputLogOnePlusV_eq :
    leaf4539InputLogOnePlusV = outerEnclosure 24
      (leaf4539Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4539RoundedFacts : LeafRoundedFacts 8
    leaf4539Certificate.logOnePlusV leaf4539InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4539InputLogOnePlusV_eq }

private noncomputable def leaf4539Inputs : Inputs :=
  inputsOfCaches globalInput sk181RoundedInputs
    chi281InputQChi innerPair108Input
    leaf4539InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4539LowerChecked :
    lowerCheck 24 leaf4539Box leaf4539Inputs = true := by
  rfl'

private theorem leaf4539CoversExact : CoversExact 8
    leaf4539Box leaf4539Certificate leaf4539InnerLog leaf4539Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk181RoundedFacts chi281RoundedFacts
    innerPair108RoundedFacts leaf4539RoundedFacts (by rfl)

private theorem leaf4539FlatSound : Sound leaf4539Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4539CertificateValid
    leaf4539InnerLogValid leaf4539CoversExact leaf4539LowerChecked

private noncomputable def leaf4540Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (223/64), kHi := (7/2), chiLo := (9/32), chiHi := (73/256) }

private noncomputable def leaf4540Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742417/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715290624) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2125890257/1073741824) }, upper := { exponent := 0, mantissa := (1023/512) } }, logOuter := sk182LogOuterCertificate, logK := sk182LogKCertificate, logChi := chi281LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432702975/137430581248) } }, logDArg := sk182LogDArgCertificate }

private noncomputable def leaf4540InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4540LocalValidity :
    LeafFacts leaf4540Box leaf4540Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4540Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715290624) }) = true
      norm_num [leaf4540Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4540CertificateValid :
    WideCertificateValid leaf4540Box leaf4540Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk182ValidityFacts chi281ValidityFacts
    leaf4540LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4540CoverageChecked :
    coverageCheck (innerAD leaf4540Box) leaf4540InnerLog = true := by
  rfl'

private theorem leaf4540InnerLogValid :
    leaf4540InnerLog.Valid 8 (innerAD leaf4540Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4540CoverageChecked

private noncomputable def leaf4540InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907335/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4540InputLogOnePlusV_eq :
    leaf4540InputLogOnePlusV = outerEnclosure 24
      (leaf4540Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4540RoundedFacts : LeafRoundedFacts 8
    leaf4540Certificate.logOnePlusV leaf4540InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4540InputLogOnePlusV_eq }

private noncomputable def leaf4540Inputs : Inputs :=
  inputsOfCaches globalInput sk182RoundedInputs
    chi281InputQChi innerPair108Input
    leaf4540InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4540LowerChecked :
    lowerCheck 24 leaf4540Box leaf4540Inputs = true := by
  rfl'

private theorem leaf4540CoversExact : CoversExact 8
    leaf4540Box leaf4540Certificate leaf4540InnerLog leaf4540Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk182RoundedFacts chi281RoundedFacts
    innerPair108RoundedFacts leaf4540RoundedFacts (by rfl)

private theorem leaf4540FlatSound : Sound leaf4540Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4540CertificateValid
    leaf4540InnerLogValid leaf4540CoversExact leaf4540LowerChecked

private noncomputable def leaf4541Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (73/256), chiHi := (37/128) }

private noncomputable def leaf4541Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871283/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357616640) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1067843571/536870912) }, upper := { exponent := 1, mantissa := (515/512) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi282LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68716339199/68715233280) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf4541InnerLog : WideLogData :=
  innerPair543Data

set_option maxRecDepth 1000000 in
private theorem leaf4541LocalValidity :
    LeafFacts leaf4541Box leaf4541Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4541Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357616640) }) = true
      norm_num [leaf4541Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4541CertificateValid :
    WideCertificateValid leaf4541Box leaf4541Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi282ValidityFacts
    leaf4541LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4541CoverageChecked :
    coverageCheck (innerAD leaf4541Box) leaf4541InnerLog = true := by
  rfl'

private theorem leaf4541InnerLogValid :
    leaf4541InnerLog.Valid 8 (innerAD leaf4541Box) :=
  wideLogDataValid_of_cachedCheck endpoint277PositiveFacts
    endpoint321PositiveFacts.valid leaf4541CoverageChecked

private noncomputable def leaf4541InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629351/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4541InputLogOnePlusV_eq :
    leaf4541InputLogOnePlusV = outerEnclosure 24
      (leaf4541Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4541RoundedFacts : LeafRoundedFacts 8
    leaf4541Certificate.logOnePlusV leaf4541InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4541InputLogOnePlusV_eq }

private noncomputable def leaf4541Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi282InputQChi innerPair543Input
    leaf4541InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4541LowerChecked :
    lowerCheck 24 leaf4541Box leaf4541Inputs = true := by
  rfl'

private theorem leaf4541CoversExact : CoversExact 8
    leaf4541Box leaf4541Certificate leaf4541InnerLog leaf4541Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi282RoundedFacts
    innerPair543RoundedFacts leaf4541RoundedFacts (by rfl)

private theorem leaf4541FlatSound : Sound leaf4541Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4541CertificateValid
    leaf4541InnerLogValid leaf4541CoversExact leaf4541LowerChecked

private noncomputable def leaf4542Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (37/128), chiHi := (75/256) }

private noncomputable def leaf4542Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871283/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357607168) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1070268255/536870912) }, upper := { exponent := 1, mantissa := (16517/16384) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi283LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716329727/68715214336) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf4542InnerLog : WideLogData :=
  innerPair545Data

set_option maxRecDepth 1000000 in
private theorem leaf4542LocalValidity :
    LeafFacts leaf4542Box leaf4542Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4542Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357607168) }) = true
      norm_num [leaf4542Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4542CertificateValid :
    WideCertificateValid leaf4542Box leaf4542Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi283ValidityFacts
    leaf4542LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4542CoverageChecked :
    coverageCheck (innerAD leaf4542Box) leaf4542InnerLog = true := by
  rfl'

private theorem leaf4542InnerLogValid :
    leaf4542InnerLog.Valid 8 (innerAD leaf4542Box) :=
  wideLogDataValid_of_cachedCheck endpoint278PositiveFacts
    endpoint322PositiveFacts.valid leaf4542CoverageChecked

private noncomputable def leaf4542InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629353/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4542InputLogOnePlusV_eq :
    leaf4542InputLogOnePlusV = outerEnclosure 24
      (leaf4542Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4542RoundedFacts : LeafRoundedFacts 8
    leaf4542Certificate.logOnePlusV leaf4542InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4542InputLogOnePlusV_eq }

private noncomputable def leaf4542Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi283InputQChi innerPair545Input
    leaf4542InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4542LowerChecked :
    lowerCheck 24 leaf4542Box leaf4542Inputs = true := by
  rfl'

private theorem leaf4542CoversExact : CoversExact 8
    leaf4542Box leaf4542Certificate leaf4542InnerLog leaf4542Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi283RoundedFacts
    innerPair545RoundedFacts leaf4542RoundedFacts (by rfl)

private theorem leaf4542FlatSound : Sound leaf4542Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4542CertificateValid
    leaf4542InnerLogValid leaf4542CoversExact leaf4542LowerChecked

private noncomputable def leaf4543Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (75/256), chiHi := (19/64) }

private noncomputable def leaf4543Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871285/536870912) }, vSqrt := { lower := (65529/65536), upper := (158335127/158329856) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1077476773/1073741824) }, upper := { exponent := 1, mantissa := (4157/4096) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi284LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (316664983/316659712) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf4543InnerLog : WideLogData :=
  innerPair119Data

set_option maxRecDepth 1000000 in
private theorem leaf4543LocalValidity :
    LeafFacts leaf4543Box leaf4543Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4543Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (158335127/158329856) }) = true
      norm_num [leaf4543Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4543CertificateValid :
    WideCertificateValid leaf4543Box leaf4543Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi284ValidityFacts
    leaf4543LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4543CoverageChecked :
    coverageCheck (innerAD leaf4543Box) leaf4543InnerLog = true := by
  rfl'

private theorem leaf4543InnerLogValid :
    leaf4543InnerLog.Valid 8 (innerAD leaf4543Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint82PositiveFacts.valid leaf4543CoverageChecked

private noncomputable def leaf4543InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (726835/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf4543InputLogOnePlusV_eq :
    leaf4543InputLogOnePlusV = outerEnclosure 24
      (leaf4543Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4543RoundedFacts : LeafRoundedFacts 8
    leaf4543Certificate.logOnePlusV leaf4543InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4543InputLogOnePlusV_eq }

private noncomputable def leaf4543Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi284InputQChi innerPair119Input
    leaf4543InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4543LowerChecked :
    lowerCheck 24 leaf4543Box leaf4543Inputs = true := by
  rfl'

private theorem leaf4543CoversExact : CoversExact 8
    leaf4543Box leaf4543Certificate leaf4543InnerLog leaf4543Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi284RoundedFacts
    innerPair119RoundedFacts leaf4543RoundedFacts (by rfl)

private theorem leaf4543FlatSound : Sound leaf4543Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4543CertificateValid
    leaf4543InnerLogValid leaf4543CoversExact leaf4543LowerChecked

private noncomputable def leaf4544Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (37/128), chiHi := (75/256) }

private noncomputable def leaf4544Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871285/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357587968) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1075117621/1073741824) }, upper := { exponent := 1, mantissa := (1037/1024) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi283LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68716310527/68715175936) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf4544InnerLog : WideLogData :=
  innerPair122Data

set_option maxRecDepth 1000000 in
private theorem leaf4544LocalValidity :
    LeafFacts leaf4544Box leaf4544Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4544Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357587968) }) = true
      norm_num [leaf4544Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4544CertificateValid :
    WideCertificateValid leaf4544Box leaf4544Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi283ValidityFacts
    leaf4544LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4544CoverageChecked :
    coverageCheck (innerAD leaf4544Box) leaf4544InnerLog = true := by
  rfl'

private theorem leaf4544InnerLogValid :
    leaf4544InnerLog.Valid 8 (innerAD leaf4544Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint323PositiveFacts.valid leaf4544CoverageChecked

private noncomputable def leaf4544InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814679/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4544InputLogOnePlusV_eq :
    leaf4544InputLogOnePlusV = outerEnclosure 24
      (leaf4544Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4544RoundedFacts : LeafRoundedFacts 8
    leaf4544Certificate.logOnePlusV leaf4544InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4544InputLogOnePlusV_eq }

private noncomputable def leaf4544Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi283InputQChi innerPair122Input
    leaf4544InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4544LowerChecked :
    lowerCheck 24 leaf4544Box leaf4544Inputs = true := by
  rfl'

private theorem leaf4544CoversExact : CoversExact 8
    leaf4544Box leaf4544Certificate leaf4544InnerLog leaf4544Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi283RoundedFacts
    innerPair122RoundedFacts leaf4544RoundedFacts (by rfl)

private theorem leaf4544FlatSound : Sound leaf4544Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4544CertificateValid
    leaf4544InnerLogValid leaf4544CoversExact leaf4544LowerChecked

private noncomputable def leaf4545Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (75/256), chiHi := (19/64) }

private noncomputable def leaf4545Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871287/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357559296) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1082391671/1073741824) }, upper := { exponent := 1, mantissa := (261/256) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi284LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68716281855/68715118592) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf4545InnerLog : WideLogData :=
  innerPair550Data

set_option maxRecDepth 1000000 in
private theorem leaf4545LocalValidity :
    LeafFacts leaf4545Box leaf4545Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4545Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357559296) }) = true
      norm_num [leaf4545Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4545CertificateValid :
    WideCertificateValid leaf4545Box leaf4545Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi284ValidityFacts
    leaf4545LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4545CoverageChecked :
    coverageCheck (innerAD leaf4545Box) leaf4545InnerLog = true := by
  rfl'

private theorem leaf4545InnerLogValid :
    leaf4545InnerLog.Valid 8 (innerAD leaf4545Box) :=
  wideLogDataValid_of_cachedCheck endpoint283PositiveFacts
    endpoint324PositiveFacts.valid leaf4545CoverageChecked

private noncomputable def leaf4545InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629365/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4545InputLogOnePlusV_eq :
    leaf4545InputLogOnePlusV = outerEnclosure 24
      (leaf4545Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4545RoundedFacts : LeafRoundedFacts 8
    leaf4545Certificate.logOnePlusV leaf4545InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4545InputLogOnePlusV_eq }

private noncomputable def leaf4545Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi284InputQChi innerPair550Input
    leaf4545InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4545LowerChecked :
    lowerCheck 24 leaf4545Box leaf4545Inputs = true := by
  rfl'

private theorem leaf4545CoversExact : CoversExact 8
    leaf4545Box leaf4545Certificate leaf4545InnerLog leaf4545Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi284RoundedFacts
    innerPair550RoundedFacts leaf4545RoundedFacts (by rfl)

private theorem leaf4545FlatSound : Sound leaf4545Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4545CertificateValid
    leaf4545InnerLogValid leaf4545CoversExact leaf4545LowerChecked

private noncomputable def leaf4546Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (19/64), chiHi := (77/256) }

private noncomputable def leaf4546Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871283/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357589760) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1074724431/1073741824) }, upper := { exponent := 1, mantissa := (16585/16384) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi285LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716312319/68715179520) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf4546InnerLog : WideLogData :=
  innerPair119Data

set_option maxRecDepth 1000000 in
private theorem leaf4546LocalValidity :
    LeafFacts leaf4546Box leaf4546Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4546Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357589760) }) = true
      norm_num [leaf4546Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4546CertificateValid :
    WideCertificateValid leaf4546Box leaf4546Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi285ValidityFacts
    leaf4546LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4546CoverageChecked :
    coverageCheck (innerAD leaf4546Box) leaf4546InnerLog = true := by
  rfl'

private theorem leaf4546InnerLogValid :
    leaf4546InnerLog.Valid 8 (innerAD leaf4546Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint82PositiveFacts.valid leaf4546CoverageChecked

private noncomputable def leaf4546InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629357/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4546InputLogOnePlusV_eq :
    leaf4546InputLogOnePlusV = outerEnclosure 24
      (leaf4546Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4546RoundedFacts : LeafRoundedFacts 8
    leaf4546Certificate.logOnePlusV leaf4546InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4546InputLogOnePlusV_eq }

private noncomputable def leaf4546Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi285InputQChi innerPair119Input
    leaf4546InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4546LowerChecked :
    lowerCheck 24 leaf4546Box leaf4546Inputs = true := by
  rfl'

private theorem leaf4546CoversExact : CoversExact 8
    leaf4546Box leaf4546Certificate leaf4546InnerLog leaf4546Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi285RoundedFacts
    innerPair119RoundedFacts leaf4546RoundedFacts (by rfl)

private theorem leaf4546FlatSound : Sound leaf4546Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4546CertificateValid
    leaf4546InnerLogValid leaf4546CoversExact leaf4546LowerChecked

private noncomputable def leaf4547Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (77/256), chiHi := (39/128) }

private noncomputable def leaf4547Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871285/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357561856) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1081801885/1073741824) }, upper := { exponent := 1, mantissa := (8347/8192) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi286LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716284415/68715123712) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf4547InnerLog : WideLogData :=
  innerPair121Data

set_option maxRecDepth 1000000 in
private theorem leaf4547LocalValidity :
    LeafFacts leaf4547Box leaf4547Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4547Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357561856) }) = true
      norm_num [leaf4547Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4547CertificateValid :
    WideCertificateValid leaf4547Box leaf4547Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi286ValidityFacts
    leaf4547LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4547CoverageChecked :
    coverageCheck (innerAD leaf4547Box) leaf4547InnerLog = true := by
  rfl'

private theorem leaf4547InnerLogValid :
    leaf4547InnerLog.Valid 8 (innerAD leaf4547Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint87PositiveFacts.valid leaf4547CoverageChecked

private noncomputable def leaf4547InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907341/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4547InputLogOnePlusV_eq :
    leaf4547InputLogOnePlusV = outerEnclosure 24
      (leaf4547Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4547RoundedFacts : LeafRoundedFacts 8
    leaf4547Certificate.logOnePlusV leaf4547InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4547InputLogOnePlusV_eq }

private noncomputable def leaf4547Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi286InputQChi innerPair121Input
    leaf4547InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4547LowerChecked :
    lowerCheck 24 leaf4547Box leaf4547Inputs = true := by
  rfl'

private theorem leaf4547CoversExact : CoversExact 8
    leaf4547Box leaf4547Certificate leaf4547InnerLog leaf4547Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi286RoundedFacts
    innerPair121RoundedFacts leaf4547RoundedFacts (by rfl)

private theorem leaf4547FlatSound : Sound leaf4547Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4547CertificateValid
    leaf4547InnerLogValid leaf4547CoversExact leaf4547LowerChecked

private noncomputable def leaf4548Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (19/64), chiHi := (77/256) }

private noncomputable def leaf4548Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871285/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357570048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1079704861/1073741824) }, upper := { exponent := 1, mantissa := (8331/8192) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi285LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716292607/68715140096) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf4548InnerLog : WideLogData :=
  innerPair121Data

set_option maxRecDepth 1000000 in
private theorem leaf4548LocalValidity :
    LeafFacts leaf4548Box leaf4548Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4548Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357570048) }) = true
      norm_num [leaf4548Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4548CertificateValid :
    WideCertificateValid leaf4548Box leaf4548Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi285ValidityFacts
    leaf4548LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4548CoverageChecked :
    coverageCheck (innerAD leaf4548Box) leaf4548InnerLog = true := by
  rfl'

private theorem leaf4548InnerLogValid :
    leaf4548InnerLog.Valid 8 (innerAD leaf4548Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint87PositiveFacts.valid leaf4548CoverageChecked

private noncomputable def leaf4548InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814681/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4548InputLogOnePlusV_eq :
    leaf4548InputLogOnePlusV = outerEnclosure 24
      (leaf4548Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4548RoundedFacts : LeafRoundedFacts 8
    leaf4548Certificate.logOnePlusV leaf4548InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4548InputLogOnePlusV_eq }

private noncomputable def leaf4548Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi285InputQChi innerPair121Input
    leaf4548InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4548LowerChecked :
    lowerCheck 24 leaf4548Box leaf4548Inputs = true := by
  rfl'

private theorem leaf4548CoversExact : CoversExact 8
    leaf4548Box leaf4548Certificate leaf4548InnerLog leaf4548Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi285RoundedFacts
    innerPair121RoundedFacts leaf4548RoundedFacts (by rfl)

private theorem leaf4548FlatSound : Sound leaf4548Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4548CertificateValid
    leaf4548InnerLogValid leaf4548CoversExact leaf4548LowerChecked

private noncomputable def leaf4549Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (77/256), chiHi := (39/128) }

private noncomputable def leaf4549Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871287/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357541888) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1086847847/1073741824) }, upper := { exponent := 1, mantissa := (4193/4096) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi286LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716264447/68715083776) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf4549InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4549LocalValidity :
    LeafFacts leaf4549Box leaf4549Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4549Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357541888) }) = true
      norm_num [leaf4549Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4549CertificateValid :
    WideCertificateValid leaf4549Box leaf4549Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi286ValidityFacts
    leaf4549LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4549CoverageChecked :
    coverageCheck (innerAD leaf4549Box) leaf4549InnerLog = true := by
  rfl'

private theorem leaf4549InnerLogValid :
    leaf4549InnerLog.Valid 8 (innerAD leaf4549Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4549CoverageChecked

private noncomputable def leaf4549InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629369/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4549InputLogOnePlusV_eq :
    leaf4549InputLogOnePlusV = outerEnclosure 24
      (leaf4549Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4549RoundedFacts : LeafRoundedFacts 8
    leaf4549Certificate.logOnePlusV leaf4549InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4549InputLogOnePlusV_eq }

private noncomputable def leaf4549Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi286InputQChi innerPair116Input
    leaf4549InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4549LowerChecked :
    lowerCheck 24 leaf4549Box leaf4549Inputs = true := by
  rfl'

private theorem leaf4549CoversExact : CoversExact 8
    leaf4549Box leaf4549Certificate leaf4549InnerLog leaf4549Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi286RoundedFacts
    innerPair116RoundedFacts leaf4549RoundedFacts (by rfl)

private theorem leaf4549FlatSound : Sound leaf4549Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4549CertificateValid
    leaf4549InnerLogValid leaf4549CoversExact leaf4549LowerChecked

private noncomputable def leaf4550Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (39/128), chiHi := (79/256) }

private noncomputable def leaf4550Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871287/536870912) }, vSqrt := { lower := (65529/65536), upper := (4908388937/4908219136) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1088879339/1073741824) }, upper := { exponent := 1, mantissa := (16803/16384) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi287LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (9816608073/9816438272) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf4550InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4550LocalValidity :
    LeafFacts leaf4550Box leaf4550Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4550Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4908388937/4908219136) }) = true
      norm_num [leaf4550Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4550CertificateValid :
    WideCertificateValid leaf4550Box leaf4550Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi287ValidityFacts
    leaf4550LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4550CoverageChecked :
    coverageCheck (innerAD leaf4550Box) leaf4550InnerLog = true := by
  rfl'

private theorem leaf4550InnerLogValid :
    leaf4550InnerLog.Valid 8 (innerAD leaf4550Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4550CoverageChecked

private noncomputable def leaf4550InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629371/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4550InputLogOnePlusV_eq :
    leaf4550InputLogOnePlusV = outerEnclosure 24
      (leaf4550Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4550RoundedFacts : LeafRoundedFacts 8
    leaf4550Certificate.logOnePlusV leaf4550InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4550InputLogOnePlusV_eq }

private noncomputable def leaf4550Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi287InputQChi innerPair116Input
    leaf4550InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4550LowerChecked :
    lowerCheck 24 leaf4550Box leaf4550Inputs = true := by
  rfl'

private theorem leaf4550CoversExact : CoversExact 8
    leaf4550Box leaf4550Certificate leaf4550InnerLog leaf4550Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi287RoundedFacts
    innerPair116RoundedFacts leaf4550RoundedFacts (by rfl)

private theorem leaf4550FlatSound : Sound leaf4550Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4550CertificateValid
    leaf4550InnerLogValid leaf4550CoversExact leaf4550LowerChecked

private noncomputable def leaf4551Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (79/256), chiHi := (5/16) }

private noncomputable def leaf4551Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871289/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357506048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1095956793/1073741824) }, upper := { exponent := 1, mantissa := (1057/1024) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi288LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716228607/68715012096) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf4551InnerLog : WideLogData :=
  innerPair311Data

set_option maxRecDepth 1000000 in
private theorem leaf4551LocalValidity :
    LeafFacts leaf4551Box leaf4551Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4551Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357506048) }) = true
      norm_num [leaf4551Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4551CertificateValid :
    WideCertificateValid leaf4551Box leaf4551Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi288ValidityFacts
    leaf4551LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4551CoverageChecked :
    coverageCheck (innerAD leaf4551Box) leaf4551InnerLog = true := by
  rfl'

private theorem leaf4551InnerLogValid :
    leaf4551InnerLog.Valid 8 (innerAD leaf4551Box) :=
  wideLogDataValid_of_cachedCheck endpoint82PositiveFacts
    endpoint86PositiveFacts.valid leaf4551CoverageChecked

private noncomputable def leaf4551InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814689/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4551InputLogOnePlusV_eq :
    leaf4551InputLogOnePlusV = outerEnclosure 24
      (leaf4551Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4551RoundedFacts : LeafRoundedFacts 8
    leaf4551Certificate.logOnePlusV leaf4551InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4551InputLogOnePlusV_eq }

private noncomputable def leaf4551Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi288InputQChi innerPair311Input
    leaf4551InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4551LowerChecked :
    lowerCheck 24 leaf4551Box leaf4551Inputs = true := by
  rfl'

private theorem leaf4551CoversExact : CoversExact 8
    leaf4551Box leaf4551Certificate leaf4551InnerLog leaf4551Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi288RoundedFacts
    innerPair311RoundedFacts leaf4551RoundedFacts (by rfl)

private theorem leaf4551FlatSound : Sound leaf4551Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4551CertificateValid
    leaf4551InnerLogValid leaf4551CoversExact leaf4551LowerChecked

private noncomputable def leaf4552Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (39/128), chiHi := (79/256) }

private noncomputable def leaf4552Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871289/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357513728) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1093990833/1073741824) }, upper := { exponent := 1, mantissa := (8441/8192) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi287LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716236287/68715027456) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf4552InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4552LocalValidity :
    LeafFacts leaf4552Box leaf4552Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4552Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357513728) }) = true
      norm_num [leaf4552Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4552CertificateValid :
    WideCertificateValid leaf4552Box leaf4552Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi287ValidityFacts
    leaf4552LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4552CoverageChecked :
    coverageCheck (innerAD leaf4552Box) leaf4552InnerLog = true := by
  rfl'

private theorem leaf4552InnerLogValid :
    leaf4552InnerLog.Valid 8 (innerAD leaf4552Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4552CoverageChecked

private noncomputable def leaf4552InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (181709/262144) }

set_option maxRecDepth 1000000 in
private theorem leaf4552InputLogOnePlusV_eq :
    leaf4552InputLogOnePlusV = outerEnclosure 24
      (leaf4552Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4552RoundedFacts : LeafRoundedFacts 8
    leaf4552Certificate.logOnePlusV leaf4552InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4552InputLogOnePlusV_eq }

private noncomputable def leaf4552Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi287InputQChi innerPair116Input
    leaf4552InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4552LowerChecked :
    lowerCheck 24 leaf4552Box leaf4552Inputs = true := by
  rfl'

private theorem leaf4552CoversExact : CoversExact 8
    leaf4552Box leaf4552Certificate leaf4552InnerLog leaf4552Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi287RoundedFacts
    innerPair116RoundedFacts leaf4552RoundedFacts (by rfl)

private theorem leaf4552FlatSound : Sound leaf4552Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4552CertificateValid
    leaf4552InnerLogValid leaf4552CoversExact leaf4552LowerChecked

private noncomputable def leaf4553Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (79/256), chiHi := (5/16) }

private noncomputable def leaf4553Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871291/536870912) }, vSqrt := { lower := (65529/65536), upper := (4908388937/4908212224) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1101133819/1073741824) }, upper := { exponent := 1, mantissa := (531/512) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi288LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (9816601161/9816424448) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf4553InnerLog : WideLogData :=
  innerPair327Data

set_option maxRecDepth 1000000 in
private theorem leaf4553LocalValidity :
    LeafFacts leaf4553Box leaf4553Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4553Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4908388937/4908212224) }) = true
      norm_num [leaf4553Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4553CertificateValid :
    WideCertificateValid leaf4553Box leaf4553Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi288ValidityFacts
    leaf4553LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4553CoverageChecked :
    coverageCheck (innerAD leaf4553Box) leaf4553InnerLog = true := by
  rfl'

private theorem leaf4553InnerLogValid :
    leaf4553InnerLog.Valid 8 (innerAD leaf4553Box) :=
  wideLogDataValid_of_cachedCheck endpoint87PositiveFacts
    endpoint86PositiveFacts.valid leaf4553CoverageChecked

private noncomputable def leaf4553InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629383/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4553InputLogOnePlusV_eq :
    leaf4553InputLogOnePlusV = outerEnclosure 24
      (leaf4553Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4553RoundedFacts : LeafRoundedFacts 8
    leaf4553Certificate.logOnePlusV leaf4553InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4553InputLogOnePlusV_eq }

private noncomputable def leaf4553Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi288InputQChi innerPair327Input
    leaf4553InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4553LowerChecked :
    lowerCheck 24 leaf4553Box leaf4553Inputs = true := by
  rfl'

private theorem leaf4553CoversExact : CoversExact 8
    leaf4553Box leaf4553Certificate leaf4553InnerLog leaf4553Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi288RoundedFacts
    innerPair327RoundedFacts leaf4553RoundedFacts (by rfl)

private theorem leaf4553FlatSound : Sound leaf4553Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4553CertificateValid
    leaf4553InnerLogValid leaf4553CoversExact leaf4553LowerChecked

private noncomputable def leaf4554Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (19/64), chiHi := (77/256) }

private noncomputable def leaf4554Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871287/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357550336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1084685291/1073741824) }, upper := { exponent := 1, mantissa := (16739/16384) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi285LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716272895/68715100672) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf4554InnerLog : WideLogData :=
  innerPair548Data

set_option maxRecDepth 1000000 in
private theorem leaf4554LocalValidity :
    LeafFacts leaf4554Box leaf4554Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4554Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357550336) }) = true
      norm_num [leaf4554Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4554CertificateValid :
    WideCertificateValid leaf4554Box leaf4554Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi285ValidityFacts
    leaf4554LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4554CoverageChecked :
    coverageCheck (innerAD leaf4554Box) leaf4554InnerLog = true := by
  rfl'

private theorem leaf4554InnerLogValid :
    leaf4554InnerLog.Valid 8 (innerAD leaf4554Box) :=
  wideLogDataValid_of_cachedCheck endpoint283PositiveFacts
    endpoint87PositiveFacts.valid leaf4554CoverageChecked

private noncomputable def leaf4554InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629367/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4554InputLogOnePlusV_eq :
    leaf4554InputLogOnePlusV = outerEnclosure 24
      (leaf4554Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4554RoundedFacts : LeafRoundedFacts 8
    leaf4554Certificate.logOnePlusV leaf4554InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4554InputLogOnePlusV_eq }

private noncomputable def leaf4554Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi285InputQChi innerPair548Input
    leaf4554InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4554LowerChecked :
    lowerCheck 24 leaf4554Box leaf4554Inputs = true := by
  rfl'

private theorem leaf4554CoversExact : CoversExact 8
    leaf4554Box leaf4554Certificate leaf4554InnerLog leaf4554Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi285RoundedFacts
    innerPair548RoundedFacts leaf4554RoundedFacts (by rfl)

private theorem leaf4554FlatSound : Sound leaf4554Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4554CertificateValid
    leaf4554InnerLogValid leaf4554CoversExact leaf4554LowerChecked

private noncomputable def leaf4555Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (77/256), chiHi := (39/128) }

private noncomputable def leaf4555Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871289/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357521920) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1091893809/1073741824) }, upper := { exponent := 1, mantissa := (8425/8192) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi286LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716244479/68715043840) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf4555InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4555LocalValidity :
    LeafFacts leaf4555Box leaf4555Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4555Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357521920) }) = true
      norm_num [leaf4555Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4555CertificateValid :
    WideCertificateValid leaf4555Box leaf4555Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi286ValidityFacts
    leaf4555LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4555CoverageChecked :
    coverageCheck (innerAD leaf4555Box) leaf4555InnerLog = true := by
  rfl'

private theorem leaf4555InnerLogValid :
    leaf4555InnerLog.Valid 8 (innerAD leaf4555Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4555CoverageChecked

private noncomputable def leaf4555InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814687/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4555InputLogOnePlusV_eq :
    leaf4555InputLogOnePlusV = outerEnclosure 24
      (leaf4555Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4555RoundedFacts : LeafRoundedFacts 8
    leaf4555Certificate.logOnePlusV leaf4555InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4555InputLogOnePlusV_eq }

private noncomputable def leaf4555Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi286InputQChi innerPair116Input
    leaf4555InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4555LowerChecked :
    lowerCheck 24 leaf4555Box leaf4555Inputs = true := by
  rfl'

private theorem leaf4555CoversExact : CoversExact 8
    leaf4555Box leaf4555Certificate leaf4555InnerLog leaf4555Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi286RoundedFacts
    innerPair116RoundedFacts leaf4555RoundedFacts (by rfl)

private theorem leaf4555FlatSound : Sound leaf4555Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4555CertificateValid
    leaf4555InnerLogValid leaf4555CoversExact leaf4555LowerChecked

private noncomputable def leaf4556Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (19/64), chiHi := (77/256) }

private noncomputable def leaf4556Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871289/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357530624) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1089665721/1073741824) }, upper := { exponent := 1, mantissa := (1051/1024) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi285LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68716253183/68715061248) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf4556InnerLog : WideLogData :=
  innerPair603Data

set_option maxRecDepth 1000000 in
private theorem leaf4556LocalValidity :
    LeafFacts leaf4556Box leaf4556Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4556Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357530624) }) = true
      norm_num [leaf4556Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4556CertificateValid :
    WideCertificateValid leaf4556Box leaf4556Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi285ValidityFacts
    leaf4556LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4556CoverageChecked :
    coverageCheck (innerAD leaf4556Box) leaf4556InnerLog = true := by
  rfl'

private theorem leaf4556InnerLogValid :
    leaf4556InnerLog.Valid 8 (innerAD leaf4556Box) :=
  wideLogDataValid_of_cachedCheck endpoint323PositiveFacts
    endpoint84PositiveFacts.valid leaf4556CoverageChecked

private noncomputable def leaf4556InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907343/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4556InputLogOnePlusV_eq :
    leaf4556InputLogOnePlusV = outerEnclosure 24
      (leaf4556Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4556RoundedFacts : LeafRoundedFacts 8
    leaf4556Certificate.logOnePlusV leaf4556InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4556InputLogOnePlusV_eq }

private noncomputable def leaf4556Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi285InputQChi innerPair603Input
    leaf4556InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4556LowerChecked :
    lowerCheck 24 leaf4556Box leaf4556Inputs = true := by
  rfl'

private theorem leaf4556CoversExact : CoversExact 8
    leaf4556Box leaf4556Certificate leaf4556InnerLog leaf4556Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi285RoundedFacts
    innerPair603RoundedFacts leaf4556RoundedFacts (by rfl)

private theorem leaf4556FlatSound : Sound leaf4556Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4556CertificateValid
    leaf4556InnerLogValid leaf4556CoversExact leaf4556LowerChecked

private noncomputable def leaf4557Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (77/256), chiHi := (39/128) }

private noncomputable def leaf4557Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871291/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357501952) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1096939771/1073741824) }, upper := { exponent := 1, mantissa := (529/512) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi286LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68716224511/68715003904) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf4557InnerLog : WideLogData :=
  innerPair604Data

set_option maxRecDepth 1000000 in
private theorem leaf4557LocalValidity :
    LeafFacts leaf4557Box leaf4557Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4557Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357501952) }) = true
      norm_num [leaf4557Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4557CertificateValid :
    WideCertificateValid leaf4557Box leaf4557Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi286ValidityFacts
    leaf4557LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4557CoverageChecked :
    coverageCheck (innerAD leaf4557Box) leaf4557InnerLog = true := by
  rfl'

private theorem leaf4557InnerLogValid :
    leaf4557InnerLog.Valid 8 (innerAD leaf4557Box) :=
  wideLogDataValid_of_cachedCheck endpoint325PositiveFacts
    endpoint326PositiveFacts.valid leaf4557CoverageChecked

private noncomputable def leaf4557InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629379/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4557InputLogOnePlusV_eq :
    leaf4557InputLogOnePlusV = outerEnclosure 24
      (leaf4557Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4557RoundedFacts : LeafRoundedFacts 8
    leaf4557Certificate.logOnePlusV leaf4557InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4557InputLogOnePlusV_eq }

private noncomputable def leaf4557Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi286InputQChi innerPair604Input
    leaf4557InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4557LowerChecked :
    lowerCheck 24 leaf4557Box leaf4557Inputs = true := by
  rfl'

private theorem leaf4557CoversExact : CoversExact 8
    leaf4557Box leaf4557Certificate leaf4557InnerLog leaf4557Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi286RoundedFacts
    innerPair604RoundedFacts leaf4557RoundedFacts (by rfl)

private theorem leaf4557FlatSound : Sound leaf4557Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4557CertificateValid
    leaf4557InnerLogValid leaf4557CoversExact leaf4557LowerChecked

private noncomputable def leaf4558Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (39/128), chiHi := (79/256) }

private noncomputable def leaf4558Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871291/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357493504) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1099102327/1073741824) }, upper := { exponent := 1, mantissa := (16961/16384) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi287LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716216063/68714987008) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf4558InnerLog : WideLogData :=
  innerPair327Data

set_option maxRecDepth 1000000 in
private theorem leaf4558LocalValidity :
    LeafFacts leaf4558Box leaf4558Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4558Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357493504) }) = true
      norm_num [leaf4558Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4558CertificateValid :
    WideCertificateValid leaf4558Box leaf4558Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi287ValidityFacts
    leaf4558LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4558CoverageChecked :
    coverageCheck (innerAD leaf4558Box) leaf4558InnerLog = true := by
  rfl'

private theorem leaf4558InnerLogValid :
    leaf4558InnerLog.Valid 8 (innerAD leaf4558Box) :=
  wideLogDataValid_of_cachedCheck endpoint87PositiveFacts
    endpoint86PositiveFacts.valid leaf4558CoverageChecked

private noncomputable def leaf4558InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629381/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4558InputLogOnePlusV_eq :
    leaf4558InputLogOnePlusV = outerEnclosure 24
      (leaf4558Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4558RoundedFacts : LeafRoundedFacts 8
    leaf4558Certificate.logOnePlusV leaf4558InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4558InputLogOnePlusV_eq }

private noncomputable def leaf4558Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi287InputQChi innerPair327Input
    leaf4558InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4558LowerChecked :
    lowerCheck 24 leaf4558Box leaf4558Inputs = true := by
  rfl'

private theorem leaf4558CoversExact : CoversExact 8
    leaf4558Box leaf4558Certificate leaf4558InnerLog leaf4558Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi287RoundedFacts
    innerPair327RoundedFacts leaf4558RoundedFacts (by rfl)

private theorem leaf4558FlatSound : Sound leaf4558Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4558CertificateValid
    leaf4558InnerLogValid leaf4558CoversExact leaf4558LowerChecked

private noncomputable def leaf4559Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (79/256), chiHi := (5/16) }

private noncomputable def leaf4559Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871293/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357465088) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1106310845/1073741824) }, upper := { exponent := 1, mantissa := (1067/1024) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi288LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716187647/68714930176) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf4559InnerLog : WideLogData :=
  innerPair329Data

set_option maxRecDepth 1000000 in
private theorem leaf4559LocalValidity :
    LeafFacts leaf4559Box leaf4559Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4559Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357465088) }) = true
      norm_num [leaf4559Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4559CertificateValid :
    WideCertificateValid leaf4559Box leaf4559Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi288ValidityFacts
    leaf4559LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4559CoverageChecked :
    coverageCheck (innerAD leaf4559Box) leaf4559InnerLog = true := by
  rfl'

private theorem leaf4559InnerLogValid :
    leaf4559InnerLog.Valid 8 (innerAD leaf4559Box) :=
  wideLogDataValid_of_cachedCheck endpoint87PositiveFacts
    endpoint284PositiveFacts.valid leaf4559CoverageChecked

private noncomputable def leaf4559InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907347/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4559InputLogOnePlusV_eq :
    leaf4559InputLogOnePlusV = outerEnclosure 24
      (leaf4559Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4559RoundedFacts : LeafRoundedFacts 8
    leaf4559Certificate.logOnePlusV leaf4559InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4559InputLogOnePlusV_eq }

private noncomputable def leaf4559Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi288InputQChi innerPair329Input
    leaf4559InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4559LowerChecked :
    lowerCheck 24 leaf4559Box leaf4559Inputs = true := by
  rfl'

private theorem leaf4559CoversExact : CoversExact 8
    leaf4559Box leaf4559Certificate leaf4559InnerLog leaf4559Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi288RoundedFacts
    innerPair329RoundedFacts leaf4559RoundedFacts (by rfl)

private theorem leaf4559FlatSound : Sound leaf4559Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4559CertificateValid
    leaf4559InnerLogValid leaf4559CoversExact leaf4559LowerChecked

private noncomputable def leaf4560Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (39/128), chiHi := (79/256) }

private noncomputable def leaf4560Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871293/536870912) }, vSqrt := { lower := (8191/8192), upper := (2021101327/2021027840) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1104213821/1073741824) }, upper := { exponent := 1, mantissa := (1065/1024) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi287LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (4042129167/4042055680) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf4560InnerLog : WideLogData :=
  innerPair316Data

set_option maxRecDepth 1000000 in
private theorem leaf4560LocalValidity :
    LeafFacts leaf4560Box leaf4560Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4560Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (2021101327/2021027840) }) = true
      norm_num [leaf4560Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4560CertificateValid :
    WideCertificateValid leaf4560Box leaf4560Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi287ValidityFacts
    leaf4560LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4560CoverageChecked :
    coverageCheck (innerAD leaf4560Box) leaf4560InnerLog = true := by
  rfl'

private theorem leaf4560InnerLogValid :
    leaf4560InnerLog.Valid 8 (innerAD leaf4560Box) :=
  wideLogDataValid_of_cachedCheck endpoint84PositiveFacts
    endpoint327PositiveFacts.valid leaf4560CoverageChecked

private noncomputable def leaf4560InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814693/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4560InputLogOnePlusV_eq :
    leaf4560InputLogOnePlusV = outerEnclosure 24
      (leaf4560Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4560RoundedFacts : LeafRoundedFacts 8
    leaf4560Certificate.logOnePlusV leaf4560InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4560InputLogOnePlusV_eq }

private noncomputable def leaf4560Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi287InputQChi innerPair316Input
    leaf4560InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4560LowerChecked :
    lowerCheck 24 leaf4560Box leaf4560Inputs = true := by
  rfl'

private theorem leaf4560CoversExact : CoversExact 8
    leaf4560Box leaf4560Certificate leaf4560InnerLog leaf4560Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi287RoundedFacts
    innerPair316RoundedFacts leaf4560RoundedFacts (by rfl)

private theorem leaf4560FlatSound : Sound leaf4560Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4560CertificateValid
    leaf4560InnerLogValid leaf4560CoversExact leaf4560LowerChecked

private noncomputable def leaf4561Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (79/256), chiHi := (5/16) }

private noncomputable def leaf4561Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871295/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357444608) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1111487871/1073741824) }, upper := { exponent := 1, mantissa := (67/64) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi288LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68716167167/68714889216) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf4561InnerLog : WideLogData :=
  innerPair248Data

set_option maxRecDepth 1000000 in
private theorem leaf4561LocalValidity :
    LeafFacts leaf4561Box leaf4561Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4561Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357444608) }) = true
      norm_num [leaf4561Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4561CertificateValid :
    WideCertificateValid leaf4561Box leaf4561Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi288ValidityFacts
    leaf4561LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4561CoverageChecked :
    coverageCheck (innerAD leaf4561Box) leaf4561InnerLog = true := by
  rfl'

private theorem leaf4561InnerLogValid :
    leaf4561InnerLog.Valid 8 (innerAD leaf4561Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint284PositiveFacts.valid leaf4561CoverageChecked

private noncomputable def leaf4561InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629393/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4561InputLogOnePlusV_eq :
    leaf4561InputLogOnePlusV = outerEnclosure 24
      (leaf4561Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4561RoundedFacts : LeafRoundedFacts 8
    leaf4561Certificate.logOnePlusV leaf4561InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4561InputLogOnePlusV_eq }

private noncomputable def leaf4561Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi288InputQChi innerPair248Input
    leaf4561InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4561LowerChecked :
    lowerCheck 24 leaf4561Box leaf4561Inputs = true := by
  rfl'

private theorem leaf4561CoversExact : CoversExact 8
    leaf4561Box leaf4561Certificate leaf4561InnerLog leaf4561Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi288RoundedFacts
    innerPair248RoundedFacts leaf4561RoundedFacts (by rfl)

private theorem leaf4561FlatSound : Sound leaf4561Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4561CertificateValid
    leaf4561InnerLogValid leaf4561CoversExact leaf4561LowerChecked

private noncomputable def component93Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (9/32), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component93Node0_sound : Sound component93Node0Box :=
  sound_of_literal_split component93Node0Box leaf4529Box leaf4530Box
    .chi (73/256) (by rfl) (by rfl)
    leaf4529FlatSound leaf4530FlatSound

private noncomputable def component93Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (9/32), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component93Node1_sound : Sound component93Node1Box :=
  sound_of_literal_split component93Node1Box leaf4531Box leaf4532Box
    .chi (73/256) (by rfl) (by rfl)
    leaf4531FlatSound leaf4532FlatSound

private noncomputable def component93Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (9/32), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component93Node2_sound : Sound component93Node2Box :=
  sound_of_literal_split component93Node2Box component93Node0Box component93Node1Box
    .k (109/32) (by rfl) (by rfl)
    component93Node0_sound component93Node1_sound

private noncomputable def component93Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (37/128), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component93Node3_sound : Sound component93Node3Box :=
  sound_of_literal_split component93Node3Box leaf4533Box leaf4534Box
    .chi (75/256) (by rfl) (by rfl)
    leaf4533FlatSound leaf4534FlatSound

private noncomputable def component93Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (37/128), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component93Node4_sound : Sound component93Node4Box :=
  sound_of_literal_split component93Node4Box leaf4535Box leaf4536Box
    .chi (75/256) (by rfl) (by rfl)
    leaf4535FlatSound leaf4536FlatSound

private noncomputable def component93Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (37/128), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component93Node5_sound : Sound component93Node5Box :=
  sound_of_literal_split component93Node5Box component93Node3Box component93Node4Box
    .k (109/32) (by rfl) (by rfl)
    component93Node3_sound component93Node4_sound

private noncomputable def component93Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (9/32), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component93Node6_sound : Sound component93Node6Box :=
  sound_of_literal_split component93Node6Box component93Node2Box component93Node5Box
    .chi (37/128) (by rfl) (by rfl)
    component93Node2_sound component93Node5_sound

private noncomputable def component93Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (9/32), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component93Node7_sound : Sound component93Node7Box :=
  sound_of_literal_split component93Node7Box leaf4537Box leaf4538Box
    .chi (73/256) (by rfl) (by rfl)
    leaf4537FlatSound leaf4538FlatSound

private noncomputable def component93Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (9/32), chiHi := (73/256) }

set_option maxRecDepth 1000000 in
private theorem component93Node8_sound : Sound component93Node8Box :=
  sound_of_literal_split component93Node8Box leaf4539Box leaf4540Box
    .k (223/64) (by rfl) (by rfl)
    leaf4539FlatSound leaf4540FlatSound

private noncomputable def component93Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (9/32), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component93Node9_sound : Sound component93Node9Box :=
  sound_of_literal_split component93Node9Box component93Node8Box leaf4541Box
    .chi (73/256) (by rfl) (by rfl)
    component93Node8_sound leaf4541FlatSound

private noncomputable def component93Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (9/32), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component93Node10_sound : Sound component93Node10Box :=
  sound_of_literal_split component93Node10Box component93Node7Box component93Node9Box
    .k (111/32) (by rfl) (by rfl)
    component93Node7_sound component93Node9_sound

private noncomputable def component93Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (37/128), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component93Node11_sound : Sound component93Node11Box :=
  sound_of_literal_split component93Node11Box leaf4542Box leaf4543Box
    .chi (75/256) (by rfl) (by rfl)
    leaf4542FlatSound leaf4543FlatSound

private noncomputable def component93Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (37/128), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component93Node12_sound : Sound component93Node12Box :=
  sound_of_literal_split component93Node12Box leaf4544Box leaf4545Box
    .chi (75/256) (by rfl) (by rfl)
    leaf4544FlatSound leaf4545FlatSound

private noncomputable def component93Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (37/128), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component93Node13_sound : Sound component93Node13Box :=
  sound_of_literal_split component93Node13Box component93Node11Box component93Node12Box
    .k (111/32) (by rfl) (by rfl)
    component93Node11_sound component93Node12_sound

private noncomputable def component93Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (9/32), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component93Node14_sound : Sound component93Node14Box :=
  sound_of_literal_split component93Node14Box component93Node10Box component93Node13Box
    .chi (37/128) (by rfl) (by rfl)
    component93Node10_sound component93Node13_sound

private noncomputable def component93Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (9/32), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component93Node15_sound : Sound component93Node15Box :=
  sound_of_literal_split component93Node15Box component93Node6Box component93Node14Box
    .k (55/16) (by rfl) (by rfl)
    component93Node6_sound component93Node14_sound

private noncomputable def component93Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (19/64), chiHi := (39/128) }

set_option maxRecDepth 1000000 in
private theorem component93Node16_sound : Sound component93Node16Box :=
  sound_of_literal_split component93Node16Box leaf4546Box leaf4547Box
    .chi (77/256) (by rfl) (by rfl)
    leaf4546FlatSound leaf4547FlatSound

private noncomputable def component93Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (19/64), chiHi := (39/128) }

set_option maxRecDepth 1000000 in
private theorem component93Node17_sound : Sound component93Node17Box :=
  sound_of_literal_split component93Node17Box leaf4548Box leaf4549Box
    .chi (77/256) (by rfl) (by rfl)
    leaf4548FlatSound leaf4549FlatSound

private noncomputable def component93Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (19/64), chiHi := (39/128) }

set_option maxRecDepth 1000000 in
private theorem component93Node18_sound : Sound component93Node18Box :=
  sound_of_literal_split component93Node18Box component93Node16Box component93Node17Box
    .k (109/32) (by rfl) (by rfl)
    component93Node16_sound component93Node17_sound

private noncomputable def component93Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (39/128), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component93Node19_sound : Sound component93Node19Box :=
  sound_of_literal_split component93Node19Box leaf4550Box leaf4551Box
    .chi (79/256) (by rfl) (by rfl)
    leaf4550FlatSound leaf4551FlatSound

private noncomputable def component93Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (39/128), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component93Node20_sound : Sound component93Node20Box :=
  sound_of_literal_split component93Node20Box leaf4552Box leaf4553Box
    .chi (79/256) (by rfl) (by rfl)
    leaf4552FlatSound leaf4553FlatSound

private noncomputable def component93Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (39/128), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component93Node21_sound : Sound component93Node21Box :=
  sound_of_literal_split component93Node21Box component93Node19Box component93Node20Box
    .k (109/32) (by rfl) (by rfl)
    component93Node19_sound component93Node20_sound

private noncomputable def component93Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (19/64), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component93Node22_sound : Sound component93Node22Box :=
  sound_of_literal_split component93Node22Box component93Node18Box component93Node21Box
    .chi (39/128) (by rfl) (by rfl)
    component93Node18_sound component93Node21_sound

private noncomputable def component93Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (19/64), chiHi := (39/128) }

set_option maxRecDepth 1000000 in
private theorem component93Node23_sound : Sound component93Node23Box :=
  sound_of_literal_split component93Node23Box leaf4554Box leaf4555Box
    .chi (77/256) (by rfl) (by rfl)
    leaf4554FlatSound leaf4555FlatSound

private noncomputable def component93Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (19/64), chiHi := (39/128) }

set_option maxRecDepth 1000000 in
private theorem component93Node24_sound : Sound component93Node24Box :=
  sound_of_literal_split component93Node24Box leaf4556Box leaf4557Box
    .chi (77/256) (by rfl) (by rfl)
    leaf4556FlatSound leaf4557FlatSound

private noncomputable def component93Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (19/64), chiHi := (39/128) }

set_option maxRecDepth 1000000 in
private theorem component93Node25_sound : Sound component93Node25Box :=
  sound_of_literal_split component93Node25Box component93Node23Box component93Node24Box
    .k (111/32) (by rfl) (by rfl)
    component93Node23_sound component93Node24_sound

private noncomputable def component93Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (39/128), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component93Node26_sound : Sound component93Node26Box :=
  sound_of_literal_split component93Node26Box leaf4558Box leaf4559Box
    .chi (79/256) (by rfl) (by rfl)
    leaf4558FlatSound leaf4559FlatSound

private noncomputable def component93Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (39/128), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component93Node27_sound : Sound component93Node27Box :=
  sound_of_literal_split component93Node27Box leaf4560Box leaf4561Box
    .chi (79/256) (by rfl) (by rfl)
    leaf4560FlatSound leaf4561FlatSound

private noncomputable def component93Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (39/128), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component93Node28_sound : Sound component93Node28Box :=
  sound_of_literal_split component93Node28Box component93Node26Box component93Node27Box
    .k (111/32) (by rfl) (by rfl)
    component93Node26_sound component93Node27_sound

private noncomputable def component93Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (19/64), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component93Node29_sound : Sound component93Node29Box :=
  sound_of_literal_split component93Node29Box component93Node25Box component93Node28Box
    .chi (39/128) (by rfl) (by rfl)
    component93Node25_sound component93Node28_sound

private noncomputable def component93Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (19/64), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component93Node30_sound : Sound component93Node30Box :=
  sound_of_literal_split component93Node30Box component93Node22Box component93Node29Box
    .k (55/16) (by rfl) (by rfl)
    component93Node22_sound component93Node29_sound

noncomputable def component93Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (9/32), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
theorem component93_sound : Sound component93Box :=
  sound_of_literal_split component93Box component93Node15Box component93Node30Box
    .chi (19/64) (by rfl) (by rfl)
    component93Node15_sound component93Node30_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
