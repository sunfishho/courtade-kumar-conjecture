import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch6
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

private noncomputable def leaf2981Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (249/64), chiLo := (11/64), chiHi := (45/256) }

private noncomputable def leaf2981Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742411/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433216512) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1788793655/1073741824) }, upper := { exponent := 0, mantissa := (27589/16384) } }, logOuter := sk233LogOuterCertificate, logK := sk233LogKCertificate, logChi := chi133LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870138367/274866433024) } }, logDArg := sk233LogDArgCertificate }

private noncomputable def leaf2981InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2981LocalValidity :
    LeafFacts leaf2981Box leaf2981Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2981Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433216512) }) = true
      norm_num [leaf2981Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2981CertificateValid :
    WideCertificateValid leaf2981Box leaf2981Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk233ValidityFacts chi133ValidityFacts
    leaf2981LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2981CoverageChecked :
    coverageCheck (innerAD leaf2981Box) leaf2981InnerLog = true := by
  rfl'

private theorem leaf2981InnerLogValid :
    leaf2981InnerLog.Valid 8 (innerAD leaf2981Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2981CoverageChecked

private noncomputable def leaf2981InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629307/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2981InputLogOnePlusV_eq :
    leaf2981InputLogOnePlusV = outerEnclosure 24
      (leaf2981Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2981RoundedFacts : LeafRoundedFacts 8
    leaf2981Certificate.logOnePlusV leaf2981InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2981InputLogOnePlusV_eq }

private noncomputable def leaf2981Inputs : Inputs :=
  inputsOfCaches globalInput sk233RoundedInputs
    chi133InputQChi innerPair56Input
    leaf2981InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2981LowerChecked :
    lowerCheck 24 leaf2981Box leaf2981Inputs = true := by
  rfl'

private theorem leaf2981CoversExact : CoversExact 8
    leaf2981Box leaf2981Certificate leaf2981InnerLog leaf2981Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk233RoundedFacts chi133RoundedFacts
    innerPair56RoundedFacts leaf2981RoundedFacts (by rfl)

private theorem leaf2981FlatSound : Sound leaf2981Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2981CertificateValid
    leaf2981InnerLogValid leaf2981CoversExact leaf2981LowerChecked

private noncomputable def leaf2982Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (249/64), kHi := (125/32), chiLo := (11/64), chiHi := (45/256) }

private noncomputable def leaf2982Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742413/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433193472) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1791677061/1073741824) }, upper := { exponent := 0, mantissa := (13817/8192) } }, logOuter := sk234LogOuterCertificate, logK := sk234LogKCertificate, logChi := chi133LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870115327/274866386944) } }, logDArg := sk234LogDArgCertificate }

private noncomputable def leaf2982InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2982LocalValidity :
    LeafFacts leaf2982Box leaf2982Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2982Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433193472) }) = true
      norm_num [leaf2982Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2982CertificateValid :
    WideCertificateValid leaf2982Box leaf2982Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk234ValidityFacts chi133ValidityFacts
    leaf2982LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2982CoverageChecked :
    coverageCheck (innerAD leaf2982Box) leaf2982InnerLog = true := by
  rfl'

private theorem leaf2982InnerLogValid :
    leaf2982InnerLog.Valid 8 (innerAD leaf2982Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2982CoverageChecked

private noncomputable def leaf2982InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907327/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2982InputLogOnePlusV_eq :
    leaf2982InputLogOnePlusV = outerEnclosure 24
      (leaf2982Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2982RoundedFacts : LeafRoundedFacts 8
    leaf2982Certificate.logOnePlusV leaf2982InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2982InputLogOnePlusV_eq }

private noncomputable def leaf2982Inputs : Inputs :=
  inputsOfCaches globalInput sk234RoundedInputs
    chi133InputQChi innerPair56Input
    leaf2982InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2982LowerChecked :
    lowerCheck 24 leaf2982Box leaf2982Inputs = true := by
  rfl'

private theorem leaf2982CoversExact : CoversExact 8
    leaf2982Box leaf2982Certificate leaf2982InnerLog leaf2982Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk234RoundedFacts chi133RoundedFacts
    innerPair56RoundedFacts leaf2982RoundedFacts (by rfl)

private theorem leaf2982FlatSound : Sound leaf2982Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2982CertificateValid
    leaf2982InnerLogValid leaf2982CoversExact leaf2982LowerChecked

private noncomputable def leaf2983Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (249/64), chiLo := (45/256), chiHi := (23/128) }

private noncomputable def leaf2983Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742413/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433089024) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1805045589/1073741824) }, upper := { exponent := 0, mantissa := (13919/8192) } }, logOuter := sk233LogOuterCertificate, logK := sk233LogKCertificate, logChi := chi134LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870010879/274866178048) } }, logDArg := sk233LogDArgCertificate }

private noncomputable def leaf2983InnerLog : WideLogData :=
  innerPair420Data

set_option maxRecDepth 1000000 in
private theorem leaf2983LocalValidity :
    LeafFacts leaf2983Box leaf2983Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2983Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433089024) }) = true
      norm_num [leaf2983Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2983CertificateValid :
    WideCertificateValid leaf2983Box leaf2983Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk233ValidityFacts chi134ValidityFacts
    leaf2983LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2983CoverageChecked :
    coverageCheck (innerAD leaf2983Box) leaf2983InnerLog = true := by
  rfl'

private theorem leaf2983InnerLogValid :
    leaf2983InnerLog.Valid 8 (innerAD leaf2983Box) :=
  wideLogDataValid_of_cachedCheck endpoint133PositiveFacts
    endpoint20PositiveFacts.valid leaf2983CoverageChecked

private noncomputable def leaf2983InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629315/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2983InputLogOnePlusV_eq :
    leaf2983InputLogOnePlusV = outerEnclosure 24
      (leaf2983Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2983RoundedFacts : LeafRoundedFacts 8
    leaf2983Certificate.logOnePlusV leaf2983InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2983InputLogOnePlusV_eq }

private noncomputable def leaf2983Inputs : Inputs :=
  inputsOfCaches globalInput sk233RoundedInputs
    chi134InputQChi innerPair420Input
    leaf2983InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2983LowerChecked :
    lowerCheck 24 leaf2983Box leaf2983Inputs = true := by
  rfl'

private theorem leaf2983CoversExact : CoversExact 8
    leaf2983Box leaf2983Certificate leaf2983InnerLog leaf2983Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk233RoundedFacts chi134RoundedFacts
    innerPair420RoundedFacts leaf2983RoundedFacts (by rfl)

private theorem leaf2983FlatSound : Sound leaf2983Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2983CertificateValid
    leaf2983InnerLogValid leaf2983CoversExact leaf2983LowerChecked

private noncomputable def leaf2984Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (249/64), kHi := (125/32), chiLo := (45/256), chiHi := (23/128) }

private noncomputable def leaf2984Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742415/1073741824) }, vSqrt := { lower := (8191/8192), upper := (5090256365/5090113536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1807994527/1073741824) }, upper := { exponent := 0, mantissa := (6971/4096) } }, logOuter := sk234LogOuterCertificate, logK := sk234LogKCertificate, logChi := chi134LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (10180369901/10180227072) } }, logDArg := sk234LogDArgCertificate }

private noncomputable def leaf2984InnerLog : WideLogData :=
  innerPair420Data

set_option maxRecDepth 1000000 in
private theorem leaf2984LocalValidity :
    LeafFacts leaf2984Box leaf2984Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2984Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5090256365/5090113536) }) = true
      norm_num [leaf2984Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2984CertificateValid :
    WideCertificateValid leaf2984Box leaf2984Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk234ValidityFacts chi134ValidityFacts
    leaf2984LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2984CoverageChecked :
    coverageCheck (innerAD leaf2984Box) leaf2984InnerLog = true := by
  rfl'

private theorem leaf2984InnerLogValid :
    leaf2984InnerLog.Valid 8 (innerAD leaf2984Box) :=
  wideLogDataValid_of_cachedCheck endpoint133PositiveFacts
    endpoint20PositiveFacts.valid leaf2984CoverageChecked

private noncomputable def leaf2984InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907329/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2984InputLogOnePlusV_eq :
    leaf2984InputLogOnePlusV = outerEnclosure 24
      (leaf2984Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2984RoundedFacts : LeafRoundedFacts 8
    leaf2984Certificate.logOnePlusV leaf2984InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2984InputLogOnePlusV_eq }

private noncomputable def leaf2984Inputs : Inputs :=
  inputsOfCaches globalInput sk234RoundedInputs
    chi134InputQChi innerPair420Input
    leaf2984InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2984LowerChecked :
    lowerCheck 24 leaf2984Box leaf2984Inputs = true := by
  rfl'

private theorem leaf2984CoversExact : CoversExact 8
    leaf2984Box leaf2984Certificate leaf2984InnerLog leaf2984Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk234RoundedFacts chi134RoundedFacts
    innerPair420RoundedFacts leaf2984RoundedFacts (by rfl)

private theorem leaf2984FlatSound : Sound leaf2984Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2984CertificateValid
    leaf2984InnerLogValid leaf2984CoversExact leaf2984LowerChecked

private noncomputable def leaf2985Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (251/64), chiLo := (11/64), chiHi := (45/256) }

private noncomputable def leaf2985Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742415/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433170432) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1794560467/1073741824) }, upper := { exponent := 0, mantissa := (27679/16384) } }, logOuter := sk235LogOuterCertificate, logK := sk235LogKCertificate, logChi := chi133LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870092287/274866340864) } }, logDArg := sk235LogDArgCertificate }

private noncomputable def leaf2985InnerLog : WideLogData :=
  innerPair476Data

set_option maxRecDepth 1000000 in
private theorem leaf2985LocalValidity :
    LeafFacts leaf2985Box leaf2985Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2985Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433170432) }) = true
      norm_num [leaf2985Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2985CertificateValid :
    WideCertificateValid leaf2985Box leaf2985Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk235ValidityFacts chi133ValidityFacts
    leaf2985LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2985CoverageChecked :
    coverageCheck (innerAD leaf2985Box) leaf2985InnerLog = true := by
  rfl'

private theorem leaf2985InnerLogValid :
    leaf2985InnerLog.Valid 8 (innerAD leaf2985Box) :=
  wideLogDataValid_of_cachedCheck endpoint200PositiveFacts
    endpoint205PositiveFacts.valid leaf2985CoverageChecked

private noncomputable def leaf2985InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814655/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2985InputLogOnePlusV_eq :
    leaf2985InputLogOnePlusV = outerEnclosure 24
      (leaf2985Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2985RoundedFacts : LeafRoundedFacts 8
    leaf2985Certificate.logOnePlusV leaf2985InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2985InputLogOnePlusV_eq }

private noncomputable def leaf2985Inputs : Inputs :=
  inputsOfCaches globalInput sk235RoundedInputs
    chi133InputQChi innerPair476Input
    leaf2985InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2985LowerChecked :
    lowerCheck 24 leaf2985Box leaf2985Inputs = true := by
  rfl'

private theorem leaf2985CoversExact : CoversExact 8
    leaf2985Box leaf2985Certificate leaf2985InnerLog leaf2985Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk235RoundedFacts chi133RoundedFacts
    innerPair476RoundedFacts leaf2985RoundedFacts (by rfl)

private theorem leaf2985FlatSound : Sound leaf2985Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2985CertificateValid
    leaf2985InnerLogValid leaf2985CoversExact leaf2985LowerChecked

private noncomputable def leaf2986Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (63/16), chiLo := (11/64), chiHi := (45/256) }

private noncomputable def leaf2986Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742417/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433147392) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1797443873/1073741824) }, upper := { exponent := 0, mantissa := (6931/4096) } }, logOuter := sk236LogOuterCertificate, logK := sk236LogKCertificate, logChi := chi133LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870069247/274866294784) } }, logDArg := sk236LogDArgCertificate }

private noncomputable def leaf2986InnerLog : WideLogData :=
  innerPair423Data

set_option maxRecDepth 1000000 in
private theorem leaf2986LocalValidity :
    LeafFacts leaf2986Box leaf2986Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2986Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433147392) }) = true
      norm_num [leaf2986Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2986CertificateValid :
    WideCertificateValid leaf2986Box leaf2986Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk236ValidityFacts chi133ValidityFacts
    leaf2986LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2986CoverageChecked :
    coverageCheck (innerAD leaf2986Box) leaf2986InnerLog = true := by
  rfl'

private theorem leaf2986InnerLogValid :
    leaf2986InnerLog.Valid 8 (innerAD leaf2986Box) :=
  wideLogDataValid_of_cachedCheck endpoint133PositiveFacts
    endpoint137PositiveFacts.valid leaf2986CoverageChecked

private noncomputable def leaf2986InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629311/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2986InputLogOnePlusV_eq :
    leaf2986InputLogOnePlusV = outerEnclosure 24
      (leaf2986Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2986RoundedFacts : LeafRoundedFacts 8
    leaf2986Certificate.logOnePlusV leaf2986InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2986InputLogOnePlusV_eq }

private noncomputable def leaf2986Inputs : Inputs :=
  inputsOfCaches globalInput sk236RoundedInputs
    chi133InputQChi innerPair423Input
    leaf2986InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2986LowerChecked :
    lowerCheck 24 leaf2986Box leaf2986Inputs = true := by
  rfl'

private theorem leaf2986CoversExact : CoversExact 8
    leaf2986Box leaf2986Certificate leaf2986InnerLog leaf2986Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk236RoundedFacts chi133RoundedFacts
    innerPair423RoundedFacts leaf2986RoundedFacts (by rfl)

private theorem leaf2986FlatSound : Sound leaf2986Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2986CertificateValid
    leaf2986InnerLogValid leaf2986CoversExact leaf2986LowerChecked

private noncomputable def leaf2987Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (251/64), chiLo := (45/256), chiHi := (23/128) }

private noncomputable def leaf2987Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742417/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486608384) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1810943465/1073741824) }, upper := { exponent := 0, mantissa := (13965/8192) } }, logOuter := sk235LogOuterCertificate, logK := sk235LogKCertificate, logChi := chi134LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973992755/54973216768) } }, logDArg := sk235LogDArgCertificate }

private noncomputable def leaf2987InnerLog : WideLogData :=
  innerPair196Data

set_option maxRecDepth 1000000 in
private theorem leaf2987LocalValidity :
    LeafFacts leaf2987Box leaf2987Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2987Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486608384) }) = true
      norm_num [leaf2987Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2987CertificateValid :
    WideCertificateValid leaf2987Box leaf2987Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk235ValidityFacts chi134ValidityFacts
    leaf2987LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2987CoverageChecked :
    coverageCheck (innerAD leaf2987Box) leaf2987InnerLog = true := by
  rfl'

private theorem leaf2987InnerLogValid :
    leaf2987InnerLog.Valid 8 (innerAD leaf2987Box) :=
  wideLogDataValid_of_cachedCheck endpoint58PositiveFacts
    endpoint136PositiveFacts.valid leaf2987CoverageChecked

private noncomputable def leaf2987InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814659/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2987InputLogOnePlusV_eq :
    leaf2987InputLogOnePlusV = outerEnclosure 24
      (leaf2987Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2987RoundedFacts : LeafRoundedFacts 8
    leaf2987Certificate.logOnePlusV leaf2987InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2987InputLogOnePlusV_eq }

private noncomputable def leaf2987Inputs : Inputs :=
  inputsOfCaches globalInput sk235RoundedInputs
    chi134InputQChi innerPair196Input
    leaf2987InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2987LowerChecked :
    lowerCheck 24 leaf2987Box leaf2987Inputs = true := by
  rfl'

private theorem leaf2987CoversExact : CoversExact 8
    leaf2987Box leaf2987Certificate leaf2987InnerLog leaf2987Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk235RoundedFacts chi134RoundedFacts
    innerPair196RoundedFacts leaf2987RoundedFacts (by rfl)

private theorem leaf2987FlatSound : Sound leaf2987Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2987CertificateValid
    leaf2987InnerLogValid leaf2987CoversExact leaf2987LowerChecked

private noncomputable def leaf2988Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (63/16), chiLo := (45/256), chiHi := (23/128) }

private noncomputable def leaf2988Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742419/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433018368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1813892403/1073741824) }, upper := { exponent := 0, mantissa := (3497/2048) } }, logOuter := sk236LogOuterCertificate, logK := sk236LogKCertificate, logChi := chi134LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869940223/274866036736) } }, logDArg := sk236LogDArgCertificate }

private noncomputable def leaf2988InnerLog : WideLogData :=
  innerPair479Data

set_option maxRecDepth 1000000 in
private theorem leaf2988LocalValidity :
    LeafFacts leaf2988Box leaf2988Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2988Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433018368) }) = true
      norm_num [leaf2988Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2988CertificateValid :
    WideCertificateValid leaf2988Box leaf2988Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk236ValidityFacts chi134ValidityFacts
    leaf2988LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2988CoverageChecked :
    coverageCheck (innerAD leaf2988Box) leaf2988InnerLog = true := by
  rfl'

private theorem leaf2988InnerLogValid :
    leaf2988InnerLog.Valid 8 (innerAD leaf2988Box) :=
  wideLogDataValid_of_cachedCheck endpoint206PositiveFacts
    endpoint207PositiveFacts.valid leaf2988CoverageChecked

private noncomputable def leaf2988InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629319/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2988InputLogOnePlusV_eq :
    leaf2988InputLogOnePlusV = outerEnclosure 24
      (leaf2988Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2988RoundedFacts : LeafRoundedFacts 8
    leaf2988Certificate.logOnePlusV leaf2988InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2988InputLogOnePlusV_eq }

private noncomputable def leaf2988Inputs : Inputs :=
  inputsOfCaches globalInput sk236RoundedInputs
    chi134InputQChi innerPair479Input
    leaf2988InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2988LowerChecked :
    lowerCheck 24 leaf2988Box leaf2988Inputs = true := by
  rfl'

private theorem leaf2988CoversExact : CoversExact 8
    leaf2988Box leaf2988Certificate leaf2988InnerLog leaf2988Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk236RoundedFacts chi134RoundedFacts
    innerPair479RoundedFacts leaf2988RoundedFacts (by rfl)

private theorem leaf2988FlatSound : Sound leaf2988Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2988CertificateValid
    leaf2988InnerLogValid leaf2988CoversExact leaf2988LowerChecked

private noncomputable def leaf2989Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (249/64), chiLo := (23/128), chiHi := (47/256) }

private noncomputable def leaf2989Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742415/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432961536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1821297523/1073741824) }, upper := { exponent := 0, mantissa := (28087/16384) } }, logOuter := sk233LogOuterCertificate, logK := sk233LogKCertificate, logChi := chi135LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869883391/274865923072) } }, logDArg := sk233LogDArgCertificate }

private noncomputable def leaf2989InnerLog : WideLogData :=
  innerPair68Data

set_option maxRecDepth 1000000 in
private theorem leaf2989LocalValidity :
    LeafFacts leaf2989Box leaf2989Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2989Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432961536) }) = true
      norm_num [leaf2989Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2989CertificateValid :
    WideCertificateValid leaf2989Box leaf2989Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk233ValidityFacts chi135ValidityFacts
    leaf2989LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2989CoverageChecked :
    coverageCheck (innerAD leaf2989Box) leaf2989InnerLog = true := by
  rfl'

private theorem leaf2989InnerLogValid :
    leaf2989InnerLog.Valid 8 (innerAD leaf2989Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint62PositiveFacts.valid leaf2989CoverageChecked

private noncomputable def leaf2989InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814661/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2989InputLogOnePlusV_eq :
    leaf2989InputLogOnePlusV = outerEnclosure 24
      (leaf2989Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2989RoundedFacts : LeafRoundedFacts 8
    leaf2989Certificate.logOnePlusV leaf2989InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2989InputLogOnePlusV_eq }

private noncomputable def leaf2989Inputs : Inputs :=
  inputsOfCaches globalInput sk233RoundedInputs
    chi135InputQChi innerPair68Input
    leaf2989InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2989LowerChecked :
    lowerCheck 24 leaf2989Box leaf2989Inputs = true := by
  rfl'

private theorem leaf2989CoversExact : CoversExact 8
    leaf2989Box leaf2989Certificate leaf2989InnerLog leaf2989Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk233RoundedFacts chi135RoundedFacts
    innerPair68RoundedFacts leaf2989RoundedFacts (by rfl)

private theorem leaf2989FlatSound : Sound leaf2989Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2989CertificateValid
    leaf2989InnerLogValid leaf2989CoversExact leaf2989LowerChecked

private noncomputable def leaf2990Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (249/64), kHi := (125/32), chiLo := (23/128), chiHi := (47/256) }

private noncomputable def leaf2990Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742417/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432937472) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1824311993/1073741824) }, upper := { exponent := 0, mantissa := (14067/8192) } }, logOuter := sk234LogOuterCertificate, logK := sk234LogKCertificate, logChi := chi135LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869859327/274865874944) } }, logDArg := sk234LogDArgCertificate }

private noncomputable def leaf2990InnerLog : WideLogData :=
  innerPair68Data

set_option maxRecDepth 1000000 in
private theorem leaf2990LocalValidity :
    LeafFacts leaf2990Box leaf2990Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2990Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432937472) }) = true
      norm_num [leaf2990Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2990CertificateValid :
    WideCertificateValid leaf2990Box leaf2990Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk234ValidityFacts chi135ValidityFacts
    leaf2990LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2990CoverageChecked :
    coverageCheck (innerAD leaf2990Box) leaf2990InnerLog = true := by
  rfl'

private theorem leaf2990InnerLogValid :
    leaf2990InnerLog.Valid 8 (innerAD leaf2990Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint62PositiveFacts.valid leaf2990CoverageChecked

private noncomputable def leaf2990InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907331/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2990InputLogOnePlusV_eq :
    leaf2990InputLogOnePlusV = outerEnclosure 24
      (leaf2990Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2990RoundedFacts : LeafRoundedFacts 8
    leaf2990Certificate.logOnePlusV leaf2990InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2990InputLogOnePlusV_eq }

private noncomputable def leaf2990Inputs : Inputs :=
  inputsOfCaches globalInput sk234RoundedInputs
    chi135InputQChi innerPair68Input
    leaf2990InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2990LowerChecked :
    lowerCheck 24 leaf2990Box leaf2990Inputs = true := by
  rfl'

private theorem leaf2990CoversExact : CoversExact 8
    leaf2990Box leaf2990Certificate leaf2990InnerLog leaf2990Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk234RoundedFacts chi135RoundedFacts
    innerPair68RoundedFacts leaf2990RoundedFacts (by rfl)

private theorem leaf2990FlatSound : Sound leaf2990Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2990CertificateValid
    leaf2990InnerLogValid leaf2990CoversExact leaf2990LowerChecked

private noncomputable def leaf2991Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (249/64), chiLo := (47/256), chiHi := (3/16) }

private noncomputable def leaf2991Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742417/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432834048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1837549457/1073741824) }, upper := { exponent := 0, mantissa := (1771/1024) } }, logOuter := sk233LogOuterCertificate, logK := sk233LogKCertificate, logChi := chi136LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869755903/274865668096) } }, logDArg := sk233LogDArgCertificate }

private noncomputable def leaf2991InnerLog : WideLogData :=
  innerPair90Data

set_option maxRecDepth 1000000 in
private theorem leaf2991LocalValidity :
    LeafFacts leaf2991Box leaf2991Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2991Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432834048) }) = true
      norm_num [leaf2991Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2991CertificateValid :
    WideCertificateValid leaf2991Box leaf2991Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk233ValidityFacts chi136ValidityFacts
    leaf2991LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2991CoverageChecked :
    coverageCheck (innerAD leaf2991Box) leaf2991InnerLog = true := by
  rfl'

private theorem leaf2991InnerLogValid :
    leaf2991InnerLog.Valid 8 (innerAD leaf2991Box) :=
  wideLogDataValid_of_cachedCheck endpoint20PositiveFacts
    endpoint139PositiveFacts.valid leaf2991CoverageChecked

private noncomputable def leaf2991InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814665/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2991InputLogOnePlusV_eq :
    leaf2991InputLogOnePlusV = outerEnclosure 24
      (leaf2991Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2991RoundedFacts : LeafRoundedFacts 8
    leaf2991Certificate.logOnePlusV leaf2991InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2991InputLogOnePlusV_eq }

private noncomputable def leaf2991Inputs : Inputs :=
  inputsOfCaches globalInput sk233RoundedInputs
    chi136InputQChi innerPair90Input
    leaf2991InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2991LowerChecked :
    lowerCheck 24 leaf2991Box leaf2991Inputs = true := by
  rfl'

private theorem leaf2991CoversExact : CoversExact 8
    leaf2991Box leaf2991Certificate leaf2991InnerLog leaf2991Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk233RoundedFacts chi136RoundedFacts
    innerPair90RoundedFacts leaf2991RoundedFacts (by rfl)

private theorem leaf2991FlatSound : Sound leaf2991Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2991CertificateValid
    leaf2991InnerLogValid leaf2991CoversExact leaf2991LowerChecked

private noncomputable def leaf2992Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (249/64), kHi := (125/32), chiLo := (47/256), chiHi := (3/16) }

private noncomputable def leaf2992Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742419/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432809472) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1840629459/1073741824) }, upper := { exponent := 0, mantissa := (887/512) } }, logOuter := sk234LogOuterCertificate, logK := sk234LogKCertificate, logChi := chi136LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869731327/274865618944) } }, logDArg := sk234LogDArgCertificate }

private noncomputable def leaf2992InnerLog : WideLogData :=
  innerPair90Data

set_option maxRecDepth 1000000 in
private theorem leaf2992LocalValidity :
    LeafFacts leaf2992Box leaf2992Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2992Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432809472) }) = true
      norm_num [leaf2992Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2992CertificateValid :
    WideCertificateValid leaf2992Box leaf2992Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk234ValidityFacts chi136ValidityFacts
    leaf2992LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2992CoverageChecked :
    coverageCheck (innerAD leaf2992Box) leaf2992InnerLog = true := by
  rfl'

private theorem leaf2992InnerLogValid :
    leaf2992InnerLog.Valid 8 (innerAD leaf2992Box) :=
  wideLogDataValid_of_cachedCheck endpoint20PositiveFacts
    endpoint139PositiveFacts.valid leaf2992CoverageChecked

private noncomputable def leaf2992InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907333/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2992InputLogOnePlusV_eq :
    leaf2992InputLogOnePlusV = outerEnclosure 24
      (leaf2992Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2992RoundedFacts : LeafRoundedFacts 8
    leaf2992Certificate.logOnePlusV leaf2992InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2992InputLogOnePlusV_eq }

private noncomputable def leaf2992Inputs : Inputs :=
  inputsOfCaches globalInput sk234RoundedInputs
    chi136InputQChi innerPair90Input
    leaf2992InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2992LowerChecked :
    lowerCheck 24 leaf2992Box leaf2992Inputs = true := by
  rfl'

private theorem leaf2992CoversExact : CoversExact 8
    leaf2992Box leaf2992Certificate leaf2992InnerLog leaf2992Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk234RoundedFacts chi136RoundedFacts
    innerPair90RoundedFacts leaf2992RoundedFacts (by rfl)

private theorem leaf2992FlatSound : Sound leaf2992Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2992CertificateValid
    leaf2992InnerLogValid leaf2992CoversExact leaf2992LowerChecked

private noncomputable def leaf2993Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (251/64), chiLo := (23/128), chiHi := (47/256) }

private noncomputable def leaf2993Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742419/1073741824) }, vSqrt := { lower := (8191/8192), upper := (299426845/299418112) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1827326463/1073741824) }, upper := { exponent := 0, mantissa := (28181/16384) } }, logOuter := sk235LogOuterCertificate, logK := sk235LogKCertificate, logChi := chi135LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (598844957/598836224) } }, logDArg := sk235LogDArgCertificate }

private noncomputable def leaf2993InnerLog : WideLogData :=
  innerPair218Data

set_option maxRecDepth 1000000 in
private theorem leaf2993LocalValidity :
    LeafFacts leaf2993Box leaf2993Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2993Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (299426845/299418112) }) = true
      norm_num [leaf2993Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2993CertificateValid :
    WideCertificateValid leaf2993Box leaf2993Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk235ValidityFacts chi135ValidityFacts
    leaf2993LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2993CoverageChecked :
    coverageCheck (innerAD leaf2993Box) leaf2993InnerLog = true := by
  rfl'

private theorem leaf2993InnerLogValid :
    leaf2993InnerLog.Valid 8 (innerAD leaf2993Box) :=
  wideLogDataValid_of_cachedCheck endpoint65PositiveFacts
    endpoint179PositiveFacts.valid leaf2993CoverageChecked

private noncomputable def leaf2993InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629325/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2993InputLogOnePlusV_eq :
    leaf2993InputLogOnePlusV = outerEnclosure 24
      (leaf2993Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2993RoundedFacts : LeafRoundedFacts 8
    leaf2993Certificate.logOnePlusV leaf2993InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2993InputLogOnePlusV_eq }

private noncomputable def leaf2993Inputs : Inputs :=
  inputsOfCaches globalInput sk235RoundedInputs
    chi135InputQChi innerPair218Input
    leaf2993InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2993LowerChecked :
    lowerCheck 24 leaf2993Box leaf2993Inputs = true := by
  rfl'

private theorem leaf2993CoversExact : CoversExact 8
    leaf2993Box leaf2993Certificate leaf2993InnerLog leaf2993Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk235RoundedFacts chi135RoundedFacts
    innerPair218RoundedFacts leaf2993RoundedFacts (by rfl)

private theorem leaf2993FlatSound : Sound leaf2993Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2993CertificateValid
    leaf2993InnerLogValid leaf2993CoversExact leaf2993LowerChecked

private noncomputable def leaf2994Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (63/16), chiLo := (23/128), chiHi := (47/256) }

private noncomputable def leaf2994Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742421/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432889344) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1830340933/1073741824) }, upper := { exponent := 0, mantissa := (7057/4096) } }, logOuter := sk236LogOuterCertificate, logK := sk236LogKCertificate, logChi := chi135LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869811199/274865778688) } }, logDArg := sk236LogDArgCertificate }

private noncomputable def leaf2994InnerLog : WideLogData :=
  innerPair480Data

set_option maxRecDepth 1000000 in
private theorem leaf2994LocalValidity :
    LeafFacts leaf2994Box leaf2994Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2994Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432889344) }) = true
      norm_num [leaf2994Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2994CertificateValid :
    WideCertificateValid leaf2994Box leaf2994Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk236ValidityFacts chi135ValidityFacts
    leaf2994LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2994CoverageChecked :
    coverageCheck (innerAD leaf2994Box) leaf2994InnerLog = true := by
  rfl'

private theorem leaf2994InnerLogValid :
    leaf2994InnerLog.Valid 8 (innerAD leaf2994Box) :=
  wideLogDataValid_of_cachedCheck endpoint208PositiveFacts
    endpoint209PositiveFacts.valid leaf2994CoverageChecked

private noncomputable def leaf2994InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629327/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2994InputLogOnePlusV_eq :
    leaf2994InputLogOnePlusV = outerEnclosure 24
      (leaf2994Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2994RoundedFacts : LeafRoundedFacts 8
    leaf2994Certificate.logOnePlusV leaf2994InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2994InputLogOnePlusV_eq }

private noncomputable def leaf2994Inputs : Inputs :=
  inputsOfCaches globalInput sk236RoundedInputs
    chi135InputQChi innerPair480Input
    leaf2994InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2994LowerChecked :
    lowerCheck 24 leaf2994Box leaf2994Inputs = true := by
  rfl'

private theorem leaf2994CoversExact : CoversExact 8
    leaf2994Box leaf2994Certificate leaf2994InnerLog leaf2994Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk236RoundedFacts chi135RoundedFacts
    innerPair480RoundedFacts leaf2994RoundedFacts (by rfl)

private theorem leaf2994FlatSound : Sound leaf2994Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2994CertificateValid
    leaf2994InnerLogValid leaf2994CoversExact leaf2994LowerChecked

private noncomputable def leaf2995Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (251/64), chiLo := (47/256), chiHi := (3/16) }

private noncomputable def leaf2995Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742421/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432784896) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1843709461/1073741824) }, upper := { exponent := 0, mantissa := (1777/1024) } }, logOuter := sk235LogOuterCertificate, logK := sk235LogKCertificate, logChi := chi136LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869706751/274865569792) } }, logDArg := sk235LogDArgCertificate }

private noncomputable def leaf2995InnerLog : WideLogData :=
  innerPair481Data

set_option maxRecDepth 1000000 in
private theorem leaf2995LocalValidity :
    LeafFacts leaf2995Box leaf2995Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2995Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432784896) }) = true
      norm_num [leaf2995Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2995CertificateValid :
    WideCertificateValid leaf2995Box leaf2995Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk235ValidityFacts chi136ValidityFacts
    leaf2995LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2995CoverageChecked :
    coverageCheck (innerAD leaf2995Box) leaf2995InnerLog = true := by
  rfl'

private theorem leaf2995InnerLogValid :
    leaf2995InnerLog.Valid 8 (innerAD leaf2995Box) :=
  wideLogDataValid_of_cachedCheck endpoint210PositiveFacts
    endpoint177PositiveFacts.valid leaf2995CoverageChecked

private noncomputable def leaf2995InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629333/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2995InputLogOnePlusV_eq :
    leaf2995InputLogOnePlusV = outerEnclosure 24
      (leaf2995Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2995RoundedFacts : LeafRoundedFacts 8
    leaf2995Certificate.logOnePlusV leaf2995InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2995InputLogOnePlusV_eq }

private noncomputable def leaf2995Inputs : Inputs :=
  inputsOfCaches globalInput sk235RoundedInputs
    chi136InputQChi innerPair481Input
    leaf2995InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2995LowerChecked :
    lowerCheck 24 leaf2995Box leaf2995Inputs = true := by
  rfl'

private theorem leaf2995CoversExact : CoversExact 8
    leaf2995Box leaf2995Certificate leaf2995InnerLog leaf2995Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk235RoundedFacts chi136RoundedFacts
    innerPair481RoundedFacts leaf2995RoundedFacts (by rfl)

private theorem leaf2995FlatSound : Sound leaf2995Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2995CertificateValid
    leaf2995InnerLogValid leaf2995CoversExact leaf2995LowerChecked

private noncomputable def leaf2996Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (63/16), chiLo := (47/256), chiHi := (95/512) }

private noncomputable def leaf2996Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484341/2147483648) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432824832) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3693612197/2147483648) }, upper := { exponent := 0, mantissa := (14177/8192) } }, logOuter := sk236LogOuterCertificate, logK := sk236LogKCertificate, logChi := chi213LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869746687/274865649664) } }, logDArg := sk236LogDArgCertificate }

private noncomputable def leaf2996InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf2996LocalValidity :
    LeafFacts leaf2996Box leaf2996Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2996Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432824832) }) = true
      norm_num [leaf2996Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2996CertificateValid :
    WideCertificateValid leaf2996Box leaf2996Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk236ValidityFacts chi213ValidityFacts
    leaf2996LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2996CoverageChecked :
    coverageCheck (innerAD leaf2996Box) leaf2996InnerLog = true := by
  rfl'

private theorem leaf2996InnerLogValid :
    leaf2996InnerLog.Valid 8 (innerAD leaf2996Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf2996CoverageChecked

private noncomputable def leaf2996InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629331/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2996InputLogOnePlusV_eq :
    leaf2996InputLogOnePlusV = outerEnclosure 24
      (leaf2996Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2996RoundedFacts : LeafRoundedFacts 8
    leaf2996Certificate.logOnePlusV leaf2996InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2996InputLogOnePlusV_eq }

private noncomputable def leaf2996Inputs : Inputs :=
  inputsOfCaches globalInput sk236RoundedInputs
    chi213InputQChi innerPair64Input
    leaf2996InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2996LowerChecked :
    lowerCheck 24 leaf2996Box leaf2996Inputs = true := by
  rfl'

private theorem leaf2996CoversExact : CoversExact 8
    leaf2996Box leaf2996Certificate leaf2996InnerLog leaf2996Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk236RoundedFacts chi213RoundedFacts
    innerPair64RoundedFacts leaf2996RoundedFacts (by rfl)

private theorem leaf2996FlatSound : Sound leaf2996Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2996CertificateValid
    leaf2996InnerLogValid leaf2996CoversExact leaf2996LowerChecked

private noncomputable def leaf2997Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (63/16), chiLo := (95/512), chiHi := (3/16) }

private noncomputable def leaf2997Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484343/2147483648) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486552064) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3710060727/2147483648) }, upper := { exponent := 0, mantissa := (445/256) } }, logOuter := sk236LogOuterCertificate, logK := sk236LogKCertificate, logChi := chi214LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973936435/54973104128) } }, logDArg := sk236LogDArgCertificate }

private noncomputable def leaf2997InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf2997LocalValidity :
    LeafFacts leaf2997Box leaf2997Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2997Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486552064) }) = true
      norm_num [leaf2997Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2997CertificateValid :
    WideCertificateValid leaf2997Box leaf2997Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk236ValidityFacts chi214ValidityFacts
    leaf2997LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2997CoverageChecked :
    coverageCheck (innerAD leaf2997Box) leaf2997InnerLog = true := by
  rfl'

private theorem leaf2997InnerLogValid :
    leaf2997InnerLog.Valid 8 (innerAD leaf2997Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf2997CoverageChecked

private noncomputable def leaf2997InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629335/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2997InputLogOnePlusV_eq :
    leaf2997InputLogOnePlusV = outerEnclosure 24
      (leaf2997Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2997RoundedFacts : LeafRoundedFacts 8
    leaf2997Certificate.logOnePlusV leaf2997InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2997InputLogOnePlusV_eq }

private noncomputable def leaf2997Inputs : Inputs :=
  inputsOfCaches globalInput sk236RoundedInputs
    chi214InputQChi innerPair64Input
    leaf2997InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2997LowerChecked :
    lowerCheck 24 leaf2997Box leaf2997Inputs = true := by
  rfl'

private theorem leaf2997CoversExact : CoversExact 8
    leaf2997Box leaf2997Certificate leaf2997InnerLog leaf2997Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk236RoundedFacts chi214RoundedFacts
    innerPair64RoundedFacts leaf2997RoundedFacts (by rfl)

private theorem leaf2997FlatSound : Sound leaf2997Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2997CertificateValid
    leaf2997InnerLogValid leaf2997CoversExact leaf2997LowerChecked

private noncomputable def leaf2998Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (11/64), chiHi := (45/256) }

private noncomputable def leaf2998Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742419/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433124352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1800327279/1073741824) }, upper := { exponent := 0, mantissa := (27769/16384) } }, logOuter := sk237LogOuterCertificate, logK := sk237LogKCertificate, logChi := chi133LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870046207/274866248704) } }, logDArg := sk237LogDArgCertificate }

private noncomputable def leaf2998InnerLog : WideLogData :=
  innerPair190Data

set_option maxRecDepth 1000000 in
private theorem leaf2998LocalValidity :
    LeafFacts leaf2998Box leaf2998Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2998Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433124352) }) = true
      norm_num [leaf2998Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2998CertificateValid :
    WideCertificateValid leaf2998Box leaf2998Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk237ValidityFacts chi133ValidityFacts
    leaf2998LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2998CoverageChecked :
    coverageCheck (innerAD leaf2998Box) leaf2998InnerLog = true := by
  rfl'

private theorem leaf2998InnerLogValid :
    leaf2998InnerLog.Valid 8 (innerAD leaf2998Box) :=
  wideLogDataValid_of_cachedCheck endpoint56PositiveFacts
    endpoint137PositiveFacts.valid leaf2998CoverageChecked

private noncomputable def leaf2998InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629313/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2998InputLogOnePlusV_eq :
    leaf2998InputLogOnePlusV = outerEnclosure 24
      (leaf2998Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2998RoundedFacts : LeafRoundedFacts 8
    leaf2998Certificate.logOnePlusV leaf2998InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2998InputLogOnePlusV_eq }

private noncomputable def leaf2998Inputs : Inputs :=
  inputsOfCaches globalInput sk237RoundedInputs
    chi133InputQChi innerPair190Input
    leaf2998InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2998LowerChecked :
    lowerCheck 24 leaf2998Box leaf2998Inputs = true := by
  rfl'

private theorem leaf2998CoversExact : CoversExact 8
    leaf2998Box leaf2998Certificate leaf2998InnerLog leaf2998Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk237RoundedFacts chi133RoundedFacts
    innerPair190RoundedFacts leaf2998RoundedFacts (by rfl)

private theorem leaf2998FlatSound : Sound leaf2998Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2998CertificateValid
    leaf2998InnerLogValid leaf2998CoversExact leaf2998LowerChecked

private noncomputable def leaf2999Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (11/64), chiHi := (89/512) }

private noncomputable def leaf2999Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484333/2147483648) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433166336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3606454645/2147483648) }, upper := { exponent := 0, mantissa := (27687/16384) } }, logOuter := sk238LogOuterCertificate, logK := sk238LogKCertificate, logChi := chi215LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870088191/274866332672) } }, logDArg := sk238LogDArgCertificate }

private noncomputable def leaf2999InnerLog : WideLogData :=
  innerPair420Data

set_option maxRecDepth 1000000 in
private theorem leaf2999LocalValidity :
    LeafFacts leaf2999Box leaf2999Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2999Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433166336) }) = true
      norm_num [leaf2999Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2999CertificateValid :
    WideCertificateValid leaf2999Box leaf2999Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk238ValidityFacts chi215ValidityFacts
    leaf2999LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2999CoverageChecked :
    coverageCheck (innerAD leaf2999Box) leaf2999InnerLog = true := by
  rfl'

private theorem leaf2999InnerLogValid :
    leaf2999InnerLog.Valid 8 (innerAD leaf2999Box) :=
  wideLogDataValid_of_cachedCheck endpoint133PositiveFacts
    endpoint20PositiveFacts.valid leaf2999CoverageChecked

private noncomputable def leaf2999InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814655/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2999InputLogOnePlusV_eq :
    leaf2999InputLogOnePlusV = outerEnclosure 24
      (leaf2999Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2999RoundedFacts : LeafRoundedFacts 8
    leaf2999Certificate.logOnePlusV leaf2999InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2999InputLogOnePlusV_eq }

private noncomputable def leaf2999Inputs : Inputs :=
  inputsOfCaches globalInput sk238RoundedInputs
    chi215InputQChi innerPair420Input
    leaf2999InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2999LowerChecked :
    lowerCheck 24 leaf2999Box leaf2999Inputs = true := by
  rfl'

private theorem leaf2999CoversExact : CoversExact 8
    leaf2999Box leaf2999Certificate leaf2999InnerLog leaf2999Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk238RoundedFacts chi215RoundedFacts
    innerPair420RoundedFacts leaf2999RoundedFacts (by rfl)

private theorem leaf2999FlatSound : Sound leaf2999Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2999CertificateValid
    leaf2999InnerLogValid leaf2999CoversExact leaf2999LowerChecked

private noncomputable def leaf3000Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (89/512), chiHi := (45/256) }

private noncomputable def leaf3000Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484335/2147483648) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433101312) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3623034239/2147483648) }, upper := { exponent := 0, mantissa := (13907/8192) } }, logOuter := sk238LogOuterCertificate, logK := sk238LogKCertificate, logChi := chi216LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870023167/274866202624) } }, logDArg := sk238LogDArgCertificate }

private noncomputable def leaf3000InnerLog : WideLogData :=
  innerPair420Data

set_option maxRecDepth 1000000 in
private theorem leaf3000LocalValidity :
    LeafFacts leaf3000Box leaf3000Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3000Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433101312) }) = true
      norm_num [leaf3000Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3000CertificateValid :
    WideCertificateValid leaf3000Box leaf3000Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk238ValidityFacts chi216ValidityFacts
    leaf3000LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3000CoverageChecked :
    coverageCheck (innerAD leaf3000Box) leaf3000InnerLog = true := by
  rfl'

private theorem leaf3000InnerLogValid :
    leaf3000InnerLog.Valid 8 (innerAD leaf3000Box) :=
  wideLogDataValid_of_cachedCheck endpoint133PositiveFacts
    endpoint20PositiveFacts.valid leaf3000CoverageChecked

private noncomputable def leaf3000InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814657/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3000InputLogOnePlusV_eq :
    leaf3000InputLogOnePlusV = outerEnclosure 24
      (leaf3000Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3000RoundedFacts : LeafRoundedFacts 8
    leaf3000Certificate.logOnePlusV leaf3000InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3000InputLogOnePlusV_eq }

private noncomputable def leaf3000Inputs : Inputs :=
  inputsOfCaches globalInput sk238RoundedInputs
    chi216InputQChi innerPair420Input
    leaf3000InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3000LowerChecked :
    lowerCheck 24 leaf3000Box leaf3000Inputs = true := by
  rfl'

private theorem leaf3000CoversExact : CoversExact 8
    leaf3000Box leaf3000Certificate leaf3000InnerLog leaf3000Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk238RoundedFacts chi216RoundedFacts
    innerPair420RoundedFacts leaf3000RoundedFacts (by rfl)

private theorem leaf3000FlatSound : Sound leaf3000Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3000CertificateValid
    leaf3000InnerLogValid leaf3000CoversExact leaf3000LowerChecked

private noncomputable def leaf3001Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (45/256), chiHi := (91/512) }

private noncomputable def leaf3001Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484335/2147483648) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433059584) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3633715955/2147483648) }, upper := { exponent := 0, mantissa := (55791/32768) } }, logOuter := sk237LogOuterCertificate, logK := sk237LogKCertificate, logChi := chi217LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869981439/274866119168) } }, logDArg := sk237LogDArgCertificate }

private noncomputable def leaf3001InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3001LocalValidity :
    LeafFacts leaf3001Box leaf3001Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3001Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433059584) }) = true
      norm_num [leaf3001Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3001CertificateValid :
    WideCertificateValid leaf3001Box leaf3001Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk237ValidityFacts chi217ValidityFacts
    leaf3001LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3001CoverageChecked :
    coverageCheck (innerAD leaf3001Box) leaf3001InnerLog = true := by
  rfl'

private theorem leaf3001InnerLogValid :
    leaf3001InnerLog.Valid 8 (innerAD leaf3001Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3001CoverageChecked

private noncomputable def leaf3001InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907329/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3001InputLogOnePlusV_eq :
    leaf3001InputLogOnePlusV = outerEnclosure 24
      (leaf3001Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3001RoundedFacts : LeafRoundedFacts 8
    leaf3001Certificate.logOnePlusV leaf3001InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3001InputLogOnePlusV_eq }

private noncomputable def leaf3001Inputs : Inputs :=
  inputsOfCaches globalInput sk237RoundedInputs
    chi217InputQChi innerPair64Input
    leaf3001InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3001LowerChecked :
    lowerCheck 24 leaf3001Box leaf3001Inputs = true := by
  rfl'

private theorem leaf3001CoversExact : CoversExact 8
    leaf3001Box leaf3001Certificate leaf3001InnerLog leaf3001Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk237RoundedFacts chi217RoundedFacts
    innerPair64RoundedFacts leaf3001RoundedFacts (by rfl)

private theorem leaf3001FlatSound : Sound leaf3001Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3001CertificateValid
    leaf3001InnerLogValid leaf3001CoversExact leaf3001LowerChecked

private noncomputable def leaf3002Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (91/512), chiHi := (23/128) }

private noncomputable def leaf3002Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484337/2147483648) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810998272) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3650230017/2147483648) }, upper := { exponent := 0, mantissa := (14011/8192) } }, logOuter := sk237LogOuterCertificate, logK := sk237LogKCertificate, logChi := chi218LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623305557/91621996544) } }, logDArg := sk237LogDArgCertificate }

private noncomputable def leaf3002InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3002LocalValidity :
    LeafFacts leaf3002Box leaf3002Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3002Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810998272) }) = true
      norm_num [leaf3002Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3002CertificateValid :
    WideCertificateValid leaf3002Box leaf3002Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk237ValidityFacts chi218ValidityFacts
    leaf3002LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3002CoverageChecked :
    coverageCheck (innerAD leaf3002Box) leaf3002InnerLog = true := by
  rfl'

private theorem leaf3002InnerLogValid :
    leaf3002InnerLog.Valid 8 (innerAD leaf3002Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3002CoverageChecked

private noncomputable def leaf3002InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453665/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf3002InputLogOnePlusV_eq :
    leaf3002InputLogOnePlusV = outerEnclosure 24
      (leaf3002Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3002RoundedFacts : LeafRoundedFacts 8
    leaf3002Certificate.logOnePlusV leaf3002InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3002InputLogOnePlusV_eq }

private noncomputable def leaf3002Inputs : Inputs :=
  inputsOfCaches globalInput sk237RoundedInputs
    chi218InputQChi innerPair64Input
    leaf3002InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3002LowerChecked :
    lowerCheck 24 leaf3002Box leaf3002Inputs = true := by
  rfl'

private theorem leaf3002CoversExact : CoversExact 8
    leaf3002Box leaf3002Certificate leaf3002InnerLog leaf3002Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk237RoundedFacts chi218RoundedFacts
    innerPair64RoundedFacts leaf3002RoundedFacts (by rfl)

private theorem leaf3002FlatSound : Sound leaf3002Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3002CertificateValid
    leaf3002InnerLogValid leaf3002CoversExact leaf3002LowerChecked

private noncomputable def leaf3003Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (45/256), chiHi := (91/512) }

private noncomputable def leaf3003Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484337/2147483648) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45811012096) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3639613833/2147483648) }, upper := { exponent := 0, mantissa := (27941/16384) } }, logOuter := sk238LogOuterCertificate, logK := sk238LogKCertificate, logChi := chi217LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623319381/91622024192) } }, logDArg := sk238LogDArgCertificate }

private noncomputable def leaf3003InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3003LocalValidity :
    LeafFacts leaf3003Box leaf3003Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3003Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45811012096) }) = true
      norm_num [leaf3003Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3003CertificateValid :
    WideCertificateValid leaf3003Box leaf3003Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk238ValidityFacts chi217ValidityFacts
    leaf3003LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3003CoverageChecked :
    coverageCheck (innerAD leaf3003Box) leaf3003InnerLog = true := by
  rfl'

private theorem leaf3003InnerLogValid :
    leaf3003InnerLog.Valid 8 (innerAD leaf3003Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3003CoverageChecked

private noncomputable def leaf3003InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814659/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3003InputLogOnePlusV_eq :
    leaf3003InputLogOnePlusV = outerEnclosure 24
      (leaf3003Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3003RoundedFacts : LeafRoundedFacts 8
    leaf3003Certificate.logOnePlusV leaf3003InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3003InputLogOnePlusV_eq }

private noncomputable def leaf3003Inputs : Inputs :=
  inputsOfCaches globalInput sk238RoundedInputs
    chi217InputQChi innerPair64Input
    leaf3003InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3003LowerChecked :
    lowerCheck 24 leaf3003Box leaf3003Inputs = true := by
  rfl'

private theorem leaf3003CoversExact : CoversExact 8
    leaf3003Box leaf3003Certificate leaf3003InnerLog leaf3003Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk238RoundedFacts chi217RoundedFacts
    innerPair64RoundedFacts leaf3003RoundedFacts (by rfl)

private theorem leaf3003FlatSound : Sound leaf3003Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3003CertificateValid
    leaf3003InnerLogValid leaf3003CoversExact leaf3003LowerChecked

private noncomputable def leaf3004Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (91/512), chiHi := (23/128) }

private noncomputable def leaf3004Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484339/2147483648) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432971264) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3656193427/2147483648) }, upper := { exponent := 0, mantissa := (7017/4096) } }, logOuter := sk238LogOuterCertificate, logK := sk238LogKCertificate, logChi := chi218LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869893119/274865942528) } }, logDArg := sk238LogDArgCertificate }

private noncomputable def leaf3004InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3004LocalValidity :
    LeafFacts leaf3004Box leaf3004Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3004Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432971264) }) = true
      norm_num [leaf3004Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3004CertificateValid :
    WideCertificateValid leaf3004Box leaf3004Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk238ValidityFacts chi218ValidityFacts
    leaf3004LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3004CoverageChecked :
    coverageCheck (innerAD leaf3004Box) leaf3004InnerLog = true := by
  rfl'

private theorem leaf3004InnerLogValid :
    leaf3004InnerLog.Valid 8 (innerAD leaf3004Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3004CoverageChecked

private noncomputable def leaf3004InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814661/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3004InputLogOnePlusV_eq :
    leaf3004InputLogOnePlusV = outerEnclosure 24
      (leaf3004Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3004RoundedFacts : LeafRoundedFacts 8
    leaf3004Certificate.logOnePlusV leaf3004InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3004InputLogOnePlusV_eq }

private noncomputable def leaf3004Inputs : Inputs :=
  inputsOfCaches globalInput sk238RoundedInputs
    chi218InputQChi innerPair64Input
    leaf3004InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3004LowerChecked :
    lowerCheck 24 leaf3004Box leaf3004Inputs = true := by
  rfl'

private theorem leaf3004CoversExact : CoversExact 8
    leaf3004Box leaf3004Certificate leaf3004InnerLog leaf3004Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk238RoundedFacts chi218RoundedFacts
    innerPair64RoundedFacts leaf3004RoundedFacts (by rfl)

private theorem leaf3004FlatSound : Sound leaf3004Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3004CertificateValid
    leaf3004InnerLogValid leaf3004CoversExact leaf3004LowerChecked

private noncomputable def leaf3005Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (11/64), chiHi := (89/512) }

private noncomputable def leaf3005Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484335/2147483648) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433143552) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3612221459/2147483648) }, upper := { exponent := 0, mantissa := (55463/32768) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi215LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870065407/274866287104) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf3005InnerLog : WideLogData :=
  innerPair420Data

set_option maxRecDepth 1000000 in
private theorem leaf3005LocalValidity :
    LeafFacts leaf3005Box leaf3005Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3005Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433143552) }) = true
      norm_num [leaf3005Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3005CertificateValid :
    WideCertificateValid leaf3005Box leaf3005Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi215ValidityFacts
    leaf3005LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3005CoverageChecked :
    coverageCheck (innerAD leaf3005Box) leaf3005InnerLog = true := by
  rfl'

private theorem leaf3005InnerLogValid :
    leaf3005InnerLog.Valid 8 (innerAD leaf3005Box) :=
  wideLogDataValid_of_cachedCheck endpoint133PositiveFacts
    endpoint20PositiveFacts.valid leaf3005CoverageChecked

private noncomputable def leaf3005InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629311/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3005InputLogOnePlusV_eq :
    leaf3005InputLogOnePlusV = outerEnclosure 24
      (leaf3005Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3005RoundedFacts : LeafRoundedFacts 8
    leaf3005Certificate.logOnePlusV leaf3005InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3005InputLogOnePlusV_eq }

private noncomputable def leaf3005Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi215InputQChi innerPair420Input
    leaf3005InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3005LowerChecked :
    lowerCheck 24 leaf3005Box leaf3005Inputs = true := by
  rfl'

private theorem leaf3005CoversExact : CoversExact 8
    leaf3005Box leaf3005Certificate leaf3005InnerLog leaf3005Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi215RoundedFacts
    innerPair420RoundedFacts leaf3005RoundedFacts (by rfl)

private theorem leaf3005FlatSound : Sound leaf3005Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3005CertificateValid
    leaf3005InnerLogValid leaf3005CoversExact leaf3005LowerChecked

private noncomputable def leaf3006Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (89/512), chiHi := (45/256) }

private noncomputable def leaf3006Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484337/2147483648) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433078272) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3628866585/2147483648) }, upper := { exponent := 0, mantissa := (27859/16384) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi216LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870000127/274866156544) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf3006InnerLog : WideLogData :=
  innerPair65Data

set_option maxRecDepth 1000000 in
private theorem leaf3006LocalValidity :
    LeafFacts leaf3006Box leaf3006Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3006Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433078272) }) = true
      norm_num [leaf3006Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3006CertificateValid :
    WideCertificateValid leaf3006Box leaf3006Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi216ValidityFacts
    leaf3006LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3006CoverageChecked :
    coverageCheck (innerAD leaf3006Box) leaf3006InnerLog = true := by
  rfl'

private theorem leaf3006InnerLogValid :
    leaf3006InnerLog.Valid 8 (innerAD leaf3006Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint20PositiveFacts.valid leaf3006CoverageChecked

private noncomputable def leaf3006InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629315/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3006InputLogOnePlusV_eq :
    leaf3006InputLogOnePlusV = outerEnclosure 24
      (leaf3006Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3006RoundedFacts : LeafRoundedFacts 8
    leaf3006Certificate.logOnePlusV leaf3006InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3006InputLogOnePlusV_eq }

private noncomputable def leaf3006Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi216InputQChi innerPair65Input
    leaf3006InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3006LowerChecked :
    lowerCheck 24 leaf3006Box leaf3006Inputs = true := by
  rfl'

private theorem leaf3006CoversExact : CoversExact 8
    leaf3006Box leaf3006Certificate leaf3006InnerLog leaf3006Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi216RoundedFacts
    innerPair65RoundedFacts leaf3006RoundedFacts (by rfl)

private theorem leaf3006FlatSound : Sound leaf3006Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3006CertificateValid
    leaf3006InnerLogValid leaf3006CoversExact leaf3006LowerChecked

private noncomputable def leaf3007Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (11/64), chiHi := (89/512) }

private noncomputable def leaf3007Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484337/2147483648) }, vSqrt := { lower := (65527/65536), upper := (5090256365/5090115584) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3617988273/2147483648) }, upper := { exponent := 0, mantissa := (217/128) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi215LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (10180371949/10180231168) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf3007InnerLog : WideLogData :=
  innerPair420Data

set_option maxRecDepth 1000000 in
private theorem leaf3007LocalValidity :
    LeafFacts leaf3007Box leaf3007Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3007Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (5090256365/5090115584) }) = true
      norm_num [leaf3007Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3007CertificateValid :
    WideCertificateValid leaf3007Box leaf3007Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi215ValidityFacts
    leaf3007LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3007CoverageChecked :
    coverageCheck (innerAD leaf3007Box) leaf3007InnerLog = true := by
  rfl'

private theorem leaf3007InnerLogValid :
    leaf3007InnerLog.Valid 8 (innerAD leaf3007Box) :=
  wideLogDataValid_of_cachedCheck endpoint133PositiveFacts
    endpoint20PositiveFacts.valid leaf3007CoverageChecked

private noncomputable def leaf3007InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629313/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3007InputLogOnePlusV_eq :
    leaf3007InputLogOnePlusV = outerEnclosure 24
      (leaf3007Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3007RoundedFacts : LeafRoundedFacts 8
    leaf3007Certificate.logOnePlusV leaf3007InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3007InputLogOnePlusV_eq }

private noncomputable def leaf3007Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi215InputQChi innerPair420Input
    leaf3007InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3007LowerChecked :
    lowerCheck 24 leaf3007Box leaf3007Inputs = true := by
  rfl'

private theorem leaf3007CoversExact : CoversExact 8
    leaf3007Box leaf3007Certificate leaf3007InnerLog leaf3007Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi215RoundedFacts
    innerPair420RoundedFacts leaf3007RoundedFacts (by rfl)

private theorem leaf3007FlatSound : Sound leaf3007Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3007CertificateValid
    leaf3007InnerLogValid leaf3007CoversExact leaf3007LowerChecked

private noncomputable def leaf3008Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (89/512), chiHi := (45/256) }

private noncomputable def leaf3008Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484339/2147483648) }, vSqrt := { lower := (65527/65536), upper := (137436921855/137433055232) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3634698931/2147483648) }, upper := { exponent := 0, mantissa := (109/64) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi216LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (274869977087/274866110464) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf3008InnerLog : WideLogData :=
  innerPair65Data

set_option maxRecDepth 1000000 in
private theorem leaf3008LocalValidity :
    LeafFacts leaf3008Box leaf3008Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3008Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (137436921855/137433055232) }) = true
      norm_num [leaf3008Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3008CertificateValid :
    WideCertificateValid leaf3008Box leaf3008Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi216ValidityFacts
    leaf3008LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3008CoverageChecked :
    coverageCheck (innerAD leaf3008Box) leaf3008InnerLog = true := by
  rfl'

private theorem leaf3008InnerLogValid :
    leaf3008InnerLog.Valid 8 (innerAD leaf3008Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint20PositiveFacts.valid leaf3008CoverageChecked

private noncomputable def leaf3008InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629317/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3008InputLogOnePlusV_eq :
    leaf3008InputLogOnePlusV = outerEnclosure 24
      (leaf3008Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3008RoundedFacts : LeafRoundedFacts 8
    leaf3008Certificate.logOnePlusV leaf3008InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3008InputLogOnePlusV_eq }

private noncomputable def leaf3008Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi216InputQChi innerPair65Input
    leaf3008InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3008LowerChecked :
    lowerCheck 24 leaf3008Box leaf3008Inputs = true := by
  rfl'

private theorem leaf3008CoversExact : CoversExact 8
    leaf3008Box leaf3008Certificate leaf3008InnerLog leaf3008Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi216RoundedFacts
    innerPair65RoundedFacts leaf3008RoundedFacts (by rfl)

private theorem leaf3008FlatSound : Sound leaf3008Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3008CertificateValid
    leaf3008InnerLogValid leaf3008CoversExact leaf3008LowerChecked

private noncomputable def leaf3009Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (45/256), chiHi := (91/512) }

private noncomputable def leaf3009Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484339/2147483648) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433012992) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3645511711/2147483648) }, upper := { exponent := 0, mantissa := (55973/32768) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi217LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869934847/274866025984) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf3009InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3009LocalValidity :
    LeafFacts leaf3009Box leaf3009Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3009Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433012992) }) = true
      norm_num [leaf3009Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3009CertificateValid :
    WideCertificateValid leaf3009Box leaf3009Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi217ValidityFacts
    leaf3009LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3009CoverageChecked :
    coverageCheck (innerAD leaf3009Box) leaf3009InnerLog = true := by
  rfl'

private theorem leaf3009InnerLogValid :
    leaf3009InnerLog.Valid 8 (innerAD leaf3009Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3009CoverageChecked

private noncomputable def leaf3009InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629319/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3009InputLogOnePlusV_eq :
    leaf3009InputLogOnePlusV = outerEnclosure 24
      (leaf3009Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3009RoundedFacts : LeafRoundedFacts 8
    leaf3009Certificate.logOnePlusV leaf3009InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3009InputLogOnePlusV_eq }

private noncomputable def leaf3009Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi217InputQChi innerPair64Input
    leaf3009InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3009LowerChecked :
    lowerCheck 24 leaf3009Box leaf3009Inputs = true := by
  rfl'

private theorem leaf3009CoversExact : CoversExact 8
    leaf3009Box leaf3009Certificate leaf3009InnerLog leaf3009Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi217RoundedFacts
    innerPair64RoundedFacts leaf3009RoundedFacts (by rfl)

private theorem leaf3009FlatSound : Sound leaf3009Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3009CertificateValid
    leaf3009InnerLogValid leaf3009CoversExact leaf3009LowerChecked

private noncomputable def leaf3010Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (91/512), chiHi := (23/128) }

private noncomputable def leaf3010Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484341/2147483648) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432947712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3662156837/2147483648) }, upper := { exponent := 0, mantissa := (14057/8192) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi218LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869869567/274865895424) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf3010InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3010LocalValidity :
    LeafFacts leaf3010Box leaf3010Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3010Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432947712) }) = true
      norm_num [leaf3010Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3010CertificateValid :
    WideCertificateValid leaf3010Box leaf3010Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi218ValidityFacts
    leaf3010LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3010CoverageChecked :
    coverageCheck (innerAD leaf3010Box) leaf3010InnerLog = true := by
  rfl'

private theorem leaf3010InnerLogValid :
    leaf3010InnerLog.Valid 8 (innerAD leaf3010Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3010CoverageChecked

private noncomputable def leaf3010InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629323/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3010InputLogOnePlusV_eq :
    leaf3010InputLogOnePlusV = outerEnclosure 24
      (leaf3010Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3010RoundedFacts : LeafRoundedFacts 8
    leaf3010Certificate.logOnePlusV leaf3010InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3010InputLogOnePlusV_eq }

private noncomputable def leaf3010Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi218InputQChi innerPair64Input
    leaf3010InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3010LowerChecked :
    lowerCheck 24 leaf3010Box leaf3010Inputs = true := by
  rfl'

private theorem leaf3010CoversExact : CoversExact 8
    leaf3010Box leaf3010Certificate leaf3010InnerLog leaf3010Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi218RoundedFacts
    innerPair64RoundedFacts leaf3010RoundedFacts (by rfl)

private theorem leaf3010FlatSound : Sound leaf3010Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3010CertificateValid
    leaf3010InnerLogValid leaf3010CoversExact leaf3010LowerChecked

private noncomputable def leaf3011Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (45/256), chiHi := (91/512) }

private noncomputable def leaf3011Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484341/2147483648) }, vSqrt := { lower := (65527/65536), upper := (137436921855/137432989696) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3651409589/2147483648) }, upper := { exponent := 0, mantissa := (219/128) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi217LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (274869911551/274865979392) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf3011InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3011LocalValidity :
    LeafFacts leaf3011Box leaf3011Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3011Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (137436921855/137432989696) }) = true
      norm_num [leaf3011Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3011CertificateValid :
    WideCertificateValid leaf3011Box leaf3011Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi217ValidityFacts
    leaf3011LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3011CoverageChecked :
    coverageCheck (innerAD leaf3011Box) leaf3011InnerLog = true := by
  rfl'

private theorem leaf3011InnerLogValid :
    leaf3011InnerLog.Valid 8 (innerAD leaf3011Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3011CoverageChecked

private noncomputable def leaf3011InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629321/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3011InputLogOnePlusV_eq :
    leaf3011InputLogOnePlusV = outerEnclosure 24
      (leaf3011Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3011RoundedFacts : LeafRoundedFacts 8
    leaf3011Certificate.logOnePlusV leaf3011InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3011InputLogOnePlusV_eq }

private noncomputable def leaf3011Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi217InputQChi innerPair64Input
    leaf3011InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3011LowerChecked :
    lowerCheck 24 leaf3011Box leaf3011Inputs = true := by
  rfl'

private theorem leaf3011CoversExact : CoversExact 8
    leaf3011Box leaf3011Certificate leaf3011InnerLog leaf3011Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi217RoundedFacts
    innerPair64RoundedFacts leaf3011RoundedFacts (by rfl)

private theorem leaf3011FlatSound : Sound leaf3011Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3011CertificateValid
    leaf3011InnerLogValid leaf3011CoversExact leaf3011LowerChecked

private noncomputable def leaf3012Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (91/512), chiHi := (23/128) }

private noncomputable def leaf3012Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484343/2147483648) }, vSqrt := { lower := (65527/65536), upper := (9162461457/9162194944) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3668120247/2147483648) }, upper := { exponent := 0, mantissa := (55/32) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi218LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (18324656401/18324389888) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf3012InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3012LocalValidity :
    LeafFacts leaf3012Box leaf3012Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3012Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (9162461457/9162194944) }) = true
      norm_num [leaf3012Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3012CertificateValid :
    WideCertificateValid leaf3012Box leaf3012Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi218ValidityFacts
    leaf3012LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3012CoverageChecked :
    coverageCheck (innerAD leaf3012Box) leaf3012InnerLog = true := by
  rfl'

private theorem leaf3012InnerLogValid :
    leaf3012InnerLog.Valid 8 (innerAD leaf3012Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3012CoverageChecked

private noncomputable def leaf3012InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629325/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3012InputLogOnePlusV_eq :
    leaf3012InputLogOnePlusV = outerEnclosure 24
      (leaf3012Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3012RoundedFacts : LeafRoundedFacts 8
    leaf3012Certificate.logOnePlusV leaf3012InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3012InputLogOnePlusV_eq }

private noncomputable def leaf3012Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi218InputQChi innerPair64Input
    leaf3012InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3012LowerChecked :
    lowerCheck 24 leaf3012Box leaf3012Inputs = true := by
  rfl'

private theorem leaf3012CoversExact : CoversExact 8
    leaf3012Box leaf3012Certificate leaf3012InnerLog leaf3012Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi218RoundedFacts
    innerPair64RoundedFacts leaf3012RoundedFacts (by rfl)

private theorem leaf3012FlatSound : Sound leaf3012Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3012CertificateValid
    leaf3012InnerLogValid leaf3012CoversExact leaf3012LowerChecked

private noncomputable def leaf3013Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (23/128), chiHi := (93/512) }

private noncomputable def leaf3013Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484339/2147483648) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432930048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3666744079/2147483648) }, upper := { exponent := 0, mantissa := (56297/32768) } }, logOuter := sk237LogOuterCertificate, logK := sk237LogKCertificate, logChi := chi219LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869851903/274865860096) } }, logDArg := sk237LogDArgCertificate }

private noncomputable def leaf3013InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3013LocalValidity :
    LeafFacts leaf3013Box leaf3013Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3013Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432930048) }) = true
      norm_num [leaf3013Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3013CertificateValid :
    WideCertificateValid leaf3013Box leaf3013Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk237ValidityFacts chi219ValidityFacts
    leaf3013LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3013CoverageChecked :
    coverageCheck (innerAD leaf3013Box) leaf3013InnerLog = true := by
  rfl'

private theorem leaf3013InnerLogValid :
    leaf3013InnerLog.Valid 8 (innerAD leaf3013Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3013CoverageChecked

private noncomputable def leaf3013InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907331/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3013InputLogOnePlusV_eq :
    leaf3013InputLogOnePlusV = outerEnclosure 24
      (leaf3013Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3013RoundedFacts : LeafRoundedFacts 8
    leaf3013Certificate.logOnePlusV leaf3013InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3013InputLogOnePlusV_eq }

private noncomputable def leaf3013Inputs : Inputs :=
  inputsOfCaches globalInput sk237RoundedInputs
    chi219InputQChi innerPair64Input
    leaf3013InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3013LowerChecked :
    lowerCheck 24 leaf3013Box leaf3013Inputs = true := by
  rfl'

private theorem leaf3013CoversExact : CoversExact 8
    leaf3013Box leaf3013Certificate leaf3013InnerLog leaf3013Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk237RoundedFacts chi219RoundedFacts
    innerPair64RoundedFacts leaf3013RoundedFacts (by rfl)

private theorem leaf3013FlatSound : Sound leaf3013Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3013CertificateValid
    leaf3013InnerLogValid leaf3013CoversExact leaf3013LowerChecked

private noncomputable def leaf3014Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (93/512), chiHi := (47/256) }

private noncomputable def leaf3014Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484341/2147483648) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486573056) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3683258141/2147483648) }, upper := { exponent := 0, mantissa := (28275/16384) } }, logOuter := sk237LogOuterCertificate, logK := sk237LogKCertificate, logChi := chi220LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973957427/54973146112) } }, logDArg := sk237LogDArgCertificate }

private noncomputable def leaf3014InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3014LocalValidity :
    LeafFacts leaf3014Box leaf3014Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3014Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486573056) }) = true
      norm_num [leaf3014Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3014CertificateValid :
    WideCertificateValid leaf3014Box leaf3014Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk237ValidityFacts chi220ValidityFacts
    leaf3014LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3014CoverageChecked :
    coverageCheck (innerAD leaf3014Box) leaf3014InnerLog = true := by
  rfl'

private theorem leaf3014InnerLogValid :
    leaf3014InnerLog.Valid 8 (innerAD leaf3014Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3014CoverageChecked

private noncomputable def leaf3014InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726833/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf3014InputLogOnePlusV_eq :
    leaf3014InputLogOnePlusV = outerEnclosure 24
      (leaf3014Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3014RoundedFacts : LeafRoundedFacts 8
    leaf3014Certificate.logOnePlusV leaf3014InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3014InputLogOnePlusV_eq }

private noncomputable def leaf3014Inputs : Inputs :=
  inputsOfCaches globalInput sk237RoundedInputs
    chi220InputQChi innerPair64Input
    leaf3014InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3014LowerChecked :
    lowerCheck 24 leaf3014Box leaf3014Inputs = true := by
  rfl'

private theorem leaf3014CoversExact : CoversExact 8
    leaf3014Box leaf3014Certificate leaf3014InnerLog leaf3014Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk237RoundedFacts chi220RoundedFacts
    innerPair64RoundedFacts leaf3014RoundedFacts (by rfl)

private theorem leaf3014FlatSound : Sound leaf3014Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3014CertificateValid
    leaf3014InnerLogValid leaf3014CoversExact leaf3014LowerChecked

private noncomputable def leaf3015Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (23/128), chiHi := (93/512) }

private noncomputable def leaf3015Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484341/2147483648) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486581248) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3672773021/2147483648) }, upper := { exponent := 0, mantissa := (28195/16384) } }, logOuter := sk238LogOuterCertificate, logK := sk238LogKCertificate, logChi := chi219LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973965619/54973162496) } }, logDArg := sk238LogDArgCertificate }

private noncomputable def leaf3015InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3015LocalValidity :
    LeafFacts leaf3015Box leaf3015Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3015Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486581248) }) = true
      norm_num [leaf3015Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3015CertificateValid :
    WideCertificateValid leaf3015Box leaf3015Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk238ValidityFacts chi219ValidityFacts
    leaf3015LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3015CoverageChecked :
    coverageCheck (innerAD leaf3015Box) leaf3015InnerLog = true := by
  rfl'

private theorem leaf3015InnerLogValid :
    leaf3015InnerLog.Valid 8 (innerAD leaf3015Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3015CoverageChecked

private noncomputable def leaf3015InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814663/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3015InputLogOnePlusV_eq :
    leaf3015InputLogOnePlusV = outerEnclosure 24
      (leaf3015Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3015RoundedFacts : LeafRoundedFacts 8
    leaf3015Certificate.logOnePlusV leaf3015InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3015InputLogOnePlusV_eq }

private noncomputable def leaf3015Inputs : Inputs :=
  inputsOfCaches globalInput sk238RoundedInputs
    chi219InputQChi innerPair64Input
    leaf3015InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3015LowerChecked :
    lowerCheck 24 leaf3015Box leaf3015Inputs = true := by
  rfl'

private theorem leaf3015CoversExact : CoversExact 8
    leaf3015Box leaf3015Certificate leaf3015InnerLog leaf3015Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk238RoundedFacts chi219RoundedFacts
    innerPair64RoundedFacts leaf3015RoundedFacts (by rfl)

private theorem leaf3015FlatSound : Sound leaf3015Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3015CertificateValid
    leaf3015InnerLogValid leaf3015CoversExact leaf3015LowerChecked

private noncomputable def leaf3016Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (93/512), chiHi := (47/256) }

private noncomputable def leaf3016Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484343/2147483648) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810947072) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3689352615/2147483648) }, upper := { exponent := 0, mantissa := (14161/8192) } }, logOuter := sk238LogOuterCertificate, logK := sk238LogKCertificate, logChi := chi220LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623254357/91621894144) } }, logDArg := sk238LogDArgCertificate }

private noncomputable def leaf3016InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3016LocalValidity :
    LeafFacts leaf3016Box leaf3016Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3016Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810947072) }) = true
      norm_num [leaf3016Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3016CertificateValid :
    WideCertificateValid leaf3016Box leaf3016Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk238ValidityFacts chi220ValidityFacts
    leaf3016LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3016CoverageChecked :
    coverageCheck (innerAD leaf3016Box) leaf3016InnerLog = true := by
  rfl'

private theorem leaf3016InnerLogValid :
    leaf3016InnerLog.Valid 8 (innerAD leaf3016Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3016CoverageChecked

private noncomputable def leaf3016InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814665/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3016InputLogOnePlusV_eq :
    leaf3016InputLogOnePlusV = outerEnclosure 24
      (leaf3016Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3016RoundedFacts : LeafRoundedFacts 8
    leaf3016Certificate.logOnePlusV leaf3016InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3016InputLogOnePlusV_eq }

private noncomputable def leaf3016Inputs : Inputs :=
  inputsOfCaches globalInput sk238RoundedInputs
    chi220InputQChi innerPair64Input
    leaf3016InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3016LowerChecked :
    lowerCheck 24 leaf3016Box leaf3016Inputs = true := by
  rfl'

private theorem leaf3016CoversExact : CoversExact 8
    leaf3016Box leaf3016Certificate leaf3016InnerLog leaf3016Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk238RoundedFacts chi220RoundedFacts
    innerPair64RoundedFacts leaf3016RoundedFacts (by rfl)

private theorem leaf3016FlatSound : Sound leaf3016Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3016CertificateValid
    leaf3016InnerLogValid leaf3016CoversExact leaf3016LowerChecked

private noncomputable def leaf3017Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (47/256), chiHi := (95/512) }

private noncomputable def leaf3017Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484343/2147483648) }, vSqrt := { lower := (8191/8192), upper := (15270769095/15270311168) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3699772203/2147483648) }, upper := { exponent := 0, mantissa := (56803/32768) } }, logOuter := sk237LogOuterCertificate, logK := sk237LogKCertificate, logChi := chi213LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (30541080263/30540622336) } }, logDArg := sk237LogDArgCertificate }

private noncomputable def leaf3017InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3017LocalValidity :
    LeafFacts leaf3017Box leaf3017Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3017Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (15270769095/15270311168) }) = true
      norm_num [leaf3017Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3017CertificateValid :
    WideCertificateValid leaf3017Box leaf3017Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk237ValidityFacts chi213ValidityFacts
    leaf3017LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3017CoverageChecked :
    coverageCheck (innerAD leaf3017Box) leaf3017InnerLog = true := by
  rfl'

private theorem leaf3017InnerLogValid :
    leaf3017InnerLog.Valid 8 (innerAD leaf3017Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3017CoverageChecked

private noncomputable def leaf3017InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907333/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3017InputLogOnePlusV_eq :
    leaf3017InputLogOnePlusV = outerEnclosure 24
      (leaf3017Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3017RoundedFacts : LeafRoundedFacts 8
    leaf3017Certificate.logOnePlusV leaf3017InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3017InputLogOnePlusV_eq }

private noncomputable def leaf3017Inputs : Inputs :=
  inputsOfCaches globalInput sk237RoundedInputs
    chi213InputQChi innerPair64Input
    leaf3017InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3017LowerChecked :
    lowerCheck 24 leaf3017Box leaf3017Inputs = true := by
  rfl'

private theorem leaf3017CoversExact : CoversExact 8
    leaf3017Box leaf3017Certificate leaf3017InnerLog leaf3017Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk237RoundedFacts chi213RoundedFacts
    innerPair64RoundedFacts leaf3017RoundedFacts (by rfl)

private theorem leaf3017FlatSound : Sound leaf3017Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3017CertificateValid
    leaf3017InnerLogValid leaf3017CoversExact leaf3017LowerChecked

private noncomputable def leaf3018Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (95/512), chiHi := (3/16) }

private noncomputable def leaf3018Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484345/2147483648) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432735744) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3716286265/2147483648) }, upper := { exponent := 0, mantissa := (1783/1024) } }, logOuter := sk237LogOuterCertificate, logK := sk237LogKCertificate, logChi := chi214LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869657599/274865471488) } }, logDArg := sk237LogDArgCertificate }

private noncomputable def leaf3018InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3018LocalValidity :
    LeafFacts leaf3018Box leaf3018Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3018Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432735744) }) = true
      norm_num [leaf3018Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3018CertificateValid :
    WideCertificateValid leaf3018Box leaf3018Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk237ValidityFacts chi214ValidityFacts
    leaf3018LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3018CoverageChecked :
    coverageCheck (innerAD leaf3018Box) leaf3018InnerLog = true := by
  rfl'

private theorem leaf3018InnerLogValid :
    leaf3018InnerLog.Valid 8 (innerAD leaf3018Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3018CoverageChecked

private noncomputable def leaf3018InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453667/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf3018InputLogOnePlusV_eq :
    leaf3018InputLogOnePlusV = outerEnclosure 24
      (leaf3018Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3018RoundedFacts : LeafRoundedFacts 8
    leaf3018Certificate.logOnePlusV leaf3018InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3018InputLogOnePlusV_eq }

private noncomputable def leaf3018Inputs : Inputs :=
  inputsOfCaches globalInput sk237RoundedInputs
    chi214InputQChi innerPair64Input
    leaf3018InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3018LowerChecked :
    lowerCheck 24 leaf3018Box leaf3018Inputs = true := by
  rfl'

private theorem leaf3018CoversExact : CoversExact 8
    leaf3018Box leaf3018Certificate leaf3018InnerLog leaf3018Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk237RoundedFacts chi214RoundedFacts
    innerPair64RoundedFacts leaf3018RoundedFacts (by rfl)

private theorem leaf3018FlatSound : Sound leaf3018Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3018CertificateValid
    leaf3018InnerLogValid leaf3018CoversExact leaf3018LowerChecked

private noncomputable def leaf3019Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (47/256), chiHi := (95/512) }

private noncomputable def leaf3019Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484345/2147483648) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432776192) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3705932209/2147483648) }, upper := { exponent := 0, mantissa := (28449/16384) } }, logOuter := sk238LogOuterCertificate, logK := sk238LogKCertificate, logChi := chi213LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869698047/274865552384) } }, logDArg := sk238LogDArgCertificate }

private noncomputable def leaf3019InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3019LocalValidity :
    LeafFacts leaf3019Box leaf3019Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3019Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432776192) }) = true
      norm_num [leaf3019Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3019CertificateValid :
    WideCertificateValid leaf3019Box leaf3019Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk238ValidityFacts chi213ValidityFacts
    leaf3019LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3019CoverageChecked :
    coverageCheck (innerAD leaf3019Box) leaf3019InnerLog = true := by
  rfl'

private theorem leaf3019InnerLogValid :
    leaf3019InnerLog.Valid 8 (innerAD leaf3019Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3019CoverageChecked

private noncomputable def leaf3019InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814667/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3019InputLogOnePlusV_eq :
    leaf3019InputLogOnePlusV = outerEnclosure 24
      (leaf3019Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3019RoundedFacts : LeafRoundedFacts 8
    leaf3019Certificate.logOnePlusV leaf3019InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3019InputLogOnePlusV_eq }

private noncomputable def leaf3019Inputs : Inputs :=
  inputsOfCaches globalInput sk238RoundedInputs
    chi213InputQChi innerPair64Input
    leaf3019InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3019LowerChecked :
    lowerCheck 24 leaf3019Box leaf3019Inputs = true := by
  rfl'

private theorem leaf3019CoversExact : CoversExact 8
    leaf3019Box leaf3019Certificate leaf3019InnerLog leaf3019Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk238RoundedFacts chi213RoundedFacts
    innerPair64RoundedFacts leaf3019RoundedFacts (by rfl)

private theorem leaf3019FlatSound : Sound leaf3019Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3019CertificateValid
    leaf3019InnerLogValid leaf3019CoversExact leaf3019LowerChecked

private noncomputable def leaf3020Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (95/512), chiHi := (3/16) }

private noncomputable def leaf3020Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484347/2147483648) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432711168) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3722511803/2147483648) }, upper := { exponent := 0, mantissa := (893/512) } }, logOuter := sk238LogOuterCertificate, logK := sk238LogKCertificate, logChi := chi214LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869633023/274865422336) } }, logDArg := sk238LogDArgCertificate }

private noncomputable def leaf3020InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3020LocalValidity :
    LeafFacts leaf3020Box leaf3020Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3020Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432711168) }) = true
      norm_num [leaf3020Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3020CertificateValid :
    WideCertificateValid leaf3020Box leaf3020Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk238ValidityFacts chi214ValidityFacts
    leaf3020LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3020CoverageChecked :
    coverageCheck (innerAD leaf3020Box) leaf3020InnerLog = true := by
  rfl'

private theorem leaf3020InnerLogValid :
    leaf3020InnerLog.Valid 8 (innerAD leaf3020Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3020CoverageChecked

private noncomputable def leaf3020InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814669/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3020InputLogOnePlusV_eq :
    leaf3020InputLogOnePlusV = outerEnclosure 24
      (leaf3020Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3020RoundedFacts : LeafRoundedFacts 8
    leaf3020Certificate.logOnePlusV leaf3020InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3020InputLogOnePlusV_eq }

private noncomputable def leaf3020Inputs : Inputs :=
  inputsOfCaches globalInput sk238RoundedInputs
    chi214InputQChi innerPair64Input
    leaf3020InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3020LowerChecked :
    lowerCheck 24 leaf3020Box leaf3020Inputs = true := by
  rfl'

private theorem leaf3020CoversExact : CoversExact 8
    leaf3020Box leaf3020Certificate leaf3020InnerLog leaf3020Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk238RoundedFacts chi214RoundedFacts
    innerPair64RoundedFacts leaf3020RoundedFacts (by rfl)

private theorem leaf3020FlatSound : Sound leaf3020Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3020CertificateValid
    leaf3020InnerLogValid leaf3020CoversExact leaf3020LowerChecked

private noncomputable def leaf3021Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (23/128), chiHi := (93/512) }

private noncomputable def leaf3021Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484343/2147483648) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432882432) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3678801963/2147483648) }, upper := { exponent := 0, mantissa := (56483/32768) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi219LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869804287/274865764864) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf3021InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3021LocalValidity :
    LeafFacts leaf3021Box leaf3021Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3021Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432882432) }) = true
      norm_num [leaf3021Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3021CertificateValid :
    WideCertificateValid leaf3021Box leaf3021Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi219ValidityFacts
    leaf3021LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3021CoverageChecked :
    coverageCheck (innerAD leaf3021Box) leaf3021InnerLog = true := by
  rfl'

private theorem leaf3021InnerLogValid :
    leaf3021InnerLog.Valid 8 (innerAD leaf3021Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3021CoverageChecked

private noncomputable def leaf3021InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629327/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3021InputLogOnePlusV_eq :
    leaf3021InputLogOnePlusV = outerEnclosure 24
      (leaf3021Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3021RoundedFacts : LeafRoundedFacts 8
    leaf3021Certificate.logOnePlusV leaf3021InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3021InputLogOnePlusV_eq }

private noncomputable def leaf3021Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi219InputQChi innerPair64Input
    leaf3021InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3021LowerChecked :
    lowerCheck 24 leaf3021Box leaf3021Inputs = true := by
  rfl'

private theorem leaf3021CoversExact : CoversExact 8
    leaf3021Box leaf3021Certificate leaf3021InnerLog leaf3021Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi219RoundedFacts
    innerPair64RoundedFacts leaf3021RoundedFacts (by rfl)

private theorem leaf3021FlatSound : Sound leaf3021Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3021CertificateValid
    leaf3021InnerLogValid leaf3021CoversExact leaf3021LowerChecked

private noncomputable def leaf3022Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (93/512), chiHi := (47/256) }

private noncomputable def leaf3022Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484345/2147483648) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432817152) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3695447089/2147483648) }, upper := { exponent := 0, mantissa := (28369/16384) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi220LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869739007/274865634304) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf3022InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3022LocalValidity :
    LeafFacts leaf3022Box leaf3022Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3022Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432817152) }) = true
      norm_num [leaf3022Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3022CertificateValid :
    WideCertificateValid leaf3022Box leaf3022Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi220ValidityFacts
    leaf3022LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3022CoverageChecked :
    coverageCheck (innerAD leaf3022Box) leaf3022InnerLog = true := by
  rfl'

private theorem leaf3022InnerLogValid :
    leaf3022InnerLog.Valid 8 (innerAD leaf3022Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3022CoverageChecked

private noncomputable def leaf3022InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629331/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3022InputLogOnePlusV_eq :
    leaf3022InputLogOnePlusV = outerEnclosure 24
      (leaf3022Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3022RoundedFacts : LeafRoundedFacts 8
    leaf3022Certificate.logOnePlusV leaf3022InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3022InputLogOnePlusV_eq }

private noncomputable def leaf3022Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi220InputQChi innerPair64Input
    leaf3022InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3022LowerChecked :
    lowerCheck 24 leaf3022Box leaf3022Inputs = true := by
  rfl'

private theorem leaf3022CoversExact : CoversExact 8
    leaf3022Box leaf3022Certificate leaf3022InnerLog leaf3022Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi220RoundedFacts
    innerPair64RoundedFacts leaf3022RoundedFacts (by rfl)

private theorem leaf3022FlatSound : Sound leaf3022Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3022CertificateValid
    leaf3022InnerLogValid leaf3022CoversExact leaf3022LowerChecked

private noncomputable def leaf3023Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (23/128), chiHi := (93/512) }

private noncomputable def leaf3023Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484345/2147483648) }, vSqrt := { lower := (65527/65536), upper := (137436921855/137432858624) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3684830905/2147483648) }, upper := { exponent := 0, mantissa := (221/128) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi219LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (274869780479/274865717248) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf3023InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3023LocalValidity :
    LeafFacts leaf3023Box leaf3023Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3023Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (137436921855/137432858624) }) = true
      norm_num [leaf3023Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3023CertificateValid :
    WideCertificateValid leaf3023Box leaf3023Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi219ValidityFacts
    leaf3023LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3023CoverageChecked :
    coverageCheck (innerAD leaf3023Box) leaf3023InnerLog = true := by
  rfl'

private theorem leaf3023InnerLogValid :
    leaf3023InnerLog.Valid 8 (innerAD leaf3023Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3023CoverageChecked

private noncomputable def leaf3023InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629329/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3023InputLogOnePlusV_eq :
    leaf3023InputLogOnePlusV = outerEnclosure 24
      (leaf3023Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3023RoundedFacts : LeafRoundedFacts 8
    leaf3023Certificate.logOnePlusV leaf3023InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3023InputLogOnePlusV_eq }

private noncomputable def leaf3023Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi219InputQChi innerPair64Input
    leaf3023InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3023LowerChecked :
    lowerCheck 24 leaf3023Box leaf3023Inputs = true := by
  rfl'

private theorem leaf3023CoversExact : CoversExact 8
    leaf3023Box leaf3023Certificate leaf3023InnerLog leaf3023Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi219RoundedFacts
    innerPair64RoundedFacts leaf3023RoundedFacts (by rfl)

private theorem leaf3023FlatSound : Sound leaf3023Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3023CertificateValid
    leaf3023InnerLogValid leaf3023CoversExact leaf3023LowerChecked

private noncomputable def leaf3024Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (93/512), chiHi := (47/256) }

private noncomputable def leaf3024Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484347/2147483648) }, vSqrt := { lower := (65527/65536), upper := (137436921855/137432793088) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3701541563/2147483648) }, upper := { exponent := 0, mantissa := (111/64) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi220LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (274869714943/274865586176) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf3024InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3024LocalValidity :
    LeafFacts leaf3024Box leaf3024Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3024Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (137436921855/137432793088) }) = true
      norm_num [leaf3024Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3024CertificateValid :
    WideCertificateValid leaf3024Box leaf3024Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi220ValidityFacts
    leaf3024LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3024CoverageChecked :
    coverageCheck (innerAD leaf3024Box) leaf3024InnerLog = true := by
  rfl'

private theorem leaf3024InnerLogValid :
    leaf3024InnerLog.Valid 8 (innerAD leaf3024Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3024CoverageChecked

private noncomputable def leaf3024InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629333/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3024InputLogOnePlusV_eq :
    leaf3024InputLogOnePlusV = outerEnclosure 24
      (leaf3024Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3024RoundedFacts : LeafRoundedFacts 8
    leaf3024Certificate.logOnePlusV leaf3024InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3024InputLogOnePlusV_eq }

private noncomputable def leaf3024Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi220InputQChi innerPair64Input
    leaf3024InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3024LowerChecked :
    lowerCheck 24 leaf3024Box leaf3024Inputs = true := by
  rfl'

private theorem leaf3024CoversExact : CoversExact 8
    leaf3024Box leaf3024Certificate leaf3024InnerLog leaf3024Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi220RoundedFacts
    innerPair64RoundedFacts leaf3024RoundedFacts (by rfl)

private theorem leaf3024FlatSound : Sound leaf3024Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3024CertificateValid
    leaf3024InnerLogValid leaf3024CoversExact leaf3024LowerChecked

private noncomputable def leaf3025Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (47/256), chiHi := (95/512) }

private noncomputable def leaf3025Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484347/2147483648) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432751872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3712092215/2147483648) }, upper := { exponent := 0, mantissa := (56993/32768) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi213LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869673727/274865503744) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf3025InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3025LocalValidity :
    LeafFacts leaf3025Box leaf3025Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3025Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432751872) }) = true
      norm_num [leaf3025Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3025CertificateValid :
    WideCertificateValid leaf3025Box leaf3025Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi213ValidityFacts
    leaf3025LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3025CoverageChecked :
    coverageCheck (innerAD leaf3025Box) leaf3025InnerLog = true := by
  rfl'

private theorem leaf3025InnerLogValid :
    leaf3025InnerLog.Valid 8 (innerAD leaf3025Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3025CoverageChecked

private noncomputable def leaf3025InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629335/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3025InputLogOnePlusV_eq :
    leaf3025InputLogOnePlusV = outerEnclosure 24
      (leaf3025Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3025RoundedFacts : LeafRoundedFacts 8
    leaf3025Certificate.logOnePlusV leaf3025InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3025InputLogOnePlusV_eq }

private noncomputable def leaf3025Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi213InputQChi innerPair64Input
    leaf3025InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3025LowerChecked :
    lowerCheck 24 leaf3025Box leaf3025Inputs = true := by
  rfl'

private theorem leaf3025CoversExact : CoversExact 8
    leaf3025Box leaf3025Certificate leaf3025InnerLog leaf3025Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi213RoundedFacts
    innerPair64RoundedFacts leaf3025RoundedFacts (by rfl)

private theorem leaf3025FlatSound : Sound leaf3025Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3025CertificateValid
    leaf3025InnerLogValid leaf3025CoversExact leaf3025LowerChecked

private noncomputable def leaf3026Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (95/512), chiHi := (3/16) }

private noncomputable def leaf3026Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484349/2147483648) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432686592) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3728737341/2147483648) }, upper := { exponent := 0, mantissa := (1789/1024) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi214LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869608447/274865373184) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf3026InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3026LocalValidity :
    LeafFacts leaf3026Box leaf3026Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3026Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432686592) }) = true
      norm_num [leaf3026Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3026CertificateValid :
    WideCertificateValid leaf3026Box leaf3026Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi214ValidityFacts
    leaf3026LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3026CoverageChecked :
    coverageCheck (innerAD leaf3026Box) leaf3026InnerLog = true := by
  rfl'

private theorem leaf3026InnerLogValid :
    leaf3026InnerLog.Valid 8 (innerAD leaf3026Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3026CoverageChecked

private noncomputable def leaf3026InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629339/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3026InputLogOnePlusV_eq :
    leaf3026InputLogOnePlusV = outerEnclosure 24
      (leaf3026Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3026RoundedFacts : LeafRoundedFacts 8
    leaf3026Certificate.logOnePlusV leaf3026InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3026InputLogOnePlusV_eq }

private noncomputable def leaf3026Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi214InputQChi innerPair64Input
    leaf3026InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3026LowerChecked :
    lowerCheck 24 leaf3026Box leaf3026Inputs = true := by
  rfl'

private theorem leaf3026CoversExact : CoversExact 8
    leaf3026Box leaf3026Certificate leaf3026InnerLog leaf3026Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi214RoundedFacts
    innerPair64RoundedFacts leaf3026RoundedFacts (by rfl)

private theorem leaf3026FlatSound : Sound leaf3026Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3026CertificateValid
    leaf3026InnerLogValid leaf3026CoversExact leaf3026LowerChecked

private noncomputable def leaf3027Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (47/256), chiHi := (95/512) }

private noncomputable def leaf3027Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484349/2147483648) }, vSqrt := { lower := (65527/65536), upper := (45812307285/45810909184) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3718252221/2147483648) }, upper := { exponent := 0, mantissa := (223/128) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi213LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (91623216469/91621818368) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf3027InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3027LocalValidity :
    LeafFacts leaf3027Box leaf3027Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3027Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (45812307285/45810909184) }) = true
      norm_num [leaf3027Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3027CertificateValid :
    WideCertificateValid leaf3027Box leaf3027Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi213ValidityFacts
    leaf3027LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3027CoverageChecked :
    coverageCheck (innerAD leaf3027Box) leaf3027InnerLog = true := by
  rfl'

private theorem leaf3027InnerLogValid :
    leaf3027InnerLog.Valid 8 (innerAD leaf3027Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3027CoverageChecked

private noncomputable def leaf3027InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629337/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3027InputLogOnePlusV_eq :
    leaf3027InputLogOnePlusV = outerEnclosure 24
      (leaf3027Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3027RoundedFacts : LeafRoundedFacts 8
    leaf3027Certificate.logOnePlusV leaf3027InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3027InputLogOnePlusV_eq }

private noncomputable def leaf3027Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi213InputQChi innerPair64Input
    leaf3027InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3027LowerChecked :
    lowerCheck 24 leaf3027Box leaf3027Inputs = true := by
  rfl'

private theorem leaf3027CoversExact : CoversExact 8
    leaf3027Box leaf3027Certificate leaf3027InnerLog leaf3027Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi213RoundedFacts
    innerPair64RoundedFacts leaf3027RoundedFacts (by rfl)

private theorem leaf3027FlatSound : Sound leaf3027Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3027CertificateValid
    leaf3027InnerLogValid leaf3027CoversExact leaf3027LowerChecked

private noncomputable def leaf3028Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (95/512), chiHi := (3/16) }

private noncomputable def leaf3028Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484351/2147483648) }, vSqrt := { lower := (65527/65536), upper := (137436921855/137432662016) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3734962879/2147483648) }, upper := { exponent := 0, mantissa := (7/4) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi214LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (274869583871/274865324032) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf3028InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3028LocalValidity :
    LeafFacts leaf3028Box leaf3028Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3028Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (137436921855/137432662016) }) = true
      norm_num [leaf3028Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3028CertificateValid :
    WideCertificateValid leaf3028Box leaf3028Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi214ValidityFacts
    leaf3028LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3028CoverageChecked :
    coverageCheck (innerAD leaf3028Box) leaf3028InnerLog = true := by
  rfl'

private theorem leaf3028InnerLogValid :
    leaf3028InnerLog.Valid 8 (innerAD leaf3028Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3028CoverageChecked

private noncomputable def leaf3028InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629341/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3028InputLogOnePlusV_eq :
    leaf3028InputLogOnePlusV = outerEnclosure 24
      (leaf3028Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3028RoundedFacts : LeafRoundedFacts 8
    leaf3028Certificate.logOnePlusV leaf3028InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3028InputLogOnePlusV_eq }

private noncomputable def leaf3028Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi214InputQChi innerPair64Input
    leaf3028InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3028LowerChecked :
    lowerCheck 24 leaf3028Box leaf3028Inputs = true := by
  rfl'

private theorem leaf3028CoversExact : CoversExact 8
    leaf3028Box leaf3028Certificate leaf3028InnerLog leaf3028Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi214RoundedFacts
    innerPair64RoundedFacts leaf3028RoundedFacts (by rfl)

private theorem leaf3028FlatSound : Sound leaf3028Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3028CertificateValid
    leaf3028InnerLogValid leaf3028CoversExact leaf3028LowerChecked

private noncomputable def component63Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (11/64), chiHi := (45/256) }

set_option maxRecDepth 1000000 in
private theorem component63Node0_sound : Sound component63Node0Box :=
  sound_of_literal_split component63Node0Box leaf2981Box leaf2982Box
    .k (249/64) (by rfl) (by rfl)
    leaf2981FlatSound leaf2982FlatSound

private noncomputable def component63Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (45/256), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component63Node1_sound : Sound component63Node1Box :=
  sound_of_literal_split component63Node1Box leaf2983Box leaf2984Box
    .k (249/64) (by rfl) (by rfl)
    leaf2983FlatSound leaf2984FlatSound

private noncomputable def component63Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (11/64), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component63Node2_sound : Sound component63Node2Box :=
  sound_of_literal_split component63Node2Box component63Node0Box component63Node1Box
    .chi (45/256) (by rfl) (by rfl)
    component63Node0_sound component63Node1_sound

private noncomputable def component63Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (11/64), chiHi := (45/256) }

set_option maxRecDepth 1000000 in
private theorem component63Node3_sound : Sound component63Node3Box :=
  sound_of_literal_split component63Node3Box leaf2985Box leaf2986Box
    .k (251/64) (by rfl) (by rfl)
    leaf2985FlatSound leaf2986FlatSound

private noncomputable def component63Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (45/256), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component63Node4_sound : Sound component63Node4Box :=
  sound_of_literal_split component63Node4Box leaf2987Box leaf2988Box
    .k (251/64) (by rfl) (by rfl)
    leaf2987FlatSound leaf2988FlatSound

private noncomputable def component63Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (11/64), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component63Node5_sound : Sound component63Node5Box :=
  sound_of_literal_split component63Node5Box component63Node3Box component63Node4Box
    .chi (45/256) (by rfl) (by rfl)
    component63Node3_sound component63Node4_sound

private noncomputable def component63Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (11/64), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component63Node6_sound : Sound component63Node6Box :=
  sound_of_literal_split component63Node6Box component63Node2Box component63Node5Box
    .k (125/32) (by rfl) (by rfl)
    component63Node2_sound component63Node5_sound

private noncomputable def component63Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (23/128), chiHi := (47/256) }

set_option maxRecDepth 1000000 in
private theorem component63Node7_sound : Sound component63Node7Box :=
  sound_of_literal_split component63Node7Box leaf2989Box leaf2990Box
    .k (249/64) (by rfl) (by rfl)
    leaf2989FlatSound leaf2990FlatSound

private noncomputable def component63Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (47/256), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component63Node8_sound : Sound component63Node8Box :=
  sound_of_literal_split component63Node8Box leaf2991Box leaf2992Box
    .k (249/64) (by rfl) (by rfl)
    leaf2991FlatSound leaf2992FlatSound

private noncomputable def component63Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (23/128), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component63Node9_sound : Sound component63Node9Box :=
  sound_of_literal_split component63Node9Box component63Node7Box component63Node8Box
    .chi (47/256) (by rfl) (by rfl)
    component63Node7_sound component63Node8_sound

private noncomputable def component63Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (23/128), chiHi := (47/256) }

set_option maxRecDepth 1000000 in
private theorem component63Node10_sound : Sound component63Node10Box :=
  sound_of_literal_split component63Node10Box leaf2993Box leaf2994Box
    .k (251/64) (by rfl) (by rfl)
    leaf2993FlatSound leaf2994FlatSound

private noncomputable def component63Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (63/16), chiLo := (47/256), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component63Node11_sound : Sound component63Node11Box :=
  sound_of_literal_split component63Node11Box leaf2996Box leaf2997Box
    .chi (95/512) (by rfl) (by rfl)
    leaf2996FlatSound leaf2997FlatSound

private noncomputable def component63Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (47/256), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component63Node12_sound : Sound component63Node12Box :=
  sound_of_literal_split component63Node12Box leaf2995Box component63Node11Box
    .k (251/64) (by rfl) (by rfl)
    leaf2995FlatSound component63Node11_sound

private noncomputable def component63Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (23/128), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component63Node13_sound : Sound component63Node13Box :=
  sound_of_literal_split component63Node13Box component63Node10Box component63Node12Box
    .chi (47/256) (by rfl) (by rfl)
    component63Node10_sound component63Node12_sound

private noncomputable def component63Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (23/128), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component63Node14_sound : Sound component63Node14Box :=
  sound_of_literal_split component63Node14Box component63Node9Box component63Node13Box
    .k (125/32) (by rfl) (by rfl)
    component63Node9_sound component63Node13_sound

private noncomputable def component63Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (11/64), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component63Node15_sound : Sound component63Node15Box :=
  sound_of_literal_split component63Node15Box component63Node6Box component63Node14Box
    .chi (23/128) (by rfl) (by rfl)
    component63Node6_sound component63Node14_sound

private noncomputable def component63Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (11/64), chiHi := (45/256) }

set_option maxRecDepth 1000000 in
private theorem component63Node16_sound : Sound component63Node16Box :=
  sound_of_literal_split component63Node16Box leaf2999Box leaf3000Box
    .chi (89/512) (by rfl) (by rfl)
    leaf2999FlatSound leaf3000FlatSound

private noncomputable def component63Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (11/64), chiHi := (45/256) }

set_option maxRecDepth 1000000 in
private theorem component63Node17_sound : Sound component63Node17Box :=
  sound_of_literal_split component63Node17Box leaf2998Box component63Node16Box
    .k (253/64) (by rfl) (by rfl)
    leaf2998FlatSound component63Node16_sound

private noncomputable def component63Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (45/256), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component63Node18_sound : Sound component63Node18Box :=
  sound_of_literal_split component63Node18Box leaf3001Box leaf3002Box
    .chi (91/512) (by rfl) (by rfl)
    leaf3001FlatSound leaf3002FlatSound

private noncomputable def component63Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (45/256), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component63Node19_sound : Sound component63Node19Box :=
  sound_of_literal_split component63Node19Box leaf3003Box leaf3004Box
    .chi (91/512) (by rfl) (by rfl)
    leaf3003FlatSound leaf3004FlatSound

private noncomputable def component63Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (45/256), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component63Node20_sound : Sound component63Node20Box :=
  sound_of_literal_split component63Node20Box component63Node18Box component63Node19Box
    .k (253/64) (by rfl) (by rfl)
    component63Node18_sound component63Node19_sound

private noncomputable def component63Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (11/64), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component63Node21_sound : Sound component63Node21Box :=
  sound_of_literal_split component63Node21Box component63Node17Box component63Node20Box
    .chi (45/256) (by rfl) (by rfl)
    component63Node17_sound component63Node20_sound

private noncomputable def component63Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (11/64), chiHi := (45/256) }

set_option maxRecDepth 1000000 in
private theorem component63Node22_sound : Sound component63Node22Box :=
  sound_of_literal_split component63Node22Box leaf3005Box leaf3006Box
    .chi (89/512) (by rfl) (by rfl)
    leaf3005FlatSound leaf3006FlatSound

private noncomputable def component63Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (11/64), chiHi := (45/256) }

set_option maxRecDepth 1000000 in
private theorem component63Node23_sound : Sound component63Node23Box :=
  sound_of_literal_split component63Node23Box leaf3007Box leaf3008Box
    .chi (89/512) (by rfl) (by rfl)
    leaf3007FlatSound leaf3008FlatSound

private noncomputable def component63Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (11/64), chiHi := (45/256) }

set_option maxRecDepth 1000000 in
private theorem component63Node24_sound : Sound component63Node24Box :=
  sound_of_literal_split component63Node24Box component63Node22Box component63Node23Box
    .k (255/64) (by rfl) (by rfl)
    component63Node22_sound component63Node23_sound

private noncomputable def component63Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (45/256), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component63Node25_sound : Sound component63Node25Box :=
  sound_of_literal_split component63Node25Box leaf3009Box leaf3010Box
    .chi (91/512) (by rfl) (by rfl)
    leaf3009FlatSound leaf3010FlatSound

private noncomputable def component63Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (45/256), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component63Node26_sound : Sound component63Node26Box :=
  sound_of_literal_split component63Node26Box leaf3011Box leaf3012Box
    .chi (91/512) (by rfl) (by rfl)
    leaf3011FlatSound leaf3012FlatSound

private noncomputable def component63Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (45/256), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component63Node27_sound : Sound component63Node27Box :=
  sound_of_literal_split component63Node27Box component63Node25Box component63Node26Box
    .k (255/64) (by rfl) (by rfl)
    component63Node25_sound component63Node26_sound

private noncomputable def component63Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (11/64), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component63Node28_sound : Sound component63Node28Box :=
  sound_of_literal_split component63Node28Box component63Node24Box component63Node27Box
    .chi (45/256) (by rfl) (by rfl)
    component63Node24_sound component63Node27_sound

private noncomputable def component63Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (11/64), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component63Node29_sound : Sound component63Node29Box :=
  sound_of_literal_split component63Node29Box component63Node21Box component63Node28Box
    .k (127/32) (by rfl) (by rfl)
    component63Node21_sound component63Node28_sound

private noncomputable def component63Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (23/128), chiHi := (47/256) }

set_option maxRecDepth 1000000 in
private theorem component63Node30_sound : Sound component63Node30Box :=
  sound_of_literal_split component63Node30Box leaf3013Box leaf3014Box
    .chi (93/512) (by rfl) (by rfl)
    leaf3013FlatSound leaf3014FlatSound

private noncomputable def component63Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (23/128), chiHi := (47/256) }

set_option maxRecDepth 1000000 in
private theorem component63Node31_sound : Sound component63Node31Box :=
  sound_of_literal_split component63Node31Box leaf3015Box leaf3016Box
    .chi (93/512) (by rfl) (by rfl)
    leaf3015FlatSound leaf3016FlatSound

private noncomputable def component63Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (23/128), chiHi := (47/256) }

set_option maxRecDepth 1000000 in
private theorem component63Node32_sound : Sound component63Node32Box :=
  sound_of_literal_split component63Node32Box component63Node30Box component63Node31Box
    .k (253/64) (by rfl) (by rfl)
    component63Node30_sound component63Node31_sound

private noncomputable def component63Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (47/256), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component63Node33_sound : Sound component63Node33Box :=
  sound_of_literal_split component63Node33Box leaf3017Box leaf3018Box
    .chi (95/512) (by rfl) (by rfl)
    leaf3017FlatSound leaf3018FlatSound

private noncomputable def component63Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (47/256), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component63Node34_sound : Sound component63Node34Box :=
  sound_of_literal_split component63Node34Box leaf3019Box leaf3020Box
    .chi (95/512) (by rfl) (by rfl)
    leaf3019FlatSound leaf3020FlatSound

private noncomputable def component63Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (47/256), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component63Node35_sound : Sound component63Node35Box :=
  sound_of_literal_split component63Node35Box component63Node33Box component63Node34Box
    .k (253/64) (by rfl) (by rfl)
    component63Node33_sound component63Node34_sound

private noncomputable def component63Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (23/128), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component63Node36_sound : Sound component63Node36Box :=
  sound_of_literal_split component63Node36Box component63Node32Box component63Node35Box
    .chi (47/256) (by rfl) (by rfl)
    component63Node32_sound component63Node35_sound

private noncomputable def component63Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (23/128), chiHi := (47/256) }

set_option maxRecDepth 1000000 in
private theorem component63Node37_sound : Sound component63Node37Box :=
  sound_of_literal_split component63Node37Box leaf3021Box leaf3022Box
    .chi (93/512) (by rfl) (by rfl)
    leaf3021FlatSound leaf3022FlatSound

private noncomputable def component63Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (23/128), chiHi := (47/256) }

set_option maxRecDepth 1000000 in
private theorem component63Node38_sound : Sound component63Node38Box :=
  sound_of_literal_split component63Node38Box leaf3023Box leaf3024Box
    .chi (93/512) (by rfl) (by rfl)
    leaf3023FlatSound leaf3024FlatSound

private noncomputable def component63Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (23/128), chiHi := (47/256) }

set_option maxRecDepth 1000000 in
private theorem component63Node39_sound : Sound component63Node39Box :=
  sound_of_literal_split component63Node39Box component63Node37Box component63Node38Box
    .k (255/64) (by rfl) (by rfl)
    component63Node37_sound component63Node38_sound

private noncomputable def component63Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (47/256), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component63Node40_sound : Sound component63Node40Box :=
  sound_of_literal_split component63Node40Box leaf3025Box leaf3026Box
    .chi (95/512) (by rfl) (by rfl)
    leaf3025FlatSound leaf3026FlatSound

private noncomputable def component63Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (47/256), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component63Node41_sound : Sound component63Node41Box :=
  sound_of_literal_split component63Node41Box leaf3027Box leaf3028Box
    .chi (95/512) (by rfl) (by rfl)
    leaf3027FlatSound leaf3028FlatSound

private noncomputable def component63Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (47/256), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component63Node42_sound : Sound component63Node42Box :=
  sound_of_literal_split component63Node42Box component63Node40Box component63Node41Box
    .k (255/64) (by rfl) (by rfl)
    component63Node40_sound component63Node41_sound

private noncomputable def component63Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (23/128), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component63Node43_sound : Sound component63Node43Box :=
  sound_of_literal_split component63Node43Box component63Node39Box component63Node42Box
    .chi (47/256) (by rfl) (by rfl)
    component63Node39_sound component63Node42_sound

private noncomputable def component63Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (23/128), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component63Node44_sound : Sound component63Node44Box :=
  sound_of_literal_split component63Node44Box component63Node36Box component63Node43Box
    .k (127/32) (by rfl) (by rfl)
    component63Node36_sound component63Node43_sound

private noncomputable def component63Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (11/64), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component63Node45_sound : Sound component63Node45Box :=
  sound_of_literal_split component63Node45Box component63Node29Box component63Node44Box
    .chi (23/128) (by rfl) (by rfl)
    component63Node29_sound component63Node44_sound

noncomputable def component63Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (11/64), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
theorem component63_sound : Sound component63Box :=
  sound_of_literal_split component63Box component63Node15Box component63Node45Box
    .k (63/16) (by rfl) (by rfl)
    component63Node15_sound component63Node45_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
