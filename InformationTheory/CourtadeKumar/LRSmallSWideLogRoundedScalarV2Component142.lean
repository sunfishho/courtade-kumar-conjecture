import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch5
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch7
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch8
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch11
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch12
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch13
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

private noncomputable def leaf6976Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (5/8), chiHi := (81/128) }

private noncomputable def leaf6976Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218003/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588752640) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (427768047/268435456) }, upper := { exponent := 1, mantissa := (6665/4096) } }, logOuter := sk151LogOuterCertificate, logK := sk151LogKCertificate, logChi := chi349LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178179327/17177505280) } }, logDArg := sk151LogDArgCertificate }

private noncomputable def leaf6976InnerLog : WideLogData :=
  innerPair750Data

set_option maxRecDepth 1000000 in
private theorem leaf6976LocalValidity :
    LeafFacts leaf6976Box leaf6976Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6976Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588752640) }) = true
      norm_num [leaf6976Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6976CertificateValid :
    WideCertificateValid leaf6976Box leaf6976Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk151ValidityFacts chi349ValidityFacts
    leaf6976LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6976CoverageChecked :
    coverageCheck (innerAD leaf6976Box) leaf6976InnerLog = true := by
  rfl'

private theorem leaf6976InnerLogValid :
    leaf6976InnerLog.Valid 8 (innerAD leaf6976Box) :=
  wideLogDataValid_of_cachedCheck endpoint483PositiveFacts
    endpoint486PositiveFacts.valid leaf6976CoverageChecked

private noncomputable def leaf6976InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629739/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6976InputLogOnePlusV_eq :
    leaf6976InputLogOnePlusV = outerEnclosure 24
      (leaf6976Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6976RoundedFacts : LeafRoundedFacts 8
    leaf6976Certificate.logOnePlusV leaf6976InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6976InputLogOnePlusV_eq }

private noncomputable def leaf6976Inputs : Inputs :=
  inputsOfCaches globalInput sk151RoundedInputs
    chi349InputQChi innerPair750Input
    leaf6976InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6976LowerChecked :
    lowerCheck 24 leaf6976Box leaf6976Inputs = true := by
  rfl'

private theorem leaf6976CoversExact : CoversExact 8
    leaf6976Box leaf6976Certificate leaf6976InnerLog leaf6976Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk151RoundedFacts chi349RoundedFacts
    innerPair750RoundedFacts leaf6976RoundedFacts (by rfl)

private theorem leaf6976FlatSound : Sound leaf6976Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6976CertificateValid
    leaf6976InnerLogValid leaf6976CoversExact leaf6976LowerChecked

private noncomputable def leaf6977Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (81/128), chiHi := (41/64) }

private noncomputable def leaf6977Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218005/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588738048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (431437837/268435456) }, upper := { exponent := 1, mantissa := (3361/2048) } }, logOuter := sk151LogOuterCertificate, logK := sk151LogKCertificate, logChi := chi350LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178164735/17177476096) } }, logDArg := sk151LogDArgCertificate }

private noncomputable def leaf6977InnerLog : WideLogData :=
  innerPair755Data

set_option maxRecDepth 1000000 in
private theorem leaf6977LocalValidity :
    LeafFacts leaf6977Box leaf6977Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6977Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588738048) }) = true
      norm_num [leaf6977Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6977CertificateValid :
    WideCertificateValid leaf6977Box leaf6977Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk151ValidityFacts chi350ValidityFacts
    leaf6977LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6977CoverageChecked :
    coverageCheck (innerAD leaf6977Box) leaf6977InnerLog = true := by
  rfl'

private theorem leaf6977InnerLogValid :
    leaf6977InnerLog.Valid 8 (innerAD leaf6977Box) :=
  wideLogDataValid_of_cachedCheck endpoint484PositiveFacts
    endpoint486PositiveFacts.valid leaf6977CoverageChecked

private noncomputable def leaf6977InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629753/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6977InputLogOnePlusV_eq :
    leaf6977InputLogOnePlusV = outerEnclosure 24
      (leaf6977Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6977RoundedFacts : LeafRoundedFacts 8
    leaf6977Certificate.logOnePlusV leaf6977InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6977InputLogOnePlusV_eq }

private noncomputable def leaf6977Inputs : Inputs :=
  inputsOfCaches globalInput sk151RoundedInputs
    chi350InputQChi innerPair755Input
    leaf6977InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6977LowerChecked :
    lowerCheck 24 leaf6977Box leaf6977Inputs = true := by
  rfl'

private theorem leaf6977CoversExact : CoversExact 8
    leaf6977Box leaf6977Certificate leaf6977InnerLog leaf6977Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk151RoundedFacts chi350RoundedFacts
    innerPair755RoundedFacts leaf6977RoundedFacts (by rfl)

private theorem leaf6977FlatSound : Sound leaf6977Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6977CertificateValid
    leaf6977InnerLogValid leaf6977CoversExact leaf6977LowerChecked

private noncomputable def leaf6978Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (5/8), chiHi := (81/128) }

private noncomputable def leaf6978Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218005/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588731904) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (433010605/268435456) }, upper := { exponent := 1, mantissa := (3373/2048) } }, logOuter := sk152LogOuterCertificate, logK := sk152LogKCertificate, logChi := chi349LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178158591/17177463808) } }, logDArg := sk152LogDArgCertificate }

private noncomputable def leaf6978InnerLog : WideLogData :=
  innerPair755Data

set_option maxRecDepth 1000000 in
private theorem leaf6978LocalValidity :
    LeafFacts leaf6978Box leaf6978Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6978Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588731904) }) = true
      norm_num [leaf6978Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6978CertificateValid :
    WideCertificateValid leaf6978Box leaf6978Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk152ValidityFacts chi349ValidityFacts
    leaf6978LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6978CoverageChecked :
    coverageCheck (innerAD leaf6978Box) leaf6978InnerLog = true := by
  rfl'

private theorem leaf6978InnerLogValid :
    leaf6978InnerLog.Valid 8 (innerAD leaf6978Box) :=
  wideLogDataValid_of_cachedCheck endpoint484PositiveFacts
    endpoint486PositiveFacts.valid leaf6978CoverageChecked

private noncomputable def leaf6978InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629759/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6978InputLogOnePlusV_eq :
    leaf6978InputLogOnePlusV = outerEnclosure 24
      (leaf6978Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6978RoundedFacts : LeafRoundedFacts 8
    leaf6978Certificate.logOnePlusV leaf6978InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6978InputLogOnePlusV_eq }

private noncomputable def leaf6978Inputs : Inputs :=
  inputsOfCaches globalInput sk152RoundedInputs
    chi349InputQChi innerPair755Input
    leaf6978InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6978LowerChecked :
    lowerCheck 24 leaf6978Box leaf6978Inputs = true := by
  rfl'

private theorem leaf6978CoversExact : CoversExact 8
    leaf6978Box leaf6978Certificate leaf6978InnerLog leaf6978Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk152RoundedFacts chi349RoundedFacts
    innerPair755RoundedFacts leaf6978RoundedFacts (by rfl)

private theorem leaf6978FlatSound : Sound leaf6978Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6978CertificateValid
    leaf6978InnerLogValid leaf6978CoversExact leaf6978LowerChecked

private noncomputable def leaf6979Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (81/128), chiHi := (41/64) }

private noncomputable def leaf6979Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218007/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588717056) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (436745927/268435456) }, upper := { exponent := 1, mantissa := (1701/1024) } }, logOuter := sk152LogOuterCertificate, logK := sk152LogKCertificate, logChi := chi350LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178143743/17177434112) } }, logDArg := sk152LogDArgCertificate }

private noncomputable def leaf6979InnerLog : WideLogData :=
  innerPair761Data

set_option maxRecDepth 1000000 in
private theorem leaf6979LocalValidity :
    LeafFacts leaf6979Box leaf6979Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6979Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588717056) }) = true
      norm_num [leaf6979Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6979CertificateValid :
    WideCertificateValid leaf6979Box leaf6979Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk152ValidityFacts chi350ValidityFacts
    leaf6979LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6979CoverageChecked :
    coverageCheck (innerAD leaf6979Box) leaf6979InnerLog = true := by
  rfl'

private theorem leaf6979InnerLogValid :
    leaf6979InnerLog.Valid 8 (innerAD leaf6979Box) :=
  wideLogDataValid_of_cachedCheck endpoint485PositiveFacts
    endpoint487PositiveFacts.valid leaf6979CoverageChecked

private noncomputable def leaf6979InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814887/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6979InputLogOnePlusV_eq :
    leaf6979InputLogOnePlusV = outerEnclosure 24
      (leaf6979Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6979RoundedFacts : LeafRoundedFacts 8
    leaf6979Certificate.logOnePlusV leaf6979InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6979InputLogOnePlusV_eq }

private noncomputable def leaf6979Inputs : Inputs :=
  inputsOfCaches globalInput sk152RoundedInputs
    chi350InputQChi innerPair761Input
    leaf6979InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6979LowerChecked :
    lowerCheck 24 leaf6979Box leaf6979Inputs = true := by
  rfl'

private theorem leaf6979CoversExact : CoversExact 8
    leaf6979Box leaf6979Certificate leaf6979InnerLog leaf6979Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk152RoundedFacts chi350RoundedFacts
    innerPair761RoundedFacts leaf6979RoundedFacts (by rfl)

private theorem leaf6979FlatSound : Sound leaf6979Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6979CertificateValid
    leaf6979InnerLogValid leaf6979CoversExact leaf6979LowerChecked

private noncomputable def leaf6980Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (41/64), chiHi := (83/128) }

private noncomputable def leaf6980Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218007/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588723456) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (435107627/268435456) }, upper := { exponent := 1, mantissa := (6779/4096) } }, logOuter := sk151LogOuterCertificate, logK := sk151LogKCertificate, logChi := chi351LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178150143/17177446912) } }, logDArg := sk151LogDArgCertificate }

private noncomputable def leaf6980InnerLog : WideLogData :=
  innerPair755Data

set_option maxRecDepth 1000000 in
private theorem leaf6980LocalValidity :
    LeafFacts leaf6980Box leaf6980Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6980Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588723456) }) = true
      norm_num [leaf6980Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6980CertificateValid :
    WideCertificateValid leaf6980Box leaf6980Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk151ValidityFacts chi351ValidityFacts
    leaf6980LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6980CoverageChecked :
    coverageCheck (innerAD leaf6980Box) leaf6980InnerLog = true := by
  rfl'

private theorem leaf6980InnerLogValid :
    leaf6980InnerLog.Valid 8 (innerAD leaf6980Box) :=
  wideLogDataValid_of_cachedCheck endpoint484PositiveFacts
    endpoint486PositiveFacts.valid leaf6980CoverageChecked

private noncomputable def leaf6980InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453721/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf6980InputLogOnePlusV_eq :
    leaf6980InputLogOnePlusV = outerEnclosure 24
      (leaf6980Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6980RoundedFacts : LeafRoundedFacts 8
    leaf6980Certificate.logOnePlusV leaf6980InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6980InputLogOnePlusV_eq }

private noncomputable def leaf6980Inputs : Inputs :=
  inputsOfCaches globalInput sk151RoundedInputs
    chi351InputQChi innerPair755Input
    leaf6980InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6980LowerChecked :
    lowerCheck 24 leaf6980Box leaf6980Inputs = true := by
  rfl'

private theorem leaf6980CoversExact : CoversExact 8
    leaf6980Box leaf6980Certificate leaf6980InnerLog leaf6980Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk151RoundedFacts chi351RoundedFacts
    innerPair755RoundedFacts leaf6980RoundedFacts (by rfl)

private theorem leaf6980FlatSound : Sound leaf6980Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6980CertificateValid
    leaf6980InnerLogValid leaf6980CoversExact leaf6980LowerChecked

private noncomputable def leaf6981Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (83/128), chiHi := (21/32) }

private noncomputable def leaf6981Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218009/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588708864) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (438777417/268435456) }, upper := { exponent := 1, mantissa := (1709/1024) } }, logOuter := sk151LogOuterCertificate, logK := sk151LogKCertificate, logChi := chi352LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178135551/17177417728) } }, logDArg := sk151LogDArgCertificate }

private noncomputable def leaf6981InnerLog : WideLogData :=
  innerPair761Data

set_option maxRecDepth 1000000 in
private theorem leaf6981LocalValidity :
    LeafFacts leaf6981Box leaf6981Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6981Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588708864) }) = true
      norm_num [leaf6981Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6981CertificateValid :
    WideCertificateValid leaf6981Box leaf6981Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk151ValidityFacts chi352ValidityFacts
    leaf6981LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6981CoverageChecked :
    coverageCheck (innerAD leaf6981Box) leaf6981InnerLog = true := by
  rfl'

private theorem leaf6981InnerLogValid :
    leaf6981InnerLog.Valid 8 (innerAD leaf6981Box) :=
  wideLogDataValid_of_cachedCheck endpoint485PositiveFacts
    endpoint487PositiveFacts.valid leaf6981CoverageChecked

private noncomputable def leaf6981InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814891/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6981InputLogOnePlusV_eq :
    leaf6981InputLogOnePlusV = outerEnclosure 24
      (leaf6981Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6981RoundedFacts : LeafRoundedFacts 8
    leaf6981Certificate.logOnePlusV leaf6981InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6981InputLogOnePlusV_eq }

private noncomputable def leaf6981Inputs : Inputs :=
  inputsOfCaches globalInput sk151RoundedInputs
    chi352InputQChi innerPair761Input
    leaf6981InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6981LowerChecked :
    lowerCheck 24 leaf6981Box leaf6981Inputs = true := by
  rfl'

private theorem leaf6981CoversExact : CoversExact 8
    leaf6981Box leaf6981Certificate leaf6981InnerLog leaf6981Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk151RoundedFacts chi352RoundedFacts
    innerPair761RoundedFacts leaf6981RoundedFacts (by rfl)

private theorem leaf6981FlatSound : Sound leaf6981Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6981CertificateValid
    leaf6981InnerLogValid leaf6981CoversExact leaf6981LowerChecked

private noncomputable def leaf6982Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (41/64), chiHi := (83/128) }

private noncomputable def leaf6982Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218009/134217728) }, vSqrt := { lower := (8191/8192), upper := (2863142229/2862900736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (440481249/268435456) }, upper := { exponent := 1, mantissa := (3431/2048) } }, logOuter := sk152LogOuterCertificate, logK := sk152LogKCertificate, logChi := chi351LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (5726042965/5725801472) } }, logDArg := sk152LogDArgCertificate }

private noncomputable def leaf6982InnerLog : WideLogData :=
  innerPair761Data

set_option maxRecDepth 1000000 in
private theorem leaf6982LocalValidity :
    LeafFacts leaf6982Box leaf6982Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6982Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (2863142229/2862900736) }) = true
      norm_num [leaf6982Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6982CertificateValid :
    WideCertificateValid leaf6982Box leaf6982Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk152ValidityFacts chi351ValidityFacts
    leaf6982LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6982CoverageChecked :
    coverageCheck (innerAD leaf6982Box) leaf6982InnerLog = true := by
  rfl'

private theorem leaf6982InnerLogValid :
    leaf6982InnerLog.Valid 8 (innerAD leaf6982Box) :=
  wideLogDataValid_of_cachedCheck endpoint485PositiveFacts
    endpoint487PositiveFacts.valid leaf6982CoverageChecked

private noncomputable def leaf6982InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907447/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6982InputLogOnePlusV_eq :
    leaf6982InputLogOnePlusV = outerEnclosure 24
      (leaf6982Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6982RoundedFacts : LeafRoundedFacts 8
    leaf6982Certificate.logOnePlusV leaf6982InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6982InputLogOnePlusV_eq }

private noncomputable def leaf6982Inputs : Inputs :=
  inputsOfCaches globalInput sk152RoundedInputs
    chi351InputQChi innerPair761Input
    leaf6982InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6982LowerChecked :
    lowerCheck 24 leaf6982Box leaf6982Inputs = true := by
  rfl'

private theorem leaf6982CoversExact : CoversExact 8
    leaf6982Box leaf6982Certificate leaf6982InnerLog leaf6982Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk152RoundedFacts chi351RoundedFacts
    innerPair761RoundedFacts leaf6982RoundedFacts (by rfl)

private theorem leaf6982FlatSound : Sound leaf6982Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6982CertificateValid
    leaf6982InnerLogValid leaf6982CoversExact leaf6982LowerChecked

private noncomputable def leaf6983Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (83/128), chiHi := (21/32) }

private noncomputable def leaf6983Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218011/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588687360) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (444216571/268435456) }, upper := { exponent := 1, mantissa := (865/512) } }, logOuter := sk152LogOuterCertificate, logK := sk152LogKCertificate, logChi := chi352LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178114047/17177374720) } }, logDArg := sk152LogDArgCertificate }

private noncomputable def leaf6983InnerLog : WideLogData :=
  innerPair762Data

set_option maxRecDepth 1000000 in
private theorem leaf6983LocalValidity :
    LeafFacts leaf6983Box leaf6983Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6983Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588687360) }) = true
      norm_num [leaf6983Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6983CertificateValid :
    WideCertificateValid leaf6983Box leaf6983Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk152ValidityFacts chi352ValidityFacts
    leaf6983LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6983CoverageChecked :
    coverageCheck (innerAD leaf6983Box) leaf6983InnerLog = true := by
  rfl'

private theorem leaf6983InnerLogValid :
    leaf6983InnerLog.Valid 8 (innerAD leaf6983Box) :=
  wideLogDataValid_of_cachedCheck endpoint485PositiveFacts
    endpoint488PositiveFacts.valid leaf6983CoverageChecked

private noncomputable def leaf6983InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629803/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6983InputLogOnePlusV_eq :
    leaf6983InputLogOnePlusV = outerEnclosure 24
      (leaf6983Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6983RoundedFacts : LeafRoundedFacts 8
    leaf6983Certificate.logOnePlusV leaf6983InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6983InputLogOnePlusV_eq }

private noncomputable def leaf6983Inputs : Inputs :=
  inputsOfCaches globalInput sk152RoundedInputs
    chi352InputQChi innerPair762Input
    leaf6983InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6983LowerChecked :
    lowerCheck 24 leaf6983Box leaf6983Inputs = true := by
  rfl'

private theorem leaf6983CoversExact : CoversExact 8
    leaf6983Box leaf6983Certificate leaf6983InnerLog leaf6983Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk152RoundedFacts chi352RoundedFacts
    innerPair762RoundedFacts leaf6983RoundedFacts (by rfl)

private theorem leaf6983FlatSound : Sound leaf6983Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6983CertificateValid
    leaf6983InnerLogValid leaf6983CoversExact leaf6983LowerChecked

private noncomputable def leaf6984Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (21/32), chiHi := (85/128) }

private noncomputable def leaf6984Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218011/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588694272) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (442447207/268435456) }, upper := { exponent := 1, mantissa := (6893/4096) } }, logOuter := sk151LogOuterCertificate, logK := sk151LogKCertificate, logChi := chi353LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178120959/17177388544) } }, logDArg := sk151LogDArgCertificate }

private noncomputable def leaf6984InnerLog : WideLogData :=
  innerPair761Data

set_option maxRecDepth 1000000 in
private theorem leaf6984LocalValidity :
    LeafFacts leaf6984Box leaf6984Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6984Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588694272) }) = true
      norm_num [leaf6984Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6984CertificateValid :
    WideCertificateValid leaf6984Box leaf6984Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk151ValidityFacts chi353ValidityFacts
    leaf6984LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6984CoverageChecked :
    coverageCheck (innerAD leaf6984Box) leaf6984InnerLog = true := by
  rfl'

private theorem leaf6984InnerLogValid :
    leaf6984InnerLog.Valid 8 (innerAD leaf6984Box) :=
  wideLogDataValid_of_cachedCheck endpoint485PositiveFacts
    endpoint487PositiveFacts.valid leaf6984CoverageChecked

private noncomputable def leaf6984InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907449/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6984InputLogOnePlusV_eq :
    leaf6984InputLogOnePlusV = outerEnclosure 24
      (leaf6984Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6984RoundedFacts : LeafRoundedFacts 8
    leaf6984Certificate.logOnePlusV leaf6984InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6984InputLogOnePlusV_eq }

private noncomputable def leaf6984Inputs : Inputs :=
  inputsOfCaches globalInput sk151RoundedInputs
    chi353InputQChi innerPair761Input
    leaf6984InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6984LowerChecked :
    lowerCheck 24 leaf6984Box leaf6984Inputs = true := by
  rfl'

private theorem leaf6984CoversExact : CoversExact 8
    leaf6984Box leaf6984Certificate leaf6984InnerLog leaf6984Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk151RoundedFacts chi353RoundedFacts
    innerPair761RoundedFacts leaf6984RoundedFacts (by rfl)

private theorem leaf6984FlatSound : Sound leaf6984Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6984CertificateValid
    leaf6984InnerLogValid leaf6984CoversExact leaf6984LowerChecked

private noncomputable def leaf6985Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (85/128), chiHi := (43/64) }

private noncomputable def leaf6985Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218013/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588679680) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (446116997/268435456) }, upper := { exponent := 1, mantissa := (3475/2048) } }, logOuter := sk151LogOuterCertificate, logK := sk151LogKCertificate, logChi := chi354LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178106367/17177359360) } }, logDArg := sk151LogDArgCertificate }

private noncomputable def leaf6985InnerLog : WideLogData :=
  innerPair765Data

set_option maxRecDepth 1000000 in
private theorem leaf6985LocalValidity :
    LeafFacts leaf6985Box leaf6985Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6985Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588679680) }) = true
      norm_num [leaf6985Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6985CertificateValid :
    WideCertificateValid leaf6985Box leaf6985Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk151ValidityFacts chi354ValidityFacts
    leaf6985LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6985CoverageChecked :
    coverageCheck (innerAD leaf6985Box) leaf6985InnerLog = true := by
  rfl'

private theorem leaf6985InnerLogValid :
    leaf6985InnerLog.Valid 8 (innerAD leaf6985Box) :=
  wideLogDataValid_of_cachedCheck endpoint486PositiveFacts
    endpoint488PositiveFacts.valid leaf6985CoverageChecked

private noncomputable def leaf6985InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814905/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6985InputLogOnePlusV_eq :
    leaf6985InputLogOnePlusV = outerEnclosure 24
      (leaf6985Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6985RoundedFacts : LeafRoundedFacts 8
    leaf6985Certificate.logOnePlusV leaf6985InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6985InputLogOnePlusV_eq }

private noncomputable def leaf6985Inputs : Inputs :=
  inputsOfCaches globalInput sk151RoundedInputs
    chi354InputQChi innerPair765Input
    leaf6985InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6985LowerChecked :
    lowerCheck 24 leaf6985Box leaf6985Inputs = true := by
  rfl'

private theorem leaf6985CoversExact : CoversExact 8
    leaf6985Box leaf6985Certificate leaf6985InnerLog leaf6985Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk151RoundedFacts chi354RoundedFacts
    innerPair765RoundedFacts leaf6985RoundedFacts (by rfl)

private theorem leaf6985FlatSound : Sound leaf6985Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6985CertificateValid
    leaf6985InnerLogValid leaf6985CoversExact leaf6985LowerChecked

private noncomputable def leaf6986Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (21/32), chiHi := (85/128) }

private noncomputable def leaf6986Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218013/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588672512) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (447951893/268435456) }, upper := { exponent := 1, mantissa := (3489/2048) } }, logOuter := sk152LogOuterCertificate, logK := sk152LogKCertificate, logChi := chi353LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178099199/17177345024) } }, logDArg := sk152LogDArgCertificate }

private noncomputable def leaf6986InnerLog : WideLogData :=
  innerPair765Data

set_option maxRecDepth 1000000 in
private theorem leaf6986LocalValidity :
    LeafFacts leaf6986Box leaf6986Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6986Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588672512) }) = true
      norm_num [leaf6986Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6986CertificateValid :
    WideCertificateValid leaf6986Box leaf6986Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk152ValidityFacts chi353ValidityFacts
    leaf6986LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6986CoverageChecked :
    coverageCheck (innerAD leaf6986Box) leaf6986InnerLog = true := by
  rfl'

private theorem leaf6986InnerLogValid :
    leaf6986InnerLog.Valid 8 (innerAD leaf6986Box) :=
  wideLogDataValid_of_cachedCheck endpoint486PositiveFacts
    endpoint488PositiveFacts.valid leaf6986CoverageChecked

private noncomputable def leaf6986InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629817/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6986InputLogOnePlusV_eq :
    leaf6986InputLogOnePlusV = outerEnclosure 24
      (leaf6986Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6986RoundedFacts : LeafRoundedFacts 8
    leaf6986Certificate.logOnePlusV leaf6986InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6986InputLogOnePlusV_eq }

private noncomputable def leaf6986Inputs : Inputs :=
  inputsOfCaches globalInput sk152RoundedInputs
    chi353InputQChi innerPair765Input
    leaf6986InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6986LowerChecked :
    lowerCheck 24 leaf6986Box leaf6986Inputs = true := by
  rfl'

private theorem leaf6986CoversExact : CoversExact 8
    leaf6986Box leaf6986Certificate leaf6986InnerLog leaf6986Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk152RoundedFacts chi353RoundedFacts
    innerPair765RoundedFacts leaf6986RoundedFacts (by rfl)

private theorem leaf6986FlatSound : Sound leaf6986Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6986CertificateValid
    leaf6986InnerLogValid leaf6986CoversExact leaf6986LowerChecked

private noncomputable def leaf6987Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (85/128), chiHi := (43/64) }

private noncomputable def leaf6987Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218015/134217728) }, vSqrt := { lower := (8191/8192), upper := (954380743/954295296) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (451687215/268435456) }, upper := { exponent := 1, mantissa := (1759/1024) } }, logOuter := sk152LogOuterCertificate, logK := sk152LogKCertificate, logChi := chi354LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (1908676039/1908590592) } }, logDArg := sk152LogDArgCertificate }

private noncomputable def leaf6987InnerLog : WideLogData :=
  innerPair765Data

set_option maxRecDepth 1000000 in
private theorem leaf6987LocalValidity :
    LeafFacts leaf6987Box leaf6987Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6987Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (954380743/954295296) }) = true
      norm_num [leaf6987Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6987CertificateValid :
    WideCertificateValid leaf6987Box leaf6987Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk152ValidityFacts chi354ValidityFacts
    leaf6987LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6987CoverageChecked :
    coverageCheck (innerAD leaf6987Box) leaf6987InnerLog = true := by
  rfl'

private theorem leaf6987InnerLogValid :
    leaf6987InnerLog.Valid 8 (innerAD leaf6987Box) :=
  wideLogDataValid_of_cachedCheck endpoint486PositiveFacts
    endpoint488PositiveFacts.valid leaf6987CoverageChecked

private noncomputable def leaf6987InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453729/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf6987InputLogOnePlusV_eq :
    leaf6987InputLogOnePlusV = outerEnclosure 24
      (leaf6987Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6987RoundedFacts : LeafRoundedFacts 8
    leaf6987Certificate.logOnePlusV leaf6987InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6987InputLogOnePlusV_eq }

private noncomputable def leaf6987Inputs : Inputs :=
  inputsOfCaches globalInput sk152RoundedInputs
    chi354InputQChi innerPair765Input
    leaf6987InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6987LowerChecked :
    lowerCheck 24 leaf6987Box leaf6987Inputs = true := by
  rfl'

private theorem leaf6987CoversExact : CoversExact 8
    leaf6987Box leaf6987Certificate leaf6987InnerLog leaf6987Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk152RoundedFacts chi354RoundedFacts
    innerPair765RoundedFacts leaf6987RoundedFacts (by rfl)

private theorem leaf6987FlatSound : Sound leaf6987Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6987CertificateValid
    leaf6987InnerLogValid leaf6987CoversExact leaf6987LowerChecked

private noncomputable def leaf6988Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (43/64), chiHi := (11/16) }

private noncomputable def leaf6988Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109065/67108864) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588650496) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (224876953/134217728) }, upper := { exponent := 1, mantissa := (883/512) } }, logOuter := sk151LogOuterCertificate, logK := sk151LogKCertificate, logChi := chi326LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178077183/17177300992) } }, logDArg := sk151LogDArgCertificate }

private noncomputable def leaf6988InnerLog : WideLogData :=
  innerPair788Data

set_option maxRecDepth 1000000 in
private theorem leaf6988LocalValidity :
    LeafFacts leaf6988Box leaf6988Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6988Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588650496) }) = true
      norm_num [leaf6988Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6988CertificateValid :
    WideCertificateValid leaf6988Box leaf6988Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk151ValidityFacts chi326ValidityFacts
    leaf6988LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6988CoverageChecked :
    coverageCheck (innerAD leaf6988Box) leaf6988InnerLog = true := by
  rfl'

private theorem leaf6988InnerLogValid :
    leaf6988InnerLog.Valid 8 (innerAD leaf6988Box) :=
  wideLogDataValid_of_cachedCheck endpoint495PositiveFacts
    endpoint559PositiveFacts.valid leaf6988CoverageChecked

private noncomputable def leaf6988InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629839/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6988InputLogOnePlusV_eq :
    leaf6988InputLogOnePlusV = outerEnclosure 24
      (leaf6988Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6988RoundedFacts : LeafRoundedFacts 8
    leaf6988Certificate.logOnePlusV leaf6988InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6988InputLogOnePlusV_eq }

private noncomputable def leaf6988Inputs : Inputs :=
  inputsOfCaches globalInput sk151RoundedInputs
    chi326InputQChi innerPair788Input
    leaf6988InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6988LowerChecked :
    lowerCheck 24 leaf6988Box leaf6988Inputs = true := by
  rfl'

private theorem leaf6988CoversExact : CoversExact 8
    leaf6988Box leaf6988Certificate leaf6988InnerLog leaf6988Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk151RoundedFacts chi326RoundedFacts
    innerPair788RoundedFacts leaf6988RoundedFacts (by rfl)

private theorem leaf6988FlatSound : Sound leaf6988Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6988CertificateValid
    leaf6988InnerLogValid leaf6988CoversExact leaf6988LowerChecked

private noncomputable def leaf6989Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (43/64), chiHi := (11/16) }

private noncomputable def leaf6989Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109067/67108864) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34354511872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (227694827/134217728) }, upper := { exponent := 1, mantissa := (447/256) } }, logOuter := sk152LogOuterCertificate, logK := sk152LogKCertificate, logChi := chi326LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68711694331/68709023744) } }, logDArg := sk152LogDArgCertificate }

private noncomputable def leaf6989InnerLog : WideLogData :=
  innerPair793Data

set_option maxRecDepth 1000000 in
private theorem leaf6989LocalValidity :
    LeafFacts leaf6989Box leaf6989Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6989Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34354511872) }) = true
      norm_num [leaf6989Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6989CertificateValid :
    WideCertificateValid leaf6989Box leaf6989Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk152ValidityFacts chi326ValidityFacts
    leaf6989LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6989CoverageChecked :
    coverageCheck (innerAD leaf6989Box) leaf6989InnerLog = true := by
  rfl'

private theorem leaf6989InnerLogValid :
    leaf6989InnerLog.Valid 8 (innerAD leaf6989Box) :=
  wideLogDataValid_of_cachedCheck endpoint497PositiveFacts
    endpoint560PositiveFacts.valid leaf6989CoverageChecked

private noncomputable def leaf6989InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629733/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6989InputLogOnePlusV_eq :
    leaf6989InputLogOnePlusV = outerEnclosure 24
      (leaf6989Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6989RoundedFacts : LeafRoundedFacts 8
    leaf6989Certificate.logOnePlusV leaf6989InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6989InputLogOnePlusV_eq }

private noncomputable def leaf6989Inputs : Inputs :=
  inputsOfCaches globalInput sk152RoundedInputs
    chi326InputQChi innerPair793Input
    leaf6989InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6989LowerChecked :
    lowerCheck 24 leaf6989Box leaf6989Inputs = true := by
  rfl'

private theorem leaf6989CoversExact : CoversExact 8
    leaf6989Box leaf6989Certificate leaf6989InnerLog leaf6989Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk152RoundedFacts chi326RoundedFacts
    innerPair793RoundedFacts leaf6989RoundedFacts (by rfl)

private theorem leaf6989FlatSound : Sound leaf6989Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6989CertificateValid
    leaf6989InnerLogValid leaf6989CoversExact leaf6989LowerChecked

private noncomputable def leaf6990Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (5/8), chiHi := (81/128) }

private noncomputable def leaf6990Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218007/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588711168) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (438253163/268435456) }, upper := { exponent := 1, mantissa := (6827/4096) } }, logOuter := sk153LogOuterCertificate, logK := sk153LogKCertificate, logChi := chi349LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178137855/17177422336) } }, logDArg := sk153LogDArgCertificate }

private noncomputable def leaf6990InnerLog : WideLogData :=
  innerPair761Data

set_option maxRecDepth 1000000 in
private theorem leaf6990LocalValidity :
    LeafFacts leaf6990Box leaf6990Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6990Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588711168) }) = true
      norm_num [leaf6990Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6990CertificateValid :
    WideCertificateValid leaf6990Box leaf6990Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk153ValidityFacts chi349ValidityFacts
    leaf6990LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6990CoverageChecked :
    coverageCheck (innerAD leaf6990Box) leaf6990InnerLog = true := by
  rfl'

private theorem leaf6990InnerLogValid :
    leaf6990InnerLog.Valid 8 (innerAD leaf6990Box) :=
  wideLogDataValid_of_cachedCheck endpoint485PositiveFacts
    endpoint487PositiveFacts.valid leaf6990CoverageChecked

private noncomputable def leaf6990InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907445/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6990InputLogOnePlusV_eq :
    leaf6990InputLogOnePlusV = outerEnclosure 24
      (leaf6990Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6990RoundedFacts : LeafRoundedFacts 8
    leaf6990Certificate.logOnePlusV leaf6990InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6990InputLogOnePlusV_eq }

private noncomputable def leaf6990Inputs : Inputs :=
  inputsOfCaches globalInput sk153RoundedInputs
    chi349InputQChi innerPair761Input
    leaf6990InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6990LowerChecked :
    lowerCheck 24 leaf6990Box leaf6990Inputs = true := by
  rfl'

private theorem leaf6990CoversExact : CoversExact 8
    leaf6990Box leaf6990Certificate leaf6990InnerLog leaf6990Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk153RoundedFacts chi349RoundedFacts
    innerPair761RoundedFacts leaf6990RoundedFacts (by rfl)

private theorem leaf6990FlatSound : Sound leaf6990Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6990CertificateValid
    leaf6990InnerLogValid leaf6990CoversExact leaf6990LowerChecked

private noncomputable def leaf6991Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (81/128), chiHi := (41/64) }

private noncomputable def leaf6991Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218009/134217728) }, vSqrt := { lower := (8191/8192), upper := (2863142229/2862898688) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (442054017/268435456) }, upper := { exponent := 1, mantissa := (3443/2048) } }, logOuter := sk153LogOuterCertificate, logK := sk153LogKCertificate, logChi := chi350LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (5726040917/5725797376) } }, logDArg := sk153LogDArgCertificate }

private noncomputable def leaf6991InnerLog : WideLogData :=
  innerPair761Data

set_option maxRecDepth 1000000 in
private theorem leaf6991LocalValidity :
    LeafFacts leaf6991Box leaf6991Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6991Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (2863142229/2862898688) }) = true
      norm_num [leaf6991Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6991CertificateValid :
    WideCertificateValid leaf6991Box leaf6991Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk153ValidityFacts chi350ValidityFacts
    leaf6991LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6991CoverageChecked :
    coverageCheck (innerAD leaf6991Box) leaf6991InnerLog = true := by
  rfl'

private theorem leaf6991InnerLogValid :
    leaf6991InnerLog.Valid 8 (innerAD leaf6991Box) :=
  wideLogDataValid_of_cachedCheck endpoint485PositiveFacts
    endpoint487PositiveFacts.valid leaf6991CoverageChecked

private noncomputable def leaf6991InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814897/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6991InputLogOnePlusV_eq :
    leaf6991InputLogOnePlusV = outerEnclosure 24
      (leaf6991Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6991RoundedFacts : LeafRoundedFacts 8
    leaf6991Certificate.logOnePlusV leaf6991InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6991InputLogOnePlusV_eq }

private noncomputable def leaf6991Inputs : Inputs :=
  inputsOfCaches globalInput sk153RoundedInputs
    chi350InputQChi innerPair761Input
    leaf6991InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6991LowerChecked :
    lowerCheck 24 leaf6991Box leaf6991Inputs = true := by
  rfl'

private theorem leaf6991CoversExact : CoversExact 8
    leaf6991Box leaf6991Certificate leaf6991InnerLog leaf6991Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk153RoundedFacts chi350RoundedFacts
    innerPair761RoundedFacts leaf6991RoundedFacts (by rfl)

private theorem leaf6991FlatSound : Sound leaf6991Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6991CertificateValid
    leaf6991InnerLogValid leaf6991CoversExact leaf6991LowerChecked

private noncomputable def leaf6992Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (5/8), chiHi := (81/128) }

private noncomputable def leaf6992Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218009/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588690432) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (443495721/268435456) }, upper := { exponent := 1, mantissa := (1727/1024) } }, logOuter := sk154LogOuterCertificate, logK := sk154LogKCertificate, logChi := chi349LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178117119/17177380864) } }, logDArg := sk154LogDArgCertificate }

private noncomputable def leaf6992InnerLog : WideLogData :=
  innerPair761Data

set_option maxRecDepth 1000000 in
private theorem leaf6992LocalValidity :
    LeafFacts leaf6992Box leaf6992Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6992Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588690432) }) = true
      norm_num [leaf6992Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6992CertificateValid :
    WideCertificateValid leaf6992Box leaf6992Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk154ValidityFacts chi349ValidityFacts
    leaf6992LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6992CoverageChecked :
    coverageCheck (innerAD leaf6992Box) leaf6992InnerLog = true := by
  rfl'

private theorem leaf6992InnerLogValid :
    leaf6992InnerLog.Valid 8 (innerAD leaf6992Box) :=
  wideLogDataValid_of_cachedCheck endpoint485PositiveFacts
    endpoint487PositiveFacts.valid leaf6992CoverageChecked

private noncomputable def leaf6992InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453725/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf6992InputLogOnePlusV_eq :
    leaf6992InputLogOnePlusV = outerEnclosure 24
      (leaf6992Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6992RoundedFacts : LeafRoundedFacts 8
    leaf6992Certificate.logOnePlusV leaf6992InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6992InputLogOnePlusV_eq }

private noncomputable def leaf6992Inputs : Inputs :=
  inputsOfCaches globalInput sk154RoundedInputs
    chi349InputQChi innerPair761Input
    leaf6992InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6992LowerChecked :
    lowerCheck 24 leaf6992Box leaf6992Inputs = true := by
  rfl'

private theorem leaf6992CoversExact : CoversExact 8
    leaf6992Box leaf6992Certificate leaf6992InnerLog leaf6992Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk154RoundedFacts chi349RoundedFacts
    innerPair761RoundedFacts leaf6992RoundedFacts (by rfl)

private theorem leaf6992FlatSound : Sound leaf6992Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6992CertificateValid
    leaf6992InnerLogValid leaf6992CoversExact leaf6992LowerChecked

private noncomputable def leaf6993Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (81/128), chiHi := (41/64) }

private noncomputable def leaf6993Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218011/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588675072) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (447362107/268435456) }, upper := { exponent := 1, mantissa := (871/512) } }, logOuter := sk154LogOuterCertificate, logK := sk154LogKCertificate, logChi := chi350LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178101759/17177350144) } }, logDArg := sk154LogDArgCertificate }

private noncomputable def leaf6993InnerLog : WideLogData :=
  innerPair765Data

set_option maxRecDepth 1000000 in
private theorem leaf6993LocalValidity :
    LeafFacts leaf6993Box leaf6993Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6993Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588675072) }) = true
      norm_num [leaf6993Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6993CertificateValid :
    WideCertificateValid leaf6993Box leaf6993Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk154ValidityFacts chi350ValidityFacts
    leaf6993LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6993CoverageChecked :
    coverageCheck (innerAD leaf6993Box) leaf6993InnerLog = true := by
  rfl'

private theorem leaf6993InnerLogValid :
    leaf6993InnerLog.Valid 8 (innerAD leaf6993Box) :=
  wideLogDataValid_of_cachedCheck endpoint486PositiveFacts
    endpoint488PositiveFacts.valid leaf6993CoverageChecked

private noncomputable def leaf6993InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629815/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6993InputLogOnePlusV_eq :
    leaf6993InputLogOnePlusV = outerEnclosure 24
      (leaf6993Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6993RoundedFacts : LeafRoundedFacts 8
    leaf6993Certificate.logOnePlusV leaf6993InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6993InputLogOnePlusV_eq }

private noncomputable def leaf6993Inputs : Inputs :=
  inputsOfCaches globalInput sk154RoundedInputs
    chi350InputQChi innerPair765Input
    leaf6993InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6993LowerChecked :
    lowerCheck 24 leaf6993Box leaf6993Inputs = true := by
  rfl'

private theorem leaf6993CoversExact : CoversExact 8
    leaf6993Box leaf6993Certificate leaf6993InnerLog leaf6993Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk154RoundedFacts chi350RoundedFacts
    innerPair765RoundedFacts leaf6993RoundedFacts (by rfl)

private theorem leaf6993FlatSound : Sound leaf6993Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6993CertificateValid
    leaf6993InnerLogValid leaf6993CoversExact leaf6993LowerChecked

private noncomputable def leaf6994Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (41/64), chiHi := (83/128) }

private noncomputable def leaf6994Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218011/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588680960) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (445854871/268435456) }, upper := { exponent := 1, mantissa := (6945/4096) } }, logOuter := sk153LogOuterCertificate, logK := sk153LogKCertificate, logChi := chi351LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178107647/17177361920) } }, logDArg := sk153LogDArgCertificate }

private noncomputable def leaf6994InnerLog : WideLogData :=
  innerPair765Data

set_option maxRecDepth 1000000 in
private theorem leaf6994LocalValidity :
    LeafFacts leaf6994Box leaf6994Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6994Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588680960) }) = true
      norm_num [leaf6994Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6994CertificateValid :
    WideCertificateValid leaf6994Box leaf6994Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk153ValidityFacts chi351ValidityFacts
    leaf6994LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6994CoverageChecked :
    coverageCheck (innerAD leaf6994Box) leaf6994InnerLog = true := by
  rfl'

private theorem leaf6994InnerLogValid :
    leaf6994InnerLog.Valid 8 (innerAD leaf6994Box) :=
  wideLogDataValid_of_cachedCheck endpoint486PositiveFacts
    endpoint488PositiveFacts.valid leaf6994CoverageChecked

private noncomputable def leaf6994InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629809/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6994InputLogOnePlusV_eq :
    leaf6994InputLogOnePlusV = outerEnclosure 24
      (leaf6994Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6994RoundedFacts : LeafRoundedFacts 8
    leaf6994Certificate.logOnePlusV leaf6994InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6994InputLogOnePlusV_eq }

private noncomputable def leaf6994Inputs : Inputs :=
  inputsOfCaches globalInput sk153RoundedInputs
    chi351InputQChi innerPair765Input
    leaf6994InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6994LowerChecked :
    lowerCheck 24 leaf6994Box leaf6994Inputs = true := by
  rfl'

private theorem leaf6994CoversExact : CoversExact 8
    leaf6994Box leaf6994Certificate leaf6994InnerLog leaf6994Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk153RoundedFacts chi351RoundedFacts
    innerPair765RoundedFacts leaf6994RoundedFacts (by rfl)

private theorem leaf6994FlatSound : Sound leaf6994Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6994CertificateValid
    leaf6994InnerLogValid leaf6994CoversExact leaf6994LowerChecked

private noncomputable def leaf6995Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (83/128), chiHi := (21/32) }

private noncomputable def leaf6995Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218013/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588665856) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (449655725/268435456) }, upper := { exponent := 1, mantissa := (1751/1024) } }, logOuter := sk153LogOuterCertificate, logK := sk153LogKCertificate, logChi := chi352LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178092543/17177331712) } }, logDArg := sk153LogDArgCertificate }

private noncomputable def leaf6995InnerLog : WideLogData :=
  innerPair765Data

set_option maxRecDepth 1000000 in
private theorem leaf6995LocalValidity :
    LeafFacts leaf6995Box leaf6995Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6995Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588665856) }) = true
      norm_num [leaf6995Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6995CertificateValid :
    WideCertificateValid leaf6995Box leaf6995Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk153ValidityFacts chi352ValidityFacts
    leaf6995LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6995CoverageChecked :
    coverageCheck (innerAD leaf6995Box) leaf6995InnerLog = true := by
  rfl'

private theorem leaf6995InnerLogValid :
    leaf6995InnerLog.Valid 8 (innerAD leaf6995Box) :=
  wideLogDataValid_of_cachedCheck endpoint486PositiveFacts
    endpoint488PositiveFacts.valid leaf6995CoverageChecked

private noncomputable def leaf6995InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (45429/65536) }

set_option maxRecDepth 1000000 in
private theorem leaf6995InputLogOnePlusV_eq :
    leaf6995InputLogOnePlusV = outerEnclosure 24
      (leaf6995Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6995RoundedFacts : LeafRoundedFacts 8
    leaf6995Certificate.logOnePlusV leaf6995InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6995InputLogOnePlusV_eq }

private noncomputable def leaf6995Inputs : Inputs :=
  inputsOfCaches globalInput sk153RoundedInputs
    chi352InputQChi innerPair765Input
    leaf6995InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6995LowerChecked :
    lowerCheck 24 leaf6995Box leaf6995Inputs = true := by
  rfl'

private theorem leaf6995CoversExact : CoversExact 8
    leaf6995Box leaf6995Certificate leaf6995InnerLog leaf6995Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk153RoundedFacts chi352RoundedFacts
    innerPair765RoundedFacts leaf6995RoundedFacts (by rfl)

private theorem leaf6995FlatSound : Sound leaf6995Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6995CertificateValid
    leaf6995InnerLogValid leaf6995CoversExact leaf6995LowerChecked

private noncomputable def leaf6996Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (41/64), chiHi := (83/128) }

private noncomputable def leaf6996Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218013/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588659712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (451228493/268435456) }, upper := { exponent := 1, mantissa := (1757/1024) } }, logOuter := sk154LogOuterCertificate, logK := sk154LogKCertificate, logChi := chi351LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178086399/17177319424) } }, logDArg := sk154LogDArgCertificate }

private noncomputable def leaf6996InnerLog : WideLogData :=
  innerPair765Data

set_option maxRecDepth 1000000 in
private theorem leaf6996LocalValidity :
    LeafFacts leaf6996Box leaf6996Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6996Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588659712) }) = true
      norm_num [leaf6996Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6996CertificateValid :
    WideCertificateValid leaf6996Box leaf6996Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk154ValidityFacts chi351ValidityFacts
    leaf6996LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6996CoverageChecked :
    coverageCheck (innerAD leaf6996Box) leaf6996InnerLog = true := by
  rfl'

private theorem leaf6996InnerLogValid :
    leaf6996InnerLog.Valid 8 (innerAD leaf6996Box) :=
  wideLogDataValid_of_cachedCheck endpoint486PositiveFacts
    endpoint488PositiveFacts.valid leaf6996CoverageChecked

private noncomputable def leaf6996InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814915/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6996InputLogOnePlusV_eq :
    leaf6996InputLogOnePlusV = outerEnclosure 24
      (leaf6996Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6996RoundedFacts : LeafRoundedFacts 8
    leaf6996Certificate.logOnePlusV leaf6996InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6996InputLogOnePlusV_eq }

private noncomputable def leaf6996Inputs : Inputs :=
  inputsOfCaches globalInput sk154RoundedInputs
    chi351InputQChi innerPair765Input
    leaf6996InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6996LowerChecked :
    lowerCheck 24 leaf6996Box leaf6996Inputs = true := by
  rfl'

private theorem leaf6996CoversExact : CoversExact 8
    leaf6996Box leaf6996Certificate leaf6996InnerLog leaf6996Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk154RoundedFacts chi351RoundedFacts
    innerPair765RoundedFacts leaf6996RoundedFacts (by rfl)

private theorem leaf6996FlatSound : Sound leaf6996Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6996CertificateValid
    leaf6996InnerLogValid leaf6996CoversExact leaf6996LowerChecked

private noncomputable def leaf6997Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (83/128), chiHi := (21/32) }

private noncomputable def leaf6997Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218015/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588644352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (455094879/268435456) }, upper := { exponent := 1, mantissa := (443/256) } }, logOuter := sk154LogOuterCertificate, logK := sk154LogKCertificate, logChi := chi352LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178071039/17177288704) } }, logDArg := sk154LogDArgCertificate }

private noncomputable def leaf6997InnerLog : WideLogData :=
  innerPair770Data

set_option maxRecDepth 1000000 in
private theorem leaf6997LocalValidity :
    LeafFacts leaf6997Box leaf6997Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6997Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588644352) }) = true
      norm_num [leaf6997Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6997CertificateValid :
    WideCertificateValid leaf6997Box leaf6997Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk154ValidityFacts chi352ValidityFacts
    leaf6997LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6997CoverageChecked :
    coverageCheck (innerAD leaf6997Box) leaf6997InnerLog = true := by
  rfl'

private theorem leaf6997InnerLogValid :
    leaf6997InnerLog.Valid 8 (innerAD leaf6997Box) :=
  wideLogDataValid_of_cachedCheck endpoint487PositiveFacts
    endpoint489PositiveFacts.valid leaf6997CoverageChecked

private noncomputable def leaf6997InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629845/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6997InputLogOnePlusV_eq :
    leaf6997InputLogOnePlusV = outerEnclosure 24
      (leaf6997Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6997RoundedFacts : LeafRoundedFacts 8
    leaf6997Certificate.logOnePlusV leaf6997InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6997InputLogOnePlusV_eq }

private noncomputable def leaf6997Inputs : Inputs :=
  inputsOfCaches globalInput sk154RoundedInputs
    chi352InputQChi innerPair770Input
    leaf6997InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6997LowerChecked :
    lowerCheck 24 leaf6997Box leaf6997Inputs = true := by
  rfl'

private theorem leaf6997CoversExact : CoversExact 8
    leaf6997Box leaf6997Certificate leaf6997InnerLog leaf6997Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk154RoundedFacts chi352RoundedFacts
    innerPair770RoundedFacts leaf6997RoundedFacts (by rfl)

private theorem leaf6997FlatSound : Sound leaf6997Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6997CertificateValid
    leaf6997InnerLogValid leaf6997CoversExact leaf6997LowerChecked

private noncomputable def leaf6998Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (21/32), chiHi := (85/128) }

private noncomputable def leaf6998Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218015/134217728) }, vSqrt := { lower := (8191/8192), upper := (22194901/22192896) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (453456579/268435456) }, upper := { exponent := 1, mantissa := (7063/4096) } }, logOuter := sk153LogOuterCertificate, logK := sk153LogKCertificate, logChi := chi353LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (44387797/44385792) } }, logDArg := sk153LogDArgCertificate }

private noncomputable def leaf6998InnerLog : WideLogData :=
  innerPair770Data

set_option maxRecDepth 1000000 in
private theorem leaf6998LocalValidity :
    LeafFacts leaf6998Box leaf6998Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6998Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22194901/22192896) }) = true
      norm_num [leaf6998Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6998CertificateValid :
    WideCertificateValid leaf6998Box leaf6998Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk153ValidityFacts chi353ValidityFacts
    leaf6998LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6998CoverageChecked :
    coverageCheck (innerAD leaf6998Box) leaf6998InnerLog = true := by
  rfl'

private theorem leaf6998InnerLogValid :
    leaf6998InnerLog.Valid 8 (innerAD leaf6998Box) :=
  wideLogDataValid_of_cachedCheck endpoint487PositiveFacts
    endpoint489PositiveFacts.valid leaf6998CoverageChecked

private noncomputable def leaf6998InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629839/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6998InputLogOnePlusV_eq :
    leaf6998InputLogOnePlusV = outerEnclosure 24
      (leaf6998Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6998RoundedFacts : LeafRoundedFacts 8
    leaf6998Certificate.logOnePlusV leaf6998InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6998InputLogOnePlusV_eq }

private noncomputable def leaf6998Inputs : Inputs :=
  inputsOfCaches globalInput sk153RoundedInputs
    chi353InputQChi innerPair770Input
    leaf6998InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6998LowerChecked :
    lowerCheck 24 leaf6998Box leaf6998Inputs = true := by
  rfl'

private theorem leaf6998CoversExact : CoversExact 8
    leaf6998Box leaf6998Certificate leaf6998InnerLog leaf6998Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk153RoundedFacts chi353RoundedFacts
    innerPair770RoundedFacts leaf6998RoundedFacts (by rfl)

private theorem leaf6998FlatSound : Sound leaf6998Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6998CertificateValid
    leaf6998InnerLogValid leaf6998CoversExact leaf6998LowerChecked

private noncomputable def leaf6999Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (85/128), chiHi := (43/64) }

private noncomputable def leaf6999Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218017/134217728) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34354542592) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (457257433/268435456) }, upper := { exponent := 1, mantissa := (3561/2048) } }, logOuter := sk153LogOuterCertificate, logK := sk153LogKCertificate, logChi := chi354LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68711725051/68709085184) } }, logDArg := sk153LogDArgCertificate }

private noncomputable def leaf6999InnerLog : WideLogData :=
  innerPair770Data

set_option maxRecDepth 1000000 in
private theorem leaf6999LocalValidity :
    LeafFacts leaf6999Box leaf6999Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6999Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34354542592) }) = true
      norm_num [leaf6999Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6999CertificateValid :
    WideCertificateValid leaf6999Box leaf6999Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk153ValidityFacts chi354ValidityFacts
    leaf6999LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6999CoverageChecked :
    coverageCheck (innerAD leaf6999Box) leaf6999InnerLog = true := by
  rfl'

private theorem leaf6999InnerLogValid :
    leaf6999InnerLog.Valid 8 (innerAD leaf6999Box) :=
  wideLogDataValid_of_cachedCheck endpoint487PositiveFacts
    endpoint489PositiveFacts.valid leaf6999CoverageChecked

private noncomputable def leaf6999InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629725/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6999InputLogOnePlusV_eq :
    leaf6999InputLogOnePlusV = outerEnclosure 24
      (leaf6999Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6999RoundedFacts : LeafRoundedFacts 8
    leaf6999Certificate.logOnePlusV leaf6999InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6999InputLogOnePlusV_eq }

private noncomputable def leaf6999Inputs : Inputs :=
  inputsOfCaches globalInput sk153RoundedInputs
    chi354InputQChi innerPair770Input
    leaf6999InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6999LowerChecked :
    lowerCheck 24 leaf6999Box leaf6999Inputs = true := by
  rfl'

private theorem leaf6999CoversExact : CoversExact 8
    leaf6999Box leaf6999Certificate leaf6999InnerLog leaf6999Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk153RoundedFacts chi354RoundedFacts
    innerPair770RoundedFacts leaf6999RoundedFacts (by rfl)

private theorem leaf6999FlatSound : Sound leaf6999Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6999CertificateValid
    leaf6999InnerLogValid leaf6999CoversExact leaf6999LowerChecked

private noncomputable def leaf7000Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (21/32), chiHi := (85/128) }

private noncomputable def leaf7000Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218017/134217728) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34354515968) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (458961265/268435456) }, upper := { exponent := 1, mantissa := (1787/1024) } }, logOuter := sk154LogOuterCertificate, logK := sk154LogKCertificate, logChi := chi353LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68711698427/68709031936) } }, logDArg := sk154LogDArgCertificate }

private noncomputable def leaf7000InnerLog : WideLogData :=
  innerPair770Data

set_option maxRecDepth 1000000 in
private theorem leaf7000LocalValidity :
    LeafFacts leaf7000Box leaf7000Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7000Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34354515968) }) = true
      norm_num [leaf7000Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7000CertificateValid :
    WideCertificateValid leaf7000Box leaf7000Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk154ValidityFacts chi353ValidityFacts
    leaf7000LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7000CoverageChecked :
    coverageCheck (innerAD leaf7000Box) leaf7000InnerLog = true := by
  rfl'

private theorem leaf7000InnerLogValid :
    leaf7000InnerLog.Valid 8 (innerAD leaf7000Box) :=
  wideLogDataValid_of_cachedCheck endpoint487PositiveFacts
    endpoint489PositiveFacts.valid leaf7000CoverageChecked

private noncomputable def leaf7000InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907433/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf7000InputLogOnePlusV_eq :
    leaf7000InputLogOnePlusV = outerEnclosure 24
      (leaf7000Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7000RoundedFacts : LeafRoundedFacts 8
    leaf7000Certificate.logOnePlusV leaf7000InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7000InputLogOnePlusV_eq }

private noncomputable def leaf7000Inputs : Inputs :=
  inputsOfCaches globalInput sk154RoundedInputs
    chi353InputQChi innerPair770Input
    leaf7000InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7000LowerChecked :
    lowerCheck 24 leaf7000Box leaf7000Inputs = true := by
  rfl'

private theorem leaf7000CoversExact : CoversExact 8
    leaf7000Box leaf7000Certificate leaf7000InnerLog leaf7000Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk154RoundedFacts chi353RoundedFacts
    innerPair770RoundedFacts leaf7000RoundedFacts (by rfl)

private theorem leaf7000FlatSound : Sound leaf7000Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7000CertificateValid
    leaf7000InnerLogValid leaf7000CoversExact leaf7000LowerChecked

private noncomputable def leaf7001Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (85/128), chiHi := (43/64) }

private noncomputable def leaf7001Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (134218019/134217728) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34354454528) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (462827651/268435456) }, upper := { exponent := 1, mantissa := (901/512) } }, logOuter := sk154LogOuterCertificate, logK := sk154LogKCertificate, logChi := chi354LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68711636987/68708909056) } }, logDArg := sk154LogDArgCertificate }

private noncomputable def leaf7001InnerLog : WideLogData :=
  innerPair775Data

set_option maxRecDepth 1000000 in
private theorem leaf7001LocalValidity :
    LeafFacts leaf7001Box leaf7001Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7001Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34354454528) }) = true
      norm_num [leaf7001Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7001CertificateValid :
    WideCertificateValid leaf7001Box leaf7001Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk154ValidityFacts chi354ValidityFacts
    leaf7001LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7001CoverageChecked :
    coverageCheck (innerAD leaf7001Box) leaf7001InnerLog = true := by
  rfl'

private theorem leaf7001InnerLogValid :
    leaf7001InnerLog.Valid 8 (innerAD leaf7001Box) :=
  wideLogDataValid_of_cachedCheck endpoint488PositiveFacts
    endpoint498PositiveFacts.valid leaf7001CoverageChecked

private noncomputable def leaf7001InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629747/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7001InputLogOnePlusV_eq :
    leaf7001InputLogOnePlusV = outerEnclosure 24
      (leaf7001Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7001RoundedFacts : LeafRoundedFacts 8
    leaf7001Certificate.logOnePlusV leaf7001InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7001InputLogOnePlusV_eq }

private noncomputable def leaf7001Inputs : Inputs :=
  inputsOfCaches globalInput sk154RoundedInputs
    chi354InputQChi innerPair775Input
    leaf7001InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7001LowerChecked :
    lowerCheck 24 leaf7001Box leaf7001Inputs = true := by
  rfl'

private theorem leaf7001CoversExact : CoversExact 8
    leaf7001Box leaf7001Certificate leaf7001InnerLog leaf7001Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk154RoundedFacts chi354RoundedFacts
    innerPair775RoundedFacts leaf7001RoundedFacts (by rfl)

private theorem leaf7001FlatSound : Sound leaf7001Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7001CertificateValid
    leaf7001InnerLogValid leaf7001CoversExact leaf7001LowerChecked

private noncomputable def leaf7002Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (43/64), chiHi := (87/128) }

private noncomputable def leaf7002Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (134218019/134217728) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34354482176) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (461058287/268435456) }, upper := { exponent := 1, mantissa := (7181/4096) } }, logOuter := sk153LogOuterCertificate, logK := sk153LogKCertificate, logChi := chi355LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68711664635/68708964352) } }, logDArg := sk153LogDArgCertificate }

private noncomputable def leaf7002InnerLog : WideLogData :=
  innerPair771Data

set_option maxRecDepth 1000000 in
private theorem leaf7002LocalValidity :
    LeafFacts leaf7002Box leaf7002Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7002Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34354482176) }) = true
      norm_num [leaf7002Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7002CertificateValid :
    WideCertificateValid leaf7002Box leaf7002Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk153ValidityFacts chi355ValidityFacts
    leaf7002LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7002CoverageChecked :
    coverageCheck (innerAD leaf7002Box) leaf7002InnerLog = true := by
  rfl'

private theorem leaf7002InnerLogValid :
    leaf7002InnerLog.Valid 8 (innerAD leaf7002Box) :=
  wideLogDataValid_of_cachedCheck endpoint487PositiveFacts
    endpoint498PositiveFacts.valid leaf7002CoverageChecked

private noncomputable def leaf7002InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907435/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf7002InputLogOnePlusV_eq :
    leaf7002InputLogOnePlusV = outerEnclosure 24
      (leaf7002Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7002RoundedFacts : LeafRoundedFacts 8
    leaf7002Certificate.logOnePlusV leaf7002InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7002InputLogOnePlusV_eq }

private noncomputable def leaf7002Inputs : Inputs :=
  inputsOfCaches globalInput sk153RoundedInputs
    chi355InputQChi innerPair771Input
    leaf7002InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7002LowerChecked :
    lowerCheck 24 leaf7002Box leaf7002Inputs = true := by
  rfl'

private theorem leaf7002CoversExact : CoversExact 8
    leaf7002Box leaf7002Certificate leaf7002InnerLog leaf7002Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk153RoundedFacts chi355RoundedFacts
    innerPair771RoundedFacts leaf7002RoundedFacts (by rfl)

private theorem leaf7002FlatSound : Sound leaf7002Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7002CertificateValid
    leaf7002InnerLogValid leaf7002CoversExact leaf7002LowerChecked

private noncomputable def leaf7003Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (87/128), chiHi := (11/16) }

private noncomputable def leaf7003Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (134218021/134217728) }, vSqrt := { lower := (8191/8192), upper := (11452394153/11451473920) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (464859141/268435456) }, upper := { exponent := 1, mantissa := (905/512) } }, logOuter := sk153LogOuterCertificate, logK := sk153LogKCertificate, logChi := chi356LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (22903868073/22902947840) } }, logDArg := sk153LogDArgCertificate }

private noncomputable def leaf7003InnerLog : WideLogData :=
  innerPair775Data

set_option maxRecDepth 1000000 in
private theorem leaf7003LocalValidity :
    LeafFacts leaf7003Box leaf7003Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7003Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (11452394153/11451473920) }) = true
      norm_num [leaf7003Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7003CertificateValid :
    WideCertificateValid leaf7003Box leaf7003Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk153ValidityFacts chi356ValidityFacts
    leaf7003LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7003CoverageChecked :
    coverageCheck (innerAD leaf7003Box) leaf7003InnerLog = true := by
  rfl'

private theorem leaf7003InnerLogValid :
    leaf7003InnerLog.Valid 8 (innerAD leaf7003Box) :=
  wideLogDataValid_of_cachedCheck endpoint488PositiveFacts
    endpoint498PositiveFacts.valid leaf7003CoverageChecked

private noncomputable def leaf7003InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629755/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7003InputLogOnePlusV_eq :
    leaf7003InputLogOnePlusV = outerEnclosure 24
      (leaf7003Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7003RoundedFacts : LeafRoundedFacts 8
    leaf7003Certificate.logOnePlusV leaf7003InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7003InputLogOnePlusV_eq }

private noncomputable def leaf7003Inputs : Inputs :=
  inputsOfCaches globalInput sk153RoundedInputs
    chi356InputQChi innerPair775Input
    leaf7003InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7003LowerChecked :
    lowerCheck 24 leaf7003Box leaf7003Inputs = true := by
  rfl'

private theorem leaf7003CoversExact : CoversExact 8
    leaf7003Box leaf7003Certificate leaf7003InnerLog leaf7003Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk153RoundedFacts chi356RoundedFacts
    innerPair775RoundedFacts leaf7003RoundedFacts (by rfl)

private theorem leaf7003FlatSound : Sound leaf7003Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7003CertificateValid
    leaf7003InnerLogValid leaf7003CoversExact leaf7003LowerChecked

private noncomputable def leaf7004Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (43/64), chiHi := (87/128) }

private noncomputable def leaf7004Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (134218021/134217728) }, vSqrt := { lower := (8191/8192), upper := (1808272761/1808125952) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (466694037/268435456) }, upper := { exponent := 1, mantissa := (1817/1024) } }, logOuter := sk154LogOuterCertificate, logK := sk154LogKCertificate, logChi := chi355LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (3616398713/3616251904) } }, logDArg := sk154LogDArgCertificate }

private noncomputable def leaf7004InnerLog : WideLogData :=
  innerPair775Data

set_option maxRecDepth 1000000 in
private theorem leaf7004LocalValidity :
    LeafFacts leaf7004Box leaf7004Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7004Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (1808272761/1808125952) }) = true
      norm_num [leaf7004Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7004CertificateValid :
    WideCertificateValid leaf7004Box leaf7004Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk154ValidityFacts chi355ValidityFacts
    leaf7004LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7004CoverageChecked :
    coverageCheck (innerAD leaf7004Box) leaf7004InnerLog = true := by
  rfl'

private theorem leaf7004InnerLogValid :
    leaf7004InnerLog.Valid 8 (innerAD leaf7004Box) :=
  wideLogDataValid_of_cachedCheck endpoint488PositiveFacts
    endpoint498PositiveFacts.valid leaf7004CoverageChecked

private noncomputable def leaf7004InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814881/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf7004InputLogOnePlusV_eq :
    leaf7004InputLogOnePlusV = outerEnclosure 24
      (leaf7004Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7004RoundedFacts : LeafRoundedFacts 8
    leaf7004Certificate.logOnePlusV leaf7004InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7004InputLogOnePlusV_eq }

private noncomputable def leaf7004Inputs : Inputs :=
  inputsOfCaches globalInput sk154RoundedInputs
    chi355InputQChi innerPair775Input
    leaf7004InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7004LowerChecked :
    lowerCheck 24 leaf7004Box leaf7004Inputs = true := by
  rfl'

private theorem leaf7004CoversExact : CoversExact 8
    leaf7004Box leaf7004Certificate leaf7004InnerLog leaf7004Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk154RoundedFacts chi355RoundedFacts
    innerPair775RoundedFacts leaf7004RoundedFacts (by rfl)

private theorem leaf7004FlatSound : Sound leaf7004Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7004CertificateValid
    leaf7004InnerLogValid leaf7004CoversExact leaf7004LowerChecked

private noncomputable def leaf7005Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (87/128), chiHi := (11/16) }

private noncomputable def leaf7005Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (134218023/134217728) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34354331648) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (470560423/268435456) }, upper := { exponent := 1, mantissa := (229/128) } }, logOuter := sk154LogOuterCertificate, logK := sk154LogKCertificate, logChi := chi356LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68711514107/68708663296) } }, logDArg := sk154LogDArgCertificate }

private noncomputable def leaf7005InnerLog : WideLogData :=
  innerPair778Data

set_option maxRecDepth 1000000 in
private theorem leaf7005LocalValidity :
    LeafFacts leaf7005Box leaf7005Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7005Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34354331648) }) = true
      norm_num [leaf7005Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7005CertificateValid :
    WideCertificateValid leaf7005Box leaf7005Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk154ValidityFacts chi356ValidityFacts
    leaf7005LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7005CoverageChecked :
    coverageCheck (innerAD leaf7005Box) leaf7005InnerLog = true := by
  rfl'

private theorem leaf7005InnerLogValid :
    leaf7005InnerLog.Valid 8 (innerAD leaf7005Box) :=
  wideLogDataValid_of_cachedCheck endpoint489PositiveFacts
    endpoint500PositiveFacts.valid leaf7005CoverageChecked

private noncomputable def leaf7005InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629777/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7005InputLogOnePlusV_eq :
    leaf7005InputLogOnePlusV = outerEnclosure 24
      (leaf7005Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7005RoundedFacts : LeafRoundedFacts 8
    leaf7005Certificate.logOnePlusV leaf7005InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7005InputLogOnePlusV_eq }

private noncomputable def leaf7005Inputs : Inputs :=
  inputsOfCaches globalInput sk154RoundedInputs
    chi356InputQChi innerPair778Input
    leaf7005InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7005LowerChecked :
    lowerCheck 24 leaf7005Box leaf7005Inputs = true := by
  rfl'

private theorem leaf7005CoversExact : CoversExact 8
    leaf7005Box leaf7005Certificate leaf7005InnerLog leaf7005Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk154RoundedFacts chi356RoundedFacts
    innerPair778RoundedFacts leaf7005RoundedFacts (by rfl)

private theorem leaf7005FlatSound : Sound leaf7005Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7005CertificateValid
    leaf7005InnerLogValid leaf7005CoversExact leaf7005LowerChecked

private noncomputable def leaf7006Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (11/16), chiHi := (45/64) }

private noncomputable def leaf7006Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109067/67108864) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34354485248) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (228546743/134217728) }, upper := { exponent := 1, mantissa := (3589/2048) } }, logOuter := sk151LogOuterCertificate, logK := sk151LogKCertificate, logChi := chi341LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68711667707/68708970496) } }, logDArg := sk151LogDArgCertificate }

private noncomputable def leaf7006InnerLog : WideLogData :=
  innerPair792Data

set_option maxRecDepth 1000000 in
private theorem leaf7006LocalValidity :
    LeafFacts leaf7006Box leaf7006Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7006Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34354485248) }) = true
      norm_num [leaf7006Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7006CertificateValid :
    WideCertificateValid leaf7006Box leaf7006Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk151ValidityFacts chi341ValidityFacts
    leaf7006LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7006CoverageChecked :
    coverageCheck (innerAD leaf7006Box) leaf7006InnerLog = true := by
  rfl'

private theorem leaf7006InnerLogValid :
    leaf7006InnerLog.Valid 8 (innerAD leaf7006Box) :=
  wideLogDataValid_of_cachedCheck endpoint497PositiveFacts
    endpoint543PositiveFacts.valid leaf7006CoverageChecked

private noncomputable def leaf7006InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629739/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7006InputLogOnePlusV_eq :
    leaf7006InputLogOnePlusV = outerEnclosure 24
      (leaf7006Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7006RoundedFacts : LeafRoundedFacts 8
    leaf7006Certificate.logOnePlusV leaf7006InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7006InputLogOnePlusV_eq }

private noncomputable def leaf7006Inputs : Inputs :=
  inputsOfCaches globalInput sk151RoundedInputs
    chi341InputQChi innerPair792Input
    leaf7006InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7006LowerChecked :
    lowerCheck 24 leaf7006Box leaf7006Inputs = true := by
  rfl'

private theorem leaf7006CoversExact : CoversExact 8
    leaf7006Box leaf7006Certificate leaf7006InnerLog leaf7006Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk151RoundedFacts chi341RoundedFacts
    innerPair792RoundedFacts leaf7006RoundedFacts (by rfl)

private theorem leaf7006FlatSound : Sound leaf7006Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7006CertificateValid
    leaf7006InnerLogValid leaf7006CoversExact leaf7006LowerChecked

private noncomputable def leaf7007Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (11/16), chiHi := (45/64) }

private noncomputable def leaf7007Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109069/67108864) }, vSqrt := { lower := (8191/8192), upper := (1808272761/1808125952) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (231430149/134217728) }, upper := { exponent := 1, mantissa := (1817/1024) } }, logOuter := sk152LogOuterCertificate, logK := sk152LogKCertificate, logChi := chi341LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (3616398713/3616251904) } }, logDArg := sk152LogDArgCertificate }

private noncomputable def leaf7007InnerLog : WideLogData :=
  innerPair775Data

set_option maxRecDepth 1000000 in
private theorem leaf7007LocalValidity :
    LeafFacts leaf7007Box leaf7007Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7007Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (1808272761/1808125952) }) = true
      norm_num [leaf7007Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7007CertificateValid :
    WideCertificateValid leaf7007Box leaf7007Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk152ValidityFacts chi341ValidityFacts
    leaf7007LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7007CoverageChecked :
    coverageCheck (innerAD leaf7007Box) leaf7007InnerLog = true := by
  rfl'

private theorem leaf7007InnerLogValid :
    leaf7007InnerLog.Valid 8 (innerAD leaf7007Box) :=
  wideLogDataValid_of_cachedCheck endpoint488PositiveFacts
    endpoint498PositiveFacts.valid leaf7007CoverageChecked

private noncomputable def leaf7007InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814881/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf7007InputLogOnePlusV_eq :
    leaf7007InputLogOnePlusV = outerEnclosure 24
      (leaf7007Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7007RoundedFacts : LeafRoundedFacts 8
    leaf7007Certificate.logOnePlusV leaf7007InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7007InputLogOnePlusV_eq }

private noncomputable def leaf7007Inputs : Inputs :=
  inputsOfCaches globalInput sk152RoundedInputs
    chi341InputQChi innerPair775Input
    leaf7007InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7007LowerChecked :
    lowerCheck 24 leaf7007Box leaf7007Inputs = true := by
  rfl'

private theorem leaf7007CoversExact : CoversExact 8
    leaf7007Box leaf7007Certificate leaf7007InnerLog leaf7007Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk152RoundedFacts chi341RoundedFacts
    innerPair775RoundedFacts leaf7007RoundedFacts (by rfl)

private theorem leaf7007FlatSound : Sound leaf7007Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7007CertificateValid
    leaf7007InnerLogValid leaf7007CoversExact leaf7007LowerChecked

private noncomputable def leaf7008Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (45/64), chiHi := (23/32) }

private noncomputable def leaf7008Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109069/67108864) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34354368512) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (232216533/134217728) }, upper := { exponent := 1, mantissa := (1823/1024) } }, logOuter := sk151LogOuterCertificate, logK := sk151LogKCertificate, logChi := chi342LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68711550971/68708737024) } }, logDArg := sk151LogDArgCertificate }

private noncomputable def leaf7008InnerLog : WideLogData :=
  innerPair775Data

set_option maxRecDepth 1000000 in
private theorem leaf7008LocalValidity :
    LeafFacts leaf7008Box leaf7008Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7008Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34354368512) }) = true
      norm_num [leaf7008Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7008CertificateValid :
    WideCertificateValid leaf7008Box leaf7008Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk151ValidityFacts chi342ValidityFacts
    leaf7008LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7008CoverageChecked :
    coverageCheck (innerAD leaf7008Box) leaf7008InnerLog = true := by
  rfl'

private theorem leaf7008InnerLogValid :
    leaf7008InnerLog.Valid 8 (innerAD leaf7008Box) :=
  wideLogDataValid_of_cachedCheck endpoint488PositiveFacts
    endpoint498PositiveFacts.valid leaf7008CoverageChecked

private noncomputable def leaf7008InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453721/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf7008InputLogOnePlusV_eq :
    leaf7008InputLogOnePlusV = outerEnclosure 24
      (leaf7008Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7008RoundedFacts : LeafRoundedFacts 8
    leaf7008Certificate.logOnePlusV leaf7008InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7008InputLogOnePlusV_eq }

private noncomputable def leaf7008Inputs : Inputs :=
  inputsOfCaches globalInput sk151RoundedInputs
    chi342InputQChi innerPair775Input
    leaf7008InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7008LowerChecked :
    lowerCheck 24 leaf7008Box leaf7008Inputs = true := by
  rfl'

private theorem leaf7008CoversExact : CoversExact 8
    leaf7008Box leaf7008Certificate leaf7008InnerLog leaf7008Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk151RoundedFacts chi342RoundedFacts
    innerPair775RoundedFacts leaf7008RoundedFacts (by rfl)

private theorem leaf7008FlatSound : Sound leaf7008Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7008CertificateValid
    leaf7008InnerLogValid leaf7008CoversExact leaf7008LowerChecked

private noncomputable def leaf7009Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (45/64), chiHi := (23/32) }

private noncomputable def leaf7009Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109071/67108864) }, vSqrt := { lower := (8191/8192), upper := (11452394153/11451424768) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (235165471/134217728) }, upper := { exponent := 1, mantissa := (923/512) } }, logOuter := sk152LogOuterCertificate, logK := sk152LogKCertificate, logChi := chi342LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (22903818921/22902849536) } }, logDArg := sk152LogDArgCertificate }

private noncomputable def leaf7009InnerLog : WideLogData :=
  innerPair778Data

set_option maxRecDepth 1000000 in
private theorem leaf7009LocalValidity :
    LeafFacts leaf7009Box leaf7009Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7009Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (11452394153/11451424768) }) = true
      norm_num [leaf7009Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7009CertificateValid :
    WideCertificateValid leaf7009Box leaf7009Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk152ValidityFacts chi342ValidityFacts
    leaf7009LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7009CoverageChecked :
    coverageCheck (innerAD leaf7009Box) leaf7009InnerLog = true := by
  rfl'

private theorem leaf7009InnerLogValid :
    leaf7009InnerLog.Valid 8 (innerAD leaf7009Box) :=
  wideLogDataValid_of_cachedCheck endpoint489PositiveFacts
    endpoint500PositiveFacts.valid leaf7009CoverageChecked

private noncomputable def leaf7009InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629791/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7009InputLogOnePlusV_eq :
    leaf7009InputLogOnePlusV = outerEnclosure 24
      (leaf7009Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7009RoundedFacts : LeafRoundedFacts 8
    leaf7009Certificate.logOnePlusV leaf7009InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7009InputLogOnePlusV_eq }

private noncomputable def leaf7009Inputs : Inputs :=
  inputsOfCaches globalInput sk152RoundedInputs
    chi342InputQChi innerPair778Input
    leaf7009InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7009LowerChecked :
    lowerCheck 24 leaf7009Box leaf7009Inputs = true := by
  rfl'

private theorem leaf7009CoversExact : CoversExact 8
    leaf7009Box leaf7009Certificate leaf7009InnerLog leaf7009Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk152RoundedFacts chi342RoundedFacts
    innerPair778RoundedFacts leaf7009RoundedFacts (by rfl)

private theorem leaf7009FlatSound : Sound leaf7009Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7009CertificateValid
    leaf7009InnerLogValid leaf7009CoversExact leaf7009LowerChecked

private noncomputable def leaf7010Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (23/32), chiHi := (47/64) }

private noncomputable def leaf7010Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109071/67108864) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34354251776) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (235886323/134217728) }, upper := { exponent := 1, mantissa := (3703/2048) } }, logOuter := sk151LogOuterCertificate, logK := sk151LogKCertificate, logChi := chi343LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68711434235/68708503552) } }, logDArg := sk151LogDArgCertificate }

private noncomputable def leaf7010InnerLog : WideLogData :=
  innerPair778Data

set_option maxRecDepth 1000000 in
private theorem leaf7010LocalValidity :
    LeafFacts leaf7010Box leaf7010Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7010Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34354251776) }) = true
      norm_num [leaf7010Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7010CertificateValid :
    WideCertificateValid leaf7010Box leaf7010Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk151ValidityFacts chi343ValidityFacts
    leaf7010LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7010CoverageChecked :
    coverageCheck (innerAD leaf7010Box) leaf7010InnerLog = true := by
  rfl'

private theorem leaf7010InnerLogValid :
    leaf7010InnerLog.Valid 8 (innerAD leaf7010Box) :=
  wideLogDataValid_of_cachedCheck endpoint489PositiveFacts
    endpoint500PositiveFacts.valid leaf7010CoverageChecked

private noncomputable def leaf7010InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907449/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf7010InputLogOnePlusV_eq :
    leaf7010InputLogOnePlusV = outerEnclosure 24
      (leaf7010Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7010RoundedFacts : LeafRoundedFacts 8
    leaf7010Certificate.logOnePlusV leaf7010InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7010InputLogOnePlusV_eq }

private noncomputable def leaf7010Inputs : Inputs :=
  inputsOfCaches globalInput sk151RoundedInputs
    chi343InputQChi innerPair778Input
    leaf7010InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7010LowerChecked :
    lowerCheck 24 leaf7010Box leaf7010Inputs = true := by
  rfl'

private theorem leaf7010CoversExact : CoversExact 8
    leaf7010Box leaf7010Certificate leaf7010InnerLog leaf7010Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk151RoundedFacts chi343RoundedFacts
    innerPair778RoundedFacts leaf7010RoundedFacts (by rfl)

private theorem leaf7010FlatSound : Sound leaf7010Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7010CertificateValid
    leaf7010InnerLogValid leaf7010CoversExact leaf7010LowerChecked

private noncomputable def leaf7011Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (23/32), chiHi := (47/64) }

private noncomputable def leaf7011Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109073/67108864) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34354155520) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (238900793/134217728) }, upper := { exponent := 1, mantissa := (1875/1024) } }, logOuter := sk152LogOuterCertificate, logK := sk152LogKCertificate, logChi := chi343LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68711337979/68708311040) } }, logDArg := sk152LogDArgCertificate }

private noncomputable def leaf7011InnerLog : WideLogData :=
  innerPair779Data

set_option maxRecDepth 1000000 in
private theorem leaf7011LocalValidity :
    LeafFacts leaf7011Box leaf7011Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7011Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34354155520) }) = true
      norm_num [leaf7011Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7011CertificateValid :
    WideCertificateValid leaf7011Box leaf7011Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk152ValidityFacts chi343ValidityFacts
    leaf7011LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7011CoverageChecked :
    coverageCheck (innerAD leaf7011Box) leaf7011InnerLog = true := by
  rfl'

private theorem leaf7011InnerLogValid :
    leaf7011InnerLog.Valid 8 (innerAD leaf7011Box) :=
  wideLogDataValid_of_cachedCheck endpoint489PositiveFacts
    endpoint501PositiveFacts.valid leaf7011CoverageChecked

private noncomputable def leaf7011InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907455/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf7011InputLogOnePlusV_eq :
    leaf7011InputLogOnePlusV = outerEnclosure 24
      (leaf7011Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7011RoundedFacts : LeafRoundedFacts 8
    leaf7011Certificate.logOnePlusV leaf7011InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7011InputLogOnePlusV_eq }

private noncomputable def leaf7011Inputs : Inputs :=
  inputsOfCaches globalInput sk152RoundedInputs
    chi343InputQChi innerPair779Input
    leaf7011InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7011LowerChecked :
    lowerCheck 24 leaf7011Box leaf7011Inputs = true := by
  rfl'

private theorem leaf7011CoversExact : CoversExact 8
    leaf7011Box leaf7011Certificate leaf7011InnerLog leaf7011Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk152RoundedFacts chi343RoundedFacts
    innerPair779RoundedFacts leaf7011RoundedFacts (by rfl)

private theorem leaf7011FlatSound : Sound leaf7011Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7011CertificateValid
    leaf7011InnerLogValid leaf7011CoversExact leaf7011LowerChecked

private noncomputable def leaf7012Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (47/64), chiHi := (3/4) }

private noncomputable def leaf7012Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109073/67108864) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34354135040) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (239556113/134217728) }, upper := { exponent := 1, mantissa := (235/128) } }, logOuter := sk151LogOuterCertificate, logK := sk151LogKCertificate, logChi := chi344LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68711317499/68708270080) } }, logDArg := sk151LogDArgCertificate }

private noncomputable def leaf7012InnerLog : WideLogData :=
  innerPair794Data

set_option maxRecDepth 1000000 in
private theorem leaf7012LocalValidity :
    LeafFacts leaf7012Box leaf7012Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7012Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34354135040) }) = true
      norm_num [leaf7012Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7012CertificateValid :
    WideCertificateValid leaf7012Box leaf7012Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk151ValidityFacts chi344ValidityFacts
    leaf7012LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7012CoverageChecked :
    coverageCheck (innerAD leaf7012Box) leaf7012InnerLog = true := by
  rfl'

private theorem leaf7012InnerLogValid :
    leaf7012InnerLog.Valid 8 (innerAD leaf7012Box) :=
  wideLogDataValid_of_cachedCheck endpoint498PositiveFacts
    endpoint501PositiveFacts.valid leaf7012CoverageChecked

private noncomputable def leaf7012InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629825/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7012InputLogOnePlusV_eq :
    leaf7012InputLogOnePlusV = outerEnclosure 24
      (leaf7012Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7012RoundedFacts : LeafRoundedFacts 8
    leaf7012Certificate.logOnePlusV leaf7012InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7012InputLogOnePlusV_eq }

private noncomputable def leaf7012Inputs : Inputs :=
  inputsOfCaches globalInput sk151RoundedInputs
    chi344InputQChi innerPair794Input
    leaf7012InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7012LowerChecked :
    lowerCheck 24 leaf7012Box leaf7012Inputs = true := by
  rfl'

private theorem leaf7012CoversExact : CoversExact 8
    leaf7012Box leaf7012Certificate leaf7012InnerLog leaf7012Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk151RoundedFacts chi344RoundedFacts
    innerPair794RoundedFacts leaf7012RoundedFacts (by rfl)

private theorem leaf7012FlatSound : Sound leaf7012Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7012CertificateValid
    leaf7012InnerLogValid leaf7012CoversExact leaf7012LowerChecked

private noncomputable def leaf7013Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (47/64), chiHi := (3/4) }

private noncomputable def leaf7013Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109075/67108864) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34354036736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (242636115/134217728) }, upper := { exponent := 1, mantissa := (119/64) } }, logOuter := sk152LogOuterCertificate, logK := sk152LogKCertificate, logChi := chi344LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68711219195/68708073472) } }, logDArg := sk152LogDArgCertificate }

private noncomputable def leaf7013InnerLog : WideLogData :=
  innerPair795Data

set_option maxRecDepth 1000000 in
private theorem leaf7013LocalValidity :
    LeafFacts leaf7013Box leaf7013Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7013Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34354036736) }) = true
      norm_num [leaf7013Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7013CertificateValid :
    WideCertificateValid leaf7013Box leaf7013Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk152ValidityFacts chi344ValidityFacts
    leaf7013LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7013CoverageChecked :
    coverageCheck (innerAD leaf7013Box) leaf7013InnerLog = true := by
  rfl'

private theorem leaf7013InnerLogValid :
    leaf7013InnerLog.Valid 8 (innerAD leaf7013Box) :=
  wideLogDataValid_of_cachedCheck endpoint498PositiveFacts
    endpoint502PositiveFacts.valid leaf7013CoverageChecked

private noncomputable def leaf7013InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629849/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7013InputLogOnePlusV_eq :
    leaf7013InputLogOnePlusV = outerEnclosure 24
      (leaf7013Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7013RoundedFacts : LeafRoundedFacts 8
    leaf7013Certificate.logOnePlusV leaf7013InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7013InputLogOnePlusV_eq }

private noncomputable def leaf7013Inputs : Inputs :=
  inputsOfCaches globalInput sk152RoundedInputs
    chi344InputQChi innerPair795Input
    leaf7013InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7013LowerChecked :
    lowerCheck 24 leaf7013Box leaf7013Inputs = true := by
  rfl'

private theorem leaf7013CoversExact : CoversExact 8
    leaf7013Box leaf7013Certificate leaf7013InnerLog leaf7013Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk152RoundedFacts chi344RoundedFacts
    innerPair795RoundedFacts leaf7013RoundedFacts (by rfl)

private theorem leaf7013FlatSound : Sound leaf7013Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7013CertificateValid
    leaf7013InnerLogValid leaf7013CoversExact leaf7013LowerChecked

private noncomputable def leaf7014Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (11/16), chiHi := (45/64) }

private noncomputable def leaf7014Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109071/67108864) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34354300928) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (234313555/134217728) }, upper := { exponent := 1, mantissa := (3679/2048) } }, logOuter := sk153LogOuterCertificate, logK := sk153LogKCertificate, logChi := chi341LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68711483387/68708601856) } }, logDArg := sk153LogDArgCertificate }

private noncomputable def leaf7014InnerLog : WideLogData :=
  innerPair855Data

set_option maxRecDepth 1000000 in
private theorem leaf7014LocalValidity :
    LeafFacts leaf7014Box leaf7014Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7014Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34354300928) }) = true
      norm_num [leaf7014Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7014CertificateValid :
    WideCertificateValid leaf7014Box leaf7014Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk153ValidityFacts chi341ValidityFacts
    leaf7014LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7014CoverageChecked :
    coverageCheck (innerAD leaf7014Box) leaf7014InnerLog = true := by
  rfl'

private theorem leaf7014InnerLogValid :
    leaf7014InnerLog.Valid 8 (innerAD leaf7014Box) :=
  wideLogDataValid_of_cachedCheck endpoint561PositiveFacts
    endpoint562PositiveFacts.valid leaf7014CoverageChecked

private noncomputable def leaf7014InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453723/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf7014InputLogOnePlusV_eq :
    leaf7014InputLogOnePlusV = outerEnclosure 24
      (leaf7014Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7014RoundedFacts : LeafRoundedFacts 8
    leaf7014Certificate.logOnePlusV leaf7014InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7014InputLogOnePlusV_eq }

private noncomputable def leaf7014Inputs : Inputs :=
  inputsOfCaches globalInput sk153RoundedInputs
    chi341InputQChi innerPair855Input
    leaf7014InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7014LowerChecked :
    lowerCheck 24 leaf7014Box leaf7014Inputs = true := by
  rfl'

private theorem leaf7014CoversExact : CoversExact 8
    leaf7014Box leaf7014Certificate leaf7014InnerLog leaf7014Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk153RoundedFacts chi341RoundedFacts
    innerPair855RoundedFacts leaf7014RoundedFacts (by rfl)

private theorem leaf7014FlatSound : Sound leaf7014Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7014CertificateValid
    leaf7014InnerLogValid leaf7014CoversExact leaf7014LowerChecked

private noncomputable def leaf7015Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (11/16), chiHi := (45/64) }

private noncomputable def leaf7015Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109073/67108864) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34354208768) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (237196961/134217728) }, upper := { exponent := 1, mantissa := (931/512) } }, logOuter := sk154LogOuterCertificate, logK := sk154LogKCertificate, logChi := chi341LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68711391227/68708417536) } }, logDArg := sk154LogDArgCertificate }

private noncomputable def leaf7015InnerLog : WideLogData :=
  innerPair797Data

set_option maxRecDepth 1000000 in
private theorem leaf7015LocalValidity :
    LeafFacts leaf7015Box leaf7015Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7015Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34354208768) }) = true
      norm_num [leaf7015Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7015CertificateValid :
    WideCertificateValid leaf7015Box leaf7015Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk154ValidityFacts chi341ValidityFacts
    leaf7015LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7015CoverageChecked :
    coverageCheck (innerAD leaf7015Box) leaf7015InnerLog = true := by
  rfl'

private theorem leaf7015InnerLogValid :
    leaf7015InnerLog.Valid 8 (innerAD leaf7015Box) :=
  wideLogDataValid_of_cachedCheck endpoint499PositiveFacts
    endpoint563PositiveFacts.valid leaf7015CoverageChecked

private noncomputable def leaf7015InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629807/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7015InputLogOnePlusV_eq :
    leaf7015InputLogOnePlusV = outerEnclosure 24
      (leaf7015Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7015RoundedFacts : LeafRoundedFacts 8
    leaf7015Certificate.logOnePlusV leaf7015InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7015InputLogOnePlusV_eq }

private noncomputable def leaf7015Inputs : Inputs :=
  inputsOfCaches globalInput sk154RoundedInputs
    chi341InputQChi innerPair797Input
    leaf7015InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7015LowerChecked :
    lowerCheck 24 leaf7015Box leaf7015Inputs = true := by
  rfl'

private theorem leaf7015CoversExact : CoversExact 8
    leaf7015Box leaf7015Certificate leaf7015InnerLog leaf7015Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk154RoundedFacts chi341RoundedFacts
    innerPair797RoundedFacts leaf7015RoundedFacts (by rfl)

private theorem leaf7015FlatSound : Sound leaf7015Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7015CertificateValid
    leaf7015InnerLogValid leaf7015CoversExact leaf7015LowerChecked

private noncomputable def leaf7016Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (45/64), chiHi := (23/32) }

private noncomputable def leaf7016Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109073/67108864) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34354180096) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (238114409/134217728) }, upper := { exponent := 1, mantissa := (1869/1024) } }, logOuter := sk153LogOuterCertificate, logK := sk153LogKCertificate, logChi := chi342LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68711362555/68708360192) } }, logDArg := sk153LogDArgCertificate }

private noncomputable def leaf7016InnerLog : WideLogData :=
  innerPair858Data

set_option maxRecDepth 1000000 in
private theorem leaf7016LocalValidity :
    LeafFacts leaf7016Box leaf7016Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7016Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34354180096) }) = true
      norm_num [leaf7016Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7016CertificateValid :
    WideCertificateValid leaf7016Box leaf7016Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk153ValidityFacts chi342ValidityFacts
    leaf7016LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7016CoverageChecked :
    coverageCheck (innerAD leaf7016Box) leaf7016InnerLog = true := by
  rfl'

private theorem leaf7016InnerLogValid :
    leaf7016InnerLog.Valid 8 (innerAD leaf7016Box) :=
  wideLogDataValid_of_cachedCheck endpoint564PositiveFacts
    endpoint565PositiveFacts.valid leaf7016CoverageChecked

private noncomputable def leaf7016InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814907/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf7016InputLogOnePlusV_eq :
    leaf7016InputLogOnePlusV = outerEnclosure 24
      (leaf7016Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7016RoundedFacts : LeafRoundedFacts 8
    leaf7016Certificate.logOnePlusV leaf7016InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7016InputLogOnePlusV_eq }

private noncomputable def leaf7016Inputs : Inputs :=
  inputsOfCaches globalInput sk153RoundedInputs
    chi342InputQChi innerPair858Input
    leaf7016InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7016LowerChecked :
    lowerCheck 24 leaf7016Box leaf7016Inputs = true := by
  rfl'

private theorem leaf7016CoversExact : CoversExact 8
    leaf7016Box leaf7016Certificate leaf7016InnerLog leaf7016Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk153RoundedFacts chi342RoundedFacts
    innerPair858RoundedFacts leaf7016RoundedFacts (by rfl)

private theorem leaf7016FlatSound : Sound leaf7016Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7016CertificateValid
    leaf7016InnerLogValid leaf7016CoversExact leaf7016LowerChecked

private noncomputable def leaf7017Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (45/64), chiHi := (23/32) }

private noncomputable def leaf7017Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109075/67108864) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34354085888) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (241063347/134217728) }, upper := { exponent := 1, mantissa := (473/256) } }, logOuter := sk154LogOuterCertificate, logK := sk154LogKCertificate, logChi := chi342LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68711268347/68708171776) } }, logDArg := sk154LogDArgCertificate }

private noncomputable def leaf7017InnerLog : WideLogData :=
  innerPair849Data

set_option maxRecDepth 1000000 in
private theorem leaf7017LocalValidity :
    LeafFacts leaf7017Box leaf7017Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7017Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34354085888) }) = true
      norm_num [leaf7017Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7017CertificateValid :
    WideCertificateValid leaf7017Box leaf7017Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk154ValidityFacts chi342ValidityFacts
    leaf7017LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7017CoverageChecked :
    coverageCheck (innerAD leaf7017Box) leaf7017InnerLog = true := by
  rfl'

private theorem leaf7017InnerLogValid :
    leaf7017InnerLog.Valid 8 (innerAD leaf7017Box) :=
  wideLogDataValid_of_cachedCheck endpoint544PositiveFacts
    endpoint566PositiveFacts.valid leaf7017CoverageChecked

private noncomputable def leaf7017InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629837/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7017InputLogOnePlusV_eq :
    leaf7017InputLogOnePlusV = outerEnclosure 24
      (leaf7017Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7017RoundedFacts : LeafRoundedFacts 8
    leaf7017Certificate.logOnePlusV leaf7017InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7017InputLogOnePlusV_eq }

private noncomputable def leaf7017Inputs : Inputs :=
  inputsOfCaches globalInput sk154RoundedInputs
    chi342InputQChi innerPair849Input
    leaf7017InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7017LowerChecked :
    lowerCheck 24 leaf7017Box leaf7017Inputs = true := by
  rfl'

private theorem leaf7017CoversExact : CoversExact 8
    leaf7017Box leaf7017Certificate leaf7017InnerLog leaf7017Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk154RoundedFacts chi342RoundedFacts
    innerPair849RoundedFacts leaf7017RoundedFacts (by rfl)

private theorem leaf7017FlatSound : Sound leaf7017Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7017CertificateValid
    leaf7017InnerLogValid leaf7017CoversExact leaf7017LowerChecked

private noncomputable def leaf7018Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (23/32), chiHi := (47/64) }

private noncomputable def leaf7018Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109075/67108864) }, vSqrt := { lower := (8191/8192), upper := (11452394153/11451353088) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (241915263/134217728) }, upper := { exponent := 1, mantissa := (3797/2048) } }, logOuter := sk153LogOuterCertificate, logK := sk153LogKCertificate, logChi := chi343LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (22903747241/22902706176) } }, logDArg := sk153LogDArgCertificate }

private noncomputable def leaf7018InnerLog : WideLogData :=
  innerPair857Data

set_option maxRecDepth 1000000 in
private theorem leaf7018LocalValidity :
    LeafFacts leaf7018Box leaf7018Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7018Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (11452394153/11451353088) }) = true
      norm_num [leaf7018Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7018CertificateValid :
    WideCertificateValid leaf7018Box leaf7018Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk153ValidityFacts chi343ValidityFacts
    leaf7018LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7018CoverageChecked :
    coverageCheck (innerAD leaf7018Box) leaf7018InnerLog = true := by
  rfl'

private theorem leaf7018InnerLogValid :
    leaf7018InnerLog.Valid 8 (innerAD leaf7018Box) :=
  wideLogDataValid_of_cachedCheck endpoint562PositiveFacts
    endpoint567PositiveFacts.valid leaf7018CoverageChecked

private noncomputable def leaf7018InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629843/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7018InputLogOnePlusV_eq :
    leaf7018InputLogOnePlusV = outerEnclosure 24
      (leaf7018Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7018RoundedFacts : LeafRoundedFacts 8
    leaf7018Certificate.logOnePlusV leaf7018InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7018InputLogOnePlusV_eq }

private noncomputable def leaf7018Inputs : Inputs :=
  inputsOfCaches globalInput sk153RoundedInputs
    chi343InputQChi innerPair857Input
    leaf7018InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7018LowerChecked :
    lowerCheck 24 leaf7018Box leaf7018Inputs = true := by
  rfl'

private theorem leaf7018CoversExact : CoversExact 8
    leaf7018Box leaf7018Certificate leaf7018InnerLog leaf7018Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk153RoundedFacts chi343RoundedFacts
    innerPair857RoundedFacts leaf7018RoundedFacts (by rfl)

private theorem leaf7018FlatSound : Sound leaf7018Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7018CertificateValid
    leaf7018InnerLogValid leaf7018CoversExact leaf7018LowerChecked

private noncomputable def leaf7019Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (23/32), chiHi := (47/64) }

private noncomputable def leaf7019Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109077/67108864) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34353963008) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (244929733/134217728) }, upper := { exponent := 1, mantissa := (961/512) } }, logOuter := sk154LogOuterCertificate, logK := sk154LogKCertificate, logChi := chi343LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68711145467/68707926016) } }, logDArg := sk154LogDArgCertificate }

private noncomputable def leaf7019InnerLog : WideLogData :=
  innerPair859Data

set_option maxRecDepth 1000000 in
private theorem leaf7019LocalValidity :
    LeafFacts leaf7019Box leaf7019Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7019Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34353963008) }) = true
      norm_num [leaf7019Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7019CertificateValid :
    WideCertificateValid leaf7019Box leaf7019Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk154ValidityFacts chi343ValidityFacts
    leaf7019LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7019CoverageChecked :
    coverageCheck (innerAD leaf7019Box) leaf7019InnerLog = true := by
  rfl'

private theorem leaf7019InnerLogValid :
    leaf7019InnerLog.Valid 8 (innerAD leaf7019Box) :=
  wideLogDataValid_of_cachedCheck endpoint568PositiveFacts
    endpoint569PositiveFacts.valid leaf7019CoverageChecked

private noncomputable def leaf7019InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629867/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7019InputLogOnePlusV_eq :
    leaf7019InputLogOnePlusV = outerEnclosure 24
      (leaf7019Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7019RoundedFacts : LeafRoundedFacts 8
    leaf7019Certificate.logOnePlusV leaf7019InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7019InputLogOnePlusV_eq }

private noncomputable def leaf7019Inputs : Inputs :=
  inputsOfCaches globalInput sk154RoundedInputs
    chi343InputQChi innerPair859Input
    leaf7019InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7019LowerChecked :
    lowerCheck 24 leaf7019Box leaf7019Inputs = true := by
  rfl'

private theorem leaf7019CoversExact : CoversExact 8
    leaf7019Box leaf7019Certificate leaf7019InnerLog leaf7019Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk154RoundedFacts chi343RoundedFacts
    innerPair859RoundedFacts leaf7019RoundedFacts (by rfl)

private theorem leaf7019FlatSound : Sound leaf7019Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7019CertificateValid
    leaf7019InnerLogValid leaf7019CoversExact leaf7019LowerChecked

private noncomputable def leaf7020Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (47/64), chiHi := (3/4) }

private noncomputable def leaf7020Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109077/67108864) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34353938432) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (245716117/134217728) }, upper := { exponent := 1, mantissa := (241/128) } }, logOuter := sk153LogOuterCertificate, logK := sk153LogKCertificate, logChi := chi344LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68711120891/68707876864) } }, logDArg := sk153LogDArgCertificate }

private noncomputable def leaf7020InnerLog : WideLogData :=
  innerPair799Data

set_option maxRecDepth 1000000 in
private theorem leaf7020LocalValidity :
    LeafFacts leaf7020Box leaf7020Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7020Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34353938432) }) = true
      norm_num [leaf7020Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7020CertificateValid :
    WideCertificateValid leaf7020Box leaf7020Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk153ValidityFacts chi344ValidityFacts
    leaf7020LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7020CoverageChecked :
    coverageCheck (innerAD leaf7020Box) leaf7020InnerLog = true := by
  rfl'

private theorem leaf7020InnerLogValid :
    leaf7020InnerLog.Valid 8 (innerAD leaf7020Box) :=
  wideLogDataValid_of_cachedCheck endpoint500PositiveFacts
    endpoint503PositiveFacts.valid leaf7020CoverageChecked

private noncomputable def leaf7020InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629873/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7020InputLogOnePlusV_eq :
    leaf7020InputLogOnePlusV = outerEnclosure 24
      (leaf7020Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7020RoundedFacts : LeafRoundedFacts 8
    leaf7020Certificate.logOnePlusV leaf7020InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7020InputLogOnePlusV_eq }

private noncomputable def leaf7020Inputs : Inputs :=
  inputsOfCaches globalInput sk153RoundedInputs
    chi344InputQChi innerPair799Input
    leaf7020InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7020LowerChecked :
    lowerCheck 24 leaf7020Box leaf7020Inputs = true := by
  rfl'

private theorem leaf7020CoversExact : CoversExact 8
    leaf7020Box leaf7020Certificate leaf7020InnerLog leaf7020Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk153RoundedFacts chi344RoundedFacts
    innerPair799RoundedFacts leaf7020RoundedFacts (by rfl)

private theorem leaf7020FlatSound : Sound leaf7020Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7020CertificateValid
    leaf7020InnerLogValid leaf7020CoversExact leaf7020LowerChecked

private noncomputable def leaf7021Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (47/64), chiHi := (3/4) }

private noncomputable def leaf7021Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109079/67108864) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34353840128) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (248796119/134217728) }, upper := { exponent := 1, mantissa := (61/32) } }, logOuter := sk154LogOuterCertificate, logK := sk154LogKCertificate, logChi := chi344LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68711022587/68707680256) } }, logDArg := sk154LogDArgCertificate }

private noncomputable def leaf7021InnerLog : WideLogData :=
  innerPair801Data

set_option maxRecDepth 1000000 in
private theorem leaf7021LocalValidity :
    LeafFacts leaf7021Box leaf7021Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7021Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34353840128) }) = true
      norm_num [leaf7021Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7021CertificateValid :
    WideCertificateValid leaf7021Box leaf7021Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk154ValidityFacts chi344ValidityFacts
    leaf7021LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7021CoverageChecked :
    coverageCheck (innerAD leaf7021Box) leaf7021InnerLog = true := by
  rfl'

private theorem leaf7021InnerLogValid :
    leaf7021InnerLog.Valid 8 (innerAD leaf7021Box) :=
  wideLogDataValid_of_cachedCheck endpoint501PositiveFacts
    endpoint503PositiveFacts.valid leaf7021CoverageChecked

private noncomputable def leaf7021InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629897/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7021InputLogOnePlusV_eq :
    leaf7021InputLogOnePlusV = outerEnclosure 24
      (leaf7021Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7021RoundedFacts : LeafRoundedFacts 8
    leaf7021Certificate.logOnePlusV leaf7021InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7021InputLogOnePlusV_eq }

private noncomputable def leaf7021Inputs : Inputs :=
  inputsOfCaches globalInput sk154RoundedInputs
    chi344InputQChi innerPair801Input
    leaf7021InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7021LowerChecked :
    lowerCheck 24 leaf7021Box leaf7021Inputs = true := by
  rfl'

private theorem leaf7021CoversExact : CoversExact 8
    leaf7021Box leaf7021Certificate leaf7021InnerLog leaf7021Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk154RoundedFacts chi344RoundedFacts
    innerPair801RoundedFacts leaf7021RoundedFacts (by rfl)

private theorem leaf7021FlatSound : Sound leaf7021Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7021CertificateValid
    leaf7021InnerLogValid leaf7021CoversExact leaf7021LowerChecked

private noncomputable def component142Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (5/8), chiHi := (41/64) }

set_option maxRecDepth 1000000 in
private theorem component142Node0_sound : Sound component142Node0Box :=
  sound_of_literal_split component142Node0Box leaf6976Box leaf6977Box
    .chi (81/128) (by rfl) (by rfl)
    leaf6976FlatSound leaf6977FlatSound

private noncomputable def component142Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (5/8), chiHi := (41/64) }

set_option maxRecDepth 1000000 in
private theorem component142Node1_sound : Sound component142Node1Box :=
  sound_of_literal_split component142Node1Box leaf6978Box leaf6979Box
    .chi (81/128) (by rfl) (by rfl)
    leaf6978FlatSound leaf6979FlatSound

private noncomputable def component142Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (5/8), chiHi := (41/64) }

set_option maxRecDepth 1000000 in
private theorem component142Node2_sound : Sound component142Node2Box :=
  sound_of_literal_split component142Node2Box component142Node0Box component142Node1Box
    .k (57/16) (by rfl) (by rfl)
    component142Node0_sound component142Node1_sound

private noncomputable def component142Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (41/64), chiHi := (21/32) }

set_option maxRecDepth 1000000 in
private theorem component142Node3_sound : Sound component142Node3Box :=
  sound_of_literal_split component142Node3Box leaf6980Box leaf6981Box
    .chi (83/128) (by rfl) (by rfl)
    leaf6980FlatSound leaf6981FlatSound

private noncomputable def component142Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (41/64), chiHi := (21/32) }

set_option maxRecDepth 1000000 in
private theorem component142Node4_sound : Sound component142Node4Box :=
  sound_of_literal_split component142Node4Box leaf6982Box leaf6983Box
    .chi (83/128) (by rfl) (by rfl)
    leaf6982FlatSound leaf6983FlatSound

private noncomputable def component142Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (41/64), chiHi := (21/32) }

set_option maxRecDepth 1000000 in
private theorem component142Node5_sound : Sound component142Node5Box :=
  sound_of_literal_split component142Node5Box component142Node3Box component142Node4Box
    .k (57/16) (by rfl) (by rfl)
    component142Node3_sound component142Node4_sound

private noncomputable def component142Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (5/8), chiHi := (21/32) }

set_option maxRecDepth 1000000 in
private theorem component142Node6_sound : Sound component142Node6Box :=
  sound_of_literal_split component142Node6Box component142Node2Box component142Node5Box
    .chi (41/64) (by rfl) (by rfl)
    component142Node2_sound component142Node5_sound

private noncomputable def component142Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (21/32), chiHi := (43/64) }

set_option maxRecDepth 1000000 in
private theorem component142Node7_sound : Sound component142Node7Box :=
  sound_of_literal_split component142Node7Box leaf6984Box leaf6985Box
    .chi (85/128) (by rfl) (by rfl)
    leaf6984FlatSound leaf6985FlatSound

private noncomputable def component142Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (21/32), chiHi := (43/64) }

set_option maxRecDepth 1000000 in
private theorem component142Node8_sound : Sound component142Node8Box :=
  sound_of_literal_split component142Node8Box leaf6986Box leaf6987Box
    .chi (85/128) (by rfl) (by rfl)
    leaf6986FlatSound leaf6987FlatSound

private noncomputable def component142Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (21/32), chiHi := (43/64) }

set_option maxRecDepth 1000000 in
private theorem component142Node9_sound : Sound component142Node9Box :=
  sound_of_literal_split component142Node9Box component142Node7Box component142Node8Box
    .k (57/16) (by rfl) (by rfl)
    component142Node7_sound component142Node8_sound

private noncomputable def component142Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (43/64), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component142Node10_sound : Sound component142Node10Box :=
  sound_of_literal_split component142Node10Box leaf6988Box leaf6989Box
    .k (57/16) (by rfl) (by rfl)
    leaf6988FlatSound leaf6989FlatSound

private noncomputable def component142Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (21/32), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component142Node11_sound : Sound component142Node11Box :=
  sound_of_literal_split component142Node11Box component142Node9Box component142Node10Box
    .chi (43/64) (by rfl) (by rfl)
    component142Node9_sound component142Node10_sound

private noncomputable def component142Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (5/8), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component142Node12_sound : Sound component142Node12Box :=
  sound_of_literal_split component142Node12Box component142Node6Box component142Node11Box
    .chi (21/32) (by rfl) (by rfl)
    component142Node6_sound component142Node11_sound

private noncomputable def component142Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (5/8), chiHi := (41/64) }

set_option maxRecDepth 1000000 in
private theorem component142Node13_sound : Sound component142Node13Box :=
  sound_of_literal_split component142Node13Box leaf6990Box leaf6991Box
    .chi (81/128) (by rfl) (by rfl)
    leaf6990FlatSound leaf6991FlatSound

private noncomputable def component142Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (5/8), chiHi := (41/64) }

set_option maxRecDepth 1000000 in
private theorem component142Node14_sound : Sound component142Node14Box :=
  sound_of_literal_split component142Node14Box leaf6992Box leaf6993Box
    .chi (81/128) (by rfl) (by rfl)
    leaf6992FlatSound leaf6993FlatSound

private noncomputable def component142Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (5/8), chiHi := (41/64) }

set_option maxRecDepth 1000000 in
private theorem component142Node15_sound : Sound component142Node15Box :=
  sound_of_literal_split component142Node15Box component142Node13Box component142Node14Box
    .k (59/16) (by rfl) (by rfl)
    component142Node13_sound component142Node14_sound

private noncomputable def component142Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (41/64), chiHi := (21/32) }

set_option maxRecDepth 1000000 in
private theorem component142Node16_sound : Sound component142Node16Box :=
  sound_of_literal_split component142Node16Box leaf6994Box leaf6995Box
    .chi (83/128) (by rfl) (by rfl)
    leaf6994FlatSound leaf6995FlatSound

private noncomputable def component142Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (41/64), chiHi := (21/32) }

set_option maxRecDepth 1000000 in
private theorem component142Node17_sound : Sound component142Node17Box :=
  sound_of_literal_split component142Node17Box leaf6996Box leaf6997Box
    .chi (83/128) (by rfl) (by rfl)
    leaf6996FlatSound leaf6997FlatSound

private noncomputable def component142Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (41/64), chiHi := (21/32) }

set_option maxRecDepth 1000000 in
private theorem component142Node18_sound : Sound component142Node18Box :=
  sound_of_literal_split component142Node18Box component142Node16Box component142Node17Box
    .k (59/16) (by rfl) (by rfl)
    component142Node16_sound component142Node17_sound

private noncomputable def component142Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (5/8), chiHi := (21/32) }

set_option maxRecDepth 1000000 in
private theorem component142Node19_sound : Sound component142Node19Box :=
  sound_of_literal_split component142Node19Box component142Node15Box component142Node18Box
    .chi (41/64) (by rfl) (by rfl)
    component142Node15_sound component142Node18_sound

private noncomputable def component142Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (21/32), chiHi := (43/64) }

set_option maxRecDepth 1000000 in
private theorem component142Node20_sound : Sound component142Node20Box :=
  sound_of_literal_split component142Node20Box leaf6998Box leaf6999Box
    .chi (85/128) (by rfl) (by rfl)
    leaf6998FlatSound leaf6999FlatSound

private noncomputable def component142Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (21/32), chiHi := (43/64) }

set_option maxRecDepth 1000000 in
private theorem component142Node21_sound : Sound component142Node21Box :=
  sound_of_literal_split component142Node21Box leaf7000Box leaf7001Box
    .chi (85/128) (by rfl) (by rfl)
    leaf7000FlatSound leaf7001FlatSound

private noncomputable def component142Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (21/32), chiHi := (43/64) }

set_option maxRecDepth 1000000 in
private theorem component142Node22_sound : Sound component142Node22Box :=
  sound_of_literal_split component142Node22Box component142Node20Box component142Node21Box
    .k (59/16) (by rfl) (by rfl)
    component142Node20_sound component142Node21_sound

private noncomputable def component142Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (43/64), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component142Node23_sound : Sound component142Node23Box :=
  sound_of_literal_split component142Node23Box leaf7002Box leaf7003Box
    .chi (87/128) (by rfl) (by rfl)
    leaf7002FlatSound leaf7003FlatSound

private noncomputable def component142Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (43/64), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component142Node24_sound : Sound component142Node24Box :=
  sound_of_literal_split component142Node24Box leaf7004Box leaf7005Box
    .chi (87/128) (by rfl) (by rfl)
    leaf7004FlatSound leaf7005FlatSound

private noncomputable def component142Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (43/64), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component142Node25_sound : Sound component142Node25Box :=
  sound_of_literal_split component142Node25Box component142Node23Box component142Node24Box
    .k (59/16) (by rfl) (by rfl)
    component142Node23_sound component142Node24_sound

private noncomputable def component142Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (21/32), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component142Node26_sound : Sound component142Node26Box :=
  sound_of_literal_split component142Node26Box component142Node22Box component142Node25Box
    .chi (43/64) (by rfl) (by rfl)
    component142Node22_sound component142Node25_sound

private noncomputable def component142Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (5/8), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component142Node27_sound : Sound component142Node27Box :=
  sound_of_literal_split component142Node27Box component142Node19Box component142Node26Box
    .chi (21/32) (by rfl) (by rfl)
    component142Node19_sound component142Node26_sound

private noncomputable def component142Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (15/4), chiLo := (5/8), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component142Node28_sound : Sound component142Node28Box :=
  sound_of_literal_split component142Node28Box component142Node12Box component142Node27Box
    .k (29/8) (by rfl) (by rfl)
    component142Node12_sound component142Node27_sound

private noncomputable def component142Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (11/16), chiHi := (45/64) }

set_option maxRecDepth 1000000 in
private theorem component142Node29_sound : Sound component142Node29Box :=
  sound_of_literal_split component142Node29Box leaf7006Box leaf7007Box
    .k (57/16) (by rfl) (by rfl)
    leaf7006FlatSound leaf7007FlatSound

private noncomputable def component142Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (45/64), chiHi := (23/32) }

set_option maxRecDepth 1000000 in
private theorem component142Node30_sound : Sound component142Node30Box :=
  sound_of_literal_split component142Node30Box leaf7008Box leaf7009Box
    .k (57/16) (by rfl) (by rfl)
    leaf7008FlatSound leaf7009FlatSound

private noncomputable def component142Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (11/16), chiHi := (23/32) }

set_option maxRecDepth 1000000 in
private theorem component142Node31_sound : Sound component142Node31Box :=
  sound_of_literal_split component142Node31Box component142Node29Box component142Node30Box
    .chi (45/64) (by rfl) (by rfl)
    component142Node29_sound component142Node30_sound

private noncomputable def component142Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (23/32), chiHi := (47/64) }

set_option maxRecDepth 1000000 in
private theorem component142Node32_sound : Sound component142Node32Box :=
  sound_of_literal_split component142Node32Box leaf7010Box leaf7011Box
    .k (57/16) (by rfl) (by rfl)
    leaf7010FlatSound leaf7011FlatSound

private noncomputable def component142Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (47/64), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component142Node33_sound : Sound component142Node33Box :=
  sound_of_literal_split component142Node33Box leaf7012Box leaf7013Box
    .k (57/16) (by rfl) (by rfl)
    leaf7012FlatSound leaf7013FlatSound

private noncomputable def component142Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (23/32), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component142Node34_sound : Sound component142Node34Box :=
  sound_of_literal_split component142Node34Box component142Node32Box component142Node33Box
    .chi (47/64) (by rfl) (by rfl)
    component142Node32_sound component142Node33_sound

private noncomputable def component142Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (11/16), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component142Node35_sound : Sound component142Node35Box :=
  sound_of_literal_split component142Node35Box component142Node31Box component142Node34Box
    .chi (23/32) (by rfl) (by rfl)
    component142Node31_sound component142Node34_sound

private noncomputable def component142Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (11/16), chiHi := (45/64) }

set_option maxRecDepth 1000000 in
private theorem component142Node36_sound : Sound component142Node36Box :=
  sound_of_literal_split component142Node36Box leaf7014Box leaf7015Box
    .k (59/16) (by rfl) (by rfl)
    leaf7014FlatSound leaf7015FlatSound

private noncomputable def component142Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (45/64), chiHi := (23/32) }

set_option maxRecDepth 1000000 in
private theorem component142Node37_sound : Sound component142Node37Box :=
  sound_of_literal_split component142Node37Box leaf7016Box leaf7017Box
    .k (59/16) (by rfl) (by rfl)
    leaf7016FlatSound leaf7017FlatSound

private noncomputable def component142Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (11/16), chiHi := (23/32) }

set_option maxRecDepth 1000000 in
private theorem component142Node38_sound : Sound component142Node38Box :=
  sound_of_literal_split component142Node38Box component142Node36Box component142Node37Box
    .chi (45/64) (by rfl) (by rfl)
    component142Node36_sound component142Node37_sound

private noncomputable def component142Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (23/32), chiHi := (47/64) }

set_option maxRecDepth 1000000 in
private theorem component142Node39_sound : Sound component142Node39Box :=
  sound_of_literal_split component142Node39Box leaf7018Box leaf7019Box
    .k (59/16) (by rfl) (by rfl)
    leaf7018FlatSound leaf7019FlatSound

private noncomputable def component142Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (47/64), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component142Node40_sound : Sound component142Node40Box :=
  sound_of_literal_split component142Node40Box leaf7020Box leaf7021Box
    .k (59/16) (by rfl) (by rfl)
    leaf7020FlatSound leaf7021FlatSound

private noncomputable def component142Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (23/32), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component142Node41_sound : Sound component142Node41Box :=
  sound_of_literal_split component142Node41Box component142Node39Box component142Node40Box
    .chi (47/64) (by rfl) (by rfl)
    component142Node39_sound component142Node40_sound

private noncomputable def component142Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (11/16), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component142Node42_sound : Sound component142Node42Box :=
  sound_of_literal_split component142Node42Box component142Node38Box component142Node41Box
    .chi (23/32) (by rfl) (by rfl)
    component142Node38_sound component142Node41_sound

private noncomputable def component142Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (15/4), chiLo := (11/16), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component142Node43_sound : Sound component142Node43Box :=
  sound_of_literal_split component142Node43Box component142Node35Box component142Node42Box
    .k (29/8) (by rfl) (by rfl)
    component142Node35_sound component142Node42_sound

noncomputable def component142Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (15/4), chiLo := (5/8), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
theorem component142_sound : Sound component142Box :=
  sound_of_literal_split component142Box component142Node28Box component142Node43Box
    .chi (11/16) (by rfl) (by rfl)
    component142Node28_sound component142Node43_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
