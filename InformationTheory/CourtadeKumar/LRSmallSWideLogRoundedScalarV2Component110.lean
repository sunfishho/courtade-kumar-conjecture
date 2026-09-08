import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch5
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch8
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch9
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

private noncomputable def leaf5435Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (249/64), chiLo := (5/16), chiHi := (81/256) }

private noncomputable def leaf5435Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742483/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9816773193/9816330496) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2373863279/2147483648) }, upper := { exponent := 1, mantissa := (36553/32768) } }, logOuter := sk233LogOuterCertificate, logK := sk233LogKCertificate, logChi := chi289LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (19633103689/19632660992) } }, logDArg := sk233LogDArgCertificate }

private noncomputable def leaf5435InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf5435LocalValidity :
    LeafFacts leaf5435Box leaf5435Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5435Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9816773193/9816330496) }) = true
      norm_num [leaf5435Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5435CertificateValid :
    WideCertificateValid leaf5435Box leaf5435Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk233ValidityFacts chi289ValidityFacts
    leaf5435LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5435CoverageChecked :
    coverageCheck (innerAD leaf5435Box) leaf5435InnerLog = true := by
  rfl'

private theorem leaf5435InnerLogValid :
    leaf5435InnerLog.Valid 8 (innerAD leaf5435Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf5435CoverageChecked

private noncomputable def leaf5435InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629459/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5435InputLogOnePlusV_eq :
    leaf5435InputLogOnePlusV = outerEnclosure 24
      (leaf5435Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5435RoundedFacts : LeafRoundedFacts 8
    leaf5435Certificate.logOnePlusV leaf5435InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5435InputLogOnePlusV_eq }

private noncomputable def leaf5435Inputs : Inputs :=
  inputsOfCaches globalInput sk233RoundedInputs
    chi289InputQChi innerPair256Input
    leaf5435InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5435LowerChecked :
    lowerCheck 24 leaf5435Box leaf5435Inputs = true := by
  rfl'

private theorem leaf5435CoversExact : CoversExact 8
    leaf5435Box leaf5435Certificate leaf5435InnerLog leaf5435Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk233RoundedFacts chi289RoundedFacts
    innerPair256RoundedFacts leaf5435RoundedFacts (by rfl)

private theorem leaf5435FlatSound : Sound leaf5435Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5435CertificateValid
    leaf5435InnerLogValid leaf5435CoversExact leaf5435LowerChecked

private noncomputable def leaf5436Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (249/64), kHi := (125/32), chiLo := (5/16), chiHi := (81/256) }

private noncomputable def leaf5436Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742485/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714292736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2379105837/2147483648) }, upper := { exponent := 1, mantissa := (18317/16384) } }, logOuter := sk234LogOuterCertificate, logK := sk234LogKCertificate, logChi := chi289LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431705087/137428585472) } }, logDArg := sk234LogDArgCertificate }

private noncomputable def leaf5436InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf5436LocalValidity :
    LeafFacts leaf5436Box leaf5436Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5436Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714292736) }) = true
      norm_num [leaf5436Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5436CertificateValid :
    WideCertificateValid leaf5436Box leaf5436Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk234ValidityFacts chi289ValidityFacts
    leaf5436LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5436CoverageChecked :
    coverageCheck (innerAD leaf5436Box) leaf5436InnerLog = true := by
  rfl'

private theorem leaf5436InnerLogValid :
    leaf5436InnerLog.Valid 8 (innerAD leaf5436Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf5436CoverageChecked

private noncomputable def leaf5436InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814731/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5436InputLogOnePlusV_eq :
    leaf5436InputLogOnePlusV = outerEnclosure 24
      (leaf5436Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5436RoundedFacts : LeafRoundedFacts 8
    leaf5436Certificate.logOnePlusV leaf5436InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5436InputLogOnePlusV_eq }

private noncomputable def leaf5436Inputs : Inputs :=
  inputsOfCaches globalInput sk234RoundedInputs
    chi289InputQChi innerPair256Input
    leaf5436InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5436LowerChecked :
    lowerCheck 24 leaf5436Box leaf5436Inputs = true := by
  rfl'

private theorem leaf5436CoversExact : CoversExact 8
    leaf5436Box leaf5436Certificate leaf5436InnerLog leaf5436Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk234RoundedFacts chi289RoundedFacts
    innerPair256RoundedFacts leaf5436RoundedFacts (by rfl)

private theorem leaf5436FlatSound : Sound leaf5436Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5436CertificateValid
    leaf5436InnerLogValid leaf5436CoversExact leaf5436LowerChecked

private noncomputable def leaf5437Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (249/64), chiLo := (81/256), chiHi := (41/128) }

private noncomputable def leaf5437Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742485/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714249728) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2390115213/2147483648) }, upper := { exponent := 1, mantissa := (18401/16384) } }, logOuter := sk233LogOuterCertificate, logK := sk233LogKCertificate, logChi := chi290LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431662079/137428499456) } }, logDArg := sk233LogDArgCertificate }

private noncomputable def leaf5437InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf5437LocalValidity :
    LeafFacts leaf5437Box leaf5437Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5437Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714249728) }) = true
      norm_num [leaf5437Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5437CertificateValid :
    WideCertificateValid leaf5437Box leaf5437Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk233ValidityFacts chi290ValidityFacts
    leaf5437LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5437CoverageChecked :
    coverageCheck (innerAD leaf5437Box) leaf5437InnerLog = true := by
  rfl'

private theorem leaf5437InnerLogValid :
    leaf5437InnerLog.Valid 8 (innerAD leaf5437Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf5437CoverageChecked

private noncomputable def leaf5437InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629467/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5437InputLogOnePlusV_eq :
    leaf5437InputLogOnePlusV = outerEnclosure 24
      (leaf5437Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5437RoundedFacts : LeafRoundedFacts 8
    leaf5437Certificate.logOnePlusV leaf5437InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5437InputLogOnePlusV_eq }

private noncomputable def leaf5437Inputs : Inputs :=
  inputsOfCaches globalInput sk233RoundedInputs
    chi290InputQChi innerPair256Input
    leaf5437InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5437LowerChecked :
    lowerCheck 24 leaf5437Box leaf5437Inputs = true := by
  rfl'

private theorem leaf5437CoversExact : CoversExact 8
    leaf5437Box leaf5437Certificate leaf5437InnerLog leaf5437Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk233RoundedFacts chi290RoundedFacts
    innerPair256RoundedFacts leaf5437RoundedFacts (by rfl)

private theorem leaf5437FlatSound : Sound leaf5437Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5437CertificateValid
    leaf5437InnerLogValid leaf5437CoversExact leaf5437LowerChecked

private noncomputable def leaf5438Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (249/64), kHi := (125/32), chiLo := (81/256), chiHi := (41/128) }

private noncomputable def leaf5438Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742487/1073741824) }, vSqrt := { lower := (8191/8192), upper := (7635268039/7634914304) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2395423303/2147483648) }, upper := { exponent := 1, mantissa := (9221/8192) } }, logOuter := sk234LogOuterCertificate, logK := sk234LogKCertificate, logChi := chi290LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (15270182343/15269828608) } }, logDArg := sk234LogDArgCertificate }

private noncomputable def leaf5438InnerLog : WideLogData :=
  innerPair300Data

set_option maxRecDepth 1000000 in
private theorem leaf5438LocalValidity :
    LeafFacts leaf5438Box leaf5438Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5438Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (7635268039/7634914304) }) = true
      norm_num [leaf5438Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5438CertificateValid :
    WideCertificateValid leaf5438Box leaf5438Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk234ValidityFacts chi290ValidityFacts
    leaf5438LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5438CoverageChecked :
    coverageCheck (innerAD leaf5438Box) leaf5438InnerLog = true := by
  rfl'

private theorem leaf5438InnerLogValid :
    leaf5438InnerLog.Valid 8 (innerAD leaf5438Box) :=
  wideLogDataValid_of_cachedCheck endpoint80PositiveFacts
    endpoint292PositiveFacts.valid leaf5438CoverageChecked

private noncomputable def leaf5438InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629469/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5438InputLogOnePlusV_eq :
    leaf5438InputLogOnePlusV = outerEnclosure 24
      (leaf5438Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5438RoundedFacts : LeafRoundedFacts 8
    leaf5438Certificate.logOnePlusV leaf5438InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5438InputLogOnePlusV_eq }

private noncomputable def leaf5438Inputs : Inputs :=
  inputsOfCaches globalInput sk234RoundedInputs
    chi290InputQChi innerPair300Input
    leaf5438InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5438LowerChecked :
    lowerCheck 24 leaf5438Box leaf5438Inputs = true := by
  rfl'

private theorem leaf5438CoversExact : CoversExact 8
    leaf5438Box leaf5438Certificate leaf5438InnerLog leaf5438Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk234RoundedFacts chi290RoundedFacts
    innerPair300RoundedFacts leaf5438RoundedFacts (by rfl)

private theorem leaf5438FlatSound : Sound leaf5438Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5438CertificateValid
    leaf5438InnerLogValid leaf5438CoversExact leaf5438LowerChecked

private noncomputable def leaf5439Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (251/64), chiLo := (5/16), chiHi := (81/256) }

private noncomputable def leaf5439Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742487/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714272000) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2384348395/2147483648) }, upper := { exponent := 1, mantissa := (36715/32768) } }, logOuter := sk235LogOuterCertificate, logK := sk235LogKCertificate, logChi := chi289LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431684351/137428544000) } }, logDArg := sk235LogDArgCertificate }

private noncomputable def leaf5439InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf5439LocalValidity :
    LeafFacts leaf5439Box leaf5439Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5439Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714272000) }) = true
      norm_num [leaf5439Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5439CertificateValid :
    WideCertificateValid leaf5439Box leaf5439Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk235ValidityFacts chi289ValidityFacts
    leaf5439LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5439CoverageChecked :
    coverageCheck (innerAD leaf5439Box) leaf5439InnerLog = true := by
  rfl'

private theorem leaf5439InnerLogValid :
    leaf5439InnerLog.Valid 8 (innerAD leaf5439Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf5439CoverageChecked

private noncomputable def leaf5439InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453683/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf5439InputLogOnePlusV_eq :
    leaf5439InputLogOnePlusV = outerEnclosure 24
      (leaf5439Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5439RoundedFacts : LeafRoundedFacts 8
    leaf5439Certificate.logOnePlusV leaf5439InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5439InputLogOnePlusV_eq }

private noncomputable def leaf5439Inputs : Inputs :=
  inputsOfCaches globalInput sk235RoundedInputs
    chi289InputQChi innerPair256Input
    leaf5439InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5439LowerChecked :
    lowerCheck 24 leaf5439Box leaf5439Inputs = true := by
  rfl'

private theorem leaf5439CoversExact : CoversExact 8
    leaf5439Box leaf5439Certificate leaf5439InnerLog leaf5439Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk235RoundedFacts chi289RoundedFacts
    innerPair256RoundedFacts leaf5439RoundedFacts (by rfl)

private theorem leaf5439FlatSound : Sound leaf5439Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5439CertificateValid
    leaf5439InnerLogValid leaf5439CoversExact leaf5439LowerChecked

private noncomputable def leaf5440Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (63/16), chiLo := (5/16), chiHi := (81/256) }

private noncomputable def leaf5440Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742489/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714251264) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2389590953/2147483648) }, upper := { exponent := 1, mantissa := (9199/8192) } }, logOuter := sk236LogOuterCertificate, logK := sk236LogKCertificate, logChi := chi289LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431663615/137428502528) } }, logDArg := sk236LogDArgCertificate }

private noncomputable def leaf5440InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf5440LocalValidity :
    LeafFacts leaf5440Box leaf5440Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5440Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714251264) }) = true
      norm_num [leaf5440Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5440CertificateValid :
    WideCertificateValid leaf5440Box leaf5440Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk236ValidityFacts chi289ValidityFacts
    leaf5440LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5440CoverageChecked :
    coverageCheck (innerAD leaf5440Box) leaf5440InnerLog = true := by
  rfl'

private theorem leaf5440InnerLogValid :
    leaf5440InnerLog.Valid 8 (innerAD leaf5440Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf5440CoverageChecked

private noncomputable def leaf5440InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629467/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5440InputLogOnePlusV_eq :
    leaf5440InputLogOnePlusV = outerEnclosure 24
      (leaf5440Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5440RoundedFacts : LeafRoundedFacts 8
    leaf5440Certificate.logOnePlusV leaf5440InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5440InputLogOnePlusV_eq }

private noncomputable def leaf5440Inputs : Inputs :=
  inputsOfCaches globalInput sk236RoundedInputs
    chi289InputQChi innerPair256Input
    leaf5440InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5440LowerChecked :
    lowerCheck 24 leaf5440Box leaf5440Inputs = true := by
  rfl'

private theorem leaf5440CoversExact : CoversExact 8
    leaf5440Box leaf5440Certificate leaf5440InnerLog leaf5440Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk236RoundedFacts chi289RoundedFacts
    innerPair256RoundedFacts leaf5440RoundedFacts (by rfl)

private theorem leaf5440FlatSound : Sound leaf5440Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5440CertificateValid
    leaf5440InnerLogValid leaf5440CoversExact leaf5440LowerChecked

private noncomputable def leaf5441Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (251/64), chiLo := (81/256), chiHi := (41/128) }

private noncomputable def leaf5441Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742489/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9816773193/9816315392) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2400731393/2147483648) }, upper := { exponent := 1, mantissa := (18483/16384) } }, logOuter := sk235LogOuterCertificate, logK := sk235LogKCertificate, logChi := chi290LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (19633088585/19632630784) } }, logDArg := sk235LogDArgCertificate }

private noncomputable def leaf5441InnerLog : WideLogData :=
  innerPair621Data

set_option maxRecDepth 1000000 in
private theorem leaf5441LocalValidity :
    LeafFacts leaf5441Box leaf5441Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5441Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9816773193/9816315392) }) = true
      norm_num [leaf5441Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5441CertificateValid :
    WideCertificateValid leaf5441Box leaf5441Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk235ValidityFacts chi290ValidityFacts
    leaf5441LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5441CoverageChecked :
    coverageCheck (innerAD leaf5441Box) leaf5441InnerLog = true := by
  rfl'

private theorem leaf5441InnerLogValid :
    leaf5441InnerLog.Valid 8 (innerAD leaf5441Box) :=
  wideLogDataValid_of_cachedCheck endpoint347PositiveFacts
    endpoint292PositiveFacts.valid leaf5441CoverageChecked

private noncomputable def leaf5441InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (363421/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf5441InputLogOnePlusV_eq :
    leaf5441InputLogOnePlusV = outerEnclosure 24
      (leaf5441Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5441RoundedFacts : LeafRoundedFacts 8
    leaf5441Certificate.logOnePlusV leaf5441InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5441InputLogOnePlusV_eq }

private noncomputable def leaf5441Inputs : Inputs :=
  inputsOfCaches globalInput sk235RoundedInputs
    chi290InputQChi innerPair621Input
    leaf5441InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5441LowerChecked :
    lowerCheck 24 leaf5441Box leaf5441Inputs = true := by
  rfl'

private theorem leaf5441CoversExact : CoversExact 8
    leaf5441Box leaf5441Certificate leaf5441InnerLog leaf5441Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk235RoundedFacts chi290RoundedFacts
    innerPair621RoundedFacts leaf5441RoundedFacts (by rfl)

private theorem leaf5441FlatSound : Sound leaf5441Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5441CertificateValid
    leaf5441InnerLogValid leaf5441CoversExact leaf5441LowerChecked

private noncomputable def leaf5442Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (63/16), chiLo := (81/256), chiHi := (41/128) }

private noncomputable def leaf5442Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742491/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714186752) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2406039483/2147483648) }, upper := { exponent := 1, mantissa := (4631/4096) } }, logOuter := sk236LogOuterCertificate, logK := sk236LogKCertificate, logChi := chi290LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431599103/137428373504) } }, logDArg := sk236LogDArgCertificate }

private noncomputable def leaf5442InnerLog : WideLogData :=
  innerPair621Data

set_option maxRecDepth 1000000 in
private theorem leaf5442LocalValidity :
    LeafFacts leaf5442Box leaf5442Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5442Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714186752) }) = true
      norm_num [leaf5442Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5442CertificateValid :
    WideCertificateValid leaf5442Box leaf5442Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk236ValidityFacts chi290ValidityFacts
    leaf5442LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5442CoverageChecked :
    coverageCheck (innerAD leaf5442Box) leaf5442InnerLog = true := by
  rfl'

private theorem leaf5442InnerLogValid :
    leaf5442InnerLog.Valid 8 (innerAD leaf5442Box) :=
  wideLogDataValid_of_cachedCheck endpoint347PositiveFacts
    endpoint292PositiveFacts.valid leaf5442CoverageChecked

private noncomputable def leaf5442InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629475/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5442InputLogOnePlusV_eq :
    leaf5442InputLogOnePlusV = outerEnclosure 24
      (leaf5442Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5442RoundedFacts : LeafRoundedFacts 8
    leaf5442Certificate.logOnePlusV leaf5442InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5442InputLogOnePlusV_eq }

private noncomputable def leaf5442Inputs : Inputs :=
  inputsOfCaches globalInput sk236RoundedInputs
    chi290InputQChi innerPair621Input
    leaf5442InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5442LowerChecked :
    lowerCheck 24 leaf5442Box leaf5442Inputs = true := by
  rfl'

private theorem leaf5442CoversExact : CoversExact 8
    leaf5442Box leaf5442Certificate leaf5442InnerLog leaf5442Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk236RoundedFacts chi290RoundedFacts
    innerPair621RoundedFacts leaf5442RoundedFacts (by rfl)

private theorem leaf5442FlatSound : Sound leaf5442Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5442CertificateValid
    leaf5442InnerLogValid leaf5442CoversExact leaf5442LowerChecked

private noncomputable def leaf5443Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (249/64), chiLo := (41/128), chiHi := (83/256) }

private noncomputable def leaf5443Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742487/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714185984) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2406367147/2147483648) }, upper := { exponent := 1, mantissa := (37051/32768) } }, logOuter := sk233LogOuterCertificate, logK := sk233LogKCertificate, logChi := chi291LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431598335/137428371968) } }, logDArg := sk233LogDArgCertificate }

private noncomputable def leaf5443InnerLog : WideLogData :=
  innerPair257Data

set_option maxRecDepth 1000000 in
private theorem leaf5443LocalValidity :
    LeafFacts leaf5443Box leaf5443Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5443Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714185984) }) = true
      norm_num [leaf5443Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5443CertificateValid :
    WideCertificateValid leaf5443Box leaf5443Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk233ValidityFacts chi291ValidityFacts
    leaf5443LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5443CoverageChecked :
    coverageCheck (innerAD leaf5443Box) leaf5443InnerLog = true := by
  rfl'

private theorem leaf5443InnerLogValid :
    leaf5443InnerLog.Valid 8 (innerAD leaf5443Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint76PositiveFacts.valid leaf5443CoverageChecked

private noncomputable def leaf5443InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629475/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5443InputLogOnePlusV_eq :
    leaf5443InputLogOnePlusV = outerEnclosure 24
      (leaf5443Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5443RoundedFacts : LeafRoundedFacts 8
    leaf5443Certificate.logOnePlusV leaf5443InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5443InputLogOnePlusV_eq }

private noncomputable def leaf5443Inputs : Inputs :=
  inputsOfCaches globalInput sk233RoundedInputs
    chi291InputQChi innerPair257Input
    leaf5443InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5443LowerChecked :
    lowerCheck 24 leaf5443Box leaf5443Inputs = true := by
  rfl'

private theorem leaf5443CoversExact : CoversExact 8
    leaf5443Box leaf5443Certificate leaf5443InnerLog leaf5443Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk233RoundedFacts chi291RoundedFacts
    innerPair257RoundedFacts leaf5443RoundedFacts (by rfl)

private theorem leaf5443FlatSound : Sound leaf5443Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5443CertificateValid
    leaf5443InnerLogValid leaf5443CoversExact leaf5443LowerChecked

private noncomputable def leaf5444Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (249/64), kHi := (125/32), chiLo := (41/128), chiHi := (83/256) }

private noncomputable def leaf5444Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742489/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9816773193/9816309248) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2411740769/2147483648) }, upper := { exponent := 1, mantissa := (18567/16384) } }, logOuter := sk234LogOuterCertificate, logK := sk234LogKCertificate, logChi := chi291LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (19633082441/19632618496) } }, logDArg := sk234LogDArgCertificate }

private noncomputable def leaf5444InnerLog : WideLogData :=
  innerPair257Data

set_option maxRecDepth 1000000 in
private theorem leaf5444LocalValidity :
    LeafFacts leaf5444Box leaf5444Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5444Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9816773193/9816309248) }) = true
      norm_num [leaf5444Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5444CertificateValid :
    WideCertificateValid leaf5444Box leaf5444Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk234ValidityFacts chi291ValidityFacts
    leaf5444LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5444CoverageChecked :
    coverageCheck (innerAD leaf5444Box) leaf5444InnerLog = true := by
  rfl'

private theorem leaf5444InnerLogValid :
    leaf5444InnerLog.Valid 8 (innerAD leaf5444Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint76PositiveFacts.valid leaf5444CoverageChecked

private noncomputable def leaf5444InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629477/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5444InputLogOnePlusV_eq :
    leaf5444InputLogOnePlusV = outerEnclosure 24
      (leaf5444Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5444RoundedFacts : LeafRoundedFacts 8
    leaf5444Certificate.logOnePlusV leaf5444InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5444InputLogOnePlusV_eq }

private noncomputable def leaf5444Inputs : Inputs :=
  inputsOfCaches globalInput sk234RoundedInputs
    chi291InputQChi innerPair257Input
    leaf5444InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5444LowerChecked :
    lowerCheck 24 leaf5444Box leaf5444Inputs = true := by
  rfl'

private theorem leaf5444CoversExact : CoversExact 8
    leaf5444Box leaf5444Certificate leaf5444InnerLog leaf5444Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk234RoundedFacts chi291RoundedFacts
    innerPair257RoundedFacts leaf5444RoundedFacts (by rfl)

private theorem leaf5444FlatSound : Sound leaf5444Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5444CertificateValid
    leaf5444InnerLogValid leaf5444CoversExact leaf5444LowerChecked

private noncomputable def leaf5445Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (249/64), chiLo := (83/256), chiHi := (21/64) }

private noncomputable def leaf5445Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742489/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714122240) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2422619081/2147483648) }, upper := { exponent := 1, mantissa := (9325/8192) } }, logOuter := sk233LogOuterCertificate, logK := sk233LogKCertificate, logChi := chi292LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431534591/137428244480) } }, logDArg := sk233LogDArgCertificate }

private noncomputable def leaf5445InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf5445LocalValidity :
    LeafFacts leaf5445Box leaf5445Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5445Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714122240) }) = true
      norm_num [leaf5445Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5445CertificateValid :
    WideCertificateValid leaf5445Box leaf5445Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk233ValidityFacts chi292ValidityFacts
    leaf5445LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5445CoverageChecked :
    coverageCheck (innerAD leaf5445Box) leaf5445InnerLog = true := by
  rfl'

private theorem leaf5445InnerLogValid :
    leaf5445InnerLog.Valid 8 (innerAD leaf5445Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf5445CoverageChecked

private noncomputable def leaf5445InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814741/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5445InputLogOnePlusV_eq :
    leaf5445InputLogOnePlusV = outerEnclosure 24
      (leaf5445Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5445RoundedFacts : LeafRoundedFacts 8
    leaf5445Certificate.logOnePlusV leaf5445InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5445InputLogOnePlusV_eq }

private noncomputable def leaf5445Inputs : Inputs :=
  inputsOfCaches globalInput sk233RoundedInputs
    chi292InputQChi innerPair264Input
    leaf5445InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5445LowerChecked :
    lowerCheck 24 leaf5445Box leaf5445Inputs = true := by
  rfl'

private theorem leaf5445CoversExact : CoversExact 8
    leaf5445Box leaf5445Certificate leaf5445InnerLog leaf5445Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk233RoundedFacts chi292RoundedFacts
    innerPair264RoundedFacts leaf5445RoundedFacts (by rfl)

private theorem leaf5445FlatSound : Sound leaf5445Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5445CertificateValid
    leaf5445InnerLogValid leaf5445CoversExact leaf5445LowerChecked

private noncomputable def leaf5446Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (249/64), kHi := (125/32), chiLo := (83/256), chiHi := (21/64) }

private noncomputable def leaf5446Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742491/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714100736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2428058235/2147483648) }, upper := { exponent := 1, mantissa := (4673/4096) } }, logOuter := sk234LogOuterCertificate, logK := sk234LogKCertificate, logChi := chi292LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431513087/137428201472) } }, logDArg := sk234LogDArgCertificate }

private noncomputable def leaf5446InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf5446LocalValidity :
    LeafFacts leaf5446Box leaf5446Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5446Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714100736) }) = true
      norm_num [leaf5446Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5446CertificateValid :
    WideCertificateValid leaf5446Box leaf5446Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk234ValidityFacts chi292ValidityFacts
    leaf5446LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5446CoverageChecked :
    coverageCheck (innerAD leaf5446Box) leaf5446InnerLog = true := by
  rfl'

private theorem leaf5446InnerLogValid :
    leaf5446InnerLog.Valid 8 (innerAD leaf5446Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf5446CoverageChecked

private noncomputable def leaf5446InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629485/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5446InputLogOnePlusV_eq :
    leaf5446InputLogOnePlusV = outerEnclosure 24
      (leaf5446Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5446RoundedFacts : LeafRoundedFacts 8
    leaf5446Certificate.logOnePlusV leaf5446InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5446InputLogOnePlusV_eq }

private noncomputable def leaf5446Inputs : Inputs :=
  inputsOfCaches globalInput sk234RoundedInputs
    chi292InputQChi innerPair264Input
    leaf5446InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5446LowerChecked :
    lowerCheck 24 leaf5446Box leaf5446Inputs = true := by
  rfl'

private theorem leaf5446CoversExact : CoversExact 8
    leaf5446Box leaf5446Certificate leaf5446InnerLog leaf5446Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk234RoundedFacts chi292RoundedFacts
    innerPair264RoundedFacts leaf5446RoundedFacts (by rfl)

private theorem leaf5446FlatSound : Sound leaf5446Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5446CertificateValid
    leaf5446InnerLogValid leaf5446CoversExact leaf5446LowerChecked

private noncomputable def leaf5447Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (251/64), chiLo := (41/128), chiHi := (83/256) }

private noncomputable def leaf5447Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742491/1073741824) }, vSqrt := { lower := (8191/8192), upper := (7635268039/7634904832) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2417114391/2147483648) }, upper := { exponent := 1, mantissa := (37217/32768) } }, logOuter := sk235LogOuterCertificate, logK := sk235LogKCertificate, logChi := chi291LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (15270172871/15269809664) } }, logDArg := sk235LogDArgCertificate }

private noncomputable def leaf5447InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf5447LocalValidity :
    LeafFacts leaf5447Box leaf5447Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5447Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (7635268039/7634904832) }) = true
      norm_num [leaf5447Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5447CertificateValid :
    WideCertificateValid leaf5447Box leaf5447Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk235ValidityFacts chi291ValidityFacts
    leaf5447LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5447CoverageChecked :
    coverageCheck (innerAD leaf5447Box) leaf5447InnerLog = true := by
  rfl'

private theorem leaf5447InnerLogValid :
    leaf5447InnerLog.Valid 8 (innerAD leaf5447Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf5447CoverageChecked

private noncomputable def leaf5447InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453685/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf5447InputLogOnePlusV_eq :
    leaf5447InputLogOnePlusV = outerEnclosure 24
      (leaf5447Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5447RoundedFacts : LeafRoundedFacts 8
    leaf5447Certificate.logOnePlusV leaf5447InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5447InputLogOnePlusV_eq }

private noncomputable def leaf5447Inputs : Inputs :=
  inputsOfCaches globalInput sk235RoundedInputs
    chi291InputQChi innerPair264Input
    leaf5447InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5447LowerChecked :
    lowerCheck 24 leaf5447Box leaf5447Inputs = true := by
  rfl'

private theorem leaf5447CoversExact : CoversExact 8
    leaf5447Box leaf5447Certificate leaf5447InnerLog leaf5447Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk235RoundedFacts chi291RoundedFacts
    innerPair264RoundedFacts leaf5447RoundedFacts (by rfl)

private theorem leaf5447FlatSound : Sound leaf5447Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5447CertificateValid
    leaf5447InnerLogValid leaf5447CoversExact leaf5447LowerChecked

private noncomputable def leaf5448Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (63/16), chiLo := (41/128), chiHi := (83/256) }

private noncomputable def leaf5448Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742493/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714122240) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2422488013/2147483648) }, upper := { exponent := 1, mantissa := (9325/8192) } }, logOuter := sk236LogOuterCertificate, logK := sk236LogKCertificate, logChi := chi291LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431534591/137428244480) } }, logDArg := sk236LogDArgCertificate }

private noncomputable def leaf5448InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf5448LocalValidity :
    LeafFacts leaf5448Box leaf5448Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5448Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714122240) }) = true
      norm_num [leaf5448Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5448CertificateValid :
    WideCertificateValid leaf5448Box leaf5448Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk236ValidityFacts chi291ValidityFacts
    leaf5448LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5448CoverageChecked :
    coverageCheck (innerAD leaf5448Box) leaf5448InnerLog = true := by
  rfl'

private theorem leaf5448InnerLogValid :
    leaf5448InnerLog.Valid 8 (innerAD leaf5448Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf5448CoverageChecked

private noncomputable def leaf5448InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814741/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5448InputLogOnePlusV_eq :
    leaf5448InputLogOnePlusV = outerEnclosure 24
      (leaf5448Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5448RoundedFacts : LeafRoundedFacts 8
    leaf5448Certificate.logOnePlusV leaf5448InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5448InputLogOnePlusV_eq }

private noncomputable def leaf5448Inputs : Inputs :=
  inputsOfCaches globalInput sk236RoundedInputs
    chi291InputQChi innerPair264Input
    leaf5448InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5448LowerChecked :
    lowerCheck 24 leaf5448Box leaf5448Inputs = true := by
  rfl'

private theorem leaf5448CoversExact : CoversExact 8
    leaf5448Box leaf5448Certificate leaf5448InnerLog leaf5448Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk236RoundedFacts chi291RoundedFacts
    innerPair264RoundedFacts leaf5448RoundedFacts (by rfl)

private theorem leaf5448FlatSound : Sound leaf5448Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5448CertificateValid
    leaf5448InnerLogValid leaf5448CoversExact leaf5448LowerChecked

private noncomputable def leaf5449Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (251/64), chiLo := (83/256), chiHi := (21/64) }

private noncomputable def leaf5449Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742493/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714079232) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2433497389/2147483648) }, upper := { exponent := 1, mantissa := (9367/8192) } }, logOuter := sk235LogOuterCertificate, logK := sk235LogKCertificate, logChi := chi292LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431491583/137428158464) } }, logDArg := sk235LogDArgCertificate }

private noncomputable def leaf5449InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf5449LocalValidity :
    LeafFacts leaf5449Box leaf5449Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5449Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714079232) }) = true
      norm_num [leaf5449Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5449CertificateValid :
    WideCertificateValid leaf5449Box leaf5449Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk235ValidityFacts chi292ValidityFacts
    leaf5449LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5449CoverageChecked :
    coverageCheck (innerAD leaf5449Box) leaf5449InnerLog = true := by
  rfl'

private theorem leaf5449InnerLogValid :
    leaf5449InnerLog.Valid 8 (innerAD leaf5449Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf5449CoverageChecked

private noncomputable def leaf5449InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726843/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf5449InputLogOnePlusV_eq :
    leaf5449InputLogOnePlusV = outerEnclosure 24
      (leaf5449Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5449RoundedFacts : LeafRoundedFacts 8
    leaf5449Certificate.logOnePlusV leaf5449InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5449InputLogOnePlusV_eq }

private noncomputable def leaf5449Inputs : Inputs :=
  inputsOfCaches globalInput sk235RoundedInputs
    chi292InputQChi innerPair264Input
    leaf5449InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5449LowerChecked :
    lowerCheck 24 leaf5449Box leaf5449Inputs = true := by
  rfl'

private theorem leaf5449CoversExact : CoversExact 8
    leaf5449Box leaf5449Certificate leaf5449InnerLog leaf5449Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk235RoundedFacts chi292RoundedFacts
    innerPair264RoundedFacts leaf5449RoundedFacts (by rfl)

private theorem leaf5449FlatSound : Sound leaf5449Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5449CertificateValid
    leaf5449InnerLogValid leaf5449CoversExact leaf5449LowerChecked

private noncomputable def leaf5450Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (63/16), chiLo := (83/256), chiHi := (21/64) }

private noncomputable def leaf5450Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742495/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714057728) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2438936543/2147483648) }, upper := { exponent := 1, mantissa := (2347/2048) } }, logOuter := sk236LogOuterCertificate, logK := sk236LogKCertificate, logChi := chi292LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431470079/137428115456) } }, logDArg := sk236LogDArgCertificate }

private noncomputable def leaf5450InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf5450LocalValidity :
    LeafFacts leaf5450Box leaf5450Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5450Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714057728) }) = true
      norm_num [leaf5450Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5450CertificateValid :
    WideCertificateValid leaf5450Box leaf5450Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk236ValidityFacts chi292ValidityFacts
    leaf5450LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5450CoverageChecked :
    coverageCheck (innerAD leaf5450Box) leaf5450InnerLog = true := by
  rfl'

private theorem leaf5450InnerLogValid :
    leaf5450InnerLog.Valid 8 (innerAD leaf5450Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf5450CoverageChecked

private noncomputable def leaf5450InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814745/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5450InputLogOnePlusV_eq :
    leaf5450InputLogOnePlusV = outerEnclosure 24
      (leaf5450Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5450RoundedFacts : LeafRoundedFacts 8
    leaf5450Certificate.logOnePlusV leaf5450InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5450InputLogOnePlusV_eq }

private noncomputable def leaf5450Inputs : Inputs :=
  inputsOfCaches globalInput sk236RoundedInputs
    chi292InputQChi innerPair264Input
    leaf5450InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5450LowerChecked :
    lowerCheck 24 leaf5450Box leaf5450Inputs = true := by
  rfl'

private theorem leaf5450CoversExact : CoversExact 8
    leaf5450Box leaf5450Certificate leaf5450InnerLog leaf5450Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk236RoundedFacts chi292RoundedFacts
    innerPair264RoundedFacts leaf5450RoundedFacts (by rfl)

private theorem leaf5450FlatSound : Sound leaf5450Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5450CertificateValid
    leaf5450InnerLogValid leaf5450CoversExact leaf5450LowerChecked

private noncomputable def leaf5451Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (5/16), chiHi := (81/256) }

private noncomputable def leaf5451Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742491/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714230528) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2394833511/2147483648) }, upper := { exponent := 1, mantissa := (36877/32768) } }, logOuter := sk237LogOuterCertificate, logK := sk237LogKCertificate, logChi := chi289LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431642879/137428461056) } }, logDArg := sk237LogDArgCertificate }

private noncomputable def leaf5451InnerLog : WideLogData :=
  innerPair300Data

set_option maxRecDepth 1000000 in
private theorem leaf5451LocalValidity :
    LeafFacts leaf5451Box leaf5451Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5451Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714230528) }) = true
      norm_num [leaf5451Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5451CertificateValid :
    WideCertificateValid leaf5451Box leaf5451Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk237ValidityFacts chi289ValidityFacts
    leaf5451LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5451CoverageChecked :
    coverageCheck (innerAD leaf5451Box) leaf5451InnerLog = true := by
  rfl'

private theorem leaf5451InnerLogValid :
    leaf5451InnerLog.Valid 8 (innerAD leaf5451Box) :=
  wideLogDataValid_of_cachedCheck endpoint80PositiveFacts
    endpoint292PositiveFacts.valid leaf5451CoverageChecked

private noncomputable def leaf5451InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629469/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5451InputLogOnePlusV_eq :
    leaf5451InputLogOnePlusV = outerEnclosure 24
      (leaf5451Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5451RoundedFacts : LeafRoundedFacts 8
    leaf5451Certificate.logOnePlusV leaf5451InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5451InputLogOnePlusV_eq }

private noncomputable def leaf5451Inputs : Inputs :=
  inputsOfCaches globalInput sk237RoundedInputs
    chi289InputQChi innerPair300Input
    leaf5451InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5451LowerChecked :
    lowerCheck 24 leaf5451Box leaf5451Inputs = true := by
  rfl'

private theorem leaf5451CoversExact : CoversExact 8
    leaf5451Box leaf5451Certificate leaf5451InnerLog leaf5451Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk237RoundedFacts chi289RoundedFacts
    innerPair300RoundedFacts leaf5451RoundedFacts (by rfl)

private theorem leaf5451FlatSound : Sound leaf5451Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5451CertificateValid
    leaf5451InnerLogValid leaf5451CoversExact leaf5451LowerChecked

private noncomputable def leaf5452Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (5/16), chiHi := (81/256) }

private noncomputable def leaf5452Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742493/1073741824) }, vSqrt := { lower := (8191/8192), upper := (455082201/455060992) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2400076069/2147483648) }, upper := { exponent := 1, mantissa := (18479/16384) } }, logOuter := sk238LogOuterCertificate, logK := sk238LogKCertificate, logChi := chi289LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (910143193/910121984) } }, logDArg := sk238LogDArgCertificate }

private noncomputable def leaf5452InnerLog : WideLogData :=
  innerPair621Data

set_option maxRecDepth 1000000 in
private theorem leaf5452LocalValidity :
    LeafFacts leaf5452Box leaf5452Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5452Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (455082201/455060992) }) = true
      norm_num [leaf5452Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5452CertificateValid :
    WideCertificateValid leaf5452Box leaf5452Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk238ValidityFacts chi289ValidityFacts
    leaf5452LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5452CoverageChecked :
    coverageCheck (innerAD leaf5452Box) leaf5452InnerLog = true := by
  rfl'

private theorem leaf5452InnerLogValid :
    leaf5452InnerLog.Valid 8 (innerAD leaf5452Box) :=
  wideLogDataValid_of_cachedCheck endpoint347PositiveFacts
    endpoint292PositiveFacts.valid leaf5452CoverageChecked

private noncomputable def leaf5452InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (363421/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf5452InputLogOnePlusV_eq :
    leaf5452InputLogOnePlusV = outerEnclosure 24
      (leaf5452Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5452RoundedFacts : LeafRoundedFacts 8
    leaf5452Certificate.logOnePlusV leaf5452InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5452InputLogOnePlusV_eq }

private noncomputable def leaf5452Inputs : Inputs :=
  inputsOfCaches globalInput sk238RoundedInputs
    chi289InputQChi innerPair621Input
    leaf5452InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5452LowerChecked :
    lowerCheck 24 leaf5452Box leaf5452Inputs = true := by
  rfl'

private theorem leaf5452CoversExact : CoversExact 8
    leaf5452Box leaf5452Certificate leaf5452InnerLog leaf5452Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk238RoundedFacts chi289RoundedFacts
    innerPair621RoundedFacts leaf5452RoundedFacts (by rfl)

private theorem leaf5452FlatSound : Sound leaf5452Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5452CertificateValid
    leaf5452InnerLogValid leaf5452CoversExact leaf5452LowerChecked

private noncomputable def leaf5453Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (81/256), chiHi := (41/128) }

private noncomputable def leaf5453Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742493/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22905804117/22904721920) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2411347573/2147483648) }, upper := { exponent := 1, mantissa := (18565/16384) } }, logOuter := sk237LogOuterCertificate, logK := sk237LogKCertificate, logChi := chi290LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45810526037/45809443840) } }, logDArg := sk237LogDArgCertificate }

private noncomputable def leaf5453InnerLog : WideLogData :=
  innerPair257Data

set_option maxRecDepth 1000000 in
private theorem leaf5453LocalValidity :
    LeafFacts leaf5453Box leaf5453Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5453Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22905804117/22904721920) }) = true
      norm_num [leaf5453Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5453CertificateValid :
    WideCertificateValid leaf5453Box leaf5453Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk237ValidityFacts chi290ValidityFacts
    leaf5453LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5453CoverageChecked :
    coverageCheck (innerAD leaf5453Box) leaf5453InnerLog = true := by
  rfl'

private theorem leaf5453InnerLogValid :
    leaf5453InnerLog.Valid 8 (innerAD leaf5453Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint76PositiveFacts.valid leaf5453CoverageChecked

private noncomputable def leaf5453InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629477/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5453InputLogOnePlusV_eq :
    leaf5453InputLogOnePlusV = outerEnclosure 24
      (leaf5453Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5453RoundedFacts : LeafRoundedFacts 8
    leaf5453Certificate.logOnePlusV leaf5453InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5453InputLogOnePlusV_eq }

private noncomputable def leaf5453Inputs : Inputs :=
  inputsOfCaches globalInput sk237RoundedInputs
    chi290InputQChi innerPair257Input
    leaf5453InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5453LowerChecked :
    lowerCheck 24 leaf5453Box leaf5453Inputs = true := by
  rfl'

private theorem leaf5453CoversExact : CoversExact 8
    leaf5453Box leaf5453Certificate leaf5453InnerLog leaf5453Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk237RoundedFacts chi290RoundedFacts
    innerPair257RoundedFacts leaf5453RoundedFacts (by rfl)

private theorem leaf5453FlatSound : Sound leaf5453Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5453CertificateValid
    leaf5453InnerLogValid leaf5453CoversExact leaf5453LowerChecked

private noncomputable def leaf5454Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (81/256), chiHi := (41/128) }

private noncomputable def leaf5454Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742495/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714144768) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2416655663/2147483648) }, upper := { exponent := 1, mantissa := (9303/8192) } }, logOuter := sk238LogOuterCertificate, logK := sk238LogKCertificate, logChi := chi290LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431557119/137428289536) } }, logDArg := sk238LogDArgCertificate }

private noncomputable def leaf5454InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf5454LocalValidity :
    LeafFacts leaf5454Box leaf5454Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5454Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714144768) }) = true
      norm_num [leaf5454Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5454CertificateValid :
    WideCertificateValid leaf5454Box leaf5454Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk238ValidityFacts chi290ValidityFacts
    leaf5454LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5454CoverageChecked :
    coverageCheck (innerAD leaf5454Box) leaf5454InnerLog = true := by
  rfl'

private theorem leaf5454InnerLogValid :
    leaf5454InnerLog.Valid 8 (innerAD leaf5454Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf5454CoverageChecked

private noncomputable def leaf5454InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453685/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf5454InputLogOnePlusV_eq :
    leaf5454InputLogOnePlusV = outerEnclosure 24
      (leaf5454Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5454RoundedFacts : LeafRoundedFacts 8
    leaf5454Certificate.logOnePlusV leaf5454InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5454InputLogOnePlusV_eq }

private noncomputable def leaf5454Inputs : Inputs :=
  inputsOfCaches globalInput sk238RoundedInputs
    chi290InputQChi innerPair264Input
    leaf5454InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5454LowerChecked :
    lowerCheck 24 leaf5454Box leaf5454Inputs = true := by
  rfl'

private theorem leaf5454CoversExact : CoversExact 8
    leaf5454Box leaf5454Certificate leaf5454InnerLog leaf5454Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk238RoundedFacts chi290RoundedFacts
    innerPair264RoundedFacts leaf5454RoundedFacts (by rfl)

private theorem leaf5454FlatSound : Sound leaf5454Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5454CertificateValid
    leaf5454InnerLogValid leaf5454CoversExact leaf5454LowerChecked

private noncomputable def leaf5455Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (5/16), chiHi := (81/256) }

private noncomputable def leaf5455Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742495/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714189056) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2405318627/2147483648) }, upper := { exponent := 1, mantissa := (37039/32768) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi289LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431601407/137428378112) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf5455InnerLog : WideLogData :=
  innerPair621Data

set_option maxRecDepth 1000000 in
private theorem leaf5455LocalValidity :
    LeafFacts leaf5455Box leaf5455Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5455Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714189056) }) = true
      norm_num [leaf5455Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5455CertificateValid :
    WideCertificateValid leaf5455Box leaf5455Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi289ValidityFacts
    leaf5455LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5455CoverageChecked :
    coverageCheck (innerAD leaf5455Box) leaf5455InnerLog = true := by
  rfl'

private theorem leaf5455InnerLogValid :
    leaf5455InnerLog.Valid 8 (innerAD leaf5455Box) :=
  wideLogDataValid_of_cachedCheck endpoint347PositiveFacts
    endpoint292PositiveFacts.valid leaf5455CoverageChecked

private noncomputable def leaf5455InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814737/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5455InputLogOnePlusV_eq :
    leaf5455InputLogOnePlusV = outerEnclosure 24
      (leaf5455Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5455RoundedFacts : LeafRoundedFacts 8
    leaf5455Certificate.logOnePlusV leaf5455InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5455InputLogOnePlusV_eq }

private noncomputable def leaf5455Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi289InputQChi innerPair621Input
    leaf5455InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5455LowerChecked :
    lowerCheck 24 leaf5455Box leaf5455Inputs = true := by
  rfl'

private theorem leaf5455CoversExact : CoversExact 8
    leaf5455Box leaf5455Certificate leaf5455InnerLog leaf5455Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi289RoundedFacts
    innerPair621RoundedFacts leaf5455RoundedFacts (by rfl)

private theorem leaf5455FlatSound : Sound leaf5455Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5455CertificateValid
    leaf5455InnerLogValid leaf5455CoversExact leaf5455LowerChecked

private noncomputable def leaf5456Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (5/16), chiHi := (81/256) }

private noncomputable def leaf5456Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742497/1073741824) }, vSqrt := { lower := (65527/65536), upper := (9816773193/9816309760) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2410561185/2147483648) }, upper := { exponent := 1, mantissa := (145/128) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi289LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (19633082953/19632619520) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf5456InnerLog : WideLogData :=
  innerPair621Data

set_option maxRecDepth 1000000 in
private theorem leaf5456LocalValidity :
    LeafFacts leaf5456Box leaf5456Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5456Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (9816773193/9816309760) }) = true
      norm_num [leaf5456Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5456CertificateValid :
    WideCertificateValid leaf5456Box leaf5456Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi289ValidityFacts
    leaf5456LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5456CoverageChecked :
    coverageCheck (innerAD leaf5456Box) leaf5456InnerLog = true := by
  rfl'

private theorem leaf5456InnerLogValid :
    leaf5456InnerLog.Valid 8 (innerAD leaf5456Box) :=
  wideLogDataValid_of_cachedCheck endpoint347PositiveFacts
    endpoint292PositiveFacts.valid leaf5456CoverageChecked

private noncomputable def leaf5456InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629477/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5456InputLogOnePlusV_eq :
    leaf5456InputLogOnePlusV = outerEnclosure 24
      (leaf5456Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5456RoundedFacts : LeafRoundedFacts 8
    leaf5456Certificate.logOnePlusV leaf5456InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5456InputLogOnePlusV_eq }

private noncomputable def leaf5456Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi289InputQChi innerPair621Input
    leaf5456InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5456LowerChecked :
    lowerCheck 24 leaf5456Box leaf5456Inputs = true := by
  rfl'

private theorem leaf5456CoversExact : CoversExact 8
    leaf5456Box leaf5456Certificate leaf5456InnerLog leaf5456Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi289RoundedFacts
    innerPair621RoundedFacts leaf5456RoundedFacts (by rfl)

private theorem leaf5456FlatSound : Sound leaf5456Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5456CertificateValid
    leaf5456InnerLogValid leaf5456CoversExact leaf5456LowerChecked

private noncomputable def leaf5457Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (81/256), chiHi := (41/128) }

private noncomputable def leaf5457Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742497/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714123776) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2421963753/2147483648) }, upper := { exponent := 1, mantissa := (18647/16384) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi290LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431536127/137428247552) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf5457InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf5457LocalValidity :
    LeafFacts leaf5457Box leaf5457Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5457Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714123776) }) = true
      norm_num [leaf5457Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5457CertificateValid :
    WideCertificateValid leaf5457Box leaf5457Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi290ValidityFacts
    leaf5457LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5457CoverageChecked :
    coverageCheck (innerAD leaf5457Box) leaf5457InnerLog = true := by
  rfl'

private theorem leaf5457InnerLogValid :
    leaf5457InnerLog.Valid 8 (innerAD leaf5457Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf5457CoverageChecked

private noncomputable def leaf5457InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814741/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5457InputLogOnePlusV_eq :
    leaf5457InputLogOnePlusV = outerEnclosure 24
      (leaf5457Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5457RoundedFacts : LeafRoundedFacts 8
    leaf5457Certificate.logOnePlusV leaf5457InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5457InputLogOnePlusV_eq }

private noncomputable def leaf5457Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi290InputQChi innerPair264Input
    leaf5457InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5457LowerChecked :
    lowerCheck 24 leaf5457Box leaf5457Inputs = true := by
  rfl'

private theorem leaf5457CoversExact : CoversExact 8
    leaf5457Box leaf5457Certificate leaf5457InnerLog leaf5457Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi290RoundedFacts
    innerPair264RoundedFacts leaf5457RoundedFacts (by rfl)

private theorem leaf5457FlatSound : Sound leaf5457Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5457CertificateValid
    leaf5457InnerLogValid leaf5457CoversExact leaf5457LowerChecked

private noncomputable def leaf5458Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (81/256), chiHi := (41/128) }

private noncomputable def leaf5458Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742499/1073741824) }, vSqrt := { lower := (65527/65536), upper := (22905804117/22904700928) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2427271843/2147483648) }, upper := { exponent := 1, mantissa := (73/64) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi290LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (45810505045/45809401856) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf5458InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf5458LocalValidity :
    LeafFacts leaf5458Box leaf5458Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5458Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (22905804117/22904700928) }) = true
      norm_num [leaf5458Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5458CertificateValid :
    WideCertificateValid leaf5458Box leaf5458Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi290ValidityFacts
    leaf5458LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5458CoverageChecked :
    coverageCheck (innerAD leaf5458Box) leaf5458InnerLog = true := by
  rfl'

private theorem leaf5458InnerLogValid :
    leaf5458InnerLog.Valid 8 (innerAD leaf5458Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf5458CoverageChecked

private noncomputable def leaf5458InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629485/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5458InputLogOnePlusV_eq :
    leaf5458InputLogOnePlusV = outerEnclosure 24
      (leaf5458Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5458RoundedFacts : LeafRoundedFacts 8
    leaf5458Certificate.logOnePlusV leaf5458InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5458InputLogOnePlusV_eq }

private noncomputable def leaf5458Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi290InputQChi innerPair264Input
    leaf5458InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5458LowerChecked :
    lowerCheck 24 leaf5458Box leaf5458Inputs = true := by
  rfl'

private theorem leaf5458CoversExact : CoversExact 8
    leaf5458Box leaf5458Certificate leaf5458InnerLog leaf5458Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi290RoundedFacts
    innerPair264RoundedFacts leaf5458RoundedFacts (by rfl)

private theorem leaf5458FlatSound : Sound leaf5458Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5458CertificateValid
    leaf5458InnerLogValid leaf5458CoversExact leaf5458LowerChecked

private noncomputable def leaf5459Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (41/128), chiHi := (83/256) }

private noncomputable def leaf5459Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742495/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714100992) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2427861635/2147483648) }, upper := { exponent := 1, mantissa := (37383/32768) } }, logOuter := sk237LogOuterCertificate, logK := sk237LogKCertificate, logChi := chi291LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431513343/137428201984) } }, logDArg := sk237LogDArgCertificate }

private noncomputable def leaf5459InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf5459LocalValidity :
    LeafFacts leaf5459Box leaf5459Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5459Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714100992) }) = true
      norm_num [leaf5459Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5459CertificateValid :
    WideCertificateValid leaf5459Box leaf5459Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk237ValidityFacts chi291ValidityFacts
    leaf5459LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5459CoverageChecked :
    coverageCheck (innerAD leaf5459Box) leaf5459InnerLog = true := by
  rfl'

private theorem leaf5459InnerLogValid :
    leaf5459InnerLog.Valid 8 (innerAD leaf5459Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf5459CoverageChecked

private noncomputable def leaf5459InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629485/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5459InputLogOnePlusV_eq :
    leaf5459InputLogOnePlusV = outerEnclosure 24
      (leaf5459Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5459RoundedFacts : LeafRoundedFacts 8
    leaf5459Certificate.logOnePlusV leaf5459InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5459InputLogOnePlusV_eq }

private noncomputable def leaf5459Inputs : Inputs :=
  inputsOfCaches globalInput sk237RoundedInputs
    chi291InputQChi innerPair264Input
    leaf5459InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5459LowerChecked :
    lowerCheck 24 leaf5459Box leaf5459Inputs = true := by
  rfl'

private theorem leaf5459CoversExact : CoversExact 8
    leaf5459Box leaf5459Certificate leaf5459InnerLog leaf5459Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk237RoundedFacts chi291RoundedFacts
    innerPair264RoundedFacts leaf5459RoundedFacts (by rfl)

private theorem leaf5459FlatSound : Sound leaf5459Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5459CertificateValid
    leaf5459InnerLogValid leaf5459CoversExact leaf5459LowerChecked

private noncomputable def leaf5460Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (41/128), chiHi := (83/256) }

private noncomputable def leaf5460Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742497/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22905804117/22904693248) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2433235257/2147483648) }, upper := { exponent := 1, mantissa := (18733/16384) } }, logOuter := sk238LogOuterCertificate, logK := sk238LogKCertificate, logChi := chi291LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45810497365/45809386496) } }, logDArg := sk238LogDArgCertificate }

private noncomputable def leaf5460InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf5460LocalValidity :
    LeafFacts leaf5460Box leaf5460Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5460Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22905804117/22904693248) }) = true
      norm_num [leaf5460Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5460CertificateValid :
    WideCertificateValid leaf5460Box leaf5460Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk238ValidityFacts chi291ValidityFacts
    leaf5460LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5460CoverageChecked :
    coverageCheck (innerAD leaf5460Box) leaf5460InnerLog = true := by
  rfl'

private theorem leaf5460InnerLogValid :
    leaf5460InnerLog.Valid 8 (innerAD leaf5460Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf5460CoverageChecked

private noncomputable def leaf5460InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726843/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf5460InputLogOnePlusV_eq :
    leaf5460InputLogOnePlusV = outerEnclosure 24
      (leaf5460Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5460RoundedFacts : LeafRoundedFacts 8
    leaf5460Certificate.logOnePlusV leaf5460InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5460InputLogOnePlusV_eq }

private noncomputable def leaf5460Inputs : Inputs :=
  inputsOfCaches globalInput sk238RoundedInputs
    chi291InputQChi innerPair264Input
    leaf5460InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5460LowerChecked :
    lowerCheck 24 leaf5460Box leaf5460Inputs = true := by
  rfl'

private theorem leaf5460CoversExact : CoversExact 8
    leaf5460Box leaf5460Certificate leaf5460InnerLog leaf5460Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk238RoundedFacts chi291RoundedFacts
    innerPair264RoundedFacts leaf5460RoundedFacts (by rfl)

private theorem leaf5460FlatSound : Sound leaf5460Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5460CertificateValid
    leaf5460InnerLogValid leaf5460CoversExact leaf5460LowerChecked

private noncomputable def leaf5461Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (83/256), chiHi := (21/64) }

private noncomputable def leaf5461Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742497/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714036224) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2444375697/2147483648) }, upper := { exponent := 1, mantissa := (9409/8192) } }, logOuter := sk237LogOuterCertificate, logK := sk237LogKCertificate, logChi := chi292LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431448575/137428072448) } }, logDArg := sk237LogDArgCertificate }

private noncomputable def leaf5461InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf5461LocalValidity :
    LeafFacts leaf5461Box leaf5461Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5461Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714036224) }) = true
      norm_num [leaf5461Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5461CertificateValid :
    WideCertificateValid leaf5461Box leaf5461Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk237ValidityFacts chi292ValidityFacts
    leaf5461LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5461CoverageChecked :
    coverageCheck (innerAD leaf5461Box) leaf5461InnerLog = true := by
  rfl'

private theorem leaf5461InnerLogValid :
    leaf5461InnerLog.Valid 8 (innerAD leaf5461Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf5461CoverageChecked

private noncomputable def leaf5461InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629493/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5461InputLogOnePlusV_eq :
    leaf5461InputLogOnePlusV = outerEnclosure 24
      (leaf5461Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5461RoundedFacts : LeafRoundedFacts 8
    leaf5461Certificate.logOnePlusV leaf5461InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5461InputLogOnePlusV_eq }

private noncomputable def leaf5461Inputs : Inputs :=
  inputsOfCaches globalInput sk237RoundedInputs
    chi292InputQChi innerPair264Input
    leaf5461InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5461LowerChecked :
    lowerCheck 24 leaf5461Box leaf5461Inputs = true := by
  rfl'

private theorem leaf5461CoversExact : CoversExact 8
    leaf5461Box leaf5461Certificate leaf5461InnerLog leaf5461Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk237RoundedFacts chi292RoundedFacts
    innerPair264RoundedFacts leaf5461RoundedFacts (by rfl)

private theorem leaf5461FlatSound : Sound leaf5461Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5461CertificateValid
    leaf5461InnerLogValid leaf5461CoversExact leaf5461LowerChecked

private noncomputable def leaf5462Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (83/256), chiHi := (21/64) }

private noncomputable def leaf5462Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742499/1073741824) }, vSqrt := { lower := (8191/8192), upper := (2216690721/2216581120) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2449814851/2147483648) }, upper := { exponent := 1, mantissa := (4715/4096) } }, logOuter := sk238LogOuterCertificate, logK := sk238LogKCertificate, logChi := chi292LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (4433271841/4433162240) } }, logDArg := sk238LogDArgCertificate }

private noncomputable def leaf5462InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf5462LocalValidity :
    LeafFacts leaf5462Box leaf5462Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5462Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (2216690721/2216581120) }) = true
      norm_num [leaf5462Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5462CertificateValid :
    WideCertificateValid leaf5462Box leaf5462Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk238ValidityFacts chi292ValidityFacts
    leaf5462LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5462CoverageChecked :
    coverageCheck (innerAD leaf5462Box) leaf5462InnerLog = true := by
  rfl'

private theorem leaf5462InnerLogValid :
    leaf5462InnerLog.Valid 8 (innerAD leaf5462Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf5462CoverageChecked

private noncomputable def leaf5462InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453687/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf5462InputLogOnePlusV_eq :
    leaf5462InputLogOnePlusV = outerEnclosure 24
      (leaf5462Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5462RoundedFacts : LeafRoundedFacts 8
    leaf5462Certificate.logOnePlusV leaf5462InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5462InputLogOnePlusV_eq }

private noncomputable def leaf5462Inputs : Inputs :=
  inputsOfCaches globalInput sk238RoundedInputs
    chi292InputQChi innerPair264Input
    leaf5462InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5462LowerChecked :
    lowerCheck 24 leaf5462Box leaf5462Inputs = true := by
  rfl'

private theorem leaf5462CoversExact : CoversExact 8
    leaf5462Box leaf5462Certificate leaf5462InnerLog leaf5462Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk238RoundedFacts chi292RoundedFacts
    innerPair264RoundedFacts leaf5462RoundedFacts (by rfl)

private theorem leaf5462FlatSound : Sound leaf5462Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5462CertificateValid
    leaf5462InnerLogValid leaf5462CoversExact leaf5462LowerChecked

private noncomputable def leaf5463Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (41/128), chiHi := (83/256) }

private noncomputable def leaf5463Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742499/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714058496) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2438608879/2147483648) }, upper := { exponent := 1, mantissa := (37549/32768) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi291LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431470847/137428116992) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf5463InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf5463LocalValidity :
    LeafFacts leaf5463Box leaf5463Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5463Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714058496) }) = true
      norm_num [leaf5463Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5463CertificateValid :
    WideCertificateValid leaf5463Box leaf5463Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi291ValidityFacts
    leaf5463LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5463CoverageChecked :
    coverageCheck (innerAD leaf5463Box) leaf5463InnerLog = true := by
  rfl'

private theorem leaf5463InnerLogValid :
    leaf5463InnerLog.Valid 8 (innerAD leaf5463Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf5463CoverageChecked

private noncomputable def leaf5463InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814745/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5463InputLogOnePlusV_eq :
    leaf5463InputLogOnePlusV = outerEnclosure 24
      (leaf5463Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5463RoundedFacts : LeafRoundedFacts 8
    leaf5463Certificate.logOnePlusV leaf5463InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5463InputLogOnePlusV_eq }

private noncomputable def leaf5463Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi291InputQChi innerPair264Input
    leaf5463InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5463LowerChecked :
    lowerCheck 24 leaf5463Box leaf5463Inputs = true := by
  rfl'

private theorem leaf5463CoversExact : CoversExact 8
    leaf5463Box leaf5463Certificate leaf5463InnerLog leaf5463Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi291RoundedFacts
    innerPair264RoundedFacts leaf5463RoundedFacts (by rfl)

private theorem leaf5463FlatSound : Sound leaf5463Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5463CertificateValid
    leaf5463InnerLogValid leaf5463CoversExact leaf5463LowerChecked

private noncomputable def leaf5464Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (41/128), chiHi := (83/256) }

private noncomputable def leaf5464Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742501/1073741824) }, vSqrt := { lower := (65527/65536), upper := (68717412351/68714037248) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2443982501/2147483648) }, upper := { exponent := 1, mantissa := (147/128) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi291LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (137431449599/137428074496) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf5464InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf5464LocalValidity :
    LeafFacts leaf5464Box leaf5464Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5464Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (68717412351/68714037248) }) = true
      norm_num [leaf5464Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5464CertificateValid :
    WideCertificateValid leaf5464Box leaf5464Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi291ValidityFacts
    leaf5464LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5464CoverageChecked :
    coverageCheck (innerAD leaf5464Box) leaf5464InnerLog = true := by
  rfl'

private theorem leaf5464InnerLogValid :
    leaf5464InnerLog.Valid 8 (innerAD leaf5464Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf5464CoverageChecked

private noncomputable def leaf5464InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629493/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5464InputLogOnePlusV_eq :
    leaf5464InputLogOnePlusV = outerEnclosure 24
      (leaf5464Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5464RoundedFacts : LeafRoundedFacts 8
    leaf5464Certificate.logOnePlusV leaf5464InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5464InputLogOnePlusV_eq }

private noncomputable def leaf5464Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi291InputQChi innerPair264Input
    leaf5464InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5464LowerChecked :
    lowerCheck 24 leaf5464Box leaf5464Inputs = true := by
  rfl'

private theorem leaf5464CoversExact : CoversExact 8
    leaf5464Box leaf5464Certificate leaf5464InnerLog leaf5464Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi291RoundedFacts
    innerPair264RoundedFacts leaf5464RoundedFacts (by rfl)

private theorem leaf5464FlatSound : Sound leaf5464Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5464CertificateValid
    leaf5464InnerLogValid leaf5464CoversExact leaf5464LowerChecked

private noncomputable def leaf5465Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (83/256), chiHi := (21/64) }

private noncomputable def leaf5465Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742501/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68713993216) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2455254005/2147483648) }, upper := { exponent := 1, mantissa := (9451/8192) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi292LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431405567/137427986432) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf5465InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf5465LocalValidity :
    LeafFacts leaf5465Box leaf5465Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5465Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68713993216) }) = true
      norm_num [leaf5465Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5465CertificateValid :
    WideCertificateValid leaf5465Box leaf5465Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi292ValidityFacts
    leaf5465LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5465CoverageChecked :
    coverageCheck (innerAD leaf5465Box) leaf5465InnerLog = true := by
  rfl'

private theorem leaf5465InnerLogValid :
    leaf5465InnerLog.Valid 8 (innerAD leaf5465Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf5465CoverageChecked

private noncomputable def leaf5465InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814749/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5465InputLogOnePlusV_eq :
    leaf5465InputLogOnePlusV = outerEnclosure 24
      (leaf5465Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5465RoundedFacts : LeafRoundedFacts 8
    leaf5465Certificate.logOnePlusV leaf5465InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5465InputLogOnePlusV_eq }

private noncomputable def leaf5465Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi292InputQChi innerPair264Input
    leaf5465InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5465LowerChecked :
    lowerCheck 24 leaf5465Box leaf5465Inputs = true := by
  rfl'

private theorem leaf5465CoversExact : CoversExact 8
    leaf5465Box leaf5465Certificate leaf5465InnerLog leaf5465Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi292RoundedFacts
    innerPair264RoundedFacts leaf5465RoundedFacts (by rfl)

private theorem leaf5465FlatSound : Sound leaf5465Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5465CertificateValid
    leaf5465InnerLogValid leaf5465CoversExact leaf5465LowerChecked

private noncomputable def leaf5466Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (83/256), chiHi := (21/64) }

private noncomputable def leaf5466Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742503/1073741824) }, vSqrt := { lower := (65527/65536), upper := (68717412351/68713971712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2460693159/2147483648) }, upper := { exponent := 1, mantissa := (37/32) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi292LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (137431384063/137427943424) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf5466InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf5466LocalValidity :
    LeafFacts leaf5466Box leaf5466Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5466Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (68717412351/68713971712) }) = true
      norm_num [leaf5466Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5466CertificateValid :
    WideCertificateValid leaf5466Box leaf5466Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi292ValidityFacts
    leaf5466LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5466CoverageChecked :
    coverageCheck (innerAD leaf5466Box) leaf5466InnerLog = true := by
  rfl'

private theorem leaf5466InnerLogValid :
    leaf5466InnerLog.Valid 8 (innerAD leaf5466Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf5466CoverageChecked

private noncomputable def leaf5466InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629501/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5466InputLogOnePlusV_eq :
    leaf5466InputLogOnePlusV = outerEnclosure 24
      (leaf5466Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5466RoundedFacts : LeafRoundedFacts 8
    leaf5466Certificate.logOnePlusV leaf5466InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5466InputLogOnePlusV_eq }

private noncomputable def leaf5466Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi292InputQChi innerPair264Input
    leaf5466InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5466LowerChecked :
    lowerCheck 24 leaf5466Box leaf5466Inputs = true := by
  rfl'

private theorem leaf5466CoversExact : CoversExact 8
    leaf5466Box leaf5466Certificate leaf5466InnerLog leaf5466Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi292RoundedFacts
    innerPair264RoundedFacts leaf5466RoundedFacts (by rfl)

private theorem leaf5466FlatSound : Sound leaf5466Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5466CertificateValid
    leaf5466InnerLogValid leaf5466CoversExact leaf5466LowerChecked

private noncomputable def leaf5467Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (249/64), chiLo := (21/64), chiHi := (85/256) }

private noncomputable def leaf5467Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742491/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714058496) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2438871015/2147483648) }, upper := { exponent := 1, mantissa := (37549/32768) } }, logOuter := sk233LogOuterCertificate, logK := sk233LogKCertificate, logChi := chi293LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431470847/137428116992) } }, logDArg := sk233LogDArgCertificate }

private noncomputable def leaf5467InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf5467LocalValidity :
    LeafFacts leaf5467Box leaf5467Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5467Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714058496) }) = true
      norm_num [leaf5467Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5467CertificateValid :
    WideCertificateValid leaf5467Box leaf5467Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk233ValidityFacts chi293ValidityFacts
    leaf5467LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5467CoverageChecked :
    coverageCheck (innerAD leaf5467Box) leaf5467InnerLog = true := by
  rfl'

private theorem leaf5467InnerLogValid :
    leaf5467InnerLog.Valid 8 (innerAD leaf5467Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf5467CoverageChecked

private noncomputable def leaf5467InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814745/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5467InputLogOnePlusV_eq :
    leaf5467InputLogOnePlusV = outerEnclosure 24
      (leaf5467Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5467RoundedFacts : LeafRoundedFacts 8
    leaf5467Certificate.logOnePlusV leaf5467InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5467InputLogOnePlusV_eq }

private noncomputable def leaf5467Inputs : Inputs :=
  inputsOfCaches globalInput sk233RoundedInputs
    chi293InputQChi innerPair264Input
    leaf5467InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5467LowerChecked :
    lowerCheck 24 leaf5467Box leaf5467Inputs = true := by
  rfl'

private theorem leaf5467CoversExact : CoversExact 8
    leaf5467Box leaf5467Certificate leaf5467InnerLog leaf5467Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk233RoundedFacts chi293RoundedFacts
    innerPair264RoundedFacts leaf5467RoundedFacts (by rfl)

private theorem leaf5467FlatSound : Sound leaf5467Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5467CertificateValid
    leaf5467InnerLogValid leaf5467CoversExact leaf5467LowerChecked

private noncomputable def leaf5468Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (249/64), kHi := (125/32), chiLo := (21/64), chiHi := (85/256) }

private noncomputable def leaf5468Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742493/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22905804117/22904678912) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2444375701/2147483648) }, upper := { exponent := 1, mantissa := (18817/16384) } }, logOuter := sk234LogOuterCertificate, logK := sk234LogKCertificate, logChi := chi293LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45810483029/45809357824) } }, logDArg := sk234LogDArgCertificate }

private noncomputable def leaf5468InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf5468LocalValidity :
    LeafFacts leaf5468Box leaf5468Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5468Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22905804117/22904678912) }) = true
      norm_num [leaf5468Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5468CertificateValid :
    WideCertificateValid leaf5468Box leaf5468Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk234ValidityFacts chi293ValidityFacts
    leaf5468LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5468CoverageChecked :
    coverageCheck (innerAD leaf5468Box) leaf5468InnerLog = true := by
  rfl'

private theorem leaf5468InnerLogValid :
    leaf5468InnerLog.Valid 8 (innerAD leaf5468Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf5468CoverageChecked

private noncomputable def leaf5468InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629493/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5468InputLogOnePlusV_eq :
    leaf5468InputLogOnePlusV = outerEnclosure 24
      (leaf5468Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5468RoundedFacts : LeafRoundedFacts 8
    leaf5468Certificate.logOnePlusV leaf5468InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5468InputLogOnePlusV_eq }

private noncomputable def leaf5468Inputs : Inputs :=
  inputsOfCaches globalInput sk234RoundedInputs
    chi293InputQChi innerPair264Input
    leaf5468InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5468LowerChecked :
    lowerCheck 24 leaf5468Box leaf5468Inputs = true := by
  rfl'

private theorem leaf5468CoversExact : CoversExact 8
    leaf5468Box leaf5468Certificate leaf5468InnerLog leaf5468Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk234RoundedFacts chi293RoundedFacts
    innerPair264RoundedFacts leaf5468RoundedFacts (by rfl)

private theorem leaf5468FlatSound : Sound leaf5468Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5468CertificateValid
    leaf5468InnerLogValid leaf5468CoversExact leaf5468LowerChecked

private noncomputable def leaf5469Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (249/64), chiLo := (85/256), chiHi := (43/128) }

private noncomputable def leaf5469Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742493/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68713994752) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2455122949/2147483648) }, upper := { exponent := 1, mantissa := (18899/16384) } }, logOuter := sk233LogOuterCertificate, logK := sk233LogKCertificate, logChi := chi294LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431407103/137427989504) } }, logDArg := sk233LogDArgCertificate }

private noncomputable def leaf5469InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf5469LocalValidity :
    LeafFacts leaf5469Box leaf5469Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5469Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68713994752) }) = true
      norm_num [leaf5469Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5469CertificateValid :
    WideCertificateValid leaf5469Box leaf5469Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk233ValidityFacts chi294ValidityFacts
    leaf5469LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5469CoverageChecked :
    coverageCheck (innerAD leaf5469Box) leaf5469InnerLog = true := by
  rfl'

private theorem leaf5469InnerLogValid :
    leaf5469InnerLog.Valid 8 (innerAD leaf5469Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf5469CoverageChecked

private noncomputable def leaf5469InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814749/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5469InputLogOnePlusV_eq :
    leaf5469InputLogOnePlusV = outerEnclosure 24
      (leaf5469Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5469RoundedFacts : LeafRoundedFacts 8
    leaf5469Certificate.logOnePlusV leaf5469InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5469InputLogOnePlusV_eq }

private noncomputable def leaf5469Inputs : Inputs :=
  inputsOfCaches globalInput sk233RoundedInputs
    chi294InputQChi innerPair264Input
    leaf5469InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5469LowerChecked :
    lowerCheck 24 leaf5469Box leaf5469Inputs = true := by
  rfl'

private theorem leaf5469CoversExact : CoversExact 8
    leaf5469Box leaf5469Certificate leaf5469InnerLog leaf5469Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk233RoundedFacts chi294RoundedFacts
    innerPair264RoundedFacts leaf5469RoundedFacts (by rfl)

private theorem leaf5469FlatSound : Sound leaf5469Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5469CertificateValid
    leaf5469InnerLogValid leaf5469CoversExact leaf5469LowerChecked

private noncomputable def leaf5470Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (249/64), kHi := (125/32), chiLo := (85/256), chiHi := (43/128) }

private noncomputable def leaf5470Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742495/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68713972736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2460693167/2147483648) }, upper := { exponent := 1, mantissa := (9471/8192) } }, logOuter := sk234LogOuterCertificate, logK := sk234LogKCertificate, logChi := chi294LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431385087/137427945472) } }, logDArg := sk234LogDArgCertificate }

private noncomputable def leaf5470InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf5470LocalValidity :
    LeafFacts leaf5470Box leaf5470Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5470Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68713972736) }) = true
      norm_num [leaf5470Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5470CertificateValid :
    WideCertificateValid leaf5470Box leaf5470Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk234ValidityFacts chi294ValidityFacts
    leaf5470LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5470CoverageChecked :
    coverageCheck (innerAD leaf5470Box) leaf5470InnerLog = true := by
  rfl'

private theorem leaf5470InnerLogValid :
    leaf5470InnerLog.Valid 8 (innerAD leaf5470Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf5470CoverageChecked

private noncomputable def leaf5470InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629501/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5470InputLogOnePlusV_eq :
    leaf5470InputLogOnePlusV = outerEnclosure 24
      (leaf5470Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5470RoundedFacts : LeafRoundedFacts 8
    leaf5470Certificate.logOnePlusV leaf5470InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5470InputLogOnePlusV_eq }

private noncomputable def leaf5470Inputs : Inputs :=
  inputsOfCaches globalInput sk234RoundedInputs
    chi294InputQChi innerPair264Input
    leaf5470InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5470LowerChecked :
    lowerCheck 24 leaf5470Box leaf5470Inputs = true := by
  rfl'

private theorem leaf5470CoversExact : CoversExact 8
    leaf5470Box leaf5470Certificate leaf5470InnerLog leaf5470Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk234RoundedFacts chi294RoundedFacts
    innerPair264RoundedFacts leaf5470RoundedFacts (by rfl)

private theorem leaf5470FlatSound : Sound leaf5470Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5470CertificateValid
    leaf5470InnerLogValid leaf5470CoversExact leaf5470LowerChecked

private noncomputable def leaf5471Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (251/64), chiLo := (21/64), chiHi := (85/256) }

private noncomputable def leaf5471Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742495/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714014976) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2449880387/2147483648) }, upper := { exponent := 1, mantissa := (37719/32768) } }, logOuter := sk235LogOuterCertificate, logK := sk235LogKCertificate, logChi := chi293LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431427327/137428029952) } }, logDArg := sk235LogDArgCertificate }

private noncomputable def leaf5471InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf5471LocalValidity :
    LeafFacts leaf5471Box leaf5471Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5471Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714014976) }) = true
      norm_num [leaf5471Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5471CertificateValid :
    WideCertificateValid leaf5471Box leaf5471Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk235ValidityFacts chi293ValidityFacts
    leaf5471LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5471CoverageChecked :
    coverageCheck (innerAD leaf5471Box) leaf5471InnerLog = true := by
  rfl'

private theorem leaf5471InnerLogValid :
    leaf5471InnerLog.Valid 8 (innerAD leaf5471Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf5471CoverageChecked

private noncomputable def leaf5471InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629495/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5471InputLogOnePlusV_eq :
    leaf5471InputLogOnePlusV = outerEnclosure 24
      (leaf5471Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5471RoundedFacts : LeafRoundedFacts 8
    leaf5471Certificate.logOnePlusV leaf5471InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5471InputLogOnePlusV_eq }

private noncomputable def leaf5471Inputs : Inputs :=
  inputsOfCaches globalInput sk235RoundedInputs
    chi293InputQChi innerPair264Input
    leaf5471InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5471LowerChecked :
    lowerCheck 24 leaf5471Box leaf5471Inputs = true := by
  rfl'

private theorem leaf5471CoversExact : CoversExact 8
    leaf5471Box leaf5471Certificate leaf5471InnerLog leaf5471Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk235RoundedFacts chi293RoundedFacts
    innerPair264RoundedFacts leaf5471RoundedFacts (by rfl)

private theorem leaf5471FlatSound : Sound leaf5471Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5471CertificateValid
    leaf5471InnerLogValid leaf5471CoversExact leaf5471LowerChecked

private noncomputable def leaf5472Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (63/16), chiLo := (21/64), chiHi := (85/256) }

private noncomputable def leaf5472Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742497/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68713993216) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2455385073/2147483648) }, upper := { exponent := 1, mantissa := (9451/8192) } }, logOuter := sk236LogOuterCertificate, logK := sk236LogKCertificate, logChi := chi293LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431405567/137427986432) } }, logDArg := sk236LogDArgCertificate }

private noncomputable def leaf5472InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf5472LocalValidity :
    LeafFacts leaf5472Box leaf5472Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5472Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68713993216) }) = true
      norm_num [leaf5472Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5472CertificateValid :
    WideCertificateValid leaf5472Box leaf5472Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk236ValidityFacts chi293ValidityFacts
    leaf5472LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5472CoverageChecked :
    coverageCheck (innerAD leaf5472Box) leaf5472InnerLog = true := by
  rfl'

private theorem leaf5472InnerLogValid :
    leaf5472InnerLog.Valid 8 (innerAD leaf5472Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf5472CoverageChecked

private noncomputable def leaf5472InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814749/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5472InputLogOnePlusV_eq :
    leaf5472InputLogOnePlusV = outerEnclosure 24
      (leaf5472Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5472RoundedFacts : LeafRoundedFacts 8
    leaf5472Certificate.logOnePlusV leaf5472InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5472InputLogOnePlusV_eq }

private noncomputable def leaf5472Inputs : Inputs :=
  inputsOfCaches globalInput sk236RoundedInputs
    chi293InputQChi innerPair264Input
    leaf5472InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5472LowerChecked :
    lowerCheck 24 leaf5472Box leaf5472Inputs = true := by
  rfl'

private theorem leaf5472CoversExact : CoversExact 8
    leaf5472Box leaf5472Certificate leaf5472InnerLog leaf5472Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk236RoundedFacts chi293RoundedFacts
    innerPair264RoundedFacts leaf5472RoundedFacts (by rfl)

private theorem leaf5472FlatSound : Sound leaf5472Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5472CertificateValid
    leaf5472InnerLogValid leaf5472CoversExact leaf5472LowerChecked

private noncomputable def leaf5473Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (251/64), chiLo := (85/256), chiHi := (43/128) }

private noncomputable def leaf5473Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742497/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22905804117/22904650240) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2466263385/2147483648) }, upper := { exponent := 1, mantissa := (18985/16384) } }, logOuter := sk235LogOuterCertificate, logK := sk235LogKCertificate, logChi := chi294LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45810454357/45809300480) } }, logDArg := sk235LogDArgCertificate }

private noncomputable def leaf5473InnerLog : WideLogData :=
  innerPair265Data

set_option maxRecDepth 1000000 in
private theorem leaf5473LocalValidity :
    LeafFacts leaf5473Box leaf5473Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5473Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22905804117/22904650240) }) = true
      norm_num [leaf5473Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5473CertificateValid :
    WideCertificateValid leaf5473Box leaf5473Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk235ValidityFacts chi294ValidityFacts
    leaf5473LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5473CoverageChecked :
    coverageCheck (innerAD leaf5473Box) leaf5473InnerLog = true := by
  rfl'

private theorem leaf5473InnerLogValid :
    leaf5473InnerLog.Valid 8 (innerAD leaf5473Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint77PositiveFacts.valid leaf5473CoverageChecked

private noncomputable def leaf5473InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629503/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5473InputLogOnePlusV_eq :
    leaf5473InputLogOnePlusV = outerEnclosure 24
      (leaf5473Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5473RoundedFacts : LeafRoundedFacts 8
    leaf5473Certificate.logOnePlusV leaf5473InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5473InputLogOnePlusV_eq }

private noncomputable def leaf5473Inputs : Inputs :=
  inputsOfCaches globalInput sk235RoundedInputs
    chi294InputQChi innerPair265Input
    leaf5473InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5473LowerChecked :
    lowerCheck 24 leaf5473Box leaf5473Inputs = true := by
  rfl'

private theorem leaf5473CoversExact : CoversExact 8
    leaf5473Box leaf5473Certificate leaf5473InnerLog leaf5473Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk235RoundedFacts chi294RoundedFacts
    innerPair265RoundedFacts leaf5473RoundedFacts (by rfl)

private theorem leaf5473FlatSound : Sound leaf5473Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5473CertificateValid
    leaf5473InnerLogValid leaf5473CoversExact leaf5473LowerChecked

private noncomputable def leaf5474Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (63/16), chiLo := (85/256), chiHi := (43/128) }

private noncomputable def leaf5474Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742499/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68713928704) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2471833603/2147483648) }, upper := { exponent := 1, mantissa := (4757/4096) } }, logOuter := sk236LogOuterCertificate, logK := sk236LogKCertificate, logChi := chi294LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431341055/137427857408) } }, logDArg := sk236LogDArgCertificate }

private noncomputable def leaf5474InnerLog : WideLogData :=
  innerPair265Data

set_option maxRecDepth 1000000 in
private theorem leaf5474LocalValidity :
    LeafFacts leaf5474Box leaf5474Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5474Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68713928704) }) = true
      norm_num [leaf5474Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5474CertificateValid :
    WideCertificateValid leaf5474Box leaf5474Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk236ValidityFacts chi294ValidityFacts
    leaf5474LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5474CoverageChecked :
    coverageCheck (innerAD leaf5474Box) leaf5474InnerLog = true := by
  rfl'

private theorem leaf5474InnerLogValid :
    leaf5474InnerLog.Valid 8 (innerAD leaf5474Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint77PositiveFacts.valid leaf5474CoverageChecked

private noncomputable def leaf5474InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814753/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5474InputLogOnePlusV_eq :
    leaf5474InputLogOnePlusV = outerEnclosure 24
      (leaf5474Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5474RoundedFacts : LeafRoundedFacts 8
    leaf5474Certificate.logOnePlusV leaf5474InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5474InputLogOnePlusV_eq }

private noncomputable def leaf5474Inputs : Inputs :=
  inputsOfCaches globalInput sk236RoundedInputs
    chi294InputQChi innerPair265Input
    leaf5474InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5474LowerChecked :
    lowerCheck 24 leaf5474Box leaf5474Inputs = true := by
  rfl'

private theorem leaf5474CoversExact : CoversExact 8
    leaf5474Box leaf5474Certificate leaf5474InnerLog leaf5474Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk236RoundedFacts chi294RoundedFacts
    innerPair265RoundedFacts leaf5474RoundedFacts (by rfl)

private theorem leaf5474FlatSound : Sound leaf5474Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5474CertificateValid
    leaf5474InnerLogValid leaf5474CoversExact leaf5474LowerChecked

private noncomputable def leaf5475Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (249/64), chiLo := (43/128), chiHi := (87/256) }

private noncomputable def leaf5475Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742495/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68713931008) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2471374883/2147483648) }, upper := { exponent := 1, mantissa := (38047/32768) } }, logOuter := sk233LogOuterCertificate, logK := sk233LogKCertificate, logChi := chi295LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431343359/137427862016) } }, logDArg := sk233LogDArgCertificate }

private noncomputable def leaf5475InnerLog : WideLogData :=
  innerPair265Data

set_option maxRecDepth 1000000 in
private theorem leaf5475LocalValidity :
    LeafFacts leaf5475Box leaf5475Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5475Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68713931008) }) = true
      norm_num [leaf5475Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5475CertificateValid :
    WideCertificateValid leaf5475Box leaf5475Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk233ValidityFacts chi295ValidityFacts
    leaf5475LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5475CoverageChecked :
    coverageCheck (innerAD leaf5475Box) leaf5475InnerLog = true := by
  rfl'

private theorem leaf5475InnerLogValid :
    leaf5475InnerLog.Valid 8 (innerAD leaf5475Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint77PositiveFacts.valid leaf5475CoverageChecked

private noncomputable def leaf5475InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814753/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5475InputLogOnePlusV_eq :
    leaf5475InputLogOnePlusV = outerEnclosure 24
      (leaf5475Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5475RoundedFacts : LeafRoundedFacts 8
    leaf5475Certificate.logOnePlusV leaf5475InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5475InputLogOnePlusV_eq }

private noncomputable def leaf5475Inputs : Inputs :=
  inputsOfCaches globalInput sk233RoundedInputs
    chi295InputQChi innerPair265Input
    leaf5475InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5475LowerChecked :
    lowerCheck 24 leaf5475Box leaf5475Inputs = true := by
  rfl'

private theorem leaf5475CoversExact : CoversExact 8
    leaf5475Box leaf5475Certificate leaf5475InnerLog leaf5475Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk233RoundedFacts chi295RoundedFacts
    innerPair265RoundedFacts leaf5475RoundedFacts (by rfl)

private theorem leaf5475FlatSound : Sound leaf5475Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5475CertificateValid
    leaf5475InnerLogValid leaf5475CoversExact leaf5475LowerChecked

private noncomputable def leaf5476Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (249/64), kHi := (125/32), chiLo := (43/128), chiHi := (87/256) }

private noncomputable def leaf5476Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742497/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68713908736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2477010633/2147483648) }, upper := { exponent := 1, mantissa := (19067/16384) } }, logOuter := sk234LogOuterCertificate, logK := sk234LogKCertificate, logChi := chi295LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431321087/137427817472) } }, logDArg := sk234LogDArgCertificate }

private noncomputable def leaf5476InnerLog : WideLogData :=
  innerPair265Data

set_option maxRecDepth 1000000 in
private theorem leaf5476LocalValidity :
    LeafFacts leaf5476Box leaf5476Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5476Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68713908736) }) = true
      norm_num [leaf5476Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5476CertificateValid :
    WideCertificateValid leaf5476Box leaf5476Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk234ValidityFacts chi295ValidityFacts
    leaf5476LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5476CoverageChecked :
    coverageCheck (innerAD leaf5476Box) leaf5476InnerLog = true := by
  rfl'

private theorem leaf5476InnerLogValid :
    leaf5476InnerLog.Valid 8 (innerAD leaf5476Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint77PositiveFacts.valid leaf5476CoverageChecked

private noncomputable def leaf5476InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907377/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5476InputLogOnePlusV_eq :
    leaf5476InputLogOnePlusV = outerEnclosure 24
      (leaf5476Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5476RoundedFacts : LeafRoundedFacts 8
    leaf5476Certificate.logOnePlusV leaf5476InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5476InputLogOnePlusV_eq }

private noncomputable def leaf5476Inputs : Inputs :=
  inputsOfCaches globalInput sk234RoundedInputs
    chi295InputQChi innerPair265Input
    leaf5476InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5476LowerChecked :
    lowerCheck 24 leaf5476Box leaf5476Inputs = true := by
  rfl'

private theorem leaf5476CoversExact : CoversExact 8
    leaf5476Box leaf5476Certificate leaf5476InnerLog leaf5476Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk234RoundedFacts chi295RoundedFacts
    innerPair265RoundedFacts leaf5476RoundedFacts (by rfl)

private theorem leaf5476FlatSound : Sound leaf5476Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5476CertificateValid
    leaf5476InnerLogValid leaf5476CoversExact leaf5476LowerChecked

private noncomputable def leaf5477Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (249/64), chiLo := (87/256), chiHi := (11/32) }

private noncomputable def leaf5477Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742497/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9816773193/9816266752) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2487626817/2147483648) }, upper := { exponent := 1, mantissa := (4787/4096) } }, logOuter := sk233LogOuterCertificate, logK := sk233LogKCertificate, logChi := chi296LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (19633039945/19632533504) } }, logDArg := sk233LogDArgCertificate }

private noncomputable def leaf5477InnerLog : WideLogData :=
  innerPair272Data

set_option maxRecDepth 1000000 in
private theorem leaf5477LocalValidity :
    LeafFacts leaf5477Box leaf5477Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5477Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9816773193/9816266752) }) = true
      norm_num [leaf5477Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5477CertificateValid :
    WideCertificateValid leaf5477Box leaf5477Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk233ValidityFacts chi296ValidityFacts
    leaf5477LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5477CoverageChecked :
    coverageCheck (innerAD leaf5477Box) leaf5477InnerLog = true := by
  rfl'

private theorem leaf5477InnerLogValid :
    leaf5477InnerLog.Valid 8 (innerAD leaf5477Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint77PositiveFacts.valid leaf5477CoverageChecked

private noncomputable def leaf5477InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814757/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5477InputLogOnePlusV_eq :
    leaf5477InputLogOnePlusV = outerEnclosure 24
      (leaf5477Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5477RoundedFacts : LeafRoundedFacts 8
    leaf5477Certificate.logOnePlusV leaf5477InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5477InputLogOnePlusV_eq }

private noncomputable def leaf5477Inputs : Inputs :=
  inputsOfCaches globalInput sk233RoundedInputs
    chi296InputQChi innerPair272Input
    leaf5477InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5477LowerChecked :
    lowerCheck 24 leaf5477Box leaf5477Inputs = true := by
  rfl'

private theorem leaf5477CoversExact : CoversExact 8
    leaf5477Box leaf5477Certificate leaf5477InnerLog leaf5477Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk233RoundedFacts chi296RoundedFacts
    innerPair272RoundedFacts leaf5477RoundedFacts (by rfl)

private theorem leaf5477FlatSound : Sound leaf5477Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5477CertificateValid
    leaf5477InnerLogValid leaf5477CoversExact leaf5477LowerChecked

private noncomputable def leaf5478Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (249/64), kHi := (125/32), chiLo := (87/256), chiHi := (11/32) }

private noncomputable def leaf5478Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742499/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22905804117/22904614912) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2493328099/2147483648) }, upper := { exponent := 1, mantissa := (2399/2048) } }, logOuter := sk234LogOuterCertificate, logK := sk234LogKCertificate, logChi := chi296LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45810419029/45809229824) } }, logDArg := sk234LogDArgCertificate }

private noncomputable def leaf5478InnerLog : WideLogData :=
  innerPair272Data

set_option maxRecDepth 1000000 in
private theorem leaf5478LocalValidity :
    LeafFacts leaf5478Box leaf5478Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5478Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22905804117/22904614912) }) = true
      norm_num [leaf5478Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5478CertificateValid :
    WideCertificateValid leaf5478Box leaf5478Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk234ValidityFacts chi296ValidityFacts
    leaf5478LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5478CoverageChecked :
    coverageCheck (innerAD leaf5478Box) leaf5478InnerLog = true := by
  rfl'

private theorem leaf5478InnerLogValid :
    leaf5478InnerLog.Valid 8 (innerAD leaf5478Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint77PositiveFacts.valid leaf5478CoverageChecked

private noncomputable def leaf5478InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907379/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5478InputLogOnePlusV_eq :
    leaf5478InputLogOnePlusV = outerEnclosure 24
      (leaf5478Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5478RoundedFacts : LeafRoundedFacts 8
    leaf5478Certificate.logOnePlusV leaf5478InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5478InputLogOnePlusV_eq }

private noncomputable def leaf5478Inputs : Inputs :=
  inputsOfCaches globalInput sk234RoundedInputs
    chi296InputQChi innerPair272Input
    leaf5478InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5478LowerChecked :
    lowerCheck 24 leaf5478Box leaf5478Inputs = true := by
  rfl'

private theorem leaf5478CoversExact : CoversExact 8
    leaf5478Box leaf5478Certificate leaf5478InnerLog leaf5478Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk234RoundedFacts chi296RoundedFacts
    innerPair272RoundedFacts leaf5478RoundedFacts (by rfl)

private theorem leaf5478FlatSound : Sound leaf5478Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5478CertificateValid
    leaf5478InnerLogValid leaf5478CoversExact leaf5478LowerChecked

private noncomputable def leaf5479Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (251/64), chiLo := (43/128), chiHi := (87/256) }

private noncomputable def leaf5479Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742499/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68713886464) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2482646383/2147483648) }, upper := { exponent := 1, mantissa := (38221/32768) } }, logOuter := sk235LogOuterCertificate, logK := sk235LogKCertificate, logChi := chi295LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431298815/137427772928) } }, logDArg := sk235LogDArgCertificate }

private noncomputable def leaf5479InnerLog : WideLogData :=
  innerPair265Data

set_option maxRecDepth 1000000 in
private theorem leaf5479LocalValidity :
    LeafFacts leaf5479Box leaf5479Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5479Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68713886464) }) = true
      norm_num [leaf5479Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5479CertificateValid :
    WideCertificateValid leaf5479Box leaf5479Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk235ValidityFacts chi295ValidityFacts
    leaf5479LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5479CoverageChecked :
    coverageCheck (innerAD leaf5479Box) leaf5479InnerLog = true := by
  rfl'

private theorem leaf5479InnerLogValid :
    leaf5479InnerLog.Valid 8 (innerAD leaf5479Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint77PositiveFacts.valid leaf5479CoverageChecked

private noncomputable def leaf5479InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629511/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5479InputLogOnePlusV_eq :
    leaf5479InputLogOnePlusV = outerEnclosure 24
      (leaf5479Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5479RoundedFacts : LeafRoundedFacts 8
    leaf5479Certificate.logOnePlusV leaf5479InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5479InputLogOnePlusV_eq }

private noncomputable def leaf5479Inputs : Inputs :=
  inputsOfCaches globalInput sk235RoundedInputs
    chi295InputQChi innerPair265Input
    leaf5479InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5479LowerChecked :
    lowerCheck 24 leaf5479Box leaf5479Inputs = true := by
  rfl'

private theorem leaf5479CoversExact : CoversExact 8
    leaf5479Box leaf5479Certificate leaf5479InnerLog leaf5479Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk235RoundedFacts chi295RoundedFacts
    innerPair265RoundedFacts leaf5479RoundedFacts (by rfl)

private theorem leaf5479FlatSound : Sound leaf5479Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5479CertificateValid
    leaf5479InnerLogValid leaf5479CoversExact leaf5479LowerChecked

private noncomputable def leaf5480Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (63/16), chiLo := (43/128), chiHi := (87/256) }

private noncomputable def leaf5480Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742501/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68713864192) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2488282133/2147483648) }, upper := { exponent := 1, mantissa := (9577/8192) } }, logOuter := sk236LogOuterCertificate, logK := sk236LogKCertificate, logChi := chi295LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431276543/137427728384) } }, logDArg := sk236LogDArgCertificate }

private noncomputable def leaf5480InnerLog : WideLogData :=
  innerPair272Data

set_option maxRecDepth 1000000 in
private theorem leaf5480LocalValidity :
    LeafFacts leaf5480Box leaf5480Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5480Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68713864192) }) = true
      norm_num [leaf5480Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5480CertificateValid :
    WideCertificateValid leaf5480Box leaf5480Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk236ValidityFacts chi295ValidityFacts
    leaf5480LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5480CoverageChecked :
    coverageCheck (innerAD leaf5480Box) leaf5480InnerLog = true := by
  rfl'

private theorem leaf5480InnerLogValid :
    leaf5480InnerLog.Valid 8 (innerAD leaf5480Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint77PositiveFacts.valid leaf5480CoverageChecked

private noncomputable def leaf5480InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814757/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5480InputLogOnePlusV_eq :
    leaf5480InputLogOnePlusV = outerEnclosure 24
      (leaf5480Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5480RoundedFacts : LeafRoundedFacts 8
    leaf5480Certificate.logOnePlusV leaf5480InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5480InputLogOnePlusV_eq }

private noncomputable def leaf5480Inputs : Inputs :=
  inputsOfCaches globalInput sk236RoundedInputs
    chi295InputQChi innerPair272Input
    leaf5480InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5480LowerChecked :
    lowerCheck 24 leaf5480Box leaf5480Inputs = true := by
  rfl'

private theorem leaf5480CoversExact : CoversExact 8
    leaf5480Box leaf5480Certificate leaf5480InnerLog leaf5480Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk236RoundedFacts chi295RoundedFacts
    innerPair272RoundedFacts leaf5480RoundedFacts (by rfl)

private theorem leaf5480FlatSound : Sound leaf5480Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5480CertificateValid
    leaf5480InnerLogValid leaf5480CoversExact leaf5480LowerChecked

private noncomputable def leaf5481Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (251/64), chiLo := (87/256), chiHi := (11/32) }

private noncomputable def leaf5481Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742501/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68713822208) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2499029381/2147483648) }, upper := { exponent := 1, mantissa := (4809/4096) } }, logOuter := sk235LogOuterCertificate, logK := sk235LogKCertificate, logChi := chi296LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431234559/137427644416) } }, logDArg := sk235LogDArgCertificate }

private noncomputable def leaf5481InnerLog : WideLogData :=
  innerPair272Data

set_option maxRecDepth 1000000 in
private theorem leaf5481LocalValidity :
    LeafFacts leaf5481Box leaf5481Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5481Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68713822208) }) = true
      norm_num [leaf5481Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5481CertificateValid :
    WideCertificateValid leaf5481Box leaf5481Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk235ValidityFacts chi296ValidityFacts
    leaf5481LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5481CoverageChecked :
    coverageCheck (innerAD leaf5481Box) leaf5481InnerLog = true := by
  rfl'

private theorem leaf5481InnerLogValid :
    leaf5481InnerLog.Valid 8 (innerAD leaf5481Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint77PositiveFacts.valid leaf5481CoverageChecked

private noncomputable def leaf5481InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629519/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5481InputLogOnePlusV_eq :
    leaf5481InputLogOnePlusV = outerEnclosure 24
      (leaf5481Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5481RoundedFacts : LeafRoundedFacts 8
    leaf5481Certificate.logOnePlusV leaf5481InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5481InputLogOnePlusV_eq }

private noncomputable def leaf5481Inputs : Inputs :=
  inputsOfCaches globalInput sk235RoundedInputs
    chi296InputQChi innerPair272Input
    leaf5481InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5481LowerChecked :
    lowerCheck 24 leaf5481Box leaf5481Inputs = true := by
  rfl'

private theorem leaf5481CoversExact : CoversExact 8
    leaf5481Box leaf5481Certificate leaf5481InnerLog leaf5481Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk235RoundedFacts chi296RoundedFacts
    innerPair272RoundedFacts leaf5481RoundedFacts (by rfl)

private theorem leaf5481FlatSound : Sound leaf5481Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5481CertificateValid
    leaf5481InnerLogValid leaf5481CoversExact leaf5481LowerChecked

private noncomputable def leaf5482Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (63/16), chiLo := (87/256), chiHi := (11/32) }

private noncomputable def leaf5482Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742503/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68713799680) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2504730663/2147483648) }, upper := { exponent := 1, mantissa := (1205/1024) } }, logOuter := sk236LogOuterCertificate, logK := sk236LogKCertificate, logChi := chi296LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431212031/137427599360) } }, logDArg := sk236LogDArgCertificate }

private noncomputable def leaf5482InnerLog : WideLogData :=
  innerPair272Data

set_option maxRecDepth 1000000 in
private theorem leaf5482LocalValidity :
    LeafFacts leaf5482Box leaf5482Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5482Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68713799680) }) = true
      norm_num [leaf5482Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5482CertificateValid :
    WideCertificateValid leaf5482Box leaf5482Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk236ValidityFacts chi296ValidityFacts
    leaf5482LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5482CoverageChecked :
    coverageCheck (innerAD leaf5482Box) leaf5482InnerLog = true := by
  rfl'

private theorem leaf5482InnerLogValid :
    leaf5482InnerLog.Valid 8 (innerAD leaf5482Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint77PositiveFacts.valid leaf5482CoverageChecked

private noncomputable def leaf5482InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814761/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5482InputLogOnePlusV_eq :
    leaf5482InputLogOnePlusV = outerEnclosure 24
      (leaf5482Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5482RoundedFacts : LeafRoundedFacts 8
    leaf5482Certificate.logOnePlusV leaf5482InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5482InputLogOnePlusV_eq }

private noncomputable def leaf5482Inputs : Inputs :=
  inputsOfCaches globalInput sk236RoundedInputs
    chi296InputQChi innerPair272Input
    leaf5482InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5482LowerChecked :
    lowerCheck 24 leaf5482Box leaf5482Inputs = true := by
  rfl'

private theorem leaf5482CoversExact : CoversExact 8
    leaf5482Box leaf5482Certificate leaf5482InnerLog leaf5482Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk236RoundedFacts chi296RoundedFacts
    innerPair272RoundedFacts leaf5482RoundedFacts (by rfl)

private theorem leaf5482FlatSound : Sound leaf5482Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5482CertificateValid
    leaf5482InnerLogValid leaf5482CoversExact leaf5482LowerChecked

private noncomputable def leaf5483Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (21/64), chiHi := (85/256) }

private noncomputable def leaf5483Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742499/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22905804117/22904657152) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2460889759/2147483648) }, upper := { exponent := 1, mantissa := (37889/32768) } }, logOuter := sk237LogOuterCertificate, logK := sk237LogKCertificate, logChi := chi293LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45810461269/45809314304) } }, logDArg := sk237LogDArgCertificate }

private noncomputable def leaf5483InnerLog : WideLogData :=
  innerPair563Data

set_option maxRecDepth 1000000 in
private theorem leaf5483LocalValidity :
    LeafFacts leaf5483Box leaf5483Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5483Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22905804117/22904657152) }) = true
      norm_num [leaf5483Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5483CertificateValid :
    WideCertificateValid leaf5483Box leaf5483Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk237ValidityFacts chi293ValidityFacts
    leaf5483LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5483CoverageChecked :
    coverageCheck (innerAD leaf5483Box) leaf5483InnerLog = true := by
  rfl'

private theorem leaf5483InnerLogValid :
    leaf5483InnerLog.Valid 8 (innerAD leaf5483Box) :=
  wideLogDataValid_of_cachedCheck endpoint295PositiveFacts
    endpoint296PositiveFacts.valid leaf5483CoverageChecked

private noncomputable def leaf5483InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629501/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5483InputLogOnePlusV_eq :
    leaf5483InputLogOnePlusV = outerEnclosure 24
      (leaf5483Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5483RoundedFacts : LeafRoundedFacts 8
    leaf5483Certificate.logOnePlusV leaf5483InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5483InputLogOnePlusV_eq }

private noncomputable def leaf5483Inputs : Inputs :=
  inputsOfCaches globalInput sk237RoundedInputs
    chi293InputQChi innerPair563Input
    leaf5483InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5483LowerChecked :
    lowerCheck 24 leaf5483Box leaf5483Inputs = true := by
  rfl'

private theorem leaf5483CoversExact : CoversExact 8
    leaf5483Box leaf5483Certificate leaf5483InnerLog leaf5483Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk237RoundedFacts chi293RoundedFacts
    innerPair563RoundedFacts leaf5483RoundedFacts (by rfl)

private theorem leaf5483FlatSound : Sound leaf5483Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5483CertificateValid
    leaf5483InnerLogValid leaf5483CoversExact leaf5483LowerChecked

private noncomputable def leaf5484Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (21/64), chiHi := (85/256) }

private noncomputable def leaf5484Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742501/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9816773193/9816278528) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2466394445/2147483648) }, upper := { exponent := 1, mantissa := (18987/16384) } }, logOuter := sk238LogOuterCertificate, logK := sk238LogKCertificate, logChi := chi293LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (19633051721/19632557056) } }, logDArg := sk238LogDArgCertificate }

private noncomputable def leaf5484InnerLog : WideLogData :=
  innerPair571Data

set_option maxRecDepth 1000000 in
private theorem leaf5484LocalValidity :
    LeafFacts leaf5484Box leaf5484Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5484Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9816773193/9816278528) }) = true
      norm_num [leaf5484Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5484CertificateValid :
    WideCertificateValid leaf5484Box leaf5484Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk238ValidityFacts chi293ValidityFacts
    leaf5484LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5484CoverageChecked :
    coverageCheck (innerAD leaf5484Box) leaf5484InnerLog = true := by
  rfl'

private theorem leaf5484InnerLogValid :
    leaf5484InnerLog.Valid 8 (innerAD leaf5484Box) :=
  wideLogDataValid_of_cachedCheck endpoint298PositiveFacts
    endpoint296PositiveFacts.valid leaf5484CoverageChecked

private noncomputable def leaf5484InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629503/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5484InputLogOnePlusV_eq :
    leaf5484InputLogOnePlusV = outerEnclosure 24
      (leaf5484Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5484RoundedFacts : LeafRoundedFacts 8
    leaf5484Certificate.logOnePlusV leaf5484InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5484InputLogOnePlusV_eq }

private noncomputable def leaf5484Inputs : Inputs :=
  inputsOfCaches globalInput sk238RoundedInputs
    chi293InputQChi innerPair571Input
    leaf5484InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5484LowerChecked :
    lowerCheck 24 leaf5484Box leaf5484Inputs = true := by
  rfl'

private theorem leaf5484CoversExact : CoversExact 8
    leaf5484Box leaf5484Certificate leaf5484InnerLog leaf5484Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk238RoundedFacts chi293RoundedFacts
    innerPair571RoundedFacts leaf5484RoundedFacts (by rfl)

private theorem leaf5484FlatSound : Sound leaf5484Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5484CertificateValid
    leaf5484InnerLogValid leaf5484CoversExact leaf5484LowerChecked

private noncomputable def leaf5485Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (85/256), chiHi := (43/128) }

private noncomputable def leaf5485Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742501/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9816773193/9816272384) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2477403821/2147483648) }, upper := { exponent := 1, mantissa := (19071/16384) } }, logOuter := sk237LogOuterCertificate, logK := sk237LogKCertificate, logChi := chi294LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (19633045577/19632544768) } }, logDArg := sk237LogDArgCertificate }

private noncomputable def leaf5485InnerLog : WideLogData :=
  innerPair265Data

set_option maxRecDepth 1000000 in
private theorem leaf5485LocalValidity :
    LeafFacts leaf5485Box leaf5485Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5485Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9816773193/9816272384) }) = true
      norm_num [leaf5485Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5485CertificateValid :
    WideCertificateValid leaf5485Box leaf5485Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk237ValidityFacts chi294ValidityFacts
    leaf5485LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5485CoverageChecked :
    coverageCheck (innerAD leaf5485Box) leaf5485InnerLog = true := by
  rfl'

private theorem leaf5485InnerLogValid :
    leaf5485InnerLog.Valid 8 (innerAD leaf5485Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint77PositiveFacts.valid leaf5485CoverageChecked

private noncomputable def leaf5485InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629509/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5485InputLogOnePlusV_eq :
    leaf5485InputLogOnePlusV = outerEnclosure 24
      (leaf5485Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5485RoundedFacts : LeafRoundedFacts 8
    leaf5485Certificate.logOnePlusV leaf5485InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5485InputLogOnePlusV_eq }

private noncomputable def leaf5485Inputs : Inputs :=
  inputsOfCaches globalInput sk237RoundedInputs
    chi294InputQChi innerPair265Input
    leaf5485InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5485LowerChecked :
    lowerCheck 24 leaf5485Box leaf5485Inputs = true := by
  rfl'

private theorem leaf5485CoversExact : CoversExact 8
    leaf5485Box leaf5485Certificate leaf5485InnerLog leaf5485Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk237RoundedFacts chi294RoundedFacts
    innerPair265RoundedFacts leaf5485RoundedFacts (by rfl)

private theorem leaf5485FlatSound : Sound leaf5485Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5485CertificateValid
    leaf5485InnerLogValid leaf5485CoversExact leaf5485LowerChecked

private noncomputable def leaf5486Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (85/256), chiHi := (43/128) }

private noncomputable def leaf5486Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742503/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22905804117/22904628224) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2482974039/2147483648) }, upper := { exponent := 1, mantissa := (9557/8192) } }, logOuter := sk238LogOuterCertificate, logK := sk238LogKCertificate, logChi := chi294LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45810432341/45809256448) } }, logDArg := sk238LogDArgCertificate }

private noncomputable def leaf5486InnerLog : WideLogData :=
  innerPair265Data

set_option maxRecDepth 1000000 in
private theorem leaf5486LocalValidity :
    LeafFacts leaf5486Box leaf5486Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5486Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22905804117/22904628224) }) = true
      norm_num [leaf5486Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5486CertificateValid :
    WideCertificateValid leaf5486Box leaf5486Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk238ValidityFacts chi294ValidityFacts
    leaf5486LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5486CoverageChecked :
    coverageCheck (innerAD leaf5486Box) leaf5486InnerLog = true := by
  rfl'

private theorem leaf5486InnerLogValid :
    leaf5486InnerLog.Valid 8 (innerAD leaf5486Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint77PositiveFacts.valid leaf5486CoverageChecked

private noncomputable def leaf5486InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629511/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5486InputLogOnePlusV_eq :
    leaf5486InputLogOnePlusV = outerEnclosure 24
      (leaf5486Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5486RoundedFacts : LeafRoundedFacts 8
    leaf5486Certificate.logOnePlusV leaf5486InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5486InputLogOnePlusV_eq }

private noncomputable def leaf5486Inputs : Inputs :=
  inputsOfCaches globalInput sk238RoundedInputs
    chi294InputQChi innerPair265Input
    leaf5486InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5486LowerChecked :
    lowerCheck 24 leaf5486Box leaf5486Inputs = true := by
  rfl'

private theorem leaf5486CoversExact : CoversExact 8
    leaf5486Box leaf5486Certificate leaf5486InnerLog leaf5486Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk238RoundedFacts chi294RoundedFacts
    innerPair265RoundedFacts leaf5486RoundedFacts (by rfl)

private theorem leaf5486FlatSound : Sound leaf5486Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5486CertificateValid
    leaf5486InnerLogValid leaf5486CoversExact leaf5486LowerChecked

private noncomputable def leaf5487Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (21/64), chiHi := (85/256) }

private noncomputable def leaf5487Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742503/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68713927936) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2471899131/2147483648) }, upper := { exponent := 1, mantissa := (38059/32768) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi293LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431340287/137427855872) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf5487InnerLog : WideLogData :=
  innerPair265Data

set_option maxRecDepth 1000000 in
private theorem leaf5487LocalValidity :
    LeafFacts leaf5487Box leaf5487Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5487Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68713927936) }) = true
      norm_num [leaf5487Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5487CertificateValid :
    WideCertificateValid leaf5487Box leaf5487Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi293ValidityFacts
    leaf5487LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5487CoverageChecked :
    coverageCheck (innerAD leaf5487Box) leaf5487InnerLog = true := by
  rfl'

private theorem leaf5487InnerLogValid :
    leaf5487InnerLog.Valid 8 (innerAD leaf5487Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint77PositiveFacts.valid leaf5487CoverageChecked

private noncomputable def leaf5487InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814753/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5487InputLogOnePlusV_eq :
    leaf5487InputLogOnePlusV = outerEnclosure 24
      (leaf5487Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5487RoundedFacts : LeafRoundedFacts 8
    leaf5487Certificate.logOnePlusV leaf5487InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5487InputLogOnePlusV_eq }

private noncomputable def leaf5487Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi293InputQChi innerPair265Input
    leaf5487InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5487LowerChecked :
    lowerCheck 24 leaf5487Box leaf5487Inputs = true := by
  rfl'

private theorem leaf5487CoversExact : CoversExact 8
    leaf5487Box leaf5487Certificate leaf5487InnerLog leaf5487Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi293RoundedFacts
    innerPair265RoundedFacts leaf5487RoundedFacts (by rfl)

private theorem leaf5487FlatSound : Sound leaf5487Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5487CertificateValid
    leaf5487InnerLogValid leaf5487CoversExact leaf5487LowerChecked

private noncomputable def leaf5488Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (21/64), chiHi := (85/256) }

private noncomputable def leaf5488Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742505/1073741824) }, vSqrt := { lower := (65527/65536), upper := (7635268039/7634878464) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2477403817/2147483648) }, upper := { exponent := 1, mantissa := (149/128) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi293LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (15270146503/15269756928) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf5488InnerLog : WideLogData :=
  innerPair265Data

set_option maxRecDepth 1000000 in
private theorem leaf5488LocalValidity :
    LeafFacts leaf5488Box leaf5488Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5488Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (7635268039/7634878464) }) = true
      norm_num [leaf5488Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5488CertificateValid :
    WideCertificateValid leaf5488Box leaf5488Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi293ValidityFacts
    leaf5488LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5488CoverageChecked :
    coverageCheck (innerAD leaf5488Box) leaf5488InnerLog = true := by
  rfl'

private theorem leaf5488InnerLogValid :
    leaf5488InnerLog.Valid 8 (innerAD leaf5488Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint77PositiveFacts.valid leaf5488CoverageChecked

private noncomputable def leaf5488InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629509/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5488InputLogOnePlusV_eq :
    leaf5488InputLogOnePlusV = outerEnclosure 24
      (leaf5488Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5488RoundedFacts : LeafRoundedFacts 8
    leaf5488Certificate.logOnePlusV leaf5488InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5488InputLogOnePlusV_eq }

private noncomputable def leaf5488Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi293InputQChi innerPair265Input
    leaf5488InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5488LowerChecked :
    lowerCheck 24 leaf5488Box leaf5488Inputs = true := by
  rfl'

private theorem leaf5488CoversExact : CoversExact 8
    leaf5488Box leaf5488Certificate leaf5488InnerLog leaf5488Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi293RoundedFacts
    innerPair265RoundedFacts leaf5488RoundedFacts (by rfl)

private theorem leaf5488FlatSound : Sound leaf5488Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5488CertificateValid
    leaf5488InnerLogValid leaf5488CoversExact leaf5488LowerChecked

private noncomputable def leaf5489Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (85/256), chiHi := (43/128) }

private noncomputable def leaf5489Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742505/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68713862656) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2488544257/2147483648) }, upper := { exponent := 1, mantissa := (19157/16384) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi294LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431275007/137427725312) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf5489InnerLog : WideLogData :=
  innerPair272Data

set_option maxRecDepth 1000000 in
private theorem leaf5489LocalValidity :
    LeafFacts leaf5489Box leaf5489Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5489Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68713862656) }) = true
      norm_num [leaf5489Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5489CertificateValid :
    WideCertificateValid leaf5489Box leaf5489Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi294ValidityFacts
    leaf5489LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5489CoverageChecked :
    coverageCheck (innerAD leaf5489Box) leaf5489InnerLog = true := by
  rfl'

private theorem leaf5489InnerLogValid :
    leaf5489InnerLog.Valid 8 (innerAD leaf5489Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint77PositiveFacts.valid leaf5489CoverageChecked

private noncomputable def leaf5489InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814757/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5489InputLogOnePlusV_eq :
    leaf5489InputLogOnePlusV = outerEnclosure 24
      (leaf5489Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5489RoundedFacts : LeafRoundedFacts 8
    leaf5489Certificate.logOnePlusV leaf5489InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5489InputLogOnePlusV_eq }

private noncomputable def leaf5489Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi294InputQChi innerPair272Input
    leaf5489InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5489LowerChecked :
    lowerCheck 24 leaf5489Box leaf5489Inputs = true := by
  rfl'

private theorem leaf5489CoversExact : CoversExact 8
    leaf5489Box leaf5489Certificate leaf5489InnerLog leaf5489Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi294RoundedFacts
    innerPair272RoundedFacts leaf5489RoundedFacts (by rfl)

private theorem leaf5489FlatSound : Sound leaf5489Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5489CertificateValid
    leaf5489InnerLogValid leaf5489CoversExact leaf5489LowerChecked

private noncomputable def leaf5490Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (85/256), chiHi := (43/128) }

private noncomputable def leaf5490Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742507/1073741824) }, vSqrt := { lower := (65527/65536), upper := (68717412351/68713840640) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2494114475/2147483648) }, upper := { exponent := 1, mantissa := (75/64) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi294LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (137431252991/137427681280) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf5490InnerLog : WideLogData :=
  innerPair272Data

set_option maxRecDepth 1000000 in
private theorem leaf5490LocalValidity :
    LeafFacts leaf5490Box leaf5490Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5490Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (68717412351/68713840640) }) = true
      norm_num [leaf5490Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5490CertificateValid :
    WideCertificateValid leaf5490Box leaf5490Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi294ValidityFacts
    leaf5490LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5490CoverageChecked :
    coverageCheck (innerAD leaf5490Box) leaf5490InnerLog = true := by
  rfl'

private theorem leaf5490InnerLogValid :
    leaf5490InnerLog.Valid 8 (innerAD leaf5490Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint77PositiveFacts.valid leaf5490CoverageChecked

private noncomputable def leaf5490InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629517/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5490InputLogOnePlusV_eq :
    leaf5490InputLogOnePlusV = outerEnclosure 24
      (leaf5490Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5490RoundedFacts : LeafRoundedFacts 8
    leaf5490Certificate.logOnePlusV leaf5490InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5490InputLogOnePlusV_eq }

private noncomputable def leaf5490Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi294InputQChi innerPair272Input
    leaf5490InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5490LowerChecked :
    lowerCheck 24 leaf5490Box leaf5490Inputs = true := by
  rfl'

private theorem leaf5490CoversExact : CoversExact 8
    leaf5490Box leaf5490Certificate leaf5490InnerLog leaf5490Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi294RoundedFacts
    innerPair272RoundedFacts leaf5490RoundedFacts (by rfl)

private theorem leaf5490FlatSound : Sound leaf5490Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5490CertificateValid
    leaf5490InnerLogValid leaf5490CoversExact leaf5490LowerChecked

private noncomputable def leaf5491Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (43/128), chiHi := (87/256) }

private noncomputable def leaf5491Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742503/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68713841920) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2493917883/2147483648) }, upper := { exponent := 1, mantissa := (38395/32768) } }, logOuter := sk237LogOuterCertificate, logK := sk237LogKCertificate, logChi := chi295LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431254271/137427683840) } }, logDArg := sk237LogDArgCertificate }

private noncomputable def leaf5491InnerLog : WideLogData :=
  innerPair272Data

set_option maxRecDepth 1000000 in
private theorem leaf5491LocalValidity :
    LeafFacts leaf5491Box leaf5491Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5491Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68713841920) }) = true
      norm_num [leaf5491Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5491CertificateValid :
    WideCertificateValid leaf5491Box leaf5491Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk237ValidityFacts chi295ValidityFacts
    leaf5491LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5491CoverageChecked :
    coverageCheck (innerAD leaf5491Box) leaf5491InnerLog = true := by
  rfl'

private theorem leaf5491InnerLogValid :
    leaf5491InnerLog.Valid 8 (innerAD leaf5491Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint77PositiveFacts.valid leaf5491CoverageChecked

private noncomputable def leaf5491InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629517/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5491InputLogOnePlusV_eq :
    leaf5491InputLogOnePlusV = outerEnclosure 24
      (leaf5491Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5491RoundedFacts : LeafRoundedFacts 8
    leaf5491Certificate.logOnePlusV leaf5491InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5491InputLogOnePlusV_eq }

private noncomputable def leaf5491Inputs : Inputs :=
  inputsOfCaches globalInput sk237RoundedInputs
    chi295InputQChi innerPair272Input
    leaf5491InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5491LowerChecked :
    lowerCheck 24 leaf5491Box leaf5491Inputs = true := by
  rfl'

private theorem leaf5491CoversExact : CoversExact 8
    leaf5491Box leaf5491Certificate leaf5491InnerLog leaf5491Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk237RoundedFacts chi295RoundedFacts
    innerPair272RoundedFacts leaf5491RoundedFacts (by rfl)

private theorem leaf5491FlatSound : Sound leaf5491Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5491CertificateValid
    leaf5491InnerLogValid leaf5491CoversExact leaf5491LowerChecked

private noncomputable def leaf5492Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (43/128), chiHi := (87/256) }

private noncomputable def leaf5492Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742505/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68713819648) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2499553633/2147483648) }, upper := { exponent := 1, mantissa := (19241/16384) } }, logOuter := sk238LogOuterCertificate, logK := sk238LogKCertificate, logChi := chi295LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431231999/137427639296) } }, logDArg := sk238LogDArgCertificate }

private noncomputable def leaf5492InnerLog : WideLogData :=
  innerPair272Data

set_option maxRecDepth 1000000 in
private theorem leaf5492LocalValidity :
    LeafFacts leaf5492Box leaf5492Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5492Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68713819648) }) = true
      norm_num [leaf5492Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5492CertificateValid :
    WideCertificateValid leaf5492Box leaf5492Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk238ValidityFacts chi295ValidityFacts
    leaf5492LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5492CoverageChecked :
    coverageCheck (innerAD leaf5492Box) leaf5492InnerLog = true := by
  rfl'

private theorem leaf5492InnerLogValid :
    leaf5492InnerLog.Valid 8 (innerAD leaf5492Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint77PositiveFacts.valid leaf5492CoverageChecked

private noncomputable def leaf5492InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629519/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5492InputLogOnePlusV_eq :
    leaf5492InputLogOnePlusV = outerEnclosure 24
      (leaf5492Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5492RoundedFacts : LeafRoundedFacts 8
    leaf5492Certificate.logOnePlusV leaf5492InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5492InputLogOnePlusV_eq }

private noncomputable def leaf5492Inputs : Inputs :=
  inputsOfCaches globalInput sk238RoundedInputs
    chi295InputQChi innerPair272Input
    leaf5492InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5492LowerChecked :
    lowerCheck 24 leaf5492Box leaf5492Inputs = true := by
  rfl'

private theorem leaf5492CoversExact : CoversExact 8
    leaf5492Box leaf5492Certificate leaf5492InnerLog leaf5492Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk238RoundedFacts chi295RoundedFacts
    innerPair272RoundedFacts leaf5492RoundedFacts (by rfl)

private theorem leaf5492FlatSound : Sound leaf5492Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5492CertificateValid
    leaf5492InnerLogValid leaf5492CoversExact leaf5492LowerChecked

private noncomputable def leaf5493Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (87/256), chiHi := (11/32) }

private noncomputable def leaf5493Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742505/1073741824) }, vSqrt := { lower := (8191/8192), upper := (7635268039/7634864128) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2510431945/2147483648) }, upper := { exponent := 1, mantissa := (4831/4096) } }, logOuter := sk237LogOuterCertificate, logK := sk237LogKCertificate, logChi := chi296LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (15270132167/15269728256) } }, logDArg := sk237LogDArgCertificate }

private noncomputable def leaf5493InnerLog : WideLogData :=
  innerPair272Data

set_option maxRecDepth 1000000 in
private theorem leaf5493LocalValidity :
    LeafFacts leaf5493Box leaf5493Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5493Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (7635268039/7634864128) }) = true
      norm_num [leaf5493Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5493CertificateValid :
    WideCertificateValid leaf5493Box leaf5493Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk237ValidityFacts chi296ValidityFacts
    leaf5493LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5493CoverageChecked :
    coverageCheck (innerAD leaf5493Box) leaf5493InnerLog = true := by
  rfl'

private theorem leaf5493InnerLogValid :
    leaf5493InnerLog.Valid 8 (innerAD leaf5493Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint77PositiveFacts.valid leaf5493CoverageChecked

private noncomputable def leaf5493InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629525/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5493InputLogOnePlusV_eq :
    leaf5493InputLogOnePlusV = outerEnclosure 24
      (leaf5493Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5493RoundedFacts : LeafRoundedFacts 8
    leaf5493Certificate.logOnePlusV leaf5493InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5493InputLogOnePlusV_eq }

private noncomputable def leaf5493Inputs : Inputs :=
  inputsOfCaches globalInput sk237RoundedInputs
    chi296InputQChi innerPair272Input
    leaf5493InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5493LowerChecked :
    lowerCheck 24 leaf5493Box leaf5493Inputs = true := by
  rfl'

private theorem leaf5493CoversExact : CoversExact 8
    leaf5493Box leaf5493Certificate leaf5493InnerLog leaf5493Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk237RoundedFacts chi296RoundedFacts
    innerPair272RoundedFacts leaf5493RoundedFacts (by rfl)

private theorem leaf5493FlatSound : Sound leaf5493Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5493CertificateValid
    leaf5493InnerLogValid leaf5493CoversExact leaf5493LowerChecked

private noncomputable def leaf5494Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (87/256), chiHi := (11/32) }

private noncomputable def leaf5494Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742507/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68713754624) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2516133227/2147483648) }, upper := { exponent := 1, mantissa := (2421/2048) } }, logOuter := sk238LogOuterCertificate, logK := sk238LogKCertificate, logChi := chi296LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431166975/137427509248) } }, logDArg := sk238LogDArgCertificate }

private noncomputable def leaf5494InnerLog : WideLogData :=
  innerPair272Data

set_option maxRecDepth 1000000 in
private theorem leaf5494LocalValidity :
    LeafFacts leaf5494Box leaf5494Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5494Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68713754624) }) = true
      norm_num [leaf5494Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5494CertificateValid :
    WideCertificateValid leaf5494Box leaf5494Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk238ValidityFacts chi296ValidityFacts
    leaf5494LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5494CoverageChecked :
    coverageCheck (innerAD leaf5494Box) leaf5494InnerLog = true := by
  rfl'

private theorem leaf5494InnerLogValid :
    leaf5494InnerLog.Valid 8 (innerAD leaf5494Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint77PositiveFacts.valid leaf5494CoverageChecked

private noncomputable def leaf5494InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629527/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5494InputLogOnePlusV_eq :
    leaf5494InputLogOnePlusV = outerEnclosure 24
      (leaf5494Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5494RoundedFacts : LeafRoundedFacts 8
    leaf5494Certificate.logOnePlusV leaf5494InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5494InputLogOnePlusV_eq }

private noncomputable def leaf5494Inputs : Inputs :=
  inputsOfCaches globalInput sk238RoundedInputs
    chi296InputQChi innerPair272Input
    leaf5494InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5494LowerChecked :
    lowerCheck 24 leaf5494Box leaf5494Inputs = true := by
  rfl'

private theorem leaf5494CoversExact : CoversExact 8
    leaf5494Box leaf5494Certificate leaf5494InnerLog leaf5494Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk238RoundedFacts chi296RoundedFacts
    innerPair272RoundedFacts leaf5494RoundedFacts (by rfl)

private theorem leaf5494FlatSound : Sound leaf5494Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5494CertificateValid
    leaf5494InnerLogValid leaf5494CoversExact leaf5494LowerChecked

private noncomputable def leaf5495Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (43/128), chiHi := (87/256) }

private noncomputable def leaf5495Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742507/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9816773193/9816256768) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2505189383/2147483648) }, upper := { exponent := 1, mantissa := (38569/32768) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi295LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (19633029961/19632513536) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf5495InnerLog : WideLogData :=
  innerPair272Data

set_option maxRecDepth 1000000 in
private theorem leaf5495LocalValidity :
    LeafFacts leaf5495Box leaf5495Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5495Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9816773193/9816256768) }) = true
      norm_num [leaf5495Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5495CertificateValid :
    WideCertificateValid leaf5495Box leaf5495Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi295ValidityFacts
    leaf5495LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5495CoverageChecked :
    coverageCheck (innerAD leaf5495Box) leaf5495InnerLog = true := by
  rfl'

private theorem leaf5495InnerLogValid :
    leaf5495InnerLog.Valid 8 (innerAD leaf5495Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint77PositiveFacts.valid leaf5495CoverageChecked

private noncomputable def leaf5495InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814761/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5495InputLogOnePlusV_eq :
    leaf5495InputLogOnePlusV = outerEnclosure 24
      (leaf5495Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5495RoundedFacts : LeafRoundedFacts 8
    leaf5495Certificate.logOnePlusV leaf5495InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5495InputLogOnePlusV_eq }

private noncomputable def leaf5495Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi295InputQChi innerPair272Input
    leaf5495InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5495LowerChecked :
    lowerCheck 24 leaf5495Box leaf5495Inputs = true := by
  rfl'

private theorem leaf5495CoversExact : CoversExact 8
    leaf5495Box leaf5495Certificate leaf5495InnerLog leaf5495Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi295RoundedFacts
    innerPair272RoundedFacts leaf5495RoundedFacts (by rfl)

private theorem leaf5495FlatSound : Sound leaf5495Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5495CertificateValid
    leaf5495InnerLogValid leaf5495CoversExact leaf5495LowerChecked

private noncomputable def leaf5496Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (43/128), chiHi := (87/256) }

private noncomputable def leaf5496Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742509/1073741824) }, vSqrt := { lower := (65527/65536), upper := (68717412351/68713775104) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2510825133/2147483648) }, upper := { exponent := 1, mantissa := (151/128) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi295LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (137431187455/137427550208) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf5496InnerLog : WideLogData :=
  innerPair272Data

set_option maxRecDepth 1000000 in
private theorem leaf5496LocalValidity :
    LeafFacts leaf5496Box leaf5496Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5496Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (68717412351/68713775104) }) = true
      norm_num [leaf5496Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5496CertificateValid :
    WideCertificateValid leaf5496Box leaf5496Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi295ValidityFacts
    leaf5496LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5496CoverageChecked :
    coverageCheck (innerAD leaf5496Box) leaf5496InnerLog = true := by
  rfl'

private theorem leaf5496InnerLogValid :
    leaf5496InnerLog.Valid 8 (innerAD leaf5496Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint77PositiveFacts.valid leaf5496CoverageChecked

private noncomputable def leaf5496InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629525/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5496InputLogOnePlusV_eq :
    leaf5496InputLogOnePlusV = outerEnclosure 24
      (leaf5496Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5496RoundedFacts : LeafRoundedFacts 8
    leaf5496Certificate.logOnePlusV leaf5496InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5496InputLogOnePlusV_eq }

private noncomputable def leaf5496Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi295InputQChi innerPair272Input
    leaf5496InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5496LowerChecked :
    lowerCheck 24 leaf5496Box leaf5496Inputs = true := by
  rfl'

private theorem leaf5496CoversExact : CoversExact 8
    leaf5496Box leaf5496Certificate leaf5496InnerLog leaf5496Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi295RoundedFacts
    innerPair272RoundedFacts leaf5496RoundedFacts (by rfl)

private theorem leaf5496FlatSound : Sound leaf5496Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5496CertificateValid
    leaf5496InnerLogValid leaf5496CoversExact leaf5496LowerChecked

private noncomputable def leaf5497Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (87/256), chiHi := (11/32) }

private noncomputable def leaf5497Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742509/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68713732096) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2521834509/2147483648) }, upper := { exponent := 1, mantissa := (4853/4096) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi296LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431144447/137427464192) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf5497InnerLog : WideLogData :=
  innerPair272Data

set_option maxRecDepth 1000000 in
private theorem leaf5497LocalValidity :
    LeafFacts leaf5497Box leaf5497Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5497Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68713732096) }) = true
      norm_num [leaf5497Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5497CertificateValid :
    WideCertificateValid leaf5497Box leaf5497Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi296ValidityFacts
    leaf5497LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5497CoverageChecked :
    coverageCheck (innerAD leaf5497Box) leaf5497InnerLog = true := by
  rfl'

private theorem leaf5497InnerLogValid :
    leaf5497InnerLog.Valid 8 (innerAD leaf5497Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint77PositiveFacts.valid leaf5497CoverageChecked

private noncomputable def leaf5497InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814765/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5497InputLogOnePlusV_eq :
    leaf5497InputLogOnePlusV = outerEnclosure 24
      (leaf5497Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5497RoundedFacts : LeafRoundedFacts 8
    leaf5497Certificate.logOnePlusV leaf5497InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5497InputLogOnePlusV_eq }

private noncomputable def leaf5497Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi296InputQChi innerPair272Input
    leaf5497InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5497LowerChecked :
    lowerCheck 24 leaf5497Box leaf5497Inputs = true := by
  rfl'

private theorem leaf5497CoversExact : CoversExact 8
    leaf5497Box leaf5497Certificate leaf5497InnerLog leaf5497Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi296RoundedFacts
    innerPair272RoundedFacts leaf5497RoundedFacts (by rfl)

private theorem leaf5497FlatSound : Sound leaf5497Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5497CertificateValid
    leaf5497InnerLogValid leaf5497CoversExact leaf5497LowerChecked

private noncomputable def leaf5498Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (87/256), chiHi := (11/32) }

private noncomputable def leaf5498Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742511/1073741824) }, vSqrt := { lower := (65527/65536), upper := (3272257731/3272081408) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2527535791/2147483648) }, upper := { exponent := 1, mantissa := (19/16) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi296LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (6544339139/6544162816) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf5498InnerLog : WideLogData :=
  innerPair272Data

set_option maxRecDepth 1000000 in
private theorem leaf5498LocalValidity :
    LeafFacts leaf5498Box leaf5498Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5498Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (3272257731/3272081408) }) = true
      norm_num [leaf5498Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5498CertificateValid :
    WideCertificateValid leaf5498Box leaf5498Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi296ValidityFacts
    leaf5498LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5498CoverageChecked :
    coverageCheck (innerAD leaf5498Box) leaf5498InnerLog = true := by
  rfl'

private theorem leaf5498InnerLogValid :
    leaf5498InnerLog.Valid 8 (innerAD leaf5498Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint77PositiveFacts.valid leaf5498CoverageChecked

private noncomputable def leaf5498InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629533/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5498InputLogOnePlusV_eq :
    leaf5498InputLogOnePlusV = outerEnclosure 24
      (leaf5498Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5498RoundedFacts : LeafRoundedFacts 8
    leaf5498Certificate.logOnePlusV leaf5498InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5498InputLogOnePlusV_eq }

private noncomputable def leaf5498Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi296InputQChi innerPair272Input
    leaf5498InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5498LowerChecked :
    lowerCheck 24 leaf5498Box leaf5498Inputs = true := by
  rfl'

private theorem leaf5498CoversExact : CoversExact 8
    leaf5498Box leaf5498Certificate leaf5498InnerLog leaf5498Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi296RoundedFacts
    innerPair272RoundedFacts leaf5498RoundedFacts (by rfl)

private theorem leaf5498FlatSound : Sound leaf5498Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5498CertificateValid
    leaf5498InnerLogValid leaf5498CoversExact leaf5498LowerChecked

private noncomputable def component110Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (5/16), chiHi := (81/256) }

set_option maxRecDepth 1000000 in
private theorem component110Node0_sound : Sound component110Node0Box :=
  sound_of_literal_split component110Node0Box leaf5435Box leaf5436Box
    .k (249/64) (by rfl) (by rfl)
    leaf5435FlatSound leaf5436FlatSound

private noncomputable def component110Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (81/256), chiHi := (41/128) }

set_option maxRecDepth 1000000 in
private theorem component110Node1_sound : Sound component110Node1Box :=
  sound_of_literal_split component110Node1Box leaf5437Box leaf5438Box
    .k (249/64) (by rfl) (by rfl)
    leaf5437FlatSound leaf5438FlatSound

private noncomputable def component110Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (5/16), chiHi := (41/128) }

set_option maxRecDepth 1000000 in
private theorem component110Node2_sound : Sound component110Node2Box :=
  sound_of_literal_split component110Node2Box component110Node0Box component110Node1Box
    .chi (81/256) (by rfl) (by rfl)
    component110Node0_sound component110Node1_sound

private noncomputable def component110Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (5/16), chiHi := (81/256) }

set_option maxRecDepth 1000000 in
private theorem component110Node3_sound : Sound component110Node3Box :=
  sound_of_literal_split component110Node3Box leaf5439Box leaf5440Box
    .k (251/64) (by rfl) (by rfl)
    leaf5439FlatSound leaf5440FlatSound

private noncomputable def component110Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (81/256), chiHi := (41/128) }

set_option maxRecDepth 1000000 in
private theorem component110Node4_sound : Sound component110Node4Box :=
  sound_of_literal_split component110Node4Box leaf5441Box leaf5442Box
    .k (251/64) (by rfl) (by rfl)
    leaf5441FlatSound leaf5442FlatSound

private noncomputable def component110Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (5/16), chiHi := (41/128) }

set_option maxRecDepth 1000000 in
private theorem component110Node5_sound : Sound component110Node5Box :=
  sound_of_literal_split component110Node5Box component110Node3Box component110Node4Box
    .chi (81/256) (by rfl) (by rfl)
    component110Node3_sound component110Node4_sound

private noncomputable def component110Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (5/16), chiHi := (41/128) }

set_option maxRecDepth 1000000 in
private theorem component110Node6_sound : Sound component110Node6Box :=
  sound_of_literal_split component110Node6Box component110Node2Box component110Node5Box
    .k (125/32) (by rfl) (by rfl)
    component110Node2_sound component110Node5_sound

private noncomputable def component110Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (41/128), chiHi := (83/256) }

set_option maxRecDepth 1000000 in
private theorem component110Node7_sound : Sound component110Node7Box :=
  sound_of_literal_split component110Node7Box leaf5443Box leaf5444Box
    .k (249/64) (by rfl) (by rfl)
    leaf5443FlatSound leaf5444FlatSound

private noncomputable def component110Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (83/256), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component110Node8_sound : Sound component110Node8Box :=
  sound_of_literal_split component110Node8Box leaf5445Box leaf5446Box
    .k (249/64) (by rfl) (by rfl)
    leaf5445FlatSound leaf5446FlatSound

private noncomputable def component110Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (41/128), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component110Node9_sound : Sound component110Node9Box :=
  sound_of_literal_split component110Node9Box component110Node7Box component110Node8Box
    .chi (83/256) (by rfl) (by rfl)
    component110Node7_sound component110Node8_sound

private noncomputable def component110Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (41/128), chiHi := (83/256) }

set_option maxRecDepth 1000000 in
private theorem component110Node10_sound : Sound component110Node10Box :=
  sound_of_literal_split component110Node10Box leaf5447Box leaf5448Box
    .k (251/64) (by rfl) (by rfl)
    leaf5447FlatSound leaf5448FlatSound

private noncomputable def component110Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (83/256), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component110Node11_sound : Sound component110Node11Box :=
  sound_of_literal_split component110Node11Box leaf5449Box leaf5450Box
    .k (251/64) (by rfl) (by rfl)
    leaf5449FlatSound leaf5450FlatSound

private noncomputable def component110Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (41/128), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component110Node12_sound : Sound component110Node12Box :=
  sound_of_literal_split component110Node12Box component110Node10Box component110Node11Box
    .chi (83/256) (by rfl) (by rfl)
    component110Node10_sound component110Node11_sound

private noncomputable def component110Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (41/128), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component110Node13_sound : Sound component110Node13Box :=
  sound_of_literal_split component110Node13Box component110Node9Box component110Node12Box
    .k (125/32) (by rfl) (by rfl)
    component110Node9_sound component110Node12_sound

private noncomputable def component110Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (5/16), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component110Node14_sound : Sound component110Node14Box :=
  sound_of_literal_split component110Node14Box component110Node6Box component110Node13Box
    .chi (41/128) (by rfl) (by rfl)
    component110Node6_sound component110Node13_sound

private noncomputable def component110Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (5/16), chiHi := (81/256) }

set_option maxRecDepth 1000000 in
private theorem component110Node15_sound : Sound component110Node15Box :=
  sound_of_literal_split component110Node15Box leaf5451Box leaf5452Box
    .k (253/64) (by rfl) (by rfl)
    leaf5451FlatSound leaf5452FlatSound

private noncomputable def component110Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (81/256), chiHi := (41/128) }

set_option maxRecDepth 1000000 in
private theorem component110Node16_sound : Sound component110Node16Box :=
  sound_of_literal_split component110Node16Box leaf5453Box leaf5454Box
    .k (253/64) (by rfl) (by rfl)
    leaf5453FlatSound leaf5454FlatSound

private noncomputable def component110Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (5/16), chiHi := (41/128) }

set_option maxRecDepth 1000000 in
private theorem component110Node17_sound : Sound component110Node17Box :=
  sound_of_literal_split component110Node17Box component110Node15Box component110Node16Box
    .chi (81/256) (by rfl) (by rfl)
    component110Node15_sound component110Node16_sound

private noncomputable def component110Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (5/16), chiHi := (81/256) }

set_option maxRecDepth 1000000 in
private theorem component110Node18_sound : Sound component110Node18Box :=
  sound_of_literal_split component110Node18Box leaf5455Box leaf5456Box
    .k (255/64) (by rfl) (by rfl)
    leaf5455FlatSound leaf5456FlatSound

private noncomputable def component110Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (81/256), chiHi := (41/128) }

set_option maxRecDepth 1000000 in
private theorem component110Node19_sound : Sound component110Node19Box :=
  sound_of_literal_split component110Node19Box leaf5457Box leaf5458Box
    .k (255/64) (by rfl) (by rfl)
    leaf5457FlatSound leaf5458FlatSound

private noncomputable def component110Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (5/16), chiHi := (41/128) }

set_option maxRecDepth 1000000 in
private theorem component110Node20_sound : Sound component110Node20Box :=
  sound_of_literal_split component110Node20Box component110Node18Box component110Node19Box
    .chi (81/256) (by rfl) (by rfl)
    component110Node18_sound component110Node19_sound

private noncomputable def component110Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (5/16), chiHi := (41/128) }

set_option maxRecDepth 1000000 in
private theorem component110Node21_sound : Sound component110Node21Box :=
  sound_of_literal_split component110Node21Box component110Node17Box component110Node20Box
    .k (127/32) (by rfl) (by rfl)
    component110Node17_sound component110Node20_sound

private noncomputable def component110Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (41/128), chiHi := (83/256) }

set_option maxRecDepth 1000000 in
private theorem component110Node22_sound : Sound component110Node22Box :=
  sound_of_literal_split component110Node22Box leaf5459Box leaf5460Box
    .k (253/64) (by rfl) (by rfl)
    leaf5459FlatSound leaf5460FlatSound

private noncomputable def component110Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (83/256), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component110Node23_sound : Sound component110Node23Box :=
  sound_of_literal_split component110Node23Box leaf5461Box leaf5462Box
    .k (253/64) (by rfl) (by rfl)
    leaf5461FlatSound leaf5462FlatSound

private noncomputable def component110Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (41/128), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component110Node24_sound : Sound component110Node24Box :=
  sound_of_literal_split component110Node24Box component110Node22Box component110Node23Box
    .chi (83/256) (by rfl) (by rfl)
    component110Node22_sound component110Node23_sound

private noncomputable def component110Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (41/128), chiHi := (83/256) }

set_option maxRecDepth 1000000 in
private theorem component110Node25_sound : Sound component110Node25Box :=
  sound_of_literal_split component110Node25Box leaf5463Box leaf5464Box
    .k (255/64) (by rfl) (by rfl)
    leaf5463FlatSound leaf5464FlatSound

private noncomputable def component110Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (83/256), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component110Node26_sound : Sound component110Node26Box :=
  sound_of_literal_split component110Node26Box leaf5465Box leaf5466Box
    .k (255/64) (by rfl) (by rfl)
    leaf5465FlatSound leaf5466FlatSound

private noncomputable def component110Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (41/128), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component110Node27_sound : Sound component110Node27Box :=
  sound_of_literal_split component110Node27Box component110Node25Box component110Node26Box
    .chi (83/256) (by rfl) (by rfl)
    component110Node25_sound component110Node26_sound

private noncomputable def component110Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (41/128), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component110Node28_sound : Sound component110Node28Box :=
  sound_of_literal_split component110Node28Box component110Node24Box component110Node27Box
    .k (127/32) (by rfl) (by rfl)
    component110Node24_sound component110Node27_sound

private noncomputable def component110Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (5/16), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component110Node29_sound : Sound component110Node29Box :=
  sound_of_literal_split component110Node29Box component110Node21Box component110Node28Box
    .chi (41/128) (by rfl) (by rfl)
    component110Node21_sound component110Node28_sound

private noncomputable def component110Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (5/16), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component110Node30_sound : Sound component110Node30Box :=
  sound_of_literal_split component110Node30Box component110Node14Box component110Node29Box
    .k (63/16) (by rfl) (by rfl)
    component110Node14_sound component110Node29_sound

private noncomputable def component110Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (21/64), chiHi := (85/256) }

set_option maxRecDepth 1000000 in
private theorem component110Node31_sound : Sound component110Node31Box :=
  sound_of_literal_split component110Node31Box leaf5467Box leaf5468Box
    .k (249/64) (by rfl) (by rfl)
    leaf5467FlatSound leaf5468FlatSound

private noncomputable def component110Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (85/256), chiHi := (43/128) }

set_option maxRecDepth 1000000 in
private theorem component110Node32_sound : Sound component110Node32Box :=
  sound_of_literal_split component110Node32Box leaf5469Box leaf5470Box
    .k (249/64) (by rfl) (by rfl)
    leaf5469FlatSound leaf5470FlatSound

private noncomputable def component110Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (21/64), chiHi := (43/128) }

set_option maxRecDepth 1000000 in
private theorem component110Node33_sound : Sound component110Node33Box :=
  sound_of_literal_split component110Node33Box component110Node31Box component110Node32Box
    .chi (85/256) (by rfl) (by rfl)
    component110Node31_sound component110Node32_sound

private noncomputable def component110Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (21/64), chiHi := (85/256) }

set_option maxRecDepth 1000000 in
private theorem component110Node34_sound : Sound component110Node34Box :=
  sound_of_literal_split component110Node34Box leaf5471Box leaf5472Box
    .k (251/64) (by rfl) (by rfl)
    leaf5471FlatSound leaf5472FlatSound

private noncomputable def component110Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (85/256), chiHi := (43/128) }

set_option maxRecDepth 1000000 in
private theorem component110Node35_sound : Sound component110Node35Box :=
  sound_of_literal_split component110Node35Box leaf5473Box leaf5474Box
    .k (251/64) (by rfl) (by rfl)
    leaf5473FlatSound leaf5474FlatSound

private noncomputable def component110Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (21/64), chiHi := (43/128) }

set_option maxRecDepth 1000000 in
private theorem component110Node36_sound : Sound component110Node36Box :=
  sound_of_literal_split component110Node36Box component110Node34Box component110Node35Box
    .chi (85/256) (by rfl) (by rfl)
    component110Node34_sound component110Node35_sound

private noncomputable def component110Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (21/64), chiHi := (43/128) }

set_option maxRecDepth 1000000 in
private theorem component110Node37_sound : Sound component110Node37Box :=
  sound_of_literal_split component110Node37Box component110Node33Box component110Node36Box
    .k (125/32) (by rfl) (by rfl)
    component110Node33_sound component110Node36_sound

private noncomputable def component110Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (43/128), chiHi := (87/256) }

set_option maxRecDepth 1000000 in
private theorem component110Node38_sound : Sound component110Node38Box :=
  sound_of_literal_split component110Node38Box leaf5475Box leaf5476Box
    .k (249/64) (by rfl) (by rfl)
    leaf5475FlatSound leaf5476FlatSound

private noncomputable def component110Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (87/256), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component110Node39_sound : Sound component110Node39Box :=
  sound_of_literal_split component110Node39Box leaf5477Box leaf5478Box
    .k (249/64) (by rfl) (by rfl)
    leaf5477FlatSound leaf5478FlatSound

private noncomputable def component110Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (43/128), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component110Node40_sound : Sound component110Node40Box :=
  sound_of_literal_split component110Node40Box component110Node38Box component110Node39Box
    .chi (87/256) (by rfl) (by rfl)
    component110Node38_sound component110Node39_sound

private noncomputable def component110Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (43/128), chiHi := (87/256) }

set_option maxRecDepth 1000000 in
private theorem component110Node41_sound : Sound component110Node41Box :=
  sound_of_literal_split component110Node41Box leaf5479Box leaf5480Box
    .k (251/64) (by rfl) (by rfl)
    leaf5479FlatSound leaf5480FlatSound

private noncomputable def component110Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (87/256), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component110Node42_sound : Sound component110Node42Box :=
  sound_of_literal_split component110Node42Box leaf5481Box leaf5482Box
    .k (251/64) (by rfl) (by rfl)
    leaf5481FlatSound leaf5482FlatSound

private noncomputable def component110Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (43/128), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component110Node43_sound : Sound component110Node43Box :=
  sound_of_literal_split component110Node43Box component110Node41Box component110Node42Box
    .chi (87/256) (by rfl) (by rfl)
    component110Node41_sound component110Node42_sound

private noncomputable def component110Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (43/128), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component110Node44_sound : Sound component110Node44Box :=
  sound_of_literal_split component110Node44Box component110Node40Box component110Node43Box
    .k (125/32) (by rfl) (by rfl)
    component110Node40_sound component110Node43_sound

private noncomputable def component110Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (21/64), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component110Node45_sound : Sound component110Node45Box :=
  sound_of_literal_split component110Node45Box component110Node37Box component110Node44Box
    .chi (43/128) (by rfl) (by rfl)
    component110Node37_sound component110Node44_sound

private noncomputable def component110Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (21/64), chiHi := (85/256) }

set_option maxRecDepth 1000000 in
private theorem component110Node46_sound : Sound component110Node46Box :=
  sound_of_literal_split component110Node46Box leaf5483Box leaf5484Box
    .k (253/64) (by rfl) (by rfl)
    leaf5483FlatSound leaf5484FlatSound

private noncomputable def component110Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (85/256), chiHi := (43/128) }

set_option maxRecDepth 1000000 in
private theorem component110Node47_sound : Sound component110Node47Box :=
  sound_of_literal_split component110Node47Box leaf5485Box leaf5486Box
    .k (253/64) (by rfl) (by rfl)
    leaf5485FlatSound leaf5486FlatSound

private noncomputable def component110Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (21/64), chiHi := (43/128) }

set_option maxRecDepth 1000000 in
private theorem component110Node48_sound : Sound component110Node48Box :=
  sound_of_literal_split component110Node48Box component110Node46Box component110Node47Box
    .chi (85/256) (by rfl) (by rfl)
    component110Node46_sound component110Node47_sound

private noncomputable def component110Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (21/64), chiHi := (85/256) }

set_option maxRecDepth 1000000 in
private theorem component110Node49_sound : Sound component110Node49Box :=
  sound_of_literal_split component110Node49Box leaf5487Box leaf5488Box
    .k (255/64) (by rfl) (by rfl)
    leaf5487FlatSound leaf5488FlatSound

private noncomputable def component110Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (85/256), chiHi := (43/128) }

set_option maxRecDepth 1000000 in
private theorem component110Node50_sound : Sound component110Node50Box :=
  sound_of_literal_split component110Node50Box leaf5489Box leaf5490Box
    .k (255/64) (by rfl) (by rfl)
    leaf5489FlatSound leaf5490FlatSound

private noncomputable def component110Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (21/64), chiHi := (43/128) }

set_option maxRecDepth 1000000 in
private theorem component110Node51_sound : Sound component110Node51Box :=
  sound_of_literal_split component110Node51Box component110Node49Box component110Node50Box
    .chi (85/256) (by rfl) (by rfl)
    component110Node49_sound component110Node50_sound

private noncomputable def component110Node52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (21/64), chiHi := (43/128) }

set_option maxRecDepth 1000000 in
private theorem component110Node52_sound : Sound component110Node52Box :=
  sound_of_literal_split component110Node52Box component110Node48Box component110Node51Box
    .k (127/32) (by rfl) (by rfl)
    component110Node48_sound component110Node51_sound

private noncomputable def component110Node53Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (43/128), chiHi := (87/256) }

set_option maxRecDepth 1000000 in
private theorem component110Node53_sound : Sound component110Node53Box :=
  sound_of_literal_split component110Node53Box leaf5491Box leaf5492Box
    .k (253/64) (by rfl) (by rfl)
    leaf5491FlatSound leaf5492FlatSound

private noncomputable def component110Node54Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (87/256), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component110Node54_sound : Sound component110Node54Box :=
  sound_of_literal_split component110Node54Box leaf5493Box leaf5494Box
    .k (253/64) (by rfl) (by rfl)
    leaf5493FlatSound leaf5494FlatSound

private noncomputable def component110Node55Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (43/128), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component110Node55_sound : Sound component110Node55Box :=
  sound_of_literal_split component110Node55Box component110Node53Box component110Node54Box
    .chi (87/256) (by rfl) (by rfl)
    component110Node53_sound component110Node54_sound

private noncomputable def component110Node56Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (43/128), chiHi := (87/256) }

set_option maxRecDepth 1000000 in
private theorem component110Node56_sound : Sound component110Node56Box :=
  sound_of_literal_split component110Node56Box leaf5495Box leaf5496Box
    .k (255/64) (by rfl) (by rfl)
    leaf5495FlatSound leaf5496FlatSound

private noncomputable def component110Node57Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (87/256), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component110Node57_sound : Sound component110Node57Box :=
  sound_of_literal_split component110Node57Box leaf5497Box leaf5498Box
    .k (255/64) (by rfl) (by rfl)
    leaf5497FlatSound leaf5498FlatSound

private noncomputable def component110Node58Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (43/128), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component110Node58_sound : Sound component110Node58Box :=
  sound_of_literal_split component110Node58Box component110Node56Box component110Node57Box
    .chi (87/256) (by rfl) (by rfl)
    component110Node56_sound component110Node57_sound

private noncomputable def component110Node59Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (43/128), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component110Node59_sound : Sound component110Node59Box :=
  sound_of_literal_split component110Node59Box component110Node55Box component110Node58Box
    .k (127/32) (by rfl) (by rfl)
    component110Node55_sound component110Node58_sound

private noncomputable def component110Node60Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (21/64), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component110Node60_sound : Sound component110Node60Box :=
  sound_of_literal_split component110Node60Box component110Node52Box component110Node59Box
    .chi (43/128) (by rfl) (by rfl)
    component110Node52_sound component110Node59_sound

private noncomputable def component110Node61Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (21/64), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component110Node61_sound : Sound component110Node61Box :=
  sound_of_literal_split component110Node61Box component110Node45Box component110Node60Box
    .k (63/16) (by rfl) (by rfl)
    component110Node45_sound component110Node60_sound

noncomputable def component110Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (5/16), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
theorem component110_sound : Sound component110Box :=
  sound_of_literal_split component110Box component110Node30Box component110Node61Box
    .chi (21/64) (by rfl) (by rfl)
    component110Node30_sound component110Node61_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
