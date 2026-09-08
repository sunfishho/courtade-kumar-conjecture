import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch7
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch11
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch5
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheSKBatch0
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

private noncomputable def leaf6418Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (3/4), chiHi := (25/32) }

private noncomputable def leaf6418Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554547/33554432) }, vSqrt := { lower := (65531/65536), upper := (34358231037/34356359168) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (83850127/67108864) }, upper := { exponent := 1, mantissa := (1337/1024) } }, logOuter := sk61LogOuterCertificate, logK := sk61LogKCertificate, logChi := chi88LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68714590205/68712718336) } }, logDArg := sk61LogDArgCertificate }

private noncomputable def leaf6418InnerLog : WideLogData :=
  innerPair287Data

set_option maxRecDepth 1000000 in
private theorem leaf6418LocalValidity :
    LeafFacts leaf6418Box leaf6418Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6418Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358231037/34356359168) }) = true
      norm_num [leaf6418Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6418CertificateValid :
    WideCertificateValid leaf6418Box leaf6418Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk61ValidityFacts chi88ValidityFacts
    leaf6418LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6418CoverageChecked :
    coverageCheck (innerAD leaf6418Box) leaf6418InnerLog = true := by
  rfl'

private theorem leaf6418InnerLogValid :
    leaf6418InnerLog.Valid 8 (innerAD leaf6418Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint91PositiveFacts.valid leaf6418CoverageChecked

private noncomputable def leaf6418InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814769/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6418InputLogOnePlusV_eq :
    leaf6418InputLogOnePlusV = outerEnclosure 24
      (leaf6418Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6418RoundedFacts : LeafRoundedFacts 8
    leaf6418Certificate.logOnePlusV leaf6418InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6418InputLogOnePlusV_eq }

private noncomputable def leaf6418Inputs : Inputs :=
  inputsOfCaches globalInput sk61RoundedInputs
    chi88InputQChi innerPair287Input
    leaf6418InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6418LowerChecked :
    lowerCheck 24 leaf6418Box leaf6418Inputs = true := by
  rfl'

private theorem leaf6418CoversExact : CoversExact 8
    leaf6418Box leaf6418Certificate leaf6418InnerLog leaf6418Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk61RoundedFacts chi88RoundedFacts
    innerPair287RoundedFacts leaf6418RoundedFacts (by rfl)

private theorem leaf6418FlatSound : Sound leaf6418Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6418CertificateValid
    leaf6418InnerLogValid leaf6418CoversExact leaf6418LowerChecked

private noncomputable def leaf6419Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (3/4), chiHi := (25/32) }

private noncomputable def leaf6419Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554549/33554432) }, vSqrt := { lower := (65531/65536), upper := (34358231037/34356256768) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (85422893/67108864) }, upper := { exponent := 1, mantissa := (681/512) } }, logOuter := sk62LogOuterCertificate, logK := sk62LogKCertificate, logChi := chi88LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68714487805/68712513536) } }, logDArg := sk62LogDArgCertificate }

private noncomputable def leaf6419InnerLog : WideLogData :=
  innerPair295Data

set_option maxRecDepth 1000000 in
private theorem leaf6419LocalValidity :
    LeafFacts leaf6419Box leaf6419Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6419Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358231037/34356256768) }) = true
      norm_num [leaf6419Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6419CertificateValid :
    WideCertificateValid leaf6419Box leaf6419Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk62ValidityFacts chi88ValidityFacts
    leaf6419LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6419CoverageChecked :
    coverageCheck (innerAD leaf6419Box) leaf6419InnerLog = true := by
  rfl'

private theorem leaf6419InnerLogValid :
    leaf6419InnerLog.Valid 8 (innerAD leaf6419Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint92PositiveFacts.valid leaf6419CoverageChecked

private noncomputable def leaf6419InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629563/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6419InputLogOnePlusV_eq :
    leaf6419InputLogOnePlusV = outerEnclosure 24
      (leaf6419Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6419RoundedFacts : LeafRoundedFacts 8
    leaf6419Certificate.logOnePlusV leaf6419InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6419InputLogOnePlusV_eq }

private noncomputable def leaf6419Inputs : Inputs :=
  inputsOfCaches globalInput sk62RoundedInputs
    chi88InputQChi innerPair295Input
    leaf6419InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6419LowerChecked :
    lowerCheck 24 leaf6419Box leaf6419Inputs = true := by
  rfl'

private theorem leaf6419CoversExact : CoversExact 8
    leaf6419Box leaf6419Certificate leaf6419InnerLog leaf6419Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk62RoundedFacts chi88RoundedFacts
    innerPair295RoundedFacts leaf6419RoundedFacts (by rfl)

private theorem leaf6419FlatSound : Sound leaf6419Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6419CertificateValid
    leaf6419InnerLogValid leaf6419CoversExact leaf6419LowerChecked

private noncomputable def leaf6420Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (25/32), chiHi := (13/16) }

private noncomputable def leaf6420Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554549/33554432) }, vSqrt := { lower := (65531/65536), upper := (34358231037/34356224000) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (85947149/67108864) }, upper := { exponent := 1, mantissa := (685/512) } }, logOuter := sk61LogOuterCertificate, logK := sk61LogKCertificate, logChi := chi89LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68714455037/68712448000) } }, logDArg := sk61LogDArgCertificate }

private noncomputable def leaf6420InnerLog : WideLogData :=
  innerPair295Data

set_option maxRecDepth 1000000 in
private theorem leaf6420LocalValidity :
    LeafFacts leaf6420Box leaf6420Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6420Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358231037/34356224000) }) = true
      norm_num [leaf6420Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6420CertificateValid :
    WideCertificateValid leaf6420Box leaf6420Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk61ValidityFacts chi89ValidityFacts
    leaf6420LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6420CoverageChecked :
    coverageCheck (innerAD leaf6420Box) leaf6420InnerLog = true := by
  rfl'

private theorem leaf6420InnerLogValid :
    leaf6420InnerLog.Valid 8 (innerAD leaf6420Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint92PositiveFacts.valid leaf6420CoverageChecked

private noncomputable def leaf6420InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629571/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6420InputLogOnePlusV_eq :
    leaf6420InputLogOnePlusV = outerEnclosure 24
      (leaf6420Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6420RoundedFacts : LeafRoundedFacts 8
    leaf6420Certificate.logOnePlusV leaf6420InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6420InputLogOnePlusV_eq }

private noncomputable def leaf6420Inputs : Inputs :=
  inputsOfCaches globalInput sk61RoundedInputs
    chi89InputQChi innerPair295Input
    leaf6420InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6420LowerChecked :
    lowerCheck 24 leaf6420Box leaf6420Inputs = true := by
  rfl'

private theorem leaf6420CoversExact : CoversExact 8
    leaf6420Box leaf6420Certificate leaf6420InnerLog leaf6420Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk61RoundedFacts chi89RoundedFacts
    innerPair295RoundedFacts leaf6420RoundedFacts (by rfl)

private theorem leaf6420FlatSound : Sound leaf6420Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6420CertificateValid
    leaf6420InnerLogValid leaf6420CoversExact leaf6420LowerChecked

private noncomputable def leaf6421Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (25/32), chiHi := (13/16) }

private noncomputable def leaf6421Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554551/33554432) }, vSqrt := { lower := (65531/65536), upper := (11452743679/11452039168) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (87585447/67108864) }, upper := { exponent := 1, mantissa := (349/256) } }, logOuter := sk62LogOuterCertificate, logK := sk62LogKCertificate, logChi := chi89LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (22904782847/22904078336) } }, logDArg := sk62LogDArgCertificate }

private noncomputable def leaf6421InnerLog : WideLogData :=
  innerPair341Data

set_option maxRecDepth 1000000 in
private theorem leaf6421LocalValidity :
    LeafFacts leaf6421Box leaf6421Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6421Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (11452743679/11452039168) }) = true
      norm_num [leaf6421Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6421CertificateValid :
    WideCertificateValid leaf6421Box leaf6421Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk62ValidityFacts chi89ValidityFacts
    leaf6421LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6421CoverageChecked :
    coverageCheck (innerAD leaf6421Box) leaf6421InnerLog = true := by
  rfl'

private theorem leaf6421InnerLogValid :
    leaf6421InnerLog.Valid 8 (innerAD leaf6421Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint93PositiveFacts.valid leaf6421CoverageChecked

private noncomputable def leaf6421InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629597/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6421InputLogOnePlusV_eq :
    leaf6421InputLogOnePlusV = outerEnclosure 24
      (leaf6421Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6421RoundedFacts : LeafRoundedFacts 8
    leaf6421Certificate.logOnePlusV leaf6421InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6421InputLogOnePlusV_eq }

private noncomputable def leaf6421Inputs : Inputs :=
  inputsOfCaches globalInput sk62RoundedInputs
    chi89InputQChi innerPair341Input
    leaf6421InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6421LowerChecked :
    lowerCheck 24 leaf6421Box leaf6421Inputs = true := by
  rfl'

private theorem leaf6421CoversExact : CoversExact 8
    leaf6421Box leaf6421Certificate leaf6421InnerLog leaf6421Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk62RoundedFacts chi89RoundedFacts
    innerPair341RoundedFacts leaf6421RoundedFacts (by rfl)

private theorem leaf6421FlatSound : Sound leaf6421Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6421CertificateValid
    leaf6421InnerLogValid leaf6421CoversExact leaf6421LowerChecked

private noncomputable def leaf6422Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (3/4), chiHi := (25/32) }

private noncomputable def leaf6422Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554551/33554432) }, vSqrt := { lower := (65531/65536), upper := (11452743679/11452051456) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (86995659/67108864) }, upper := { exponent := 1, mantissa := (1387/1024) } }, logOuter := sk63LogOuterCertificate, logK := sk63LogKCertificate, logChi := chi88LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (22904795135/22904102912) } }, logDArg := sk63LogDArgCertificate }

private noncomputable def leaf6422InnerLog : WideLogData :=
  innerPair341Data

set_option maxRecDepth 1000000 in
private theorem leaf6422LocalValidity :
    LeafFacts leaf6422Box leaf6422Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6422Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (11452743679/11452051456) }) = true
      norm_num [leaf6422Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6422CertificateValid :
    WideCertificateValid leaf6422Box leaf6422Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk63ValidityFacts chi88ValidityFacts
    leaf6422LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6422CoverageChecked :
    coverageCheck (innerAD leaf6422Box) leaf6422InnerLog = true := by
  rfl'

private theorem leaf6422InnerLogValid :
    leaf6422InnerLog.Valid 8 (innerAD leaf6422Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint93PositiveFacts.valid leaf6422CoverageChecked

private noncomputable def leaf6422InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (2907397/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6422InputLogOnePlusV_eq :
    leaf6422InputLogOnePlusV = outerEnclosure 24
      (leaf6422Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6422RoundedFacts : LeafRoundedFacts 8
    leaf6422Certificate.logOnePlusV leaf6422InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6422InputLogOnePlusV_eq }

private noncomputable def leaf6422Inputs : Inputs :=
  inputsOfCaches globalInput sk63RoundedInputs
    chi88InputQChi innerPair341Input
    leaf6422InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6422LowerChecked :
    lowerCheck 24 leaf6422Box leaf6422Inputs = true := by
  rfl'

private theorem leaf6422CoversExact : CoversExact 8
    leaf6422Box leaf6422Certificate leaf6422InnerLog leaf6422Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk63RoundedFacts chi88RoundedFacts
    innerPair341RoundedFacts leaf6422RoundedFacts (by rfl)

private theorem leaf6422FlatSound : Sound leaf6422Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6422CertificateValid
    leaf6422InnerLogValid leaf6422CoversExact leaf6422LowerChecked

private noncomputable def leaf6423Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (3/4), chiHi := (25/32) }

private noncomputable def leaf6423Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554553/33554432) }, vSqrt := { lower := (65531/65536), upper := (34358231037/34356051968) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (88568425/67108864) }, upper := { exponent := 1, mantissa := (353/256) } }, logOuter := sk64LogOuterCertificate, logK := sk64LogKCertificate, logChi := chi88LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68714283005/68712103936) } }, logDArg := sk64LogDArgCertificate }

private noncomputable def leaf6423InnerLog : WideLogData :=
  innerPair347Data

set_option maxRecDepth 1000000 in
private theorem leaf6423LocalValidity :
    LeafFacts leaf6423Box leaf6423Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6423Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358231037/34356051968) }) = true
      norm_num [leaf6423Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6423CertificateValid :
    WideCertificateValid leaf6423Box leaf6423Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk64ValidityFacts chi88ValidityFacts
    leaf6423LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6423CoverageChecked :
    coverageCheck (innerAD leaf6423Box) leaf6423InnerLog = true := by
  rfl'

private theorem leaf6423InnerLogValid :
    leaf6423InnerLog.Valid 8 (innerAD leaf6423Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint96PositiveFacts.valid leaf6423CoverageChecked

private noncomputable def leaf6423InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629613/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6423InputLogOnePlusV_eq :
    leaf6423InputLogOnePlusV = outerEnclosure 24
      (leaf6423Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6423RoundedFacts : LeafRoundedFacts 8
    leaf6423Certificate.logOnePlusV leaf6423InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6423InputLogOnePlusV_eq }

private noncomputable def leaf6423Inputs : Inputs :=
  inputsOfCaches globalInput sk64RoundedInputs
    chi88InputQChi innerPair347Input
    leaf6423InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6423LowerChecked :
    lowerCheck 24 leaf6423Box leaf6423Inputs = true := by
  rfl'

private theorem leaf6423CoversExact : CoversExact 8
    leaf6423Box leaf6423Certificate leaf6423InnerLog leaf6423Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk64RoundedFacts chi88RoundedFacts
    innerPair347RoundedFacts leaf6423RoundedFacts (by rfl)

private theorem leaf6423FlatSound : Sound leaf6423Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6423CertificateValid
    leaf6423InnerLogValid leaf6423CoversExact leaf6423LowerChecked

private noncomputable def leaf6424Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (25/32), chiHi := (13/16) }

private noncomputable def leaf6424Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554553/33554432) }, vSqrt := { lower := (65531/65536), upper := (34358231037/34356011008) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (89223745/67108864) }, upper := { exponent := 1, mantissa := (711/512) } }, logOuter := sk63LogOuterCertificate, logK := sk63LogKCertificate, logChi := chi89LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68714242045/68712022016) } }, logDArg := sk63LogDArgCertificate }

private noncomputable def leaf6424InnerLog : WideLogData :=
  innerPair347Data

set_option maxRecDepth 1000000 in
private theorem leaf6424LocalValidity :
    LeafFacts leaf6424Box leaf6424Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6424Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358231037/34356011008) }) = true
      norm_num [leaf6424Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6424CertificateValid :
    WideCertificateValid leaf6424Box leaf6424Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk63ValidityFacts chi89ValidityFacts
    leaf6424LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6424CoverageChecked :
    coverageCheck (innerAD leaf6424Box) leaf6424InnerLog = true := by
  rfl'

private theorem leaf6424InnerLogValid :
    leaf6424InnerLog.Valid 8 (innerAD leaf6424Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint96PositiveFacts.valid leaf6424CoverageChecked

private noncomputable def leaf6424InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629623/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6424InputLogOnePlusV_eq :
    leaf6424InputLogOnePlusV = outerEnclosure 24
      (leaf6424Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6424RoundedFacts : LeafRoundedFacts 8
    leaf6424Certificate.logOnePlusV leaf6424InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6424InputLogOnePlusV_eq }

private noncomputable def leaf6424Inputs : Inputs :=
  inputsOfCaches globalInput sk63RoundedInputs
    chi89InputQChi innerPair347Input
    leaf6424InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6424LowerChecked :
    lowerCheck 24 leaf6424Box leaf6424Inputs = true := by
  rfl'

private theorem leaf6424CoversExact : CoversExact 8
    leaf6424Box leaf6424Certificate leaf6424InnerLog leaf6424Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk63RoundedFacts chi89RoundedFacts
    innerPair347RoundedFacts leaf6424RoundedFacts (by rfl)

private theorem leaf6424FlatSound : Sound leaf6424Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6424CertificateValid
    leaf6424InnerLogValid leaf6424CoversExact leaf6424LowerChecked

private noncomputable def leaf6425Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (25/32), chiHi := (13/16) }

private noncomputable def leaf6425Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554555/33554432) }, vSqrt := { lower := (65531/65536), upper := (34358231037/34355904512) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (90862043/67108864) }, upper := { exponent := 1, mantissa := (181/128) } }, logOuter := sk64LogOuterCertificate, logK := sk64LogKCertificate, logChi := chi89LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68714135549/68711809024) } }, logDArg := sk64LogDArgCertificate }

private noncomputable def leaf6425InnerLog : WideLogData :=
  innerPair354Data

set_option maxRecDepth 1000000 in
private theorem leaf6425LocalValidity :
    LeafFacts leaf6425Box leaf6425Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6425Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358231037/34355904512) }) = true
      norm_num [leaf6425Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6425CertificateValid :
    WideCertificateValid leaf6425Box leaf6425Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk64ValidityFacts chi89ValidityFacts
    leaf6425LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6425CoverageChecked :
    coverageCheck (innerAD leaf6425Box) leaf6425InnerLog = true := by
  rfl'

private theorem leaf6425InnerLogValid :
    leaf6425InnerLog.Valid 8 (innerAD leaf6425Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint97PositiveFacts.valid leaf6425CoverageChecked

private noncomputable def leaf6425InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629649/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6425InputLogOnePlusV_eq :
    leaf6425InputLogOnePlusV = outerEnclosure 24
      (leaf6425Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6425RoundedFacts : LeafRoundedFacts 8
    leaf6425Certificate.logOnePlusV leaf6425InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6425InputLogOnePlusV_eq }

private noncomputable def leaf6425Inputs : Inputs :=
  inputsOfCaches globalInput sk64RoundedInputs
    chi89InputQChi innerPair354Input
    leaf6425InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6425LowerChecked :
    lowerCheck 24 leaf6425Box leaf6425Inputs = true := by
  rfl'

private theorem leaf6425CoversExact : CoversExact 8
    leaf6425Box leaf6425Certificate leaf6425InnerLog leaf6425Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk64RoundedFacts chi89RoundedFacts
    innerPair354RoundedFacts leaf6425RoundedFacts (by rfl)

private theorem leaf6425FlatSound : Sound leaf6425Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6425CertificateValid
    leaf6425InnerLogValid leaf6425CoversExact leaf6425LowerChecked

private noncomputable def leaf6426Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (13/16), chiHi := (27/32) }

private noncomputable def leaf6426Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554551/33554432) }, vSqrt := { lower := (65531/65536), upper := (2642940849/2642776064) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (88044171/67108864) }, upper := { exponent := 1, mantissa := (1403/1024) } }, logOuter := sk61LogOuterCertificate, logK := sk61LogKCertificate, logChi := chi90LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (5285716913/5285552128) } }, logDArg := sk61LogDArgCertificate }

private noncomputable def leaf6426InnerLog : WideLogData :=
  innerPair341Data

set_option maxRecDepth 1000000 in
private theorem leaf6426LocalValidity :
    LeafFacts leaf6426Box leaf6426Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6426Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (2642940849/2642776064) }) = true
      norm_num [leaf6426Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6426CertificateValid :
    WideCertificateValid leaf6426Box leaf6426Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk61ValidityFacts chi90ValidityFacts
    leaf6426LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6426CoverageChecked :
    coverageCheck (innerAD leaf6426Box) leaf6426InnerLog = true := by
  rfl'

private theorem leaf6426InnerLogValid :
    leaf6426InnerLog.Valid 8 (innerAD leaf6426Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint93PositiveFacts.valid leaf6426CoverageChecked

private noncomputable def leaf6426InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (2907401/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6426InputLogOnePlusV_eq :
    leaf6426InputLogOnePlusV = outerEnclosure 24
      (leaf6426Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6426RoundedFacts : LeafRoundedFacts 8
    leaf6426Certificate.logOnePlusV leaf6426InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6426InputLogOnePlusV_eq }

private noncomputable def leaf6426Inputs : Inputs :=
  inputsOfCaches globalInput sk61RoundedInputs
    chi90InputQChi innerPair341Input
    leaf6426InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6426LowerChecked :
    lowerCheck 24 leaf6426Box leaf6426Inputs = true := by
  rfl'

private theorem leaf6426CoversExact : CoversExact 8
    leaf6426Box leaf6426Certificate leaf6426InnerLog leaf6426Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk61RoundedFacts chi90RoundedFacts
    innerPair341RoundedFacts leaf6426RoundedFacts (by rfl)

private theorem leaf6426FlatSound : Sound leaf6426Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6426CertificateValid
    leaf6426InnerLogValid leaf6426CoversExact leaf6426LowerChecked

private noncomputable def leaf6427Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (13/16), chiHi := (27/32) }

private noncomputable def leaf6427Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554553/33554432) }, vSqrt := { lower := (65531/65536), upper := (34358231037/34355978240) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (89748001/67108864) }, upper := { exponent := 1, mantissa := (715/512) } }, logOuter := sk62LogOuterCertificate, logK := sk62LogKCertificate, logChi := chi90LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68714209277/68711956480) } }, logDArg := sk62LogDArgCertificate }

private noncomputable def leaf6427InnerLog : WideLogData :=
  innerPair347Data

set_option maxRecDepth 1000000 in
private theorem leaf6427LocalValidity :
    LeafFacts leaf6427Box leaf6427Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6427Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358231037/34355978240) }) = true
      norm_num [leaf6427Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6427CertificateValid :
    WideCertificateValid leaf6427Box leaf6427Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk62ValidityFacts chi90ValidityFacts
    leaf6427LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6427CoverageChecked :
    coverageCheck (innerAD leaf6427Box) leaf6427InnerLog = true := by
  rfl'

private theorem leaf6427InnerLogValid :
    leaf6427InnerLog.Valid 8 (innerAD leaf6427Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint96PositiveFacts.valid leaf6427CoverageChecked

private noncomputable def leaf6427InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629631/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6427InputLogOnePlusV_eq :
    leaf6427InputLogOnePlusV = outerEnclosure 24
      (leaf6427Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6427RoundedFacts : LeafRoundedFacts 8
    leaf6427Certificate.logOnePlusV leaf6427InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6427InputLogOnePlusV_eq }

private noncomputable def leaf6427Inputs : Inputs :=
  inputsOfCaches globalInput sk62RoundedInputs
    chi90InputQChi innerPair347Input
    leaf6427InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6427LowerChecked :
    lowerCheck 24 leaf6427Box leaf6427Inputs = true := by
  rfl'

private theorem leaf6427CoversExact : CoversExact 8
    leaf6427Box leaf6427Certificate leaf6427InnerLog leaf6427Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk62RoundedFacts chi90RoundedFacts
    innerPair347RoundedFacts leaf6427RoundedFacts (by rfl)

private theorem leaf6427FlatSound : Sound leaf6427Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6427CertificateValid
    leaf6427InnerLogValid leaf6427CoversExact leaf6427LowerChecked

private noncomputable def leaf6428Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (27/32), chiHi := (7/8) }

private noncomputable def leaf6428Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554553/33554432) }, vSqrt := { lower := (65531/65536), upper := (34358231037/34355953664) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (90141193/67108864) }, upper := { exponent := 1, mantissa := (359/256) } }, logOuter := sk61LogOuterCertificate, logK := sk61LogKCertificate, logChi := chi91LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68714184701/68711907328) } }, logDArg := sk61LogDArgCertificate }

private noncomputable def leaf6428InnerLog : WideLogData :=
  innerPair347Data

set_option maxRecDepth 1000000 in
private theorem leaf6428LocalValidity :
    LeafFacts leaf6428Box leaf6428Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6428Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358231037/34355953664) }) = true
      norm_num [leaf6428Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6428CertificateValid :
    WideCertificateValid leaf6428Box leaf6428Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk61ValidityFacts chi91ValidityFacts
    leaf6428LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6428CoverageChecked :
    coverageCheck (innerAD leaf6428Box) leaf6428InnerLog = true := by
  rfl'

private theorem leaf6428InnerLogValid :
    leaf6428InnerLog.Valid 8 (innerAD leaf6428Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint96PositiveFacts.valid leaf6428CoverageChecked

private noncomputable def leaf6428InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629637/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6428InputLogOnePlusV_eq :
    leaf6428InputLogOnePlusV = outerEnclosure 24
      (leaf6428Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6428RoundedFacts : LeafRoundedFacts 8
    leaf6428Certificate.logOnePlusV leaf6428InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6428InputLogOnePlusV_eq }

private noncomputable def leaf6428Inputs : Inputs :=
  inputsOfCaches globalInput sk61RoundedInputs
    chi91InputQChi innerPair347Input
    leaf6428InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6428LowerChecked :
    lowerCheck 24 leaf6428Box leaf6428Inputs = true := by
  rfl'

private theorem leaf6428CoversExact : CoversExact 8
    leaf6428Box leaf6428Certificate leaf6428InnerLog leaf6428Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk61RoundedFacts chi91RoundedFacts
    innerPair347RoundedFacts leaf6428RoundedFacts (by rfl)

private theorem leaf6428FlatSound : Sound leaf6428Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6428CertificateValid
    leaf6428InnerLogValid leaf6428CoversExact leaf6428LowerChecked

private noncomputable def leaf6429Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (27/32), chiHi := (7/8) }

private noncomputable def leaf6429Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554555/33554432) }, vSqrt := { lower := (65531/65536), upper := (483918747/483885056) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (91910555/67108864) }, upper := { exponent := 1, mantissa := (183/128) } }, logOuter := sk62LogOuterCertificate, logK := sk62LogKCertificate, logChi := chi91LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (967803803/967770112) } }, logDArg := sk62LogDArgCertificate }

private noncomputable def leaf6429InnerLog : WideLogData :=
  innerPair354Data

set_option maxRecDepth 1000000 in
private theorem leaf6429LocalValidity :
    LeafFacts leaf6429Box leaf6429Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6429Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (483918747/483885056) }) = true
      norm_num [leaf6429Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6429CertificateValid :
    WideCertificateValid leaf6429Box leaf6429Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk62ValidityFacts chi91ValidityFacts
    leaf6429LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6429CoverageChecked :
    coverageCheck (innerAD leaf6429Box) leaf6429InnerLog = true := by
  rfl'

private theorem leaf6429InnerLogValid :
    leaf6429InnerLog.Valid 8 (innerAD leaf6429Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint97PositiveFacts.valid leaf6429CoverageChecked

private noncomputable def leaf6429InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629665/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6429InputLogOnePlusV_eq :
    leaf6429InputLogOnePlusV = outerEnclosure 24
      (leaf6429Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6429RoundedFacts : LeafRoundedFacts 8
    leaf6429Certificate.logOnePlusV leaf6429InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6429InputLogOnePlusV_eq }

private noncomputable def leaf6429Inputs : Inputs :=
  inputsOfCaches globalInput sk62RoundedInputs
    chi91InputQChi innerPair354Input
    leaf6429InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6429LowerChecked :
    lowerCheck 24 leaf6429Box leaf6429Inputs = true := by
  rfl'

private theorem leaf6429CoversExact : CoversExact 8
    leaf6429Box leaf6429Certificate leaf6429InnerLog leaf6429Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk62RoundedFacts chi91RoundedFacts
    innerPair354RoundedFacts leaf6429RoundedFacts (by rfl)

private theorem leaf6429FlatSound : Sound leaf6429Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6429CertificateValid
    leaf6429InnerLogValid leaf6429CoversExact leaf6429LowerChecked

private noncomputable def leaf6430Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (13/16), chiHi := (27/32) }

private noncomputable def leaf6430Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554555/33554432) }, vSqrt := { lower := (65531/65536), upper := (34358231037/34355867648) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (91451831/67108864) }, upper := { exponent := 1, mantissa := (1457/1024) } }, logOuter := sk63LogOuterCertificate, logK := sk63LogKCertificate, logChi := chi90LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68714098685/68711735296) } }, logDArg := sk63LogDArgCertificate }

private noncomputable def leaf6430InnerLog : WideLogData :=
  innerPair354Data

set_option maxRecDepth 1000000 in
private theorem leaf6430LocalValidity :
    LeafFacts leaf6430Box leaf6430Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6430Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358231037/34355867648) }) = true
      norm_num [leaf6430Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6430CertificateValid :
    WideCertificateValid leaf6430Box leaf6430Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk63ValidityFacts chi90ValidityFacts
    leaf6430LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6430CoverageChecked :
    coverageCheck (innerAD leaf6430Box) leaf6430InnerLog = true := by
  rfl'

private theorem leaf6430InnerLogValid :
    leaf6430InnerLog.Valid 8 (innerAD leaf6430Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint97PositiveFacts.valid leaf6430CoverageChecked

private noncomputable def leaf6430InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814829/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6430InputLogOnePlusV_eq :
    leaf6430InputLogOnePlusV = outerEnclosure 24
      (leaf6430Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6430RoundedFacts : LeafRoundedFacts 8
    leaf6430Certificate.logOnePlusV leaf6430InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6430InputLogOnePlusV_eq }

private noncomputable def leaf6430Inputs : Inputs :=
  inputsOfCaches globalInput sk63RoundedInputs
    chi90InputQChi innerPair354Input
    leaf6430InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6430LowerChecked :
    lowerCheck 24 leaf6430Box leaf6430Inputs = true := by
  rfl'

private theorem leaf6430CoversExact : CoversExact 8
    leaf6430Box leaf6430Certificate leaf6430InnerLog leaf6430Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk63RoundedFacts chi90RoundedFacts
    innerPair354RoundedFacts leaf6430RoundedFacts (by rfl)

private theorem leaf6430FlatSound : Sound leaf6430Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6430CertificateValid
    leaf6430InnerLogValid leaf6430CoversExact leaf6430LowerChecked

private noncomputable def leaf6431Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (13/16), chiHi := (27/32) }

private noncomputable def leaf6431Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554557/33554432) }, vSqrt := { lower := (65531/65536), upper := (34358231037/34355757056) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (93155661/67108864) }, upper := { exponent := 1, mantissa := (371/256) } }, logOuter := sk64LogOuterCertificate, logK := sk64LogKCertificate, logChi := chi90LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68713988093/68711514112) } }, logDArg := sk64LogDArgCertificate }

private noncomputable def leaf6431InnerLog : WideLogData :=
  innerPair358Data

set_option maxRecDepth 1000000 in
private theorem leaf6431LocalValidity :
    LeafFacts leaf6431Box leaf6431Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6431Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358231037/34355757056) }) = true
      norm_num [leaf6431Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6431CertificateValid :
    WideCertificateValid leaf6431Box leaf6431Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk64ValidityFacts chi90ValidityFacts
    leaf6431LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6431CoverageChecked :
    coverageCheck (innerAD leaf6431Box) leaf6431InnerLog = true := by
  rfl'

private theorem leaf6431InnerLogValid :
    leaf6431InnerLog.Valid 8 (innerAD leaf6431Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint98PositiveFacts.valid leaf6431CoverageChecked

private noncomputable def leaf6431InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629685/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6431InputLogOnePlusV_eq :
    leaf6431InputLogOnePlusV = outerEnclosure 24
      (leaf6431Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6431RoundedFacts : LeafRoundedFacts 8
    leaf6431Certificate.logOnePlusV leaf6431InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6431InputLogOnePlusV_eq }

private noncomputable def leaf6431Inputs : Inputs :=
  inputsOfCaches globalInput sk64RoundedInputs
    chi90InputQChi innerPair358Input
    leaf6431InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6431LowerChecked :
    lowerCheck 24 leaf6431Box leaf6431Inputs = true := by
  rfl'

private theorem leaf6431CoversExact : CoversExact 8
    leaf6431Box leaf6431Certificate leaf6431InnerLog leaf6431Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk64RoundedFacts chi90RoundedFacts
    innerPair358RoundedFacts leaf6431RoundedFacts (by rfl)

private theorem leaf6431FlatSound : Sound leaf6431Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6431CertificateValid
    leaf6431InnerLogValid leaf6431CoversExact leaf6431LowerChecked

private noncomputable def leaf6432Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (27/32), chiHi := (7/8) }

private noncomputable def leaf6432Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554557/33554432) }, vSqrt := { lower := (65531/65536), upper := (11452743679/11451908096) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (93679917/67108864) }, upper := { exponent := 1, mantissa := (373/256) } }, logOuter := sk63LogOuterCertificate, logK := sk63LogKCertificate, logChi := chi91LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (22904651775/22903816192) } }, logDArg := sk63LogDArgCertificate }

private noncomputable def leaf6432InnerLog : WideLogData :=
  innerPair358Data

set_option maxRecDepth 1000000 in
private theorem leaf6432LocalValidity :
    LeafFacts leaf6432Box leaf6432Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6432Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (11452743679/11451908096) }) = true
      norm_num [leaf6432Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6432CertificateValid :
    WideCertificateValid leaf6432Box leaf6432Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk63ValidityFacts chi91ValidityFacts
    leaf6432LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6432CoverageChecked :
    coverageCheck (innerAD leaf6432Box) leaf6432InnerLog = true := by
  rfl'

private theorem leaf6432InnerLogValid :
    leaf6432InnerLog.Valid 8 (innerAD leaf6432Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint98PositiveFacts.valid leaf6432CoverageChecked

private noncomputable def leaf6432InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629693/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6432InputLogOnePlusV_eq :
    leaf6432InputLogOnePlusV = outerEnclosure 24
      (leaf6432Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6432RoundedFacts : LeafRoundedFacts 8
    leaf6432Certificate.logOnePlusV leaf6432InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6432InputLogOnePlusV_eq }

private noncomputable def leaf6432Inputs : Inputs :=
  inputsOfCaches globalInput sk63RoundedInputs
    chi91InputQChi innerPair358Input
    leaf6432InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6432LowerChecked :
    lowerCheck 24 leaf6432Box leaf6432Inputs = true := by
  rfl'

private theorem leaf6432CoversExact : CoversExact 8
    leaf6432Box leaf6432Certificate leaf6432InnerLog leaf6432Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk63RoundedFacts chi91RoundedFacts
    innerPair358RoundedFacts leaf6432RoundedFacts (by rfl)

private theorem leaf6432FlatSound : Sound leaf6432Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6432CertificateValid
    leaf6432InnerLogValid leaf6432CoversExact leaf6432LowerChecked

private noncomputable def leaf6433Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (27/32), chiHi := (7/8) }

private noncomputable def leaf6433Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554559/33554432) }, vSqrt := { lower := (65531/65536), upper := (8589426687/8588902400) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (95449279/67108864) }, upper := { exponent := 1, mantissa := (95/64) } }, logOuter := sk64LogOuterCertificate, logK := sk64LogKCertificate, logChi := chi91LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (17178329087/17177804800) } }, logDArg := sk64LogDArgCertificate }

private noncomputable def leaf6433InnerLog : WideLogData :=
  innerPair369Data

set_option maxRecDepth 1000000 in
private theorem leaf6433LocalValidity :
    LeafFacts leaf6433Box leaf6433Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6433Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (8589426687/8588902400) }) = true
      norm_num [leaf6433Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6433CertificateValid :
    WideCertificateValid leaf6433Box leaf6433Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk64ValidityFacts chi91ValidityFacts
    leaf6433LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6433CoverageChecked :
    coverageCheck (innerAD leaf6433Box) leaf6433InnerLog = true := by
  rfl'

private theorem leaf6433InnerLogValid :
    leaf6433InnerLog.Valid 8 (innerAD leaf6433Box) :=
  wideLogDataValid_of_cachedCheck endpoint96PositiveFacts
    endpoint99PositiveFacts.valid leaf6433CoverageChecked

private noncomputable def leaf6433InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629593/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6433InputLogOnePlusV_eq :
    leaf6433InputLogOnePlusV = outerEnclosure 24
      (leaf6433Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6433RoundedFacts : LeafRoundedFacts 8
    leaf6433Certificate.logOnePlusV leaf6433InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6433InputLogOnePlusV_eq }

private noncomputable def leaf6433Inputs : Inputs :=
  inputsOfCaches globalInput sk64RoundedInputs
    chi91InputQChi innerPair369Input
    leaf6433InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6433LowerChecked :
    lowerCheck 24 leaf6433Box leaf6433Inputs = true := by
  rfl'

private theorem leaf6433CoversExact : CoversExact 8
    leaf6433Box leaf6433Certificate leaf6433InnerLog leaf6433Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk64RoundedFacts chi91RoundedFacts
    innerPair369RoundedFacts leaf6433RoundedFacts (by rfl)

private theorem leaf6433FlatSound : Sound leaf6433Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6433CertificateValid
    leaf6433InnerLogValid leaf6433CoversExact leaf6433LowerChecked

private noncomputable def leaf6434Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (7/8), chiHi := (29/32) }

private noncomputable def leaf6434Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554555/33554432) }, vSqrt := { lower := (65531/65536), upper := (34358231037/34355818496) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (92238215/67108864) }, upper := { exponent := 1, mantissa := (1469/1024) } }, logOuter := sk61LogOuterCertificate, logK := sk61LogKCertificate, logChi := chi92LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68714049533/68711636992) } }, logDArg := sk61LogDArgCertificate }

private noncomputable def leaf6434InnerLog : WideLogData :=
  innerPair354Data

set_option maxRecDepth 1000000 in
private theorem leaf6434LocalValidity :
    LeafFacts leaf6434Box leaf6434Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6434Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358231037/34355818496) }) = true
      norm_num [leaf6434Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6434CertificateValid :
    WideCertificateValid leaf6434Box leaf6434Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk61ValidityFacts chi92ValidityFacts
    leaf6434LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6434CoverageChecked :
    coverageCheck (innerAD leaf6434Box) leaf6434InnerLog = true := by
  rfl'

private theorem leaf6434InnerLogValid :
    leaf6434InnerLog.Valid 8 (innerAD leaf6434Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint97PositiveFacts.valid leaf6434CoverageChecked

private noncomputable def leaf6434InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814835/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6434InputLogOnePlusV_eq :
    leaf6434InputLogOnePlusV = outerEnclosure 24
      (leaf6434Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6434RoundedFacts : LeafRoundedFacts 8
    leaf6434Certificate.logOnePlusV leaf6434InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6434InputLogOnePlusV_eq }

private noncomputable def leaf6434Inputs : Inputs :=
  inputsOfCaches globalInput sk61RoundedInputs
    chi92InputQChi innerPair354Input
    leaf6434InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6434LowerChecked :
    lowerCheck 24 leaf6434Box leaf6434Inputs = true := by
  rfl'

private theorem leaf6434CoversExact : CoversExact 8
    leaf6434Box leaf6434Certificate leaf6434InnerLog leaf6434Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk61RoundedFacts chi92RoundedFacts
    innerPair354RoundedFacts leaf6434RoundedFacts (by rfl)

private theorem leaf6434FlatSound : Sound leaf6434Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6434CertificateValid
    leaf6434InnerLogValid leaf6434CoversExact leaf6434LowerChecked

private noncomputable def leaf6435Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (7/8), chiHi := (29/32) }

private noncomputable def leaf6435Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554557/33554432) }, vSqrt := { lower := (65531/65536), upper := (11452743679/11451899904) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (94073109/67108864) }, upper := { exponent := 1, mantissa := (749/512) } }, logOuter := sk62LogOuterCertificate, logK := sk62LogKCertificate, logChi := chi92LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (22904643583/22903799808) } }, logDArg := sk62LogDArgCertificate }

private noncomputable def leaf6435InnerLog : WideLogData :=
  innerPair358Data

set_option maxRecDepth 1000000 in
private theorem leaf6435LocalValidity :
    LeafFacts leaf6435Box leaf6435Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6435Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (11452743679/11451899904) }) = true
      norm_num [leaf6435Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6435CertificateValid :
    WideCertificateValid leaf6435Box leaf6435Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk62ValidityFacts chi92ValidityFacts
    leaf6435LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6435CoverageChecked :
    coverageCheck (innerAD leaf6435Box) leaf6435InnerLog = true := by
  rfl'

private theorem leaf6435InnerLogValid :
    leaf6435InnerLog.Valid 8 (innerAD leaf6435Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint98PositiveFacts.valid leaf6435CoverageChecked

private noncomputable def leaf6435InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629699/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6435InputLogOnePlusV_eq :
    leaf6435InputLogOnePlusV = outerEnclosure 24
      (leaf6435Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6435RoundedFacts : LeafRoundedFacts 8
    leaf6435Certificate.logOnePlusV leaf6435InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6435InputLogOnePlusV_eq }

private noncomputable def leaf6435Inputs : Inputs :=
  inputsOfCaches globalInput sk62RoundedInputs
    chi92InputQChi innerPair358Input
    leaf6435InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6435LowerChecked :
    lowerCheck 24 leaf6435Box leaf6435Inputs = true := by
  rfl'

private theorem leaf6435CoversExact : CoversExact 8
    leaf6435Box leaf6435Certificate leaf6435InnerLog leaf6435Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk62RoundedFacts chi92RoundedFacts
    innerPair358RoundedFacts leaf6435RoundedFacts (by rfl)

private theorem leaf6435FlatSound : Sound leaf6435Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6435CertificateValid
    leaf6435InnerLogValid leaf6435CoversExact leaf6435LowerChecked

private noncomputable def leaf6436Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (29/32), chiHi := (15/16) }

private noncomputable def leaf6436Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554557/33554432) }, vSqrt := { lower := (65531/65536), upper := (34358231037/34355683328) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (94335237/67108864) }, upper := { exponent := 1, mantissa := (751/512) } }, logOuter := sk61LogOuterCertificate, logK := sk61LogKCertificate, logChi := chi93LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68713914365/68711366656) } }, logDArg := sk61LogDArgCertificate }

private noncomputable def leaf6436InnerLog : WideLogData :=
  innerPair358Data

set_option maxRecDepth 1000000 in
private theorem leaf6436LocalValidity :
    LeafFacts leaf6436Box leaf6436Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6436Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358231037/34355683328) }) = true
      norm_num [leaf6436Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6436CertificateValid :
    WideCertificateValid leaf6436Box leaf6436Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk61ValidityFacts chi93ValidityFacts
    leaf6436LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6436CoverageChecked :
    coverageCheck (innerAD leaf6436Box) leaf6436InnerLog = true := by
  rfl'

private theorem leaf6436InnerLogValid :
    leaf6436InnerLog.Valid 8 (innerAD leaf6436Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint98PositiveFacts.valid leaf6436CoverageChecked

private noncomputable def leaf6436InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629703/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6436InputLogOnePlusV_eq :
    leaf6436InputLogOnePlusV = outerEnclosure 24
      (leaf6436Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6436RoundedFacts : LeafRoundedFacts 8
    leaf6436Certificate.logOnePlusV leaf6436InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6436InputLogOnePlusV_eq }

private noncomputable def leaf6436Inputs : Inputs :=
  inputsOfCaches globalInput sk61RoundedInputs
    chi93InputQChi innerPair358Input
    leaf6436InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6436LowerChecked :
    lowerCheck 24 leaf6436Box leaf6436Inputs = true := by
  rfl'

private theorem leaf6436CoversExact : CoversExact 8
    leaf6436Box leaf6436Certificate leaf6436InnerLog leaf6436Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk61RoundedFacts chi93RoundedFacts
    innerPair358RoundedFacts leaf6436RoundedFacts (by rfl)

private theorem leaf6436FlatSound : Sound leaf6436Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6436CertificateValid
    leaf6436InnerLogValid leaf6436CoversExact leaf6436LowerChecked

private noncomputable def leaf6437Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (29/32), chiHi := (15/16) }

private noncomputable def leaf6437Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554559/33554432) }, vSqrt := { lower := (65531/65536), upper := (67633281/67629056) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (96235663/67108864) }, upper := { exponent := 1, mantissa := (383/256) } }, logOuter := sk62LogOuterCertificate, logK := sk62LogKCertificate, logChi := chi93LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (135262337/135258112) } }, logDArg := sk62LogDArgCertificate }

private noncomputable def leaf6437InnerLog : WideLogData :=
  innerPair369Data

set_option maxRecDepth 1000000 in
private theorem leaf6437LocalValidity :
    LeafFacts leaf6437Box leaf6437Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6437Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (67633281/67629056) }) = true
      norm_num [leaf6437Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6437CertificateValid :
    WideCertificateValid leaf6437Box leaf6437Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk62ValidityFacts chi93ValidityFacts
    leaf6437LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6437CoverageChecked :
    coverageCheck (innerAD leaf6437Box) leaf6437InnerLog = true := by
  rfl'

private theorem leaf6437InnerLogValid :
    leaf6437InnerLog.Valid 8 (innerAD leaf6437Box) :=
  wideLogDataValid_of_cachedCheck endpoint96PositiveFacts
    endpoint99PositiveFacts.valid leaf6437CoverageChecked

private noncomputable def leaf6437InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629605/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6437InputLogOnePlusV_eq :
    leaf6437InputLogOnePlusV = outerEnclosure 24
      (leaf6437Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6437RoundedFacts : LeafRoundedFacts 8
    leaf6437Certificate.logOnePlusV leaf6437InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6437InputLogOnePlusV_eq }

private noncomputable def leaf6437Inputs : Inputs :=
  inputsOfCaches globalInput sk62RoundedInputs
    chi93InputQChi innerPair369Input
    leaf6437InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6437LowerChecked :
    lowerCheck 24 leaf6437Box leaf6437Inputs = true := by
  rfl'

private theorem leaf6437CoversExact : CoversExact 8
    leaf6437Box leaf6437Certificate leaf6437InnerLog leaf6437Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk62RoundedFacts chi93RoundedFacts
    innerPair369RoundedFacts leaf6437RoundedFacts (by rfl)

private theorem leaf6437FlatSound : Sound leaf6437Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6437CertificateValid
    leaf6437InnerLogValid leaf6437CoversExact leaf6437LowerChecked

private noncomputable def leaf6438Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (15/16), chiHi := (31/32) }

private noncomputable def leaf6438Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554559/33554432) }, vSqrt := { lower := (65531/65536), upper := (8589426687/8588887040) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (96432259/67108864) }, upper := { exponent := 1, mantissa := (1535/1024) } }, logOuter := sk61LogOuterCertificate, logK := sk61LogKCertificate, logChi := chi94LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (17178313727/17177774080) } }, logDArg := sk61LogDArgCertificate }

private noncomputable def leaf6438InnerLog : WideLogData :=
  innerPair369Data

set_option maxRecDepth 1000000 in
private theorem leaf6438LocalValidity :
    LeafFacts leaf6438Box leaf6438Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6438Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (8589426687/8588887040) }) = true
      norm_num [leaf6438Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6438CertificateValid :
    WideCertificateValid leaf6438Box leaf6438Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk61ValidityFacts chi94ValidityFacts
    leaf6438LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6438CoverageChecked :
    coverageCheck (innerAD leaf6438Box) leaf6438InnerLog = true := by
  rfl'

private theorem leaf6438InnerLogValid :
    leaf6438InnerLog.Valid 8 (innerAD leaf6438Box) :=
  wideLogDataValid_of_cachedCheck endpoint96PositiveFacts
    endpoint99PositiveFacts.valid leaf6438CoverageChecked

private noncomputable def leaf6438InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (1453701/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf6438InputLogOnePlusV_eq :
    leaf6438InputLogOnePlusV = outerEnclosure 24
      (leaf6438Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6438RoundedFacts : LeafRoundedFacts 8
    leaf6438Certificate.logOnePlusV leaf6438InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6438InputLogOnePlusV_eq }

private noncomputable def leaf6438Inputs : Inputs :=
  inputsOfCaches globalInput sk61RoundedInputs
    chi94InputQChi innerPair369Input
    leaf6438InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6438LowerChecked :
    lowerCheck 24 leaf6438Box leaf6438Inputs = true := by
  rfl'

private theorem leaf6438CoversExact : CoversExact 8
    leaf6438Box leaf6438Certificate leaf6438InnerLog leaf6438Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk61RoundedFacts chi94RoundedFacts
    innerPair369RoundedFacts leaf6438RoundedFacts (by rfl)

private theorem leaf6438FlatSound : Sound leaf6438Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6438CertificateValid
    leaf6438InnerLogValid leaf6438CoversExact leaf6438LowerChecked

private noncomputable def leaf6439Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (15/16), chiHi := (31/32) }

private noncomputable def leaf6439Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554561/33554432) }, vSqrt := { lower := (65531/65536), upper := (8589426687/8588855296) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (98398217/67108864) }, upper := { exponent := 1, mantissa := (783/512) } }, logOuter := sk62LogOuterCertificate, logK := sk62LogKCertificate, logChi := chi94LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (17178281983/17177710592) } }, logDArg := sk62LogDArgCertificate }

private noncomputable def leaf6439InnerLog : WideLogData :=
  innerPair374Data

set_option maxRecDepth 1000000 in
private theorem leaf6439LocalValidity :
    LeafFacts leaf6439Box leaf6439Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6439Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (8589426687/8588855296) }) = true
      norm_num [leaf6439Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6439CertificateValid :
    WideCertificateValid leaf6439Box leaf6439Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk62ValidityFacts chi94ValidityFacts
    leaf6439LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6439CoverageChecked :
    coverageCheck (innerAD leaf6439Box) leaf6439InnerLog = true := by
  rfl'

private theorem leaf6439InnerLogValid :
    leaf6439InnerLog.Valid 8 (innerAD leaf6439Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint482PositiveFacts.valid leaf6439CoverageChecked

private noncomputable def leaf6439InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629639/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6439InputLogOnePlusV_eq :
    leaf6439InputLogOnePlusV = outerEnclosure 24
      (leaf6439Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6439RoundedFacts : LeafRoundedFacts 8
    leaf6439Certificate.logOnePlusV leaf6439InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6439InputLogOnePlusV_eq }

private noncomputable def leaf6439Inputs : Inputs :=
  inputsOfCaches globalInput sk62RoundedInputs
    chi94InputQChi innerPair374Input
    leaf6439InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6439LowerChecked :
    lowerCheck 24 leaf6439Box leaf6439Inputs = true := by
  rfl'

private theorem leaf6439CoversExact : CoversExact 8
    leaf6439Box leaf6439Certificate leaf6439InnerLog leaf6439Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk62RoundedFacts chi94RoundedFacts
    innerPair374RoundedFacts leaf6439RoundedFacts (by rfl)

private theorem leaf6439FlatSound : Sound leaf6439Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6439CertificateValid
    leaf6439InnerLogValid leaf6439CoversExact leaf6439LowerChecked

private noncomputable def leaf6440Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (31/32), chiHi := (1) }

private noncomputable def leaf6440Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554561/33554432) }, vSqrt := { lower := (65531/65536), upper := (8589426687/8588853248) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (98529281/67108864) }, upper := { exponent := 1, mantissa := (49/32) } }, logOuter := sk61LogOuterCertificate, logK := sk61LogKCertificate, logChi := chi95LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (17178279935/17177706496) } }, logDArg := sk61LogDArgCertificate }

private noncomputable def leaf6440InnerLog : WideLogData :=
  innerPair374Data

set_option maxRecDepth 1000000 in
private theorem leaf6440LocalValidity :
    LeafFacts leaf6440Box leaf6440Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6440Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (8589426687/8588853248) }) = true
      norm_num [leaf6440Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6440CertificateValid :
    WideCertificateValid leaf6440Box leaf6440Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk61ValidityFacts chi95ValidityFacts
    leaf6440LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6440CoverageChecked :
    coverageCheck (innerAD leaf6440Box) leaf6440InnerLog = true := by
  rfl'

private theorem leaf6440InnerLogValid :
    leaf6440InnerLog.Valid 8 (innerAD leaf6440Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint482PositiveFacts.valid leaf6440CoverageChecked

private noncomputable def leaf6440InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629641/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6440InputLogOnePlusV_eq :
    leaf6440InputLogOnePlusV = outerEnclosure 24
      (leaf6440Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6440RoundedFacts : LeafRoundedFacts 8
    leaf6440Certificate.logOnePlusV leaf6440InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6440InputLogOnePlusV_eq }

private noncomputable def leaf6440Inputs : Inputs :=
  inputsOfCaches globalInput sk61RoundedInputs
    chi95InputQChi innerPair374Input
    leaf6440InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6440LowerChecked :
    lowerCheck 24 leaf6440Box leaf6440Inputs = true := by
  rfl'

private theorem leaf6440CoversExact : CoversExact 8
    leaf6440Box leaf6440Certificate leaf6440InnerLog leaf6440Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk61RoundedFacts chi95RoundedFacts
    innerPair374RoundedFacts leaf6440RoundedFacts (by rfl)

private theorem leaf6440FlatSound : Sound leaf6440Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6440CertificateValid
    leaf6440InnerLogValid leaf6440CoversExact leaf6440LowerChecked

private noncomputable def leaf6441Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (31/32), chiHi := (1) }

private noncomputable def leaf6441Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554563/33554432) }, vSqrt := { lower := (65531/65536), upper := (2863142229/2862940160) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (100560771/67108864) }, upper := { exponent := 1, mantissa := (25/16) } }, logOuter := sk62LogOuterCertificate, logK := sk62LogKCertificate, logChi := chi95LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (5726082389/5725880320) } }, logDArg := sk62LogDArgCertificate }

private noncomputable def leaf6441InnerLog : WideLogData :=
  innerPair377Data

set_option maxRecDepth 1000000 in
private theorem leaf6441LocalValidity :
    LeafFacts leaf6441Box leaf6441Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6441Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (2863142229/2862940160) }) = true
      norm_num [leaf6441Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6441CertificateValid :
    WideCertificateValid leaf6441Box leaf6441Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk62ValidityFacts chi95ValidityFacts
    leaf6441LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6441CoverageChecked :
    coverageCheck (innerAD leaf6441Box) leaf6441InnerLog = true := by
  rfl'

private theorem leaf6441InnerLogValid :
    leaf6441InnerLog.Valid 8 (innerAD leaf6441Box) :=
  wideLogDataValid_of_cachedCheck endpoint98PositiveFacts
    endpoint483PositiveFacts.valid leaf6441CoverageChecked

private noncomputable def leaf6441InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629673/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6441InputLogOnePlusV_eq :
    leaf6441InputLogOnePlusV = outerEnclosure 24
      (leaf6441Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6441RoundedFacts : LeafRoundedFacts 8
    leaf6441Certificate.logOnePlusV leaf6441InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6441InputLogOnePlusV_eq }

private noncomputable def leaf6441Inputs : Inputs :=
  inputsOfCaches globalInput sk62RoundedInputs
    chi95InputQChi innerPair377Input
    leaf6441InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6441LowerChecked :
    lowerCheck 24 leaf6441Box leaf6441Inputs = true := by
  rfl'

private theorem leaf6441CoversExact : CoversExact 8
    leaf6441Box leaf6441Certificate leaf6441InnerLog leaf6441Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk62RoundedFacts chi95RoundedFacts
    innerPair377RoundedFacts leaf6441RoundedFacts (by rfl)

private theorem leaf6441FlatSound : Sound leaf6441Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6441CertificateValid
    leaf6441InnerLogValid leaf6441CoversExact leaf6441LowerChecked

private noncomputable def leaf6442Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (7/8), chiHi := (29/32) }

private noncomputable def leaf6442Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554559/33554432) }, vSqrt := { lower := (65531/65536), upper := (8589426687/8588895232) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (95908003/67108864) }, upper := { exponent := 1, mantissa := (1527/1024) } }, logOuter := sk63LogOuterCertificate, logK := sk63LogKCertificate, logChi := chi92LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (17178321919/17177790464) } }, logDArg := sk63LogDArgCertificate }

private noncomputable def leaf6442InnerLog : WideLogData :=
  innerPair369Data

set_option maxRecDepth 1000000 in
private theorem leaf6442LocalValidity :
    LeafFacts leaf6442Box leaf6442Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6442Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (8589426687/8588895232) }) = true
      norm_num [leaf6442Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6442CertificateValid :
    WideCertificateValid leaf6442Box leaf6442Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk63ValidityFacts chi92ValidityFacts
    leaf6442LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6442CoverageChecked :
    coverageCheck (innerAD leaf6442Box) leaf6442InnerLog = true := by
  rfl'

private theorem leaf6442InnerLogValid :
    leaf6442InnerLog.Valid 8 (innerAD leaf6442Box) :=
  wideLogDataValid_of_cachedCheck endpoint96PositiveFacts
    endpoint99PositiveFacts.valid leaf6442CoverageChecked

private noncomputable def leaf6442InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (363425/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf6442InputLogOnePlusV_eq :
    leaf6442InputLogOnePlusV = outerEnclosure 24
      (leaf6442Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6442RoundedFacts : LeafRoundedFacts 8
    leaf6442Certificate.logOnePlusV leaf6442InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6442InputLogOnePlusV_eq }

private noncomputable def leaf6442Inputs : Inputs :=
  inputsOfCaches globalInput sk63RoundedInputs
    chi92InputQChi innerPair369Input
    leaf6442InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6442LowerChecked :
    lowerCheck 24 leaf6442Box leaf6442Inputs = true := by
  rfl'

private theorem leaf6442CoversExact : CoversExact 8
    leaf6442Box leaf6442Certificate leaf6442InnerLog leaf6442Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk63RoundedFacts chi92RoundedFacts
    innerPair369RoundedFacts leaf6442RoundedFacts (by rfl)

private theorem leaf6442FlatSound : Sound leaf6442Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6442CertificateValid
    leaf6442InnerLogValid leaf6442CoversExact leaf6442LowerChecked

private noncomputable def leaf6443Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (7/8), chiHi := (29/32) }

private noncomputable def leaf6443Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554561/33554432) }, vSqrt := { lower := (65531/65536), upper := (8589426687/8588865536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (97742897/67108864) }, upper := { exponent := 1, mantissa := (389/256) } }, logOuter := sk64LogOuterCertificate, logK := sk64LogKCertificate, logChi := chi92LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (17178292223/17177731072) } }, logDArg := sk64LogDArgCertificate }

private noncomputable def leaf6443InnerLog : WideLogData :=
  innerPair374Data

set_option maxRecDepth 1000000 in
private theorem leaf6443LocalValidity :
    LeafFacts leaf6443Box leaf6443Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6443Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (8589426687/8588865536) }) = true
      norm_num [leaf6443Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6443CertificateValid :
    WideCertificateValid leaf6443Box leaf6443Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk64ValidityFacts chi92ValidityFacts
    leaf6443LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6443CoverageChecked :
    coverageCheck (innerAD leaf6443Box) leaf6443InnerLog = true := by
  rfl'

private theorem leaf6443InnerLogValid :
    leaf6443InnerLog.Valid 8 (innerAD leaf6443Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint482PositiveFacts.valid leaf6443CoverageChecked

private noncomputable def leaf6443InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629629/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6443InputLogOnePlusV_eq :
    leaf6443InputLogOnePlusV = outerEnclosure 24
      (leaf6443Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6443RoundedFacts : LeafRoundedFacts 8
    leaf6443Certificate.logOnePlusV leaf6443InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6443InputLogOnePlusV_eq }

private noncomputable def leaf6443Inputs : Inputs :=
  inputsOfCaches globalInput sk64RoundedInputs
    chi92InputQChi innerPair374Input
    leaf6443InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6443LowerChecked :
    lowerCheck 24 leaf6443Box leaf6443Inputs = true := by
  rfl'

private theorem leaf6443CoversExact : CoversExact 8
    leaf6443Box leaf6443Certificate leaf6443InnerLog leaf6443Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk64RoundedFacts chi92RoundedFacts
    innerPair374RoundedFacts leaf6443RoundedFacts (by rfl)

private theorem leaf6443FlatSound : Sound leaf6443Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6443CertificateValid
    leaf6443InnerLogValid leaf6443CoversExact leaf6443LowerChecked

private noncomputable def leaf6444Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (29/32), chiHi := (15/16) }

private noncomputable def leaf6444Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554561/33554432) }, vSqrt := { lower := (65531/65536), upper := (8589426687/8588859392) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (98136089/67108864) }, upper := { exponent := 1, mantissa := (781/512) } }, logOuter := sk63LogOuterCertificate, logK := sk63LogKCertificate, logChi := chi93LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (17178286079/17177718784) } }, logDArg := sk63LogDArgCertificate }

private noncomputable def leaf6444InnerLog : WideLogData :=
  innerPair374Data

set_option maxRecDepth 1000000 in
private theorem leaf6444LocalValidity :
    LeafFacts leaf6444Box leaf6444Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6444Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (8589426687/8588859392) }) = true
      norm_num [leaf6444Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6444CertificateValid :
    WideCertificateValid leaf6444Box leaf6444Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk63ValidityFacts chi93ValidityFacts
    leaf6444LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6444CoverageChecked :
    coverageCheck (innerAD leaf6444Box) leaf6444InnerLog = true := by
  rfl'

private theorem leaf6444InnerLogValid :
    leaf6444InnerLog.Valid 8 (innerAD leaf6444Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint482PositiveFacts.valid leaf6444CoverageChecked

private noncomputable def leaf6444InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629635/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6444InputLogOnePlusV_eq :
    leaf6444InputLogOnePlusV = outerEnclosure 24
      (leaf6444Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6444RoundedFacts : LeafRoundedFacts 8
    leaf6444Certificate.logOnePlusV leaf6444InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6444InputLogOnePlusV_eq }

private noncomputable def leaf6444Inputs : Inputs :=
  inputsOfCaches globalInput sk63RoundedInputs
    chi93InputQChi innerPair374Input
    leaf6444InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6444LowerChecked :
    lowerCheck 24 leaf6444Box leaf6444Inputs = true := by
  rfl'

private theorem leaf6444CoversExact : CoversExact 8
    leaf6444Box leaf6444Certificate leaf6444InnerLog leaf6444Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk63RoundedFacts chi93RoundedFacts
    innerPair374RoundedFacts leaf6444RoundedFacts (by rfl)

private theorem leaf6444FlatSound : Sound leaf6444Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6444CertificateValid
    leaf6444InnerLogValid leaf6444CoversExact leaf6444LowerChecked

private noncomputable def leaf6445Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (29/32), chiHi := (15/16) }

private noncomputable def leaf6445Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554563/33554432) }, vSqrt := { lower := (65531/65536), upper := (8589426687/8588828672) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (100036515/67108864) }, upper := { exponent := 1, mantissa := (199/128) } }, logOuter := sk64LogOuterCertificate, logK := sk64LogKCertificate, logChi := chi93LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (17178255359/17177657344) } }, logDArg := sk64LogDArgCertificate }

private noncomputable def leaf6445InnerLog : WideLogData :=
  innerPair377Data

set_option maxRecDepth 1000000 in
private theorem leaf6445LocalValidity :
    LeafFacts leaf6445Box leaf6445Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6445Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (8589426687/8588828672) }) = true
      norm_num [leaf6445Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6445CertificateValid :
    WideCertificateValid leaf6445Box leaf6445Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk64ValidityFacts chi93ValidityFacts
    leaf6445LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6445CoverageChecked :
    coverageCheck (innerAD leaf6445Box) leaf6445InnerLog = true := by
  rfl'

private theorem leaf6445InnerLogValid :
    leaf6445InnerLog.Valid 8 (innerAD leaf6445Box) :=
  wideLogDataValid_of_cachedCheck endpoint98PositiveFacts
    endpoint483PositiveFacts.valid leaf6445CoverageChecked

private noncomputable def leaf6445InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629665/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6445InputLogOnePlusV_eq :
    leaf6445InputLogOnePlusV = outerEnclosure 24
      (leaf6445Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6445RoundedFacts : LeafRoundedFacts 8
    leaf6445Certificate.logOnePlusV leaf6445InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6445InputLogOnePlusV_eq }

private noncomputable def leaf6445Inputs : Inputs :=
  inputsOfCaches globalInput sk64RoundedInputs
    chi93InputQChi innerPair377Input
    leaf6445InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6445LowerChecked :
    lowerCheck 24 leaf6445Box leaf6445Inputs = true := by
  rfl'

private theorem leaf6445CoversExact : CoversExact 8
    leaf6445Box leaf6445Certificate leaf6445InnerLog leaf6445Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk64RoundedFacts chi93RoundedFacts
    innerPair377RoundedFacts leaf6445RoundedFacts (by rfl)

private theorem leaf6445FlatSound : Sound leaf6445Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6445CertificateValid
    leaf6445InnerLogValid leaf6445CoversExact leaf6445LowerChecked

private noncomputable def leaf6446Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (15/16), chiHi := (31/32) }

private noncomputable def leaf6446Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554563/33554432) }, vSqrt := { lower := (65531/65536), upper := (954380743/954313728) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (100364175/67108864) }, upper := { exponent := 1, mantissa := (1597/1024) } }, logOuter := sk63LogOuterCertificate, logK := sk63LogKCertificate, logChi := chi94LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (1908694471/1908627456) } }, logDArg := sk63LogDArgCertificate }

private noncomputable def leaf6446InnerLog : WideLogData :=
  innerPair377Data

set_option maxRecDepth 1000000 in
private theorem leaf6446LocalValidity :
    LeafFacts leaf6446Box leaf6446Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6446Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (954380743/954313728) }) = true
      norm_num [leaf6446Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6446CertificateValid :
    WideCertificateValid leaf6446Box leaf6446Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk63ValidityFacts chi94ValidityFacts
    leaf6446LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6446CoverageChecked :
    coverageCheck (innerAD leaf6446Box) leaf6446InnerLog = true := by
  rfl'

private theorem leaf6446InnerLogValid :
    leaf6446InnerLog.Valid 8 (innerAD leaf6446Box) :=
  wideLogDataValid_of_cachedCheck endpoint98PositiveFacts
    endpoint483PositiveFacts.valid leaf6446CoverageChecked

private noncomputable def leaf6446InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814835/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6446InputLogOnePlusV_eq :
    leaf6446InputLogOnePlusV = outerEnclosure 24
      (leaf6446Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6446RoundedFacts : LeafRoundedFacts 8
    leaf6446Certificate.logOnePlusV leaf6446InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6446InputLogOnePlusV_eq }

private noncomputable def leaf6446Inputs : Inputs :=
  inputsOfCaches globalInput sk63RoundedInputs
    chi94InputQChi innerPair377Input
    leaf6446InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6446LowerChecked :
    lowerCheck 24 leaf6446Box leaf6446Inputs = true := by
  rfl'

private theorem leaf6446CoversExact : CoversExact 8
    leaf6446Box leaf6446Certificate leaf6446InnerLog leaf6446Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk63RoundedFacts chi94RoundedFacts
    innerPair377RoundedFacts leaf6446RoundedFacts (by rfl)

private theorem leaf6446FlatSound : Sound leaf6446Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6446CertificateValid
    leaf6446InnerLogValid leaf6446CoversExact leaf6446LowerChecked

private noncomputable def leaf6447Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (15/16), chiHi := (31/32) }

private noncomputable def leaf6447Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554565/33554432) }, vSqrt := { lower := (65531/65536), upper := (8589426687/8588791808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (102330133/67108864) }, upper := { exponent := 1, mantissa := (407/256) } }, logOuter := sk64LogOuterCertificate, logK := sk64LogKCertificate, logChi := chi94LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (17178218495/17177583616) } }, logDArg := sk64LogDArgCertificate }

private noncomputable def leaf6447InnerLog : WideLogData :=
  innerPair383Data

set_option maxRecDepth 1000000 in
private theorem leaf6447LocalValidity :
    LeafFacts leaf6447Box leaf6447Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6447Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (8589426687/8588791808) }) = true
      norm_num [leaf6447Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6447CertificateValid :
    WideCertificateValid leaf6447Box leaf6447Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk64ValidityFacts chi94ValidityFacts
    leaf6447LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6447CoverageChecked :
    coverageCheck (innerAD leaf6447Box) leaf6447InnerLog = true := by
  rfl'

private theorem leaf6447InnerLogValid :
    leaf6447InnerLog.Valid 8 (innerAD leaf6447Box) :=
  wideLogDataValid_of_cachedCheck endpoint99PositiveFacts
    endpoint484PositiveFacts.valid leaf6447CoverageChecked

private noncomputable def leaf6447InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629701/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6447InputLogOnePlusV_eq :
    leaf6447InputLogOnePlusV = outerEnclosure 24
      (leaf6447Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6447RoundedFacts : LeafRoundedFacts 8
    leaf6447Certificate.logOnePlusV leaf6447InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6447InputLogOnePlusV_eq }

private noncomputable def leaf6447Inputs : Inputs :=
  inputsOfCaches globalInput sk64RoundedInputs
    chi94InputQChi innerPair383Input
    leaf6447InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6447LowerChecked :
    lowerCheck 24 leaf6447Box leaf6447Inputs = true := by
  rfl'

private theorem leaf6447CoversExact : CoversExact 8
    leaf6447Box leaf6447Certificate leaf6447InnerLog leaf6447Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk64RoundedFacts chi94RoundedFacts
    innerPair383RoundedFacts leaf6447RoundedFacts (by rfl)

private theorem leaf6447FlatSound : Sound leaf6447Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6447CertificateValid
    leaf6447InnerLogValid leaf6447CoversExact leaf6447LowerChecked

private noncomputable def leaf6448Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (31/32), chiHi := (1) }

private noncomputable def leaf6448Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554565/33554432) }, vSqrt := { lower := (65531/65536), upper := (8589426687/8588787712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (102592261/67108864) }, upper := { exponent := 1, mantissa := (51/32) } }, logOuter := sk63LogOuterCertificate, logK := sk63LogKCertificate, logChi := chi95LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (17178214399/17177575424) } }, logDArg := sk63LogDArgCertificate }

private noncomputable def leaf6448InnerLog : WideLogData :=
  innerPair383Data

set_option maxRecDepth 1000000 in
private theorem leaf6448LocalValidity :
    LeafFacts leaf6448Box leaf6448Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6448Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (8589426687/8588787712) }) = true
      norm_num [leaf6448Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6448CertificateValid :
    WideCertificateValid leaf6448Box leaf6448Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk63ValidityFacts chi95ValidityFacts
    leaf6448LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6448CoverageChecked :
    coverageCheck (innerAD leaf6448Box) leaf6448InnerLog = true := by
  rfl'

private theorem leaf6448InnerLogValid :
    leaf6448InnerLog.Valid 8 (innerAD leaf6448Box) :=
  wideLogDataValid_of_cachedCheck endpoint99PositiveFacts
    endpoint484PositiveFacts.valid leaf6448CoverageChecked

private noncomputable def leaf6448InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629705/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6448InputLogOnePlusV_eq :
    leaf6448InputLogOnePlusV = outerEnclosure 24
      (leaf6448Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6448RoundedFacts : LeafRoundedFacts 8
    leaf6448Certificate.logOnePlusV leaf6448InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6448InputLogOnePlusV_eq }

private noncomputable def leaf6448Inputs : Inputs :=
  inputsOfCaches globalInput sk63RoundedInputs
    chi95InputQChi innerPair383Input
    leaf6448InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6448LowerChecked :
    lowerCheck 24 leaf6448Box leaf6448Inputs = true := by
  rfl'

private theorem leaf6448CoversExact : CoversExact 8
    leaf6448Box leaf6448Certificate leaf6448InnerLog leaf6448Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk63RoundedFacts chi95RoundedFacts
    innerPair383RoundedFacts leaf6448RoundedFacts (by rfl)

private theorem leaf6448FlatSound : Sound leaf6448Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6448CertificateValid
    leaf6448InnerLogValid leaf6448CoversExact leaf6448LowerChecked

private noncomputable def leaf6449Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (31/32), chiHi := (1) }

private noncomputable def leaf6449Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554567/33554432) }, vSqrt := { lower := (65531/65536), upper := (8589426687/8588754944) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (104623751/67108864) }, upper := { exponent := 1, mantissa := (13/8) } }, logOuter := sk64LogOuterCertificate, logK := sk64LogKCertificate, logChi := chi95LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (17178181631/17177509888) } }, logDArg := sk64LogDArgCertificate }

private noncomputable def leaf6449InnerLog : WideLogData :=
  innerPair745Data

set_option maxRecDepth 1000000 in
private theorem leaf6449LocalValidity :
    LeafFacts leaf6449Box leaf6449Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6449Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (8589426687/8588754944) }) = true
      norm_num [leaf6449Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6449CertificateValid :
    WideCertificateValid leaf6449Box leaf6449Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk64ValidityFacts chi95ValidityFacts
    leaf6449LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6449CoverageChecked :
    coverageCheck (innerAD leaf6449Box) leaf6449InnerLog = true := by
  rfl'

private theorem leaf6449InnerLogValid :
    leaf6449InnerLog.Valid 8 (innerAD leaf6449Box) :=
  wideLogDataValid_of_cachedCheck endpoint482PositiveFacts
    endpoint485PositiveFacts.valid leaf6449CoverageChecked

private noncomputable def leaf6449InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629737/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6449InputLogOnePlusV_eq :
    leaf6449InputLogOnePlusV = outerEnclosure 24
      (leaf6449Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6449RoundedFacts : LeafRoundedFacts 8
    leaf6449Certificate.logOnePlusV leaf6449InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6449InputLogOnePlusV_eq }

private noncomputable def leaf6449Inputs : Inputs :=
  inputsOfCaches globalInput sk64RoundedInputs
    chi95InputQChi innerPair745Input
    leaf6449InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6449LowerChecked :
    lowerCheck 24 leaf6449Box leaf6449Inputs = true := by
  rfl'

private theorem leaf6449CoversExact : CoversExact 8
    leaf6449Box leaf6449Certificate leaf6449InnerLog leaf6449Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk64RoundedFacts chi95RoundedFacts
    innerPair745RoundedFacts leaf6449RoundedFacts (by rfl)

private theorem leaf6449FlatSound : Sound leaf6449Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6449CertificateValid
    leaf6449InnerLogValid leaf6449CoversExact leaf6449LowerChecked

private noncomputable def leaf6450Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (3/4), chiHi := (25/32) }

private noncomputable def leaf6450Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554555/33554432) }, vSqrt := { lower := (65531/65536), upper := (34358231037/34355949568) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (90141191/67108864) }, upper := { exponent := 1, mantissa := (1437/1024) } }, logOuter := sk69LogOuterCertificate, logK := sk69LogKCertificate, logChi := chi88LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68714180605/68711899136) } }, logDArg := sk69LogDArgCertificate }

private noncomputable def leaf6450InnerLog : WideLogData :=
  innerPair347Data

set_option maxRecDepth 1000000 in
private theorem leaf6450LocalValidity :
    LeafFacts leaf6450Box leaf6450Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6450Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358231037/34355949568) }) = true
      norm_num [leaf6450Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6450CertificateValid :
    WideCertificateValid leaf6450Box leaf6450Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk69ValidityFacts chi88ValidityFacts
    leaf6450LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6450CoverageChecked :
    coverageCheck (innerAD leaf6450Box) leaf6450InnerLog = true := by
  rfl'

private theorem leaf6450InnerLogValid :
    leaf6450InnerLog.Valid 8 (innerAD leaf6450Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint96PositiveFacts.valid leaf6450CoverageChecked

private noncomputable def leaf6450InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814819/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6450InputLogOnePlusV_eq :
    leaf6450InputLogOnePlusV = outerEnclosure 24
      (leaf6450Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6450RoundedFacts : LeafRoundedFacts 8
    leaf6450Certificate.logOnePlusV leaf6450InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6450InputLogOnePlusV_eq }

private noncomputable def leaf6450Inputs : Inputs :=
  inputsOfCaches globalInput sk69RoundedInputs
    chi88InputQChi innerPair347Input
    leaf6450InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6450LowerChecked :
    lowerCheck 24 leaf6450Box leaf6450Inputs = true := by
  rfl'

private theorem leaf6450CoversExact : CoversExact 8
    leaf6450Box leaf6450Certificate leaf6450InnerLog leaf6450Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk69RoundedFacts chi88RoundedFacts
    innerPair347RoundedFacts leaf6450RoundedFacts (by rfl)

private theorem leaf6450FlatSound : Sound leaf6450Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6450CertificateValid
    leaf6450InnerLogValid leaf6450CoversExact leaf6450LowerChecked

private noncomputable def leaf6451Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (3/4), chiHi := (25/32) }

private noncomputable def leaf6451Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554557/33554432) }, vSqrt := { lower := (65531/65536), upper := (11452743679/11451949056) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (91713957/67108864) }, upper := { exponent := 1, mantissa := (731/512) } }, logOuter := sk70LogOuterCertificate, logK := sk70LogKCertificate, logChi := chi88LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (22904692735/22903898112) } }, logDArg := sk70LogDArgCertificate }

private noncomputable def leaf6451InnerLog : WideLogData :=
  innerPair354Data

set_option maxRecDepth 1000000 in
private theorem leaf6451LocalValidity :
    LeafFacts leaf6451Box leaf6451Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6451Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (11452743679/11451949056) }) = true
      norm_num [leaf6451Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6451CertificateValid :
    WideCertificateValid leaf6451Box leaf6451Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk70ValidityFacts chi88ValidityFacts
    leaf6451LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6451CoverageChecked :
    coverageCheck (innerAD leaf6451Box) leaf6451InnerLog = true := by
  rfl'

private theorem leaf6451InnerLogValid :
    leaf6451InnerLog.Valid 8 (innerAD leaf6451Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint97PositiveFacts.valid leaf6451CoverageChecked

private noncomputable def leaf6451InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629663/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6451InputLogOnePlusV_eq :
    leaf6451InputLogOnePlusV = outerEnclosure 24
      (leaf6451Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6451RoundedFacts : LeafRoundedFacts 8
    leaf6451Certificate.logOnePlusV leaf6451InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6451InputLogOnePlusV_eq }

private noncomputable def leaf6451Inputs : Inputs :=
  inputsOfCaches globalInput sk70RoundedInputs
    chi88InputQChi innerPair354Input
    leaf6451InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6451LowerChecked :
    lowerCheck 24 leaf6451Box leaf6451Inputs = true := by
  rfl'

private theorem leaf6451CoversExact : CoversExact 8
    leaf6451Box leaf6451Certificate leaf6451InnerLog leaf6451Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk70RoundedFacts chi88RoundedFacts
    innerPair354RoundedFacts leaf6451RoundedFacts (by rfl)

private theorem leaf6451FlatSound : Sound leaf6451Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6451CertificateValid
    leaf6451InnerLogValid leaf6451CoversExact leaf6451LowerChecked

private noncomputable def leaf6452Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (25/32), chiHi := (13/16) }

private noncomputable def leaf6452Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554557/33554432) }, vSqrt := { lower := (65531/65536), upper := (11452743679/11451932672) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (92500341/67108864) }, upper := { exponent := 1, mantissa := (737/512) } }, logOuter := sk69LogOuterCertificate, logK := sk69LogKCertificate, logChi := chi89LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (22904676351/22903865344) } }, logDArg := sk69LogDArgCertificate }

private noncomputable def leaf6452InnerLog : WideLogData :=
  innerPair358Data

set_option maxRecDepth 1000000 in
private theorem leaf6452LocalValidity :
    LeafFacts leaf6452Box leaf6452Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6452Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (11452743679/11451932672) }) = true
      norm_num [leaf6452Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6452CertificateValid :
    WideCertificateValid leaf6452Box leaf6452Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk69ValidityFacts chi89ValidityFacts
    leaf6452LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6452CoverageChecked :
    coverageCheck (innerAD leaf6452Box) leaf6452InnerLog = true := by
  rfl'

private theorem leaf6452InnerLogValid :
    leaf6452InnerLog.Valid 8 (innerAD leaf6452Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint98PositiveFacts.valid leaf6452CoverageChecked

private noncomputable def leaf6452InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629675/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6452InputLogOnePlusV_eq :
    leaf6452InputLogOnePlusV = outerEnclosure 24
      (leaf6452Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6452RoundedFacts : LeafRoundedFacts 8
    leaf6452Certificate.logOnePlusV leaf6452InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6452InputLogOnePlusV_eq }

private noncomputable def leaf6452Inputs : Inputs :=
  inputsOfCaches globalInput sk69RoundedInputs
    chi89InputQChi innerPair358Input
    leaf6452InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6452LowerChecked :
    lowerCheck 24 leaf6452Box leaf6452Inputs = true := by
  rfl'

private theorem leaf6452CoversExact : CoversExact 8
    leaf6452Box leaf6452Certificate leaf6452InnerLog leaf6452Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk69RoundedFacts chi89RoundedFacts
    innerPair358RoundedFacts leaf6452RoundedFacts (by rfl)

private theorem leaf6452FlatSound : Sound leaf6452Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6452CertificateValid
    leaf6452InnerLogValid leaf6452CoversExact leaf6452LowerChecked

private noncomputable def leaf6453Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (25/32), chiHi := (13/16) }

private noncomputable def leaf6453Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554559/33554432) }, vSqrt := { lower := (65531/65536), upper := (34358231037/34355691520) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (94138639/67108864) }, upper := { exponent := 1, mantissa := (375/256) } }, logOuter := sk70LogOuterCertificate, logK := sk70LogKCertificate, logChi := chi89LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68713922557/68711383040) } }, logDArg := sk70LogDArgCertificate }

private noncomputable def leaf6453InnerLog : WideLogData :=
  innerPair358Data

set_option maxRecDepth 1000000 in
private theorem leaf6453LocalValidity :
    LeafFacts leaf6453Box leaf6453Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6453Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358231037/34355691520) }) = true
      norm_num [leaf6453Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6453CertificateValid :
    WideCertificateValid leaf6453Box leaf6453Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk70ValidityFacts chi89ValidityFacts
    leaf6453LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6453CoverageChecked :
    coverageCheck (innerAD leaf6453Box) leaf6453InnerLog = true := by
  rfl'

private theorem leaf6453InnerLogValid :
    leaf6453InnerLog.Valid 8 (innerAD leaf6453Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint98PositiveFacts.valid leaf6453CoverageChecked

private noncomputable def leaf6453InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629701/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6453InputLogOnePlusV_eq :
    leaf6453InputLogOnePlusV = outerEnclosure 24
      (leaf6453Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6453RoundedFacts : LeafRoundedFacts 8
    leaf6453Certificate.logOnePlusV leaf6453InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6453InputLogOnePlusV_eq }

private noncomputable def leaf6453Inputs : Inputs :=
  inputsOfCaches globalInput sk70RoundedInputs
    chi89InputQChi innerPair358Input
    leaf6453InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6453LowerChecked :
    lowerCheck 24 leaf6453Box leaf6453Inputs = true := by
  rfl'

private theorem leaf6453CoversExact : CoversExact 8
    leaf6453Box leaf6453Certificate leaf6453InnerLog leaf6453Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk70RoundedFacts chi89RoundedFacts
    innerPair358RoundedFacts leaf6453RoundedFacts (by rfl)

private theorem leaf6453FlatSound : Sound leaf6453Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6453CertificateValid
    leaf6453InnerLogValid leaf6453CoversExact leaf6453LowerChecked

private noncomputable def leaf6454Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (3/4), chiHi := (25/32) }

private noncomputable def leaf6454Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554559/33554432) }, vSqrt := { lower := (65531/65536), upper := (34358231037/34355744768) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (93286723/67108864) }, upper := { exponent := 1, mantissa := (1487/1024) } }, logOuter := sk67LogOuterCertificate, logK := sk67LogKCertificate, logChi := chi88LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68713975805/68711489536) } }, logDArg := sk67LogDArgCertificate }

private noncomputable def leaf6454InnerLog : WideLogData :=
  innerPair358Data

set_option maxRecDepth 1000000 in
private theorem leaf6454LocalValidity :
    LeafFacts leaf6454Box leaf6454Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6454Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358231037/34355744768) }) = true
      norm_num [leaf6454Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6454CertificateValid :
    WideCertificateValid leaf6454Box leaf6454Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk67ValidityFacts chi88ValidityFacts
    leaf6454LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6454CoverageChecked :
    coverageCheck (innerAD leaf6454Box) leaf6454InnerLog = true := by
  rfl'

private theorem leaf6454InnerLogValid :
    leaf6454InnerLog.Valid 8 (innerAD leaf6454Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint98PositiveFacts.valid leaf6454CoverageChecked

private noncomputable def leaf6454InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (1453711/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf6454InputLogOnePlusV_eq :
    leaf6454InputLogOnePlusV = outerEnclosure 24
      (leaf6454Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6454RoundedFacts : LeafRoundedFacts 8
    leaf6454Certificate.logOnePlusV leaf6454InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6454InputLogOnePlusV_eq }

private noncomputable def leaf6454Inputs : Inputs :=
  inputsOfCaches globalInput sk67RoundedInputs
    chi88InputQChi innerPair358Input
    leaf6454InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6454LowerChecked :
    lowerCheck 24 leaf6454Box leaf6454Inputs = true := by
  rfl'

private theorem leaf6454CoversExact : CoversExact 8
    leaf6454Box leaf6454Certificate leaf6454InnerLog leaf6454Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk67RoundedFacts chi88RoundedFacts
    innerPair358RoundedFacts leaf6454RoundedFacts (by rfl)

private theorem leaf6454FlatSound : Sound leaf6454Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6454CertificateValid
    leaf6454InnerLogValid leaf6454CoversExact leaf6454LowerChecked

private noncomputable def leaf6455Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (3/4), chiHi := (25/32) }

private noncomputable def leaf6455Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554561/33554432) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34355642368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (94859489/67108864) }, upper := { exponent := 1, mantissa := (189/128) } }, logOuter := sk68LogOuterCertificate, logK := sk68LogKCertificate, logChi := chi88LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68713873405/68711284736) } }, logDArg := sk68LogDArgCertificate }

private noncomputable def leaf6455InnerLog : WideLogData :=
  innerPair369Data

set_option maxRecDepth 1000000 in
private theorem leaf6455LocalValidity :
    LeafFacts leaf6455Box leaf6455Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6455Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34355642368) }) = true
      norm_num [leaf6455Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6455CertificateValid :
    WideCertificateValid leaf6455Box leaf6455Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk68ValidityFacts chi88ValidityFacts
    leaf6455LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6455CoverageChecked :
    coverageCheck (innerAD leaf6455Box) leaf6455InnerLog = true := by
  rfl'

private theorem leaf6455InnerLogValid :
    leaf6455InnerLog.Valid 8 (innerAD leaf6455Box) :=
  wideLogDataValid_of_cachedCheck endpoint96PositiveFacts
    endpoint99PositiveFacts.valid leaf6455CoverageChecked

private noncomputable def leaf6455InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629713/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6455InputLogOnePlusV_eq :
    leaf6455InputLogOnePlusV = outerEnclosure 24
      (leaf6455Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6455RoundedFacts : LeafRoundedFacts 8
    leaf6455Certificate.logOnePlusV leaf6455InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6455InputLogOnePlusV_eq }

private noncomputable def leaf6455Inputs : Inputs :=
  inputsOfCaches globalInput sk68RoundedInputs
    chi88InputQChi innerPair369Input
    leaf6455InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6455LowerChecked :
    lowerCheck 24 leaf6455Box leaf6455Inputs = true := by
  rfl'

private theorem leaf6455CoversExact : CoversExact 8
    leaf6455Box leaf6455Certificate leaf6455InnerLog leaf6455Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk68RoundedFacts chi88RoundedFacts
    innerPair369RoundedFacts leaf6455RoundedFacts (by rfl)

private theorem leaf6455FlatSound : Sound leaf6455Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6455CertificateValid
    leaf6455InnerLogValid leaf6455CoversExact leaf6455LowerChecked

private noncomputable def leaf6456Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (25/32), chiHi := (13/16) }

private noncomputable def leaf6456Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554561/33554432) }, vSqrt := { lower := (32765/32768), upper := (8589426687/8588896256) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (95776937/67108864) }, upper := { exponent := 1, mantissa := (763/512) } }, logOuter := sk67LogOuterCertificate, logK := sk67LogKCertificate, logChi := chi89LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (17178322943/17177792512) } }, logDArg := sk67LogDArgCertificate }

private noncomputable def leaf6456InnerLog : WideLogData :=
  innerPair369Data

set_option maxRecDepth 1000000 in
private theorem leaf6456LocalValidity :
    LeafFacts leaf6456Box leaf6456Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6456Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8589426687/8588896256) }) = true
      norm_num [leaf6456Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6456CertificateValid :
    WideCertificateValid leaf6456Box leaf6456Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk67ValidityFacts chi89ValidityFacts
    leaf6456LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6456CoverageChecked :
    coverageCheck (innerAD leaf6456Box) leaf6456InnerLog = true := by
  rfl'

private theorem leaf6456InnerLogValid :
    leaf6456InnerLog.Valid 8 (innerAD leaf6456Box) :=
  wideLogDataValid_of_cachedCheck endpoint96PositiveFacts
    endpoint99PositiveFacts.valid leaf6456CoverageChecked

private noncomputable def leaf6456InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629599/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6456InputLogOnePlusV_eq :
    leaf6456InputLogOnePlusV = outerEnclosure 24
      (leaf6456Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6456RoundedFacts : LeafRoundedFacts 8
    leaf6456Certificate.logOnePlusV leaf6456InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6456InputLogOnePlusV_eq }

private noncomputable def leaf6456Inputs : Inputs :=
  inputsOfCaches globalInput sk67RoundedInputs
    chi89InputQChi innerPair369Input
    leaf6456InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6456LowerChecked :
    lowerCheck 24 leaf6456Box leaf6456Inputs = true := by
  rfl'

private theorem leaf6456CoversExact : CoversExact 8
    leaf6456Box leaf6456Certificate leaf6456InnerLog leaf6456Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk67RoundedFacts chi89RoundedFacts
    innerPair369RoundedFacts leaf6456RoundedFacts (by rfl)

private theorem leaf6456FlatSound : Sound leaf6456Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6456CertificateValid
    leaf6456InnerLogValid leaf6456CoversExact leaf6456LowerChecked

private noncomputable def leaf6457Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (25/32), chiHi := (13/16) }

private noncomputable def leaf6457Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554563/33554432) }, vSqrt := { lower := (32765/32768), upper := (954380743/954318848) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (97415235/67108864) }, upper := { exponent := 1, mantissa := (97/64) } }, logOuter := sk68LogOuterCertificate, logK := sk68LogKCertificate, logChi := chi89LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (1908699591/1908637696) } }, logDArg := sk68LogDArgCertificate }

private noncomputable def leaf6457InnerLog : WideLogData :=
  innerPair374Data

set_option maxRecDepth 1000000 in
private theorem leaf6457LocalValidity :
    LeafFacts leaf6457Box leaf6457Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6457Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (954380743/954318848) }) = true
      norm_num [leaf6457Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6457CertificateValid :
    WideCertificateValid leaf6457Box leaf6457Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk68ValidityFacts chi89ValidityFacts
    leaf6457LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6457CoverageChecked :
    coverageCheck (innerAD leaf6457Box) leaf6457InnerLog = true := by
  rfl'

private theorem leaf6457InnerLogValid :
    leaf6457InnerLog.Valid 8 (innerAD leaf6457Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint482PositiveFacts.valid leaf6457CoverageChecked

private noncomputable def leaf6457InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629625/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6457InputLogOnePlusV_eq :
    leaf6457InputLogOnePlusV = outerEnclosure 24
      (leaf6457Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6457RoundedFacts : LeafRoundedFacts 8
    leaf6457Certificate.logOnePlusV leaf6457InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6457InputLogOnePlusV_eq }

private noncomputable def leaf6457Inputs : Inputs :=
  inputsOfCaches globalInput sk68RoundedInputs
    chi89InputQChi innerPair374Input
    leaf6457InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6457LowerChecked :
    lowerCheck 24 leaf6457Box leaf6457Inputs = true := by
  rfl'

private theorem leaf6457CoversExact : CoversExact 8
    leaf6457Box leaf6457Certificate leaf6457InnerLog leaf6457Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk68RoundedFacts chi89RoundedFacts
    innerPair374RoundedFacts leaf6457RoundedFacts (by rfl)

private theorem leaf6457FlatSound : Sound leaf6457Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6457CertificateValid
    leaf6457InnerLogValid leaf6457CoversExact leaf6457LowerChecked

private noncomputable def leaf6458Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (13/16), chiHi := (27/32) }

private noncomputable def leaf6458Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554559/33554432) }, vSqrt := { lower := (65531/65536), upper := (34358231037/34355646464) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (94859491/67108864) }, upper := { exponent := 1, mantissa := (1511/1024) } }, logOuter := sk69LogOuterCertificate, logK := sk69LogKCertificate, logChi := chi90LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68713877501/68711292928) } }, logDArg := sk69LogDArgCertificate }

private noncomputable def leaf6458InnerLog : WideLogData :=
  innerPair369Data

set_option maxRecDepth 1000000 in
private theorem leaf6458LocalValidity :
    LeafFacts leaf6458Box leaf6458Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6458Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358231037/34355646464) }) = true
      norm_num [leaf6458Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6458CertificateValid :
    WideCertificateValid leaf6458Box leaf6458Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk69ValidityFacts chi90ValidityFacts
    leaf6458LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6458CoverageChecked :
    coverageCheck (innerAD leaf6458Box) leaf6458InnerLog = true := by
  rfl'

private theorem leaf6458InnerLogValid :
    leaf6458InnerLog.Valid 8 (innerAD leaf6458Box) :=
  wideLogDataValid_of_cachedCheck endpoint96PositiveFacts
    endpoint99PositiveFacts.valid leaf6458CoverageChecked

private noncomputable def leaf6458InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (726857/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf6458InputLogOnePlusV_eq :
    leaf6458InputLogOnePlusV = outerEnclosure 24
      (leaf6458Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6458RoundedFacts : LeafRoundedFacts 8
    leaf6458Certificate.logOnePlusV leaf6458InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6458InputLogOnePlusV_eq }

private noncomputable def leaf6458Inputs : Inputs :=
  inputsOfCaches globalInput sk69RoundedInputs
    chi90InputQChi innerPair369Input
    leaf6458InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6458LowerChecked :
    lowerCheck 24 leaf6458Box leaf6458Inputs = true := by
  rfl'

private theorem leaf6458CoversExact : CoversExact 8
    leaf6458Box leaf6458Certificate leaf6458InnerLog leaf6458Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk69RoundedFacts chi90RoundedFacts
    innerPair369RoundedFacts leaf6458RoundedFacts (by rfl)

private theorem leaf6458FlatSound : Sound leaf6458Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6458CertificateValid
    leaf6458InnerLogValid leaf6458CoversExact leaf6458LowerChecked

private noncomputable def leaf6459Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (13/16), chiHi := (27/32) }

private noncomputable def leaf6459Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554561/33554432) }, vSqrt := { lower := (65531/65536), upper := (8589426687/8588883968) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (96563321/67108864) }, upper := { exponent := 1, mantissa := (769/512) } }, logOuter := sk70LogOuterCertificate, logK := sk70LogKCertificate, logChi := chi90LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (17178310655/17177767936) } }, logDArg := sk70LogDArgCertificate }

private noncomputable def leaf6459InnerLog : WideLogData :=
  innerPair374Data

set_option maxRecDepth 1000000 in
private theorem leaf6459LocalValidity :
    LeafFacts leaf6459Box leaf6459Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6459Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (8589426687/8588883968) }) = true
      norm_num [leaf6459Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6459CertificateValid :
    WideCertificateValid leaf6459Box leaf6459Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk70ValidityFacts chi90ValidityFacts
    leaf6459LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6459CoverageChecked :
    coverageCheck (innerAD leaf6459Box) leaf6459InnerLog = true := by
  rfl'

private theorem leaf6459InnerLogValid :
    leaf6459InnerLog.Valid 8 (innerAD leaf6459Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint482PositiveFacts.valid leaf6459CoverageChecked

private noncomputable def leaf6459InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629611/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6459InputLogOnePlusV_eq :
    leaf6459InputLogOnePlusV = outerEnclosure 24
      (leaf6459Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6459RoundedFacts : LeafRoundedFacts 8
    leaf6459Certificate.logOnePlusV leaf6459InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6459InputLogOnePlusV_eq }

private noncomputable def leaf6459Inputs : Inputs :=
  inputsOfCaches globalInput sk70RoundedInputs
    chi90InputQChi innerPair374Input
    leaf6459InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6459LowerChecked :
    lowerCheck 24 leaf6459Box leaf6459Inputs = true := by
  rfl'

private theorem leaf6459CoversExact : CoversExact 8
    leaf6459Box leaf6459Certificate leaf6459InnerLog leaf6459Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk70RoundedFacts chi90RoundedFacts
    innerPair374RoundedFacts leaf6459RoundedFacts (by rfl)

private theorem leaf6459FlatSound : Sound leaf6459Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6459CertificateValid
    leaf6459InnerLogValid leaf6459CoversExact leaf6459LowerChecked

private noncomputable def leaf6460Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (27/32), chiHi := (7/8) }

private noncomputable def leaf6460Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554561/33554432) }, vSqrt := { lower := (65531/65536), upper := (8589426687/8588873728) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (97218641/67108864) }, upper := { exponent := 1, mantissa := (387/256) } }, logOuter := sk69LogOuterCertificate, logK := sk69LogKCertificate, logChi := chi91LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (17178300415/17177747456) } }, logDArg := sk69LogDArgCertificate }

private noncomputable def leaf6460InnerLog : WideLogData :=
  innerPair374Data

set_option maxRecDepth 1000000 in
private theorem leaf6460LocalValidity :
    LeafFacts leaf6460Box leaf6460Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6460Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (8589426687/8588873728) }) = true
      norm_num [leaf6460Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6460CertificateValid :
    WideCertificateValid leaf6460Box leaf6460Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk69ValidityFacts chi91ValidityFacts
    leaf6460LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6460CoverageChecked :
    coverageCheck (innerAD leaf6460Box) leaf6460InnerLog = true := by
  rfl'

private theorem leaf6460InnerLogValid :
    leaf6460InnerLog.Valid 8 (innerAD leaf6460Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint482PositiveFacts.valid leaf6460CoverageChecked

private noncomputable def leaf6460InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629621/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6460InputLogOnePlusV_eq :
    leaf6460InputLogOnePlusV = outerEnclosure 24
      (leaf6460Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6460RoundedFacts : LeafRoundedFacts 8
    leaf6460Certificate.logOnePlusV leaf6460InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6460InputLogOnePlusV_eq }

private noncomputable def leaf6460Inputs : Inputs :=
  inputsOfCaches globalInput sk69RoundedInputs
    chi91InputQChi innerPair374Input
    leaf6460InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6460LowerChecked :
    lowerCheck 24 leaf6460Box leaf6460Inputs = true := by
  rfl'

private theorem leaf6460CoversExact : CoversExact 8
    leaf6460Box leaf6460Certificate leaf6460InnerLog leaf6460Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk69RoundedFacts chi91RoundedFacts
    innerPair374RoundedFacts leaf6460RoundedFacts (by rfl)

private theorem leaf6460FlatSound : Sound leaf6460Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6460CertificateValid
    leaf6460InnerLogValid leaf6460CoversExact leaf6460LowerChecked

private noncomputable def leaf6461Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (27/32), chiHi := (7/8) }

private noncomputable def leaf6461Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554563/33554432) }, vSqrt := { lower := (65531/65536), upper := (2863142229/2862948352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (98988003/67108864) }, upper := { exponent := 1, mantissa := (197/128) } }, logOuter := sk70LogOuterCertificate, logK := sk70LogKCertificate, logChi := chi91LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (5726090581/5725896704) } }, logDArg := sk70LogDArgCertificate }

private noncomputable def leaf6461InnerLog : WideLogData :=
  innerPair377Data

set_option maxRecDepth 1000000 in
private theorem leaf6461LocalValidity :
    LeafFacts leaf6461Box leaf6461Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6461Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (2863142229/2862948352) }) = true
      norm_num [leaf6461Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6461CertificateValid :
    WideCertificateValid leaf6461Box leaf6461Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk70ValidityFacts chi91ValidityFacts
    leaf6461LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6461CoverageChecked :
    coverageCheck (innerAD leaf6461Box) leaf6461InnerLog = true := by
  rfl'

private theorem leaf6461InnerLogValid :
    leaf6461InnerLog.Valid 8 (innerAD leaf6461Box) :=
  wideLogDataValid_of_cachedCheck endpoint98PositiveFacts
    endpoint483PositiveFacts.valid leaf6461CoverageChecked

private noncomputable def leaf6461InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629649/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6461InputLogOnePlusV_eq :
    leaf6461InputLogOnePlusV = outerEnclosure 24
      (leaf6461Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6461RoundedFacts : LeafRoundedFacts 8
    leaf6461Certificate.logOnePlusV leaf6461InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6461InputLogOnePlusV_eq }

private noncomputable def leaf6461Inputs : Inputs :=
  inputsOfCaches globalInput sk70RoundedInputs
    chi91InputQChi innerPair377Input
    leaf6461InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6461LowerChecked :
    lowerCheck 24 leaf6461Box leaf6461Inputs = true := by
  rfl'

private theorem leaf6461CoversExact : CoversExact 8
    leaf6461Box leaf6461Certificate leaf6461InnerLog leaf6461Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk70RoundedFacts chi91RoundedFacts
    innerPair377RoundedFacts leaf6461RoundedFacts (by rfl)

private theorem leaf6461FlatSound : Sound leaf6461Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6461CertificateValid
    leaf6461InnerLogValid leaf6461CoversExact leaf6461LowerChecked

private noncomputable def leaf6462Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (13/16), chiHi := (27/32) }

private noncomputable def leaf6462Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554563/33554432) }, vSqrt := { lower := (32765/32768), upper := (8589426687/8588856320) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (98267151/67108864) }, upper := { exponent := 1, mantissa := (1565/1024) } }, logOuter := sk67LogOuterCertificate, logK := sk67LogKCertificate, logChi := chi90LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (17178283007/17177712640) } }, logDArg := sk67LogDArgCertificate }

private noncomputable def leaf6462InnerLog : WideLogData :=
  innerPair374Data

set_option maxRecDepth 1000000 in
private theorem leaf6462LocalValidity :
    LeafFacts leaf6462Box leaf6462Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6462Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8589426687/8588856320) }) = true
      norm_num [leaf6462Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6462CertificateValid :
    WideCertificateValid leaf6462Box leaf6462Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk67ValidityFacts chi90ValidityFacts
    leaf6462LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6462CoverageChecked :
    coverageCheck (innerAD leaf6462Box) leaf6462InnerLog = true := by
  rfl'

private theorem leaf6462InnerLogValid :
    leaf6462InnerLog.Valid 8 (innerAD leaf6462Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint482PositiveFacts.valid leaf6462CoverageChecked

private noncomputable def leaf6462InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814819/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6462InputLogOnePlusV_eq :
    leaf6462InputLogOnePlusV = outerEnclosure 24
      (leaf6462Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6462RoundedFacts : LeafRoundedFacts 8
    leaf6462Certificate.logOnePlusV leaf6462InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6462InputLogOnePlusV_eq }

private noncomputable def leaf6462Inputs : Inputs :=
  inputsOfCaches globalInput sk67RoundedInputs
    chi90InputQChi innerPair374Input
    leaf6462InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6462LowerChecked :
    lowerCheck 24 leaf6462Box leaf6462Inputs = true := by
  rfl'

private theorem leaf6462CoversExact : CoversExact 8
    leaf6462Box leaf6462Certificate leaf6462InnerLog leaf6462Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk67RoundedFacts chi90RoundedFacts
    innerPair374RoundedFacts leaf6462RoundedFacts (by rfl)

private theorem leaf6462FlatSound : Sound leaf6462Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6462CertificateValid
    leaf6462InnerLogValid leaf6462CoversExact leaf6462LowerChecked

private noncomputable def leaf6463Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (13/16), chiHi := (27/32) }

private noncomputable def leaf6463Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554565/33554432) }, vSqrt := { lower := (32765/32768), upper := (8589426687/8588828672) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (99970981/67108864) }, upper := { exponent := 1, mantissa := (199/128) } }, logOuter := sk68LogOuterCertificate, logK := sk68LogKCertificate, logChi := chi90LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (17178255359/17177657344) } }, logDArg := sk68LogDArgCertificate }

private noncomputable def leaf6463InnerLog : WideLogData :=
  innerPair377Data

set_option maxRecDepth 1000000 in
private theorem leaf6463LocalValidity :
    LeafFacts leaf6463Box leaf6463Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6463Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8589426687/8588828672) }) = true
      norm_num [leaf6463Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6463CertificateValid :
    WideCertificateValid leaf6463Box leaf6463Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk68ValidityFacts chi90ValidityFacts
    leaf6463LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6463CoverageChecked :
    coverageCheck (innerAD leaf6463Box) leaf6463InnerLog = true := by
  rfl'

private theorem leaf6463InnerLogValid :
    leaf6463InnerLog.Valid 8 (innerAD leaf6463Box) :=
  wideLogDataValid_of_cachedCheck endpoint98PositiveFacts
    endpoint483PositiveFacts.valid leaf6463CoverageChecked

private noncomputable def leaf6463InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629665/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6463InputLogOnePlusV_eq :
    leaf6463InputLogOnePlusV = outerEnclosure 24
      (leaf6463Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6463RoundedFacts : LeafRoundedFacts 8
    leaf6463Certificate.logOnePlusV leaf6463InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6463InputLogOnePlusV_eq }

private noncomputable def leaf6463Inputs : Inputs :=
  inputsOfCaches globalInput sk68RoundedInputs
    chi90InputQChi innerPair377Input
    leaf6463InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6463LowerChecked :
    lowerCheck 24 leaf6463Box leaf6463Inputs = true := by
  rfl'

private theorem leaf6463CoversExact : CoversExact 8
    leaf6463Box leaf6463Certificate leaf6463InnerLog leaf6463Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk68RoundedFacts chi90RoundedFacts
    innerPair377RoundedFacts leaf6463RoundedFacts (by rfl)

private theorem leaf6463FlatSound : Sound leaf6463Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6463CertificateValid
    leaf6463InnerLogValid leaf6463CoversExact leaf6463LowerChecked

private noncomputable def leaf6464Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (27/32), chiHi := (7/8) }

private noncomputable def leaf6464Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554565/33554432) }, vSqrt := { lower := (32765/32768), upper := (8589426687/8588816384) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (100757365/67108864) }, upper := { exponent := 1, mantissa := (401/256) } }, logOuter := sk67LogOuterCertificate, logK := sk67LogKCertificate, logChi := chi91LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (17178243071/17177632768) } }, logDArg := sk67LogDArgCertificate }

private noncomputable def leaf6464InnerLog : WideLogData :=
  innerPair383Data

set_option maxRecDepth 1000000 in
private theorem leaf6464LocalValidity :
    LeafFacts leaf6464Box leaf6464Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6464Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8589426687/8588816384) }) = true
      norm_num [leaf6464Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6464CertificateValid :
    WideCertificateValid leaf6464Box leaf6464Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk67ValidityFacts chi91ValidityFacts
    leaf6464LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6464CoverageChecked :
    coverageCheck (innerAD leaf6464Box) leaf6464InnerLog = true := by
  rfl'

private theorem leaf6464InnerLogValid :
    leaf6464InnerLog.Valid 8 (innerAD leaf6464Box) :=
  wideLogDataValid_of_cachedCheck endpoint99PositiveFacts
    endpoint484PositiveFacts.valid leaf6464CoverageChecked

private noncomputable def leaf6464InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629677/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6464InputLogOnePlusV_eq :
    leaf6464InputLogOnePlusV = outerEnclosure 24
      (leaf6464Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6464RoundedFacts : LeafRoundedFacts 8
    leaf6464Certificate.logOnePlusV leaf6464InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6464InputLogOnePlusV_eq }

private noncomputable def leaf6464Inputs : Inputs :=
  inputsOfCaches globalInput sk67RoundedInputs
    chi91InputQChi innerPair383Input
    leaf6464InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6464LowerChecked :
    lowerCheck 24 leaf6464Box leaf6464Inputs = true := by
  rfl'

private theorem leaf6464CoversExact : CoversExact 8
    leaf6464Box leaf6464Certificate leaf6464InnerLog leaf6464Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk67RoundedFacts chi91RoundedFacts
    innerPair383RoundedFacts leaf6464RoundedFacts (by rfl)

private theorem leaf6464FlatSound : Sound leaf6464Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6464CertificateValid
    leaf6464InnerLogValid leaf6464CoversExact leaf6464LowerChecked

private noncomputable def leaf6465Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (27/32), chiHi := (7/8) }

private noncomputable def leaf6465Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554567/33554432) }, vSqrt := { lower := (32765/32768), upper := (8589426687/8588787712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (102526727/67108864) }, upper := { exponent := 1, mantissa := (51/32) } }, logOuter := sk68LogOuterCertificate, logK := sk68LogKCertificate, logChi := chi91LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (17178214399/17177575424) } }, logDArg := sk68LogDArgCertificate }

private noncomputable def leaf6465InnerLog : WideLogData :=
  innerPair383Data

set_option maxRecDepth 1000000 in
private theorem leaf6465LocalValidity :
    LeafFacts leaf6465Box leaf6465Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6465Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8589426687/8588787712) }) = true
      norm_num [leaf6465Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6465CertificateValid :
    WideCertificateValid leaf6465Box leaf6465Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk68ValidityFacts chi91ValidityFacts
    leaf6465LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6465CoverageChecked :
    coverageCheck (innerAD leaf6465Box) leaf6465InnerLog = true := by
  rfl'

private theorem leaf6465InnerLogValid :
    leaf6465InnerLog.Valid 8 (innerAD leaf6465Box) :=
  wideLogDataValid_of_cachedCheck endpoint99PositiveFacts
    endpoint484PositiveFacts.valid leaf6465CoverageChecked

private noncomputable def leaf6465InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629705/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6465InputLogOnePlusV_eq :
    leaf6465InputLogOnePlusV = outerEnclosure 24
      (leaf6465Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6465RoundedFacts : LeafRoundedFacts 8
    leaf6465Certificate.logOnePlusV leaf6465InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6465InputLogOnePlusV_eq }

private noncomputable def leaf6465Inputs : Inputs :=
  inputsOfCaches globalInput sk68RoundedInputs
    chi91InputQChi innerPair383Input
    leaf6465InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6465LowerChecked :
    lowerCheck 24 leaf6465Box leaf6465Inputs = true := by
  rfl'

private theorem leaf6465CoversExact : CoversExact 8
    leaf6465Box leaf6465Certificate leaf6465InnerLog leaf6465Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk68RoundedFacts chi91RoundedFacts
    innerPair383RoundedFacts leaf6465RoundedFacts (by rfl)

private theorem leaf6465FlatSound : Sound leaf6465Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6465CertificateValid
    leaf6465InnerLogValid leaf6465CoversExact leaf6465LowerChecked

private noncomputable def leaf6466Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (7/8), chiHi := (29/32) }

private noncomputable def leaf6466Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554563/33554432) }, vSqrt := { lower := (65531/65536), upper := (2863142229/2862945280) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (99577791/67108864) }, upper := { exponent := 1, mantissa := (1585/1024) } }, logOuter := sk69LogOuterCertificate, logK := sk69LogKCertificate, logChi := chi92LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (5726087509/5725890560) } }, logDArg := sk69LogDArgCertificate }

private noncomputable def leaf6466InnerLog : WideLogData :=
  innerPair377Data

set_option maxRecDepth 1000000 in
private theorem leaf6466LocalValidity :
    LeafFacts leaf6466Box leaf6466Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6466Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (2863142229/2862945280) }) = true
      norm_num [leaf6466Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6466CertificateValid :
    WideCertificateValid leaf6466Box leaf6466Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk69ValidityFacts chi92ValidityFacts
    leaf6466LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6466CoverageChecked :
    coverageCheck (innerAD leaf6466Box) leaf6466InnerLog = true := by
  rfl'

private theorem leaf6466InnerLogValid :
    leaf6466InnerLog.Valid 8 (innerAD leaf6466Box) :=
  wideLogDataValid_of_cachedCheck endpoint98PositiveFacts
    endpoint483PositiveFacts.valid leaf6466CoverageChecked

private noncomputable def leaf6466InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814829/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6466InputLogOnePlusV_eq :
    leaf6466InputLogOnePlusV = outerEnclosure 24
      (leaf6466Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6466RoundedFacts : LeafRoundedFacts 8
    leaf6466Certificate.logOnePlusV leaf6466InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6466InputLogOnePlusV_eq }

private noncomputable def leaf6466Inputs : Inputs :=
  inputsOfCaches globalInput sk69RoundedInputs
    chi92InputQChi innerPair377Input
    leaf6466InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6466LowerChecked :
    lowerCheck 24 leaf6466Box leaf6466Inputs = true := by
  rfl'

private theorem leaf6466CoversExact : CoversExact 8
    leaf6466Box leaf6466Certificate leaf6466InnerLog leaf6466Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk69RoundedFacts chi92RoundedFacts
    innerPair377RoundedFacts leaf6466RoundedFacts (by rfl)

private theorem leaf6466FlatSound : Sound leaf6466Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6466CertificateValid
    leaf6466InnerLogValid leaf6466CoversExact leaf6466LowerChecked

private noncomputable def leaf6467Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (7/8), chiHi := (29/32) }

private noncomputable def leaf6467Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554565/33554432) }, vSqrt := { lower := (65531/65536), upper := (8589426687/8588806144) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (101412685/67108864) }, upper := { exponent := 1, mantissa := (807/512) } }, logOuter := sk70LogOuterCertificate, logK := sk70LogKCertificate, logChi := chi92LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (17178232831/17177612288) } }, logDArg := sk70LogDArgCertificate }

private noncomputable def leaf6467InnerLog : WideLogData :=
  innerPair383Data

set_option maxRecDepth 1000000 in
private theorem leaf6467LocalValidity :
    LeafFacts leaf6467Box leaf6467Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6467Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (8589426687/8588806144) }) = true
      norm_num [leaf6467Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6467CertificateValid :
    WideCertificateValid leaf6467Box leaf6467Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk70ValidityFacts chi92ValidityFacts
    leaf6467LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6467CoverageChecked :
    coverageCheck (innerAD leaf6467Box) leaf6467InnerLog = true := by
  rfl'

private theorem leaf6467InnerLogValid :
    leaf6467InnerLog.Valid 8 (innerAD leaf6467Box) :=
  wideLogDataValid_of_cachedCheck endpoint99PositiveFacts
    endpoint484PositiveFacts.valid leaf6467CoverageChecked

private noncomputable def leaf6467InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629687/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6467InputLogOnePlusV_eq :
    leaf6467InputLogOnePlusV = outerEnclosure 24
      (leaf6467Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6467RoundedFacts : LeafRoundedFacts 8
    leaf6467Certificate.logOnePlusV leaf6467InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6467InputLogOnePlusV_eq }

private noncomputable def leaf6467Inputs : Inputs :=
  inputsOfCaches globalInput sk70RoundedInputs
    chi92InputQChi innerPair383Input
    leaf6467InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6467LowerChecked :
    lowerCheck 24 leaf6467Box leaf6467Inputs = true := by
  rfl'

private theorem leaf6467CoversExact : CoversExact 8
    leaf6467Box leaf6467Certificate leaf6467InnerLog leaf6467Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk70RoundedFacts chi92RoundedFacts
    innerPair383RoundedFacts leaf6467RoundedFacts (by rfl)

private theorem leaf6467FlatSound : Sound leaf6467Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6467CertificateValid
    leaf6467InnerLogValid leaf6467CoversExact leaf6467LowerChecked

private noncomputable def leaf6468Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (29/32), chiHi := (15/16) }

private noncomputable def leaf6468Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554565/33554432) }, vSqrt := { lower := (65531/65536), upper := (8589426687/8588797952) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (101936941/67108864) }, upper := { exponent := 1, mantissa := (811/512) } }, logOuter := sk69LogOuterCertificate, logK := sk69LogKCertificate, logChi := chi93LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (17178224639/17177595904) } }, logDArg := sk69LogDArgCertificate }

private noncomputable def leaf6468InnerLog : WideLogData :=
  innerPair383Data

set_option maxRecDepth 1000000 in
private theorem leaf6468LocalValidity :
    LeafFacts leaf6468Box leaf6468Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6468Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (8589426687/8588797952) }) = true
      norm_num [leaf6468Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6468CertificateValid :
    WideCertificateValid leaf6468Box leaf6468Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk69ValidityFacts chi93ValidityFacts
    leaf6468LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6468CoverageChecked :
    coverageCheck (innerAD leaf6468Box) leaf6468InnerLog = true := by
  rfl'

private theorem leaf6468InnerLogValid :
    leaf6468InnerLog.Valid 8 (innerAD leaf6468Box) :=
  wideLogDataValid_of_cachedCheck endpoint99PositiveFacts
    endpoint484PositiveFacts.valid leaf6468CoverageChecked

private noncomputable def leaf6468InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629695/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6468InputLogOnePlusV_eq :
    leaf6468InputLogOnePlusV = outerEnclosure 24
      (leaf6468Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6468RoundedFacts : LeafRoundedFacts 8
    leaf6468Certificate.logOnePlusV leaf6468InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6468InputLogOnePlusV_eq }

private noncomputable def leaf6468Inputs : Inputs :=
  inputsOfCaches globalInput sk69RoundedInputs
    chi93InputQChi innerPair383Input
    leaf6468InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6468LowerChecked :
    lowerCheck 24 leaf6468Box leaf6468Inputs = true := by
  rfl'

private theorem leaf6468CoversExact : CoversExact 8
    leaf6468Box leaf6468Certificate leaf6468InnerLog leaf6468Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk69RoundedFacts chi93RoundedFacts
    innerPair383RoundedFacts leaf6468RoundedFacts (by rfl)

private theorem leaf6468FlatSound : Sound leaf6468Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6468CertificateValid
    leaf6468InnerLogValid leaf6468CoversExact leaf6468LowerChecked

private noncomputable def leaf6469Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (29/32), chiHi := (15/16) }

private noncomputable def leaf6469Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554567/33554432) }, vSqrt := { lower := (65531/65536), upper := (8589426687/8588767232) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (103837367/67108864) }, upper := { exponent := 1, mantissa := (413/256) } }, logOuter := sk70LogOuterCertificate, logK := sk70LogKCertificate, logChi := chi93LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (17178193919/17177534464) } }, logDArg := sk70LogDArgCertificate }

private noncomputable def leaf6469InnerLog : WideLogData :=
  innerPair745Data

set_option maxRecDepth 1000000 in
private theorem leaf6469LocalValidity :
    LeafFacts leaf6469Box leaf6469Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6469Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (8589426687/8588767232) }) = true
      norm_num [leaf6469Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6469CertificateValid :
    WideCertificateValid leaf6469Box leaf6469Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk70ValidityFacts chi93ValidityFacts
    leaf6469LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6469CoverageChecked :
    coverageCheck (innerAD leaf6469Box) leaf6469InnerLog = true := by
  rfl'

private theorem leaf6469InnerLogValid :
    leaf6469InnerLog.Valid 8 (innerAD leaf6469Box) :=
  wideLogDataValid_of_cachedCheck endpoint482PositiveFacts
    endpoint485PositiveFacts.valid leaf6469CoverageChecked

private noncomputable def leaf6469InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629725/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6469InputLogOnePlusV_eq :
    leaf6469InputLogOnePlusV = outerEnclosure 24
      (leaf6469Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6469RoundedFacts : LeafRoundedFacts 8
    leaf6469Certificate.logOnePlusV leaf6469InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6469InputLogOnePlusV_eq }

private noncomputable def leaf6469Inputs : Inputs :=
  inputsOfCaches globalInput sk70RoundedInputs
    chi93InputQChi innerPair745Input
    leaf6469InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6469LowerChecked :
    lowerCheck 24 leaf6469Box leaf6469Inputs = true := by
  rfl'

private theorem leaf6469CoversExact : CoversExact 8
    leaf6469Box leaf6469Certificate leaf6469InnerLog leaf6469Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk70RoundedFacts chi93RoundedFacts
    innerPair745RoundedFacts leaf6469RoundedFacts (by rfl)

private theorem leaf6469FlatSound : Sound leaf6469Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6469CertificateValid
    leaf6469InnerLogValid leaf6469CoversExact leaf6469LowerChecked

private noncomputable def leaf6470Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (7/8), chiHi := (29/32) }

private noncomputable def leaf6470Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554567/33554432) }, vSqrt := { lower := (32765/32768), upper := (8589426687/8588776448) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (103247579/67108864) }, upper := { exponent := 1, mantissa := (1643/1024) } }, logOuter := sk67LogOuterCertificate, logK := sk67LogKCertificate, logChi := chi92LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (17178203135/17177552896) } }, logDArg := sk67LogDArgCertificate }

private noncomputable def leaf6470InnerLog : WideLogData :=
  innerPair745Data

set_option maxRecDepth 1000000 in
private theorem leaf6470LocalValidity :
    LeafFacts leaf6470Box leaf6470Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6470Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8589426687/8588776448) }) = true
      norm_num [leaf6470Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6470CertificateValid :
    WideCertificateValid leaf6470Box leaf6470Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk67ValidityFacts chi92ValidityFacts
    leaf6470LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6470CoverageChecked :
    coverageCheck (innerAD leaf6470Box) leaf6470InnerLog = true := by
  rfl'

private theorem leaf6470InnerLogValid :
    leaf6470InnerLog.Valid 8 (innerAD leaf6470Box) :=
  wideLogDataValid_of_cachedCheck endpoint482PositiveFacts
    endpoint485PositiveFacts.valid leaf6470CoverageChecked

private noncomputable def leaf6470InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907429/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6470InputLogOnePlusV_eq :
    leaf6470InputLogOnePlusV = outerEnclosure 24
      (leaf6470Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6470RoundedFacts : LeafRoundedFacts 8
    leaf6470Certificate.logOnePlusV leaf6470InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6470InputLogOnePlusV_eq }

private noncomputable def leaf6470Inputs : Inputs :=
  inputsOfCaches globalInput sk67RoundedInputs
    chi92InputQChi innerPair745Input
    leaf6470InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6470LowerChecked :
    lowerCheck 24 leaf6470Box leaf6470Inputs = true := by
  rfl'

private theorem leaf6470CoversExact : CoversExact 8
    leaf6470Box leaf6470Certificate leaf6470InnerLog leaf6470Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk67RoundedFacts chi92RoundedFacts
    innerPair745RoundedFacts leaf6470RoundedFacts (by rfl)

private theorem leaf6470FlatSound : Sound leaf6470Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6470CertificateValid
    leaf6470InnerLogValid leaf6470CoversExact leaf6470LowerChecked

private noncomputable def leaf6471Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (7/8), chiHi := (29/32) }

private noncomputable def leaf6471Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554569/33554432) }, vSqrt := { lower := (32765/32768), upper := (2863142229/2862915584) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (105082473/67108864) }, upper := { exponent := 1, mantissa := (209/128) } }, logOuter := sk68LogOuterCertificate, logK := sk68LogKCertificate, logChi := chi92LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (5726057813/5725831168) } }, logDArg := sk68LogDArgCertificate }

private noncomputable def leaf6471InnerLog : WideLogData :=
  innerPair750Data

set_option maxRecDepth 1000000 in
private theorem leaf6471LocalValidity :
    LeafFacts leaf6471Box leaf6471Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6471Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (2863142229/2862915584) }) = true
      norm_num [leaf6471Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6471CertificateValid :
    WideCertificateValid leaf6471Box leaf6471Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk68ValidityFacts chi92ValidityFacts
    leaf6471LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6471CoverageChecked :
    coverageCheck (innerAD leaf6471Box) leaf6471InnerLog = true := by
  rfl'

private theorem leaf6471InnerLogValid :
    leaf6471InnerLog.Valid 8 (innerAD leaf6471Box) :=
  wideLogDataValid_of_cachedCheck endpoint483PositiveFacts
    endpoint486PositiveFacts.valid leaf6471CoverageChecked

private noncomputable def leaf6471InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629745/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6471InputLogOnePlusV_eq :
    leaf6471InputLogOnePlusV = outerEnclosure 24
      (leaf6471Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6471RoundedFacts : LeafRoundedFacts 8
    leaf6471Certificate.logOnePlusV leaf6471InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6471InputLogOnePlusV_eq }

private noncomputable def leaf6471Inputs : Inputs :=
  inputsOfCaches globalInput sk68RoundedInputs
    chi92InputQChi innerPair750Input
    leaf6471InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6471LowerChecked :
    lowerCheck 24 leaf6471Box leaf6471Inputs = true := by
  rfl'

private theorem leaf6471CoversExact : CoversExact 8
    leaf6471Box leaf6471Certificate leaf6471InnerLog leaf6471Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk68RoundedFacts chi92RoundedFacts
    innerPair750RoundedFacts leaf6471RoundedFacts (by rfl)

private theorem leaf6471FlatSound : Sound leaf6471Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6471CertificateValid
    leaf6471InnerLogValid leaf6471CoversExact leaf6471LowerChecked

private noncomputable def leaf6472Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (29/32), chiHi := (15/16) }

private noncomputable def leaf6472Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554569/33554432) }, vSqrt := { lower := (32765/32768), upper := (8589426687/8588736512) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (105737793/67108864) }, upper := { exponent := 1, mantissa := (841/512) } }, logOuter := sk67LogOuterCertificate, logK := sk67LogKCertificate, logChi := chi93LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (17178163199/17177473024) } }, logDArg := sk67LogDArgCertificate }

private noncomputable def leaf6472InnerLog : WideLogData :=
  innerPair750Data

set_option maxRecDepth 1000000 in
private theorem leaf6472LocalValidity :
    LeafFacts leaf6472Box leaf6472Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6472Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8589426687/8588736512) }) = true
      norm_num [leaf6472Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6472CertificateValid :
    WideCertificateValid leaf6472Box leaf6472Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk67ValidityFacts chi93ValidityFacts
    leaf6472LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6472CoverageChecked :
    coverageCheck (innerAD leaf6472Box) leaf6472InnerLog = true := by
  rfl'

private theorem leaf6472InnerLogValid :
    leaf6472InnerLog.Valid 8 (innerAD leaf6472Box) :=
  wideLogDataValid_of_cachedCheck endpoint483PositiveFacts
    endpoint486PositiveFacts.valid leaf6472CoverageChecked

private noncomputable def leaf6472InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629755/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6472InputLogOnePlusV_eq :
    leaf6472InputLogOnePlusV = outerEnclosure 24
      (leaf6472Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6472RoundedFacts : LeafRoundedFacts 8
    leaf6472Certificate.logOnePlusV leaf6472InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6472InputLogOnePlusV_eq }

private noncomputable def leaf6472Inputs : Inputs :=
  inputsOfCaches globalInput sk67RoundedInputs
    chi93InputQChi innerPair750Input
    leaf6472InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6472LowerChecked :
    lowerCheck 24 leaf6472Box leaf6472Inputs = true := by
  rfl'

private theorem leaf6472CoversExact : CoversExact 8
    leaf6472Box leaf6472Certificate leaf6472InnerLog leaf6472Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk67RoundedFacts chi93RoundedFacts
    innerPair750RoundedFacts leaf6472RoundedFacts (by rfl)

private theorem leaf6472FlatSound : Sound leaf6472Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6472CertificateValid
    leaf6472InnerLogValid leaf6472CoversExact leaf6472LowerChecked

private noncomputable def leaf6473Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (29/32), chiHi := (15/16) }

private noncomputable def leaf6473Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554571/33554432) }, vSqrt := { lower := (32765/32768), upper := (199754109/199737344) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (107638219/67108864) }, upper := { exponent := 1, mantissa := (107/64) } }, logOuter := sk68LogOuterCertificate, logK := sk68LogKCertificate, logChi := chi93LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (399491453/399474688) } }, logDArg := sk68LogDArgCertificate }

private noncomputable def leaf6473InnerLog : WideLogData :=
  innerPair756Data

set_option maxRecDepth 1000000 in
private theorem leaf6473LocalValidity :
    LeafFacts leaf6473Box leaf6473Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6473Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (199754109/199737344) }) = true
      norm_num [leaf6473Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6473CertificateValid :
    WideCertificateValid leaf6473Box leaf6473Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk68ValidityFacts chi93ValidityFacts
    leaf6473LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6473CoverageChecked :
    coverageCheck (innerAD leaf6473Box) leaf6473InnerLog = true := by
  rfl'

private theorem leaf6473InnerLogValid :
    leaf6473InnerLog.Valid 8 (innerAD leaf6473Box) :=
  wideLogDataValid_of_cachedCheck endpoint484PositiveFacts
    endpoint487PositiveFacts.valid leaf6473CoverageChecked

private noncomputable def leaf6473InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629785/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6473InputLogOnePlusV_eq :
    leaf6473InputLogOnePlusV = outerEnclosure 24
      (leaf6473Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6473RoundedFacts : LeafRoundedFacts 8
    leaf6473Certificate.logOnePlusV leaf6473InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6473InputLogOnePlusV_eq }

private noncomputable def leaf6473Inputs : Inputs :=
  inputsOfCaches globalInput sk68RoundedInputs
    chi93InputQChi innerPair756Input
    leaf6473InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6473LowerChecked :
    lowerCheck 24 leaf6473Box leaf6473Inputs = true := by
  rfl'

private theorem leaf6473CoversExact : CoversExact 8
    leaf6473Box leaf6473Certificate leaf6473InnerLog leaf6473Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk68RoundedFacts chi93RoundedFacts
    innerPair756RoundedFacts leaf6473RoundedFacts (by rfl)

private theorem leaf6473FlatSound : Sound leaf6473Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6473CertificateValid
    leaf6473InnerLogValid leaf6473CoversExact leaf6473LowerChecked

private noncomputable def leaf6474Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (15/16), chiHi := (31/32) }

private noncomputable def leaf6474Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554567/33554432) }, vSqrt := { lower := (65531/65536), upper := (67633281/67628032) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (104296091/67108864) }, upper := { exponent := 1, mantissa := (1659/1024) } }, logOuter := sk69LogOuterCertificate, logK := sk69LogKCertificate, logChi := chi94LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (135261313/135256064) } }, logDArg := sk69LogDArgCertificate }

private noncomputable def leaf6474InnerLog : WideLogData :=
  innerPair745Data

set_option maxRecDepth 1000000 in
private theorem leaf6474LocalValidity :
    LeafFacts leaf6474Box leaf6474Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6474Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (67633281/67628032) }) = true
      norm_num [leaf6474Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6474CertificateValid :
    WideCertificateValid leaf6474Box leaf6474Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk69ValidityFacts chi94ValidityFacts
    leaf6474LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6474CoverageChecked :
    coverageCheck (innerAD leaf6474Box) leaf6474InnerLog = true := by
  rfl'

private theorem leaf6474InnerLogValid :
    leaf6474InnerLog.Valid 8 (innerAD leaf6474Box) :=
  wideLogDataValid_of_cachedCheck endpoint482PositiveFacts
    endpoint485PositiveFacts.valid leaf6474CoverageChecked

private noncomputable def leaf6474InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (2907433/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6474InputLogOnePlusV_eq :
    leaf6474InputLogOnePlusV = outerEnclosure 24
      (leaf6474Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6474RoundedFacts : LeafRoundedFacts 8
    leaf6474Certificate.logOnePlusV leaf6474InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6474InputLogOnePlusV_eq }

private noncomputable def leaf6474Inputs : Inputs :=
  inputsOfCaches globalInput sk69RoundedInputs
    chi94InputQChi innerPair745Input
    leaf6474InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6474LowerChecked :
    lowerCheck 24 leaf6474Box leaf6474Inputs = true := by
  rfl'

private theorem leaf6474CoversExact : CoversExact 8
    leaf6474Box leaf6474Certificate leaf6474InnerLog leaf6474Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk69RoundedFacts chi94RoundedFacts
    innerPair745RoundedFacts leaf6474RoundedFacts (by rfl)

private theorem leaf6474FlatSound : Sound leaf6474Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6474CertificateValid
    leaf6474InnerLogValid leaf6474CoversExact leaf6474LowerChecked

private noncomputable def leaf6475Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (15/16), chiHi := (31/32) }

private noncomputable def leaf6475Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554569/33554432) }, vSqrt := { lower := (65531/65536), upper := (2863142229/2862909440) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (106262049/67108864) }, upper := { exponent := 1, mantissa := (845/512) } }, logOuter := sk70LogOuterCertificate, logK := sk70LogKCertificate, logChi := chi94LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (5726051669/5725818880) } }, logDArg := sk70LogDArgCertificate }

private noncomputable def leaf6475InnerLog : WideLogData :=
  innerPair750Data

set_option maxRecDepth 1000000 in
private theorem leaf6475LocalValidity :
    LeafFacts leaf6475Box leaf6475Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6475Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (2863142229/2862909440) }) = true
      norm_num [leaf6475Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6475CertificateValid :
    WideCertificateValid leaf6475Box leaf6475Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk70ValidityFacts chi94ValidityFacts
    leaf6475LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6475CoverageChecked :
    coverageCheck (innerAD leaf6475Box) leaf6475InnerLog = true := by
  rfl'

private theorem leaf6475InnerLogValid :
    leaf6475InnerLog.Valid 8 (innerAD leaf6475Box) :=
  wideLogDataValid_of_cachedCheck endpoint483PositiveFacts
    endpoint486PositiveFacts.valid leaf6475CoverageChecked

private noncomputable def leaf6475InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629763/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6475InputLogOnePlusV_eq :
    leaf6475InputLogOnePlusV = outerEnclosure 24
      (leaf6475Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6475RoundedFacts : LeafRoundedFacts 8
    leaf6475Certificate.logOnePlusV leaf6475InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6475InputLogOnePlusV_eq }

private noncomputable def leaf6475Inputs : Inputs :=
  inputsOfCaches globalInput sk70RoundedInputs
    chi94InputQChi innerPair750Input
    leaf6475InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6475LowerChecked :
    lowerCheck 24 leaf6475Box leaf6475Inputs = true := by
  rfl'

private theorem leaf6475CoversExact : CoversExact 8
    leaf6475Box leaf6475Certificate leaf6475InnerLog leaf6475Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk70RoundedFacts chi94RoundedFacts
    innerPair750RoundedFacts leaf6475RoundedFacts (by rfl)

private theorem leaf6475FlatSound : Sound leaf6475Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6475CertificateValid
    leaf6475InnerLogValid leaf6475CoversExact leaf6475LowerChecked

private noncomputable def leaf6476Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (31/32), chiHi := (1) }

private noncomputable def leaf6476Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554569/33554432) }, vSqrt := { lower := (65531/65536), upper := (954380743/954302464) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (106655241/67108864) }, upper := { exponent := 1, mantissa := (53/32) } }, logOuter := sk69LogOuterCertificate, logK := sk69LogKCertificate, logChi := chi95LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (1908683207/1908604928) } }, logDArg := sk69LogDArgCertificate }

private noncomputable def leaf6476InnerLog : WideLogData :=
  innerPair750Data

set_option maxRecDepth 1000000 in
private theorem leaf6476LocalValidity :
    LeafFacts leaf6476Box leaf6476Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6476Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (954380743/954302464) }) = true
      norm_num [leaf6476Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6476CertificateValid :
    WideCertificateValid leaf6476Box leaf6476Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk69ValidityFacts chi95ValidityFacts
    leaf6476LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6476CoverageChecked :
    coverageCheck (innerAD leaf6476Box) leaf6476InnerLog = true := by
  rfl'

private theorem leaf6476InnerLogValid :
    leaf6476InnerLog.Valid 8 (innerAD leaf6476Box) :=
  wideLogDataValid_of_cachedCheck endpoint483PositiveFacts
    endpoint486PositiveFacts.valid leaf6476CoverageChecked

private noncomputable def leaf6476InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629769/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6476InputLogOnePlusV_eq :
    leaf6476InputLogOnePlusV = outerEnclosure 24
      (leaf6476Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6476RoundedFacts : LeafRoundedFacts 8
    leaf6476Certificate.logOnePlusV leaf6476InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6476InputLogOnePlusV_eq }

private noncomputable def leaf6476Inputs : Inputs :=
  inputsOfCaches globalInput sk69RoundedInputs
    chi95InputQChi innerPair750Input
    leaf6476InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6476LowerChecked :
    lowerCheck 24 leaf6476Box leaf6476Inputs = true := by
  rfl'

private theorem leaf6476CoversExact : CoversExact 8
    leaf6476Box leaf6476Certificate leaf6476InnerLog leaf6476Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk69RoundedFacts chi95RoundedFacts
    innerPair750RoundedFacts leaf6476RoundedFacts (by rfl)

private theorem leaf6476FlatSound : Sound leaf6476Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6476CertificateValid
    leaf6476InnerLogValid leaf6476CoversExact leaf6476LowerChecked

private noncomputable def leaf6477Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (31/32), chiHi := (1) }

private noncomputable def leaf6477Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554571/33554432) }, vSqrt := { lower := (65531/65536), upper := (8589426687/8588689408) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (108686731/67108864) }, upper := { exponent := 1, mantissa := (27/16) } }, logOuter := sk70LogOuterCertificate, logK := sk70LogKCertificate, logChi := chi95LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (17178116095/17177378816) } }, logDArg := sk70LogDArgCertificate }

private noncomputable def leaf6477InnerLog : WideLogData :=
  innerPair756Data

set_option maxRecDepth 1000000 in
private theorem leaf6477LocalValidity :
    LeafFacts leaf6477Box leaf6477Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6477Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (8589426687/8588689408) }) = true
      norm_num [leaf6477Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6477CertificateValid :
    WideCertificateValid leaf6477Box leaf6477Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk70ValidityFacts chi95ValidityFacts
    leaf6477LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6477CoverageChecked :
    coverageCheck (innerAD leaf6477Box) leaf6477InnerLog = true := by
  rfl'

private theorem leaf6477InnerLogValid :
    leaf6477InnerLog.Valid 8 (innerAD leaf6477Box) :=
  wideLogDataValid_of_cachedCheck endpoint484PositiveFacts
    endpoint487PositiveFacts.valid leaf6477CoverageChecked

private noncomputable def leaf6477InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629801/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6477InputLogOnePlusV_eq :
    leaf6477InputLogOnePlusV = outerEnclosure 24
      (leaf6477Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6477RoundedFacts : LeafRoundedFacts 8
    leaf6477Certificate.logOnePlusV leaf6477InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6477InputLogOnePlusV_eq }

private noncomputable def leaf6477Inputs : Inputs :=
  inputsOfCaches globalInput sk70RoundedInputs
    chi95InputQChi innerPair756Input
    leaf6477InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6477LowerChecked :
    lowerCheck 24 leaf6477Box leaf6477Inputs = true := by
  rfl'

private theorem leaf6477CoversExact : CoversExact 8
    leaf6477Box leaf6477Certificate leaf6477InnerLog leaf6477Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk70RoundedFacts chi95RoundedFacts
    innerPair756RoundedFacts leaf6477RoundedFacts (by rfl)

private theorem leaf6477FlatSound : Sound leaf6477Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6477CertificateValid
    leaf6477InnerLogValid leaf6477CoversExact leaf6477LowerChecked

private noncomputable def leaf6478Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (15/16), chiHi := (31/32) }

private noncomputable def leaf6478Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554571/33554432) }, vSqrt := { lower := (32765/32768), upper := (8589426687/8588696576) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (108228007/67108864) }, upper := { exponent := 1, mantissa := (1721/1024) } }, logOuter := sk67LogOuterCertificate, logK := sk67LogKCertificate, logChi := chi94LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (17178123263/17177393152) } }, logDArg := sk67LogDArgCertificate }

private noncomputable def leaf6478InnerLog : WideLogData :=
  innerPair756Data

set_option maxRecDepth 1000000 in
private theorem leaf6478LocalValidity :
    LeafFacts leaf6478Box leaf6478Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6478Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8589426687/8588696576) }) = true
      norm_num [leaf6478Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6478CertificateValid :
    WideCertificateValid leaf6478Box leaf6478Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk67ValidityFacts chi94ValidityFacts
    leaf6478LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6478CoverageChecked :
    coverageCheck (innerAD leaf6478Box) leaf6478InnerLog = true := by
  rfl'

private theorem leaf6478InnerLogValid :
    leaf6478InnerLog.Valid 8 (innerAD leaf6478Box) :=
  wideLogDataValid_of_cachedCheck endpoint484PositiveFacts
    endpoint487PositiveFacts.valid leaf6478CoverageChecked

private noncomputable def leaf6478InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814897/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6478InputLogOnePlusV_eq :
    leaf6478InputLogOnePlusV = outerEnclosure 24
      (leaf6478Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6478RoundedFacts : LeafRoundedFacts 8
    leaf6478Certificate.logOnePlusV leaf6478InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6478InputLogOnePlusV_eq }

private noncomputable def leaf6478Inputs : Inputs :=
  inputsOfCaches globalInput sk67RoundedInputs
    chi94InputQChi innerPair756Input
    leaf6478InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6478LowerChecked :
    lowerCheck 24 leaf6478Box leaf6478Inputs = true := by
  rfl'

private theorem leaf6478CoversExact : CoversExact 8
    leaf6478Box leaf6478Certificate leaf6478InnerLog leaf6478Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk67RoundedFacts chi94RoundedFacts
    innerPair756RoundedFacts leaf6478RoundedFacts (by rfl)

private theorem leaf6478FlatSound : Sound leaf6478Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6478CertificateValid
    leaf6478InnerLogValid leaf6478CoversExact leaf6478LowerChecked

private noncomputable def leaf6479Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (15/16), chiHi := (31/32) }

private noncomputable def leaf6479Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554573/33554432) }, vSqrt := { lower := (32765/32768), upper := (8589426687/8588664832) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (110193965/67108864) }, upper := { exponent := 1, mantissa := (219/128) } }, logOuter := sk68LogOuterCertificate, logK := sk68LogKCertificate, logChi := chi94LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (17178091519/17177329664) } }, logDArg := sk68LogDArgCertificate }

private noncomputable def leaf6479InnerLog : WideLogData :=
  innerPair762Data

set_option maxRecDepth 1000000 in
private theorem leaf6479LocalValidity :
    LeafFacts leaf6479Box leaf6479Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6479Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8589426687/8588664832) }) = true
      norm_num [leaf6479Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6479CertificateValid :
    WideCertificateValid leaf6479Box leaf6479Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk68ValidityFacts chi94ValidityFacts
    leaf6479LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6479CoverageChecked :
    coverageCheck (innerAD leaf6479Box) leaf6479InnerLog = true := by
  rfl'

private theorem leaf6479InnerLogValid :
    leaf6479InnerLog.Valid 8 (innerAD leaf6479Box) :=
  wideLogDataValid_of_cachedCheck endpoint485PositiveFacts
    endpoint488PositiveFacts.valid leaf6479CoverageChecked

private noncomputable def leaf6479InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629825/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6479InputLogOnePlusV_eq :
    leaf6479InputLogOnePlusV = outerEnclosure 24
      (leaf6479Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6479RoundedFacts : LeafRoundedFacts 8
    leaf6479Certificate.logOnePlusV leaf6479InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6479InputLogOnePlusV_eq }

private noncomputable def leaf6479Inputs : Inputs :=
  inputsOfCaches globalInput sk68RoundedInputs
    chi94InputQChi innerPair762Input
    leaf6479InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6479LowerChecked :
    lowerCheck 24 leaf6479Box leaf6479Inputs = true := by
  rfl'

private theorem leaf6479CoversExact : CoversExact 8
    leaf6479Box leaf6479Certificate leaf6479InnerLog leaf6479Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk68RoundedFacts chi94RoundedFacts
    innerPair762RoundedFacts leaf6479RoundedFacts (by rfl)

private theorem leaf6479FlatSound : Sound leaf6479Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6479CertificateValid
    leaf6479InnerLogValid leaf6479CoversExact leaf6479LowerChecked

private noncomputable def leaf6480Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (31/32), chiHi := (1) }

private noncomputable def leaf6480Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554573/33554432) }, vSqrt := { lower := (32765/32768), upper := (8589426687/8588656640) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (110718221/67108864) }, upper := { exponent := 1, mantissa := (55/32) } }, logOuter := sk67LogOuterCertificate, logK := sk67LogKCertificate, logChi := chi95LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (17178083327/17177313280) } }, logDArg := sk67LogDArgCertificate }

private noncomputable def leaf6480InnerLog : WideLogData :=
  innerPair762Data

set_option maxRecDepth 1000000 in
private theorem leaf6480LocalValidity :
    LeafFacts leaf6480Box leaf6480Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6480Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8589426687/8588656640) }) = true
      norm_num [leaf6480Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6480CertificateValid :
    WideCertificateValid leaf6480Box leaf6480Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk67ValidityFacts chi95ValidityFacts
    leaf6480LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6480CoverageChecked :
    coverageCheck (innerAD leaf6480Box) leaf6480InnerLog = true := by
  rfl'

private theorem leaf6480InnerLogValid :
    leaf6480InnerLog.Valid 8 (innerAD leaf6480Box) :=
  wideLogDataValid_of_cachedCheck endpoint485PositiveFacts
    endpoint488PositiveFacts.valid leaf6480CoverageChecked

private noncomputable def leaf6480InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629833/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6480InputLogOnePlusV_eq :
    leaf6480InputLogOnePlusV = outerEnclosure 24
      (leaf6480Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6480RoundedFacts : LeafRoundedFacts 8
    leaf6480Certificate.logOnePlusV leaf6480InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6480InputLogOnePlusV_eq }

private noncomputable def leaf6480Inputs : Inputs :=
  inputsOfCaches globalInput sk67RoundedInputs
    chi95InputQChi innerPair762Input
    leaf6480InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6480LowerChecked :
    lowerCheck 24 leaf6480Box leaf6480Inputs = true := by
  rfl'

private theorem leaf6480CoversExact : CoversExact 8
    leaf6480Box leaf6480Certificate leaf6480InnerLog leaf6480Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk67RoundedFacts chi95RoundedFacts
    innerPair762RoundedFacts leaf6480RoundedFacts (by rfl)

private theorem leaf6480FlatSound : Sound leaf6480Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6480CertificateValid
    leaf6480InnerLogValid leaf6480CoversExact leaf6480LowerChecked

private noncomputable def leaf6481Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (31/32), chiHi := (1) }

private noncomputable def leaf6481Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (33554575/33554432) }, vSqrt := { lower := (32765/32768), upper := (11452394153/11451498496) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (112749711/67108864) }, upper := { exponent := 1, mantissa := (7/4) } }, logOuter := sk68LogOuterCertificate, logK := sk68LogKCertificate, logChi := chi95LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (22903892649/22902996992) } }, logDArg := sk68LogDArgCertificate }

private noncomputable def leaf6481InnerLog : WideLogData :=
  innerPair766Data

set_option maxRecDepth 1000000 in
private theorem leaf6481LocalValidity :
    LeafFacts leaf6481Box leaf6481Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6481Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (11452394153/11451498496) }) = true
      norm_num [leaf6481Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6481CertificateValid :
    WideCertificateValid leaf6481Box leaf6481Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk68ValidityFacts chi95ValidityFacts
    leaf6481LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6481CoverageChecked :
    coverageCheck (innerAD leaf6481Box) leaf6481InnerLog = true := by
  rfl'

private theorem leaf6481InnerLogValid :
    leaf6481InnerLog.Valid 8 (innerAD leaf6481Box) :=
  wideLogDataValid_of_cachedCheck endpoint486PositiveFacts
    endpoint489PositiveFacts.valid leaf6481CoverageChecked

private noncomputable def leaf6481InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629737/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6481InputLogOnePlusV_eq :
    leaf6481InputLogOnePlusV = outerEnclosure 24
      (leaf6481Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6481RoundedFacts : LeafRoundedFacts 8
    leaf6481Certificate.logOnePlusV leaf6481InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6481InputLogOnePlusV_eq }

private noncomputable def leaf6481Inputs : Inputs :=
  inputsOfCaches globalInput sk68RoundedInputs
    chi95InputQChi innerPair766Input
    leaf6481InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6481LowerChecked :
    lowerCheck 24 leaf6481Box leaf6481Inputs = true := by
  rfl'

private theorem leaf6481CoversExact : CoversExact 8
    leaf6481Box leaf6481Certificate leaf6481InnerLog leaf6481Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk68RoundedFacts chi95RoundedFacts
    innerPair766RoundedFacts leaf6481RoundedFacts (by rfl)

private theorem leaf6481FlatSound : Sound leaf6481Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6481CertificateValid
    leaf6481InnerLogValid leaf6481CoversExact leaf6481LowerChecked

private noncomputable def component129Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (17/8), chiLo := (3/4), chiHi := (25/32) }

set_option maxRecDepth 1000000 in
private theorem component129Node0_sound : Sound component129Node0Box :=
  sound_of_literal_split component129Node0Box leaf6418Box leaf6419Box
    .k (33/16) (by rfl) (by rfl)
    leaf6418FlatSound leaf6419FlatSound

private noncomputable def component129Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (17/8), chiLo := (25/32), chiHi := (13/16) }

set_option maxRecDepth 1000000 in
private theorem component129Node1_sound : Sound component129Node1Box :=
  sound_of_literal_split component129Node1Box leaf6420Box leaf6421Box
    .k (33/16) (by rfl) (by rfl)
    leaf6420FlatSound leaf6421FlatSound

private noncomputable def component129Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (17/8), chiLo := (3/4), chiHi := (13/16) }

set_option maxRecDepth 1000000 in
private theorem component129Node2_sound : Sound component129Node2Box :=
  sound_of_literal_split component129Node2Box component129Node0Box component129Node1Box
    .chi (25/32) (by rfl) (by rfl)
    component129Node0_sound component129Node1_sound

private noncomputable def component129Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (9/4), chiLo := (3/4), chiHi := (25/32) }

set_option maxRecDepth 1000000 in
private theorem component129Node3_sound : Sound component129Node3Box :=
  sound_of_literal_split component129Node3Box leaf6422Box leaf6423Box
    .k (35/16) (by rfl) (by rfl)
    leaf6422FlatSound leaf6423FlatSound

private noncomputable def component129Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (9/4), chiLo := (25/32), chiHi := (13/16) }

set_option maxRecDepth 1000000 in
private theorem component129Node4_sound : Sound component129Node4Box :=
  sound_of_literal_split component129Node4Box leaf6424Box leaf6425Box
    .k (35/16) (by rfl) (by rfl)
    leaf6424FlatSound leaf6425FlatSound

private noncomputable def component129Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (9/4), chiLo := (3/4), chiHi := (13/16) }

set_option maxRecDepth 1000000 in
private theorem component129Node5_sound : Sound component129Node5Box :=
  sound_of_literal_split component129Node5Box component129Node3Box component129Node4Box
    .chi (25/32) (by rfl) (by rfl)
    component129Node3_sound component129Node4_sound

private noncomputable def component129Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (9/4), chiLo := (3/4), chiHi := (13/16) }

set_option maxRecDepth 1000000 in
private theorem component129Node6_sound : Sound component129Node6Box :=
  sound_of_literal_split component129Node6Box component129Node2Box component129Node5Box
    .k (17/8) (by rfl) (by rfl)
    component129Node2_sound component129Node5_sound

private noncomputable def component129Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (17/8), chiLo := (13/16), chiHi := (27/32) }

set_option maxRecDepth 1000000 in
private theorem component129Node7_sound : Sound component129Node7Box :=
  sound_of_literal_split component129Node7Box leaf6426Box leaf6427Box
    .k (33/16) (by rfl) (by rfl)
    leaf6426FlatSound leaf6427FlatSound

private noncomputable def component129Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (17/8), chiLo := (27/32), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component129Node8_sound : Sound component129Node8Box :=
  sound_of_literal_split component129Node8Box leaf6428Box leaf6429Box
    .k (33/16) (by rfl) (by rfl)
    leaf6428FlatSound leaf6429FlatSound

private noncomputable def component129Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (17/8), chiLo := (13/16), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component129Node9_sound : Sound component129Node9Box :=
  sound_of_literal_split component129Node9Box component129Node7Box component129Node8Box
    .chi (27/32) (by rfl) (by rfl)
    component129Node7_sound component129Node8_sound

private noncomputable def component129Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (9/4), chiLo := (13/16), chiHi := (27/32) }

set_option maxRecDepth 1000000 in
private theorem component129Node10_sound : Sound component129Node10Box :=
  sound_of_literal_split component129Node10Box leaf6430Box leaf6431Box
    .k (35/16) (by rfl) (by rfl)
    leaf6430FlatSound leaf6431FlatSound

private noncomputable def component129Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (9/4), chiLo := (27/32), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component129Node11_sound : Sound component129Node11Box :=
  sound_of_literal_split component129Node11Box leaf6432Box leaf6433Box
    .k (35/16) (by rfl) (by rfl)
    leaf6432FlatSound leaf6433FlatSound

private noncomputable def component129Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (9/4), chiLo := (13/16), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component129Node12_sound : Sound component129Node12Box :=
  sound_of_literal_split component129Node12Box component129Node10Box component129Node11Box
    .chi (27/32) (by rfl) (by rfl)
    component129Node10_sound component129Node11_sound

private noncomputable def component129Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (9/4), chiLo := (13/16), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component129Node13_sound : Sound component129Node13Box :=
  sound_of_literal_split component129Node13Box component129Node9Box component129Node12Box
    .k (17/8) (by rfl) (by rfl)
    component129Node9_sound component129Node12_sound

private noncomputable def component129Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (9/4), chiLo := (3/4), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component129Node14_sound : Sound component129Node14Box :=
  sound_of_literal_split component129Node14Box component129Node6Box component129Node13Box
    .chi (13/16) (by rfl) (by rfl)
    component129Node6_sound component129Node13_sound

private noncomputable def component129Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (17/8), chiLo := (7/8), chiHi := (29/32) }

set_option maxRecDepth 1000000 in
private theorem component129Node15_sound : Sound component129Node15Box :=
  sound_of_literal_split component129Node15Box leaf6434Box leaf6435Box
    .k (33/16) (by rfl) (by rfl)
    leaf6434FlatSound leaf6435FlatSound

private noncomputable def component129Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (17/8), chiLo := (29/32), chiHi := (15/16) }

set_option maxRecDepth 1000000 in
private theorem component129Node16_sound : Sound component129Node16Box :=
  sound_of_literal_split component129Node16Box leaf6436Box leaf6437Box
    .k (33/16) (by rfl) (by rfl)
    leaf6436FlatSound leaf6437FlatSound

private noncomputable def component129Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (17/8), chiLo := (7/8), chiHi := (15/16) }

set_option maxRecDepth 1000000 in
private theorem component129Node17_sound : Sound component129Node17Box :=
  sound_of_literal_split component129Node17Box component129Node15Box component129Node16Box
    .chi (29/32) (by rfl) (by rfl)
    component129Node15_sound component129Node16_sound

private noncomputable def component129Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (17/8), chiLo := (15/16), chiHi := (31/32) }

set_option maxRecDepth 1000000 in
private theorem component129Node18_sound : Sound component129Node18Box :=
  sound_of_literal_split component129Node18Box leaf6438Box leaf6439Box
    .k (33/16) (by rfl) (by rfl)
    leaf6438FlatSound leaf6439FlatSound

private noncomputable def component129Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (17/8), chiLo := (31/32), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component129Node19_sound : Sound component129Node19Box :=
  sound_of_literal_split component129Node19Box leaf6440Box leaf6441Box
    .k (33/16) (by rfl) (by rfl)
    leaf6440FlatSound leaf6441FlatSound

private noncomputable def component129Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (17/8), chiLo := (15/16), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component129Node20_sound : Sound component129Node20Box :=
  sound_of_literal_split component129Node20Box component129Node18Box component129Node19Box
    .chi (31/32) (by rfl) (by rfl)
    component129Node18_sound component129Node19_sound

private noncomputable def component129Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (17/8), chiLo := (7/8), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component129Node21_sound : Sound component129Node21Box :=
  sound_of_literal_split component129Node21Box component129Node17Box component129Node20Box
    .chi (15/16) (by rfl) (by rfl)
    component129Node17_sound component129Node20_sound

private noncomputable def component129Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (9/4), chiLo := (7/8), chiHi := (29/32) }

set_option maxRecDepth 1000000 in
private theorem component129Node22_sound : Sound component129Node22Box :=
  sound_of_literal_split component129Node22Box leaf6442Box leaf6443Box
    .k (35/16) (by rfl) (by rfl)
    leaf6442FlatSound leaf6443FlatSound

private noncomputable def component129Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (9/4), chiLo := (29/32), chiHi := (15/16) }

set_option maxRecDepth 1000000 in
private theorem component129Node23_sound : Sound component129Node23Box :=
  sound_of_literal_split component129Node23Box leaf6444Box leaf6445Box
    .k (35/16) (by rfl) (by rfl)
    leaf6444FlatSound leaf6445FlatSound

private noncomputable def component129Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (9/4), chiLo := (7/8), chiHi := (15/16) }

set_option maxRecDepth 1000000 in
private theorem component129Node24_sound : Sound component129Node24Box :=
  sound_of_literal_split component129Node24Box component129Node22Box component129Node23Box
    .chi (29/32) (by rfl) (by rfl)
    component129Node22_sound component129Node23_sound

private noncomputable def component129Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (9/4), chiLo := (15/16), chiHi := (31/32) }

set_option maxRecDepth 1000000 in
private theorem component129Node25_sound : Sound component129Node25Box :=
  sound_of_literal_split component129Node25Box leaf6446Box leaf6447Box
    .k (35/16) (by rfl) (by rfl)
    leaf6446FlatSound leaf6447FlatSound

private noncomputable def component129Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (9/4), chiLo := (31/32), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component129Node26_sound : Sound component129Node26Box :=
  sound_of_literal_split component129Node26Box leaf6448Box leaf6449Box
    .k (35/16) (by rfl) (by rfl)
    leaf6448FlatSound leaf6449FlatSound

private noncomputable def component129Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (9/4), chiLo := (15/16), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component129Node27_sound : Sound component129Node27Box :=
  sound_of_literal_split component129Node27Box component129Node25Box component129Node26Box
    .chi (31/32) (by rfl) (by rfl)
    component129Node25_sound component129Node26_sound

private noncomputable def component129Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (9/4), chiLo := (7/8), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component129Node28_sound : Sound component129Node28Box :=
  sound_of_literal_split component129Node28Box component129Node24Box component129Node27Box
    .chi (15/16) (by rfl) (by rfl)
    component129Node24_sound component129Node27_sound

private noncomputable def component129Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (9/4), chiLo := (7/8), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component129Node29_sound : Sound component129Node29Box :=
  sound_of_literal_split component129Node29Box component129Node21Box component129Node28Box
    .k (17/8) (by rfl) (by rfl)
    component129Node21_sound component129Node28_sound

private noncomputable def component129Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (9/4), chiLo := (3/4), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component129Node30_sound : Sound component129Node30Box :=
  sound_of_literal_split component129Node30Box component129Node14Box component129Node29Box
    .chi (7/8) (by rfl) (by rfl)
    component129Node14_sound component129Node29_sound

private noncomputable def component129Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (19/8), chiLo := (3/4), chiHi := (25/32) }

set_option maxRecDepth 1000000 in
private theorem component129Node31_sound : Sound component129Node31Box :=
  sound_of_literal_split component129Node31Box leaf6450Box leaf6451Box
    .k (37/16) (by rfl) (by rfl)
    leaf6450FlatSound leaf6451FlatSound

private noncomputable def component129Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (19/8), chiLo := (25/32), chiHi := (13/16) }

set_option maxRecDepth 1000000 in
private theorem component129Node32_sound : Sound component129Node32Box :=
  sound_of_literal_split component129Node32Box leaf6452Box leaf6453Box
    .k (37/16) (by rfl) (by rfl)
    leaf6452FlatSound leaf6453FlatSound

private noncomputable def component129Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (19/8), chiLo := (3/4), chiHi := (13/16) }

set_option maxRecDepth 1000000 in
private theorem component129Node33_sound : Sound component129Node33Box :=
  sound_of_literal_split component129Node33Box component129Node31Box component129Node32Box
    .chi (25/32) (by rfl) (by rfl)
    component129Node31_sound component129Node32_sound

private noncomputable def component129Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (5/2), chiLo := (3/4), chiHi := (25/32) }

set_option maxRecDepth 1000000 in
private theorem component129Node34_sound : Sound component129Node34Box :=
  sound_of_literal_split component129Node34Box leaf6454Box leaf6455Box
    .k (39/16) (by rfl) (by rfl)
    leaf6454FlatSound leaf6455FlatSound

private noncomputable def component129Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (5/2), chiLo := (25/32), chiHi := (13/16) }

set_option maxRecDepth 1000000 in
private theorem component129Node35_sound : Sound component129Node35Box :=
  sound_of_literal_split component129Node35Box leaf6456Box leaf6457Box
    .k (39/16) (by rfl) (by rfl)
    leaf6456FlatSound leaf6457FlatSound

private noncomputable def component129Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (5/2), chiLo := (3/4), chiHi := (13/16) }

set_option maxRecDepth 1000000 in
private theorem component129Node36_sound : Sound component129Node36Box :=
  sound_of_literal_split component129Node36Box component129Node34Box component129Node35Box
    .chi (25/32) (by rfl) (by rfl)
    component129Node34_sound component129Node35_sound

private noncomputable def component129Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (5/2), chiLo := (3/4), chiHi := (13/16) }

set_option maxRecDepth 1000000 in
private theorem component129Node37_sound : Sound component129Node37Box :=
  sound_of_literal_split component129Node37Box component129Node33Box component129Node36Box
    .k (19/8) (by rfl) (by rfl)
    component129Node33_sound component129Node36_sound

private noncomputable def component129Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (19/8), chiLo := (13/16), chiHi := (27/32) }

set_option maxRecDepth 1000000 in
private theorem component129Node38_sound : Sound component129Node38Box :=
  sound_of_literal_split component129Node38Box leaf6458Box leaf6459Box
    .k (37/16) (by rfl) (by rfl)
    leaf6458FlatSound leaf6459FlatSound

private noncomputable def component129Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (19/8), chiLo := (27/32), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component129Node39_sound : Sound component129Node39Box :=
  sound_of_literal_split component129Node39Box leaf6460Box leaf6461Box
    .k (37/16) (by rfl) (by rfl)
    leaf6460FlatSound leaf6461FlatSound

private noncomputable def component129Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (19/8), chiLo := (13/16), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component129Node40_sound : Sound component129Node40Box :=
  sound_of_literal_split component129Node40Box component129Node38Box component129Node39Box
    .chi (27/32) (by rfl) (by rfl)
    component129Node38_sound component129Node39_sound

private noncomputable def component129Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (5/2), chiLo := (13/16), chiHi := (27/32) }

set_option maxRecDepth 1000000 in
private theorem component129Node41_sound : Sound component129Node41Box :=
  sound_of_literal_split component129Node41Box leaf6462Box leaf6463Box
    .k (39/16) (by rfl) (by rfl)
    leaf6462FlatSound leaf6463FlatSound

private noncomputable def component129Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (5/2), chiLo := (27/32), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component129Node42_sound : Sound component129Node42Box :=
  sound_of_literal_split component129Node42Box leaf6464Box leaf6465Box
    .k (39/16) (by rfl) (by rfl)
    leaf6464FlatSound leaf6465FlatSound

private noncomputable def component129Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (5/2), chiLo := (13/16), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component129Node43_sound : Sound component129Node43Box :=
  sound_of_literal_split component129Node43Box component129Node41Box component129Node42Box
    .chi (27/32) (by rfl) (by rfl)
    component129Node41_sound component129Node42_sound

private noncomputable def component129Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (5/2), chiLo := (13/16), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component129Node44_sound : Sound component129Node44Box :=
  sound_of_literal_split component129Node44Box component129Node40Box component129Node43Box
    .k (19/8) (by rfl) (by rfl)
    component129Node40_sound component129Node43_sound

private noncomputable def component129Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (5/2), chiLo := (3/4), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component129Node45_sound : Sound component129Node45Box :=
  sound_of_literal_split component129Node45Box component129Node37Box component129Node44Box
    .chi (13/16) (by rfl) (by rfl)
    component129Node37_sound component129Node44_sound

private noncomputable def component129Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (19/8), chiLo := (7/8), chiHi := (29/32) }

set_option maxRecDepth 1000000 in
private theorem component129Node46_sound : Sound component129Node46Box :=
  sound_of_literal_split component129Node46Box leaf6466Box leaf6467Box
    .k (37/16) (by rfl) (by rfl)
    leaf6466FlatSound leaf6467FlatSound

private noncomputable def component129Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (19/8), chiLo := (29/32), chiHi := (15/16) }

set_option maxRecDepth 1000000 in
private theorem component129Node47_sound : Sound component129Node47Box :=
  sound_of_literal_split component129Node47Box leaf6468Box leaf6469Box
    .k (37/16) (by rfl) (by rfl)
    leaf6468FlatSound leaf6469FlatSound

private noncomputable def component129Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (19/8), chiLo := (7/8), chiHi := (15/16) }

set_option maxRecDepth 1000000 in
private theorem component129Node48_sound : Sound component129Node48Box :=
  sound_of_literal_split component129Node48Box component129Node46Box component129Node47Box
    .chi (29/32) (by rfl) (by rfl)
    component129Node46_sound component129Node47_sound

private noncomputable def component129Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (5/2), chiLo := (7/8), chiHi := (29/32) }

set_option maxRecDepth 1000000 in
private theorem component129Node49_sound : Sound component129Node49Box :=
  sound_of_literal_split component129Node49Box leaf6470Box leaf6471Box
    .k (39/16) (by rfl) (by rfl)
    leaf6470FlatSound leaf6471FlatSound

private noncomputable def component129Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (5/2), chiLo := (29/32), chiHi := (15/16) }

set_option maxRecDepth 1000000 in
private theorem component129Node50_sound : Sound component129Node50Box :=
  sound_of_literal_split component129Node50Box leaf6472Box leaf6473Box
    .k (39/16) (by rfl) (by rfl)
    leaf6472FlatSound leaf6473FlatSound

private noncomputable def component129Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (5/2), chiLo := (7/8), chiHi := (15/16) }

set_option maxRecDepth 1000000 in
private theorem component129Node51_sound : Sound component129Node51Box :=
  sound_of_literal_split component129Node51Box component129Node49Box component129Node50Box
    .chi (29/32) (by rfl) (by rfl)
    component129Node49_sound component129Node50_sound

private noncomputable def component129Node52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (5/2), chiLo := (7/8), chiHi := (15/16) }

set_option maxRecDepth 1000000 in
private theorem component129Node52_sound : Sound component129Node52Box :=
  sound_of_literal_split component129Node52Box component129Node48Box component129Node51Box
    .k (19/8) (by rfl) (by rfl)
    component129Node48_sound component129Node51_sound

private noncomputable def component129Node53Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (19/8), chiLo := (15/16), chiHi := (31/32) }

set_option maxRecDepth 1000000 in
private theorem component129Node53_sound : Sound component129Node53Box :=
  sound_of_literal_split component129Node53Box leaf6474Box leaf6475Box
    .k (37/16) (by rfl) (by rfl)
    leaf6474FlatSound leaf6475FlatSound

private noncomputable def component129Node54Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (19/8), chiLo := (31/32), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component129Node54_sound : Sound component129Node54Box :=
  sound_of_literal_split component129Node54Box leaf6476Box leaf6477Box
    .k (37/16) (by rfl) (by rfl)
    leaf6476FlatSound leaf6477FlatSound

private noncomputable def component129Node55Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (19/8), chiLo := (15/16), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component129Node55_sound : Sound component129Node55Box :=
  sound_of_literal_split component129Node55Box component129Node53Box component129Node54Box
    .chi (31/32) (by rfl) (by rfl)
    component129Node53_sound component129Node54_sound

private noncomputable def component129Node56Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (5/2), chiLo := (15/16), chiHi := (31/32) }

set_option maxRecDepth 1000000 in
private theorem component129Node56_sound : Sound component129Node56Box :=
  sound_of_literal_split component129Node56Box leaf6478Box leaf6479Box
    .k (39/16) (by rfl) (by rfl)
    leaf6478FlatSound leaf6479FlatSound

private noncomputable def component129Node57Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (5/2), chiLo := (31/32), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component129Node57_sound : Sound component129Node57Box :=
  sound_of_literal_split component129Node57Box leaf6480Box leaf6481Box
    .k (39/16) (by rfl) (by rfl)
    leaf6480FlatSound leaf6481FlatSound

private noncomputable def component129Node58Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (5/2), chiLo := (15/16), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component129Node58_sound : Sound component129Node58Box :=
  sound_of_literal_split component129Node58Box component129Node56Box component129Node57Box
    .chi (31/32) (by rfl) (by rfl)
    component129Node56_sound component129Node57_sound

private noncomputable def component129Node59Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (5/2), chiLo := (15/16), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component129Node59_sound : Sound component129Node59Box :=
  sound_of_literal_split component129Node59Box component129Node55Box component129Node58Box
    .k (19/8) (by rfl) (by rfl)
    component129Node55_sound component129Node58_sound

private noncomputable def component129Node60Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (5/2), chiLo := (7/8), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component129Node60_sound : Sound component129Node60Box :=
  sound_of_literal_split component129Node60Box component129Node52Box component129Node59Box
    .chi (15/16) (by rfl) (by rfl)
    component129Node52_sound component129Node59_sound

private noncomputable def component129Node61Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (5/2), chiLo := (3/4), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component129Node61_sound : Sound component129Node61Box :=
  sound_of_literal_split component129Node61Box component129Node45Box component129Node60Box
    .chi (7/8) (by rfl) (by rfl)
    component129Node45_sound component129Node60_sound

noncomputable def component129Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (5/2), chiLo := (3/4), chiHi := (1) }

set_option maxRecDepth 1000000 in
theorem component129_sound : Sound component129Box :=
  sound_of_literal_split component129Box component129Node30Box component129Node61Box
    .k (9/4) (by rfl) (by rfl)
    component129Node30_sound component129Node61_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
