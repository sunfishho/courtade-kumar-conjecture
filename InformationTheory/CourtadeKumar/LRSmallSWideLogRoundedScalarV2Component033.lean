import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch6
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheSKBatch1
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

private noncomputable def leaf1420Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (3/32), chiHi := (25/256) }

private noncomputable def leaf1420Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435603/268435456) }, vSqrt := { lower := (65529/65536), upper := (22369664/22369213) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (343895407/268435456) }, upper := { exponent := 0, mantissa := (5321/4096) } }, logOuter := sk123LogOuterCertificate, logK := sk123LogKCertificate, logChi := chi131LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (44738877/44738426) } }, logDArg := sk123LogDArgCertificate }

private noncomputable def leaf1420InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1420LocalValidity :
    LeafFacts leaf1420Box leaf1420Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1420Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22369664/22369213) }) = true
      norm_num [leaf1420Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1420CertificateValid :
    WideCertificateValid leaf1420Box leaf1420Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk123ValidityFacts chi131ValidityFacts
    leaf1420LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1420CoverageChecked :
    coverageCheck (innerAD leaf1420Box) leaf1420InnerLog = true := by
  rfl'

private theorem leaf1420InnerLogValid :
    leaf1420InnerLog.Valid 8 (innerAD leaf1420Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1420CoverageChecked

private noncomputable def leaf1420InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814625/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1420InputLogOnePlusV_eq :
    leaf1420InputLogOnePlusV = outerEnclosure 24
      (leaf1420Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1420RoundedFacts : LeafRoundedFacts 8
    leaf1420Certificate.logOnePlusV leaf1420InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1420InputLogOnePlusV_eq }

private noncomputable def leaf1420Inputs : Inputs :=
  inputsOfCaches globalInput sk123RoundedInputs
    chi131InputQChi innerPair16Input
    leaf1420InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1420LowerChecked :
    lowerCheck 24 leaf1420Box leaf1420Inputs = true := by
  rfl'

private theorem leaf1420CoversExact : CoversExact 8
    leaf1420Box leaf1420Certificate leaf1420InnerLog leaf1420Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk123RoundedFacts chi131RoundedFacts
    innerPair16RoundedFacts leaf1420RoundedFacts (by rfl)

private theorem leaf1420FlatSound : Sound leaf1420Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1420CertificateValid
    leaf1420InnerLogValid leaf1420CoversExact leaf1420LowerChecked

private noncomputable def leaf1421Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (25/256), chiHi := (13/128) }

private noncomputable def leaf1421Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435605/268435456) }, vSqrt := { lower := (65529/65536), upper := (33554496/33553795) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (347040941/268435456) }, upper := { exponent := 0, mantissa := (2685/2048) } }, logOuter := sk123LogOuterCertificate, logK := sk123LogKCertificate, logChi := chi132LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (67108291/67107590) } }, logDArg := sk123LogDArgCertificate }

private noncomputable def leaf1421InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1421LocalValidity :
    LeafFacts leaf1421Box leaf1421Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1421Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (33554496/33553795) }) = true
      norm_num [leaf1421Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1421CertificateValid :
    WideCertificateValid leaf1421Box leaf1421Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk123ValidityFacts chi132ValidityFacts
    leaf1421LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1421CoverageChecked :
    coverageCheck (innerAD leaf1421Box) leaf1421InnerLog = true := by
  rfl'

private theorem leaf1421InnerLogValid :
    leaf1421InnerLog.Valid 8 (innerAD leaf1421Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1421CoverageChecked

private noncomputable def leaf1421InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453657/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf1421InputLogOnePlusV_eq :
    leaf1421InputLogOnePlusV = outerEnclosure 24
      (leaf1421Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1421RoundedFacts : LeafRoundedFacts 8
    leaf1421Certificate.logOnePlusV leaf1421InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1421InputLogOnePlusV_eq }

private noncomputable def leaf1421Inputs : Inputs :=
  inputsOfCaches globalInput sk123RoundedInputs
    chi132InputQChi innerPair16Input
    leaf1421InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1421LowerChecked :
    lowerCheck 24 leaf1421Box leaf1421Inputs = true := by
  rfl'

private theorem leaf1421CoversExact : CoversExact 8
    leaf1421Box leaf1421Certificate leaf1421InnerLog leaf1421Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk123RoundedFacts chi132RoundedFacts
    innerPair16RoundedFacts leaf1421RoundedFacts (by rfl)

private theorem leaf1421FlatSound : Sound leaf1421Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1421CertificateValid
    leaf1421InnerLogValid leaf1421CoversExact leaf1421LowerChecked

private noncomputable def leaf1422Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (13/128), chiHi := (7/64) }

private noncomputable def leaf1422Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435677/268435456) }, vSqrt := { lower := (65529/65536), upper := (33554464/33553753) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (350186405/268435456) }, upper := { exponent := 0, mantissa := (2727/2048) } }, logOuter := sk133LogOuterCertificate, logK := sk133LogKCertificate, logChi := chi106LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (67108217/67107506) } }, logDArg := sk133LogDArgCertificate }

private noncomputable def leaf1422InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf1422LocalValidity :
    LeafFacts leaf1422Box leaf1422Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1422Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (33554464/33553753) }) = true
      norm_num [leaf1422Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1422CertificateValid :
    WideCertificateValid leaf1422Box leaf1422Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk133ValidityFacts chi106ValidityFacts
    leaf1422LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1422CoverageChecked :
    coverageCheck (innerAD leaf1422Box) leaf1422InnerLog = true := by
  rfl'

private theorem leaf1422InnerLogValid :
    leaf1422InnerLog.Valid 8 (innerAD leaf1422Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf1422CoverageChecked

private noncomputable def leaf1422InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814629/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1422InputLogOnePlusV_eq :
    leaf1422InputLogOnePlusV = outerEnclosure 24
      (leaf1422Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1422RoundedFacts : LeafRoundedFacts 8
    leaf1422Certificate.logOnePlusV leaf1422InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1422InputLogOnePlusV_eq }

private noncomputable def leaf1422Inputs : Inputs :=
  inputsOfCaches globalInput sk133RoundedInputs
    chi106InputQChi innerPair17Input
    leaf1422InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1422LowerChecked :
    lowerCheck 24 leaf1422Box leaf1422Inputs = true := by
  rfl'

private theorem leaf1422CoversExact : CoversExact 8
    leaf1422Box leaf1422Certificate leaf1422InnerLog leaf1422Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk133RoundedFacts chi106RoundedFacts
    innerPair17RoundedFacts leaf1422RoundedFacts (by rfl)

private theorem leaf1422FlatSound : Sound leaf1422Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1422CertificateValid
    leaf1422InnerLogValid leaf1422CoversExact leaf1422LowerChecked

private noncomputable def leaf1423Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (13/128), chiHi := (7/64) }

private noncomputable def leaf1423Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435679/268435456) }, vSqrt := { lower := (65529/65536), upper := (16777232/16776873) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (351038319/268435456) }, upper := { exponent := 0, mantissa := (1367/1024) } }, logOuter := sk134LogOuterCertificate, logK := sk134LogKCertificate, logChi := chi106LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (33554105/33553746) } }, logDArg := sk134LogDArgCertificate }

private noncomputable def leaf1423InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf1423LocalValidity :
    LeafFacts leaf1423Box leaf1423Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1423Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (16777232/16776873) }) = true
      norm_num [leaf1423Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1423CertificateValid :
    WideCertificateValid leaf1423Box leaf1423Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk134ValidityFacts chi106ValidityFacts
    leaf1423LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1423CoverageChecked :
    coverageCheck (innerAD leaf1423Box) leaf1423InnerLog = true := by
  rfl'

private theorem leaf1423InnerLogValid :
    leaf1423InnerLog.Valid 8 (innerAD leaf1423Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf1423CoverageChecked

private noncomputable def leaf1423InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907315/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1423InputLogOnePlusV_eq :
    leaf1423InputLogOnePlusV = outerEnclosure 24
      (leaf1423Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1423RoundedFacts : LeafRoundedFacts 8
    leaf1423Certificate.logOnePlusV leaf1423InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1423InputLogOnePlusV_eq }

private noncomputable def leaf1423Inputs : Inputs :=
  inputsOfCaches globalInput sk134RoundedInputs
    chi106InputQChi innerPair17Input
    leaf1423InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1423LowerChecked :
    lowerCheck 24 leaf1423Box leaf1423Inputs = true := by
  rfl'

private theorem leaf1423CoversExact : CoversExact 8
    leaf1423Box leaf1423Certificate leaf1423InnerLog leaf1423Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk134RoundedFacts chi106RoundedFacts
    innerPair17RoundedFacts leaf1423RoundedFacts (by rfl)

private theorem leaf1423FlatSound : Sound leaf1423Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1423CertificateValid
    leaf1423InnerLogValid leaf1423CoversExact leaf1423LowerChecked

private noncomputable def leaf1424Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (3/32), chiHi := (25/256) }

private noncomputable def leaf1424Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435605/268435456) }, vSqrt := { lower := (65529/65536), upper := (33554496/33553807) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (345468173/268435456) }, upper := { exponent := 0, mantissa := (2673/2048) } }, logOuter := sk124LogOuterCertificate, logK := sk124LogKCertificate, logChi := chi131LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (67108303/67107614) } }, logDArg := sk124LogDArgCertificate }

private noncomputable def leaf1424InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1424LocalValidity :
    LeafFacts leaf1424Box leaf1424Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1424Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (33554496/33553807) }) = true
      norm_num [leaf1424Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1424CertificateValid :
    WideCertificateValid leaf1424Box leaf1424Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk124ValidityFacts chi131ValidityFacts
    leaf1424LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1424CoverageChecked :
    coverageCheck (innerAD leaf1424Box) leaf1424InnerLog = true := by
  rfl'

private theorem leaf1424InnerLogValid :
    leaf1424InnerLog.Valid 8 (innerAD leaf1424Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1424CoverageChecked

private noncomputable def leaf1424InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629253/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1424InputLogOnePlusV_eq :
    leaf1424InputLogOnePlusV = outerEnclosure 24
      (leaf1424Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1424RoundedFacts : LeafRoundedFacts 8
    leaf1424Certificate.logOnePlusV leaf1424InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1424InputLogOnePlusV_eq }

private noncomputable def leaf1424Inputs : Inputs :=
  inputsOfCaches globalInput sk124RoundedInputs
    chi131InputQChi innerPair16Input
    leaf1424InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1424LowerChecked :
    lowerCheck 24 leaf1424Box leaf1424Inputs = true := by
  rfl'

private theorem leaf1424CoversExact : CoversExact 8
    leaf1424Box leaf1424Certificate leaf1424InnerLog leaf1424Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk124RoundedFacts chi131RoundedFacts
    innerPair16RoundedFacts leaf1424RoundedFacts (by rfl)

private theorem leaf1424FlatSound : Sound leaf1424Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1424CertificateValid
    leaf1424InnerLogValid leaf1424CoversExact leaf1424LowerChecked

private noncomputable def leaf1425Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (25/256), chiHi := (13/128) }

private noncomputable def leaf1425Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435607/268435456) }, vSqrt := { lower := (65529/65536), upper := (5592416/5592297) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (348679239/268435456) }, upper := { exponent := 0, mantissa := (1349/1024) } }, logOuter := sk124LogOuterCertificate, logK := sk124LogKCertificate, logChi := chi132LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (11184713/11184594) } }, logDArg := sk124LogDArgCertificate }

private noncomputable def leaf1425InnerLog : WideLogData :=
  innerPair437Data

set_option maxRecDepth 1000000 in
private theorem leaf1425LocalValidity :
    LeafFacts leaf1425Box leaf1425Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1425Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (5592416/5592297) }) = true
      norm_num [leaf1425Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1425CertificateValid :
    WideCertificateValid leaf1425Box leaf1425Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk124ValidityFacts chi132ValidityFacts
    leaf1425LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1425CoverageChecked :
    coverageCheck (innerAD leaf1425Box) leaf1425InnerLog = true := by
  rfl'

private theorem leaf1425InnerLogValid :
    leaf1425InnerLog.Valid 8 (innerAD leaf1425Box) :=
  wideLogDataValid_of_cachedCheck endpoint145PositiveFacts
    endpoint146PositiveFacts.valid leaf1425CoverageChecked

private noncomputable def leaf1425InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629259/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1425InputLogOnePlusV_eq :
    leaf1425InputLogOnePlusV = outerEnclosure 24
      (leaf1425Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1425RoundedFacts : LeafRoundedFacts 8
    leaf1425Certificate.logOnePlusV leaf1425InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1425InputLogOnePlusV_eq }

private noncomputable def leaf1425Inputs : Inputs :=
  inputsOfCaches globalInput sk124RoundedInputs
    chi132InputQChi innerPair437Input
    leaf1425InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1425LowerChecked :
    lowerCheck 24 leaf1425Box leaf1425Inputs = true := by
  rfl'

private theorem leaf1425CoversExact : CoversExact 8
    leaf1425Box leaf1425Certificate leaf1425InnerLog leaf1425Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk124RoundedFacts chi132RoundedFacts
    innerPair437RoundedFacts leaf1425RoundedFacts (by rfl)

private theorem leaf1425FlatSound : Sound leaf1425Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1425CertificateValid
    leaf1425InnerLogValid leaf1425CoversExact leaf1425LowerChecked

private noncomputable def leaf1426Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (13/128), chiHi := (27/256) }

private noncomputable def leaf1426Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871163/536870912) }, vSqrt := { lower := (65529/65536), upper := (134217856/134215055) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (703813431/536870912) }, upper := { exponent := 0, mantissa := (10865/8192) } }, logOuter := sk135LogOuterCertificate, logK := sk135LogKCertificate, logChi := chi149LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (268432911/268430110) } }, logDArg := sk135LogDArgCertificate }

private noncomputable def leaf1426InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf1426LocalValidity :
    LeafFacts leaf1426Box leaf1426Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1426Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (134217856/134215055) }) = true
      norm_num [leaf1426Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1426CertificateValid :
    WideCertificateValid leaf1426Box leaf1426Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk135ValidityFacts chi149ValidityFacts
    leaf1426LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1426CoverageChecked :
    coverageCheck (innerAD leaf1426Box) leaf1426InnerLog = true := by
  rfl'

private theorem leaf1426InnerLogValid :
    leaf1426InnerLog.Valid 8 (innerAD leaf1426Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf1426CoverageChecked

private noncomputable def leaf1426InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453657/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf1426InputLogOnePlusV_eq :
    leaf1426InputLogOnePlusV = outerEnclosure 24
      (leaf1426Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1426RoundedFacts : LeafRoundedFacts 8
    leaf1426Certificate.logOnePlusV leaf1426InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1426InputLogOnePlusV_eq }

private noncomputable def leaf1426Inputs : Inputs :=
  inputsOfCaches globalInput sk135RoundedInputs
    chi149InputQChi innerPair17Input
    leaf1426InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1426LowerChecked :
    lowerCheck 24 leaf1426Box leaf1426Inputs = true := by
  rfl'

private theorem leaf1426CoversExact : CoversExact 8
    leaf1426Box leaf1426Certificate leaf1426InnerLog leaf1426Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk135RoundedFacts chi149RoundedFacts
    innerPair17RoundedFacts leaf1426RoundedFacts (by rfl)

private theorem leaf1426FlatSound : Sound leaf1426Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1426CertificateValid
    leaf1426InnerLogValid leaf1426CoversExact leaf1426LowerChecked

private noncomputable def leaf1427Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (13/128), chiHi := (27/256) }

private noncomputable def leaf1427Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871165/536870912) }, vSqrt := { lower := (65529/65536), upper := (33554464/33553757) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (705517261/536870912) }, upper := { exponent := 0, mantissa := (2723/2048) } }, logOuter := sk136LogOuterCertificate, logK := sk136LogKCertificate, logChi := chi149LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (67108221/67107514) } }, logDArg := sk136LogDArgCertificate }

private noncomputable def leaf1427InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1427LocalValidity :
    LeafFacts leaf1427Box leaf1427Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1427Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (33554464/33553757) }) = true
      norm_num [leaf1427Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1427CertificateValid :
    WideCertificateValid leaf1427Box leaf1427Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk136ValidityFacts chi149ValidityFacts
    leaf1427LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1427CoverageChecked :
    coverageCheck (innerAD leaf1427Box) leaf1427InnerLog = true := by
  rfl'

private theorem leaf1427InnerLogValid :
    leaf1427InnerLog.Valid 8 (innerAD leaf1427Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1427CoverageChecked

private noncomputable def leaf1427InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629257/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1427InputLogOnePlusV_eq :
    leaf1427InputLogOnePlusV = outerEnclosure 24
      (leaf1427Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1427RoundedFacts : LeafRoundedFacts 8
    leaf1427Certificate.logOnePlusV leaf1427InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1427InputLogOnePlusV_eq }

private noncomputable def leaf1427Inputs : Inputs :=
  inputsOfCaches globalInput sk136RoundedInputs
    chi149InputQChi innerPair21Input
    leaf1427InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1427LowerChecked :
    lowerCheck 24 leaf1427Box leaf1427Inputs = true := by
  rfl'

private theorem leaf1427CoversExact : CoversExact 8
    leaf1427Box leaf1427Certificate leaf1427InnerLog leaf1427Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk136RoundedFacts chi149RoundedFacts
    innerPair21RoundedFacts leaf1427RoundedFacts (by rfl)

private theorem leaf1427FlatSound : Sound leaf1427Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1427CertificateValid
    leaf1427InnerLogValid leaf1427CoversExact leaf1427LowerChecked

private noncomputable def leaf1428Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (27/256), chiHi := (7/64) }

private noncomputable def leaf1428Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871165/536870912) }, vSqrt := { lower := (65529/65536), upper := (33554464/33553739) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (710235565/536870912) }, upper := { exponent := 0, mantissa := (2741/2048) } }, logOuter := sk135LogOuterCertificate, logK := sk135LogKCertificate, logChi := chi150LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (67108203/67107478) } }, logDArg := sk135LogDArgCertificate }

private noncomputable def leaf1428InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1428LocalValidity :
    LeafFacts leaf1428Box leaf1428Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1428Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (33554464/33553739) }) = true
      norm_num [leaf1428Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1428CertificateValid :
    WideCertificateValid leaf1428Box leaf1428Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk135ValidityFacts chi150ValidityFacts
    leaf1428LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1428CoverageChecked :
    coverageCheck (innerAD leaf1428Box) leaf1428InnerLog = true := by
  rfl'

private theorem leaf1428InnerLogValid :
    leaf1428InnerLog.Valid 8 (innerAD leaf1428Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1428CoverageChecked

private noncomputable def leaf1428InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814631/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1428InputLogOnePlusV_eq :
    leaf1428InputLogOnePlusV = outerEnclosure 24
      (leaf1428Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1428RoundedFacts : LeafRoundedFacts 8
    leaf1428Certificate.logOnePlusV leaf1428InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1428InputLogOnePlusV_eq }

private noncomputable def leaf1428Inputs : Inputs :=
  inputsOfCaches globalInput sk135RoundedInputs
    chi150InputQChi innerPair21Input
    leaf1428InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1428LowerChecked :
    lowerCheck 24 leaf1428Box leaf1428Inputs = true := by
  rfl'

private theorem leaf1428CoversExact : CoversExact 8
    leaf1428Box leaf1428Certificate leaf1428InnerLog leaf1428Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk135RoundedFacts chi150RoundedFacts
    innerPair21RoundedFacts leaf1428RoundedFacts (by rfl)

private theorem leaf1428FlatSound : Sound leaf1428Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1428CertificateValid
    leaf1428InnerLogValid leaf1428CoversExact leaf1428LowerChecked

private noncomputable def leaf1429Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (27/256), chiHi := (7/64) }

private noncomputable def leaf1429Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871167/536870912) }, vSqrt := { lower := (65529/65536), upper := (8388616/8388433) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (712004927/536870912) }, upper := { exponent := 0, mantissa := (687/512) } }, logOuter := sk136LogOuterCertificate, logK := sk136LogKCertificate, logChi := chi150LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (16777049/16776866) } }, logDArg := sk136LogDArgCertificate }

private noncomputable def leaf1429InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1429LocalValidity :
    LeafFacts leaf1429Box leaf1429Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1429Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8388616/8388433) }) = true
      norm_num [leaf1429Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1429CertificateValid :
    WideCertificateValid leaf1429Box leaf1429Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk136ValidityFacts chi150ValidityFacts
    leaf1429LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1429CoverageChecked :
    coverageCheck (innerAD leaf1429Box) leaf1429InnerLog = true := by
  rfl'

private theorem leaf1429InnerLogValid :
    leaf1429InnerLog.Valid 8 (innerAD leaf1429Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1429CoverageChecked

private noncomputable def leaf1429InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (726829/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf1429InputLogOnePlusV_eq :
    leaf1429InputLogOnePlusV = outerEnclosure 24
      (leaf1429Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1429RoundedFacts : LeafRoundedFacts 8
    leaf1429Certificate.logOnePlusV leaf1429InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1429InputLogOnePlusV_eq }

private noncomputable def leaf1429Inputs : Inputs :=
  inputsOfCaches globalInput sk136RoundedInputs
    chi150InputQChi innerPair21Input
    leaf1429InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1429LowerChecked :
    lowerCheck 24 leaf1429Box leaf1429Inputs = true := by
  rfl'

private theorem leaf1429CoversExact : CoversExact 8
    leaf1429Box leaf1429Certificate leaf1429InnerLog leaf1429Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk136RoundedFacts chi150RoundedFacts
    innerPair21RoundedFacts leaf1429RoundedFacts (by rfl)

private theorem leaf1429FlatSound : Sound leaf1429Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1429CertificateValid
    leaf1429InnerLogValid leaf1429CoversExact leaf1429LowerChecked

private noncomputable def leaf1430Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (7/64), chiHi := (15/128) }

private noncomputable def leaf1430Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435679/268435456) }, vSqrt := { lower := (65529/65536), upper := (67108928/67107409) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (356477475/268435456) }, upper := { exponent := 0, mantissa := (5551/4096) } }, logOuter := sk133LogOuterCertificate, logK := sk133LogKCertificate, logChi := chi98LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (134216337/134214818) } }, logDArg := sk133LogDArgCertificate }

private noncomputable def leaf1430InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1430LocalValidity :
    LeafFacts leaf1430Box leaf1430Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1430Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (67108928/67107409) }) = true
      norm_num [leaf1430Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1430CertificateValid :
    WideCertificateValid leaf1430Box leaf1430Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk133ValidityFacts chi98ValidityFacts
    leaf1430LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1430CoverageChecked :
    coverageCheck (innerAD leaf1430Box) leaf1430InnerLog = true := by
  rfl'

private theorem leaf1430InnerLogValid :
    leaf1430InnerLog.Valid 8 (innerAD leaf1430Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1430CoverageChecked

private noncomputable def leaf1430InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629271/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1430InputLogOnePlusV_eq :
    leaf1430InputLogOnePlusV = outerEnclosure 24
      (leaf1430Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1430RoundedFacts : LeafRoundedFacts 8
    leaf1430Certificate.logOnePlusV leaf1430InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1430InputLogOnePlusV_eq }

private noncomputable def leaf1430Inputs : Inputs :=
  inputsOfCaches globalInput sk133RoundedInputs
    chi98InputQChi innerPair21Input
    leaf1430InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1430LowerChecked :
    lowerCheck 24 leaf1430Box leaf1430Inputs = true := by
  rfl'

private theorem leaf1430CoversExact : CoversExact 8
    leaf1430Box leaf1430Certificate leaf1430InnerLog leaf1430Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk133RoundedFacts chi98RoundedFacts
    innerPair21RoundedFacts leaf1430RoundedFacts (by rfl)

private theorem leaf1430FlatSound : Sound leaf1430Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1430CertificateValid
    leaf1430InnerLogValid leaf1430CoversExact leaf1430LowerChecked

private noncomputable def leaf1431Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (7/64), chiHi := (15/128) }

private noncomputable def leaf1431Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435681/268435456) }, vSqrt := { lower := (65529/65536), upper := (33554464/33553697) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (357394921/268435456) }, upper := { exponent := 0, mantissa := (2783/2048) } }, logOuter := sk134LogOuterCertificate, logK := sk134LogKCertificate, logChi := chi98LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (67108161/67107394) } }, logDArg := sk134LogDArgCertificate }

private noncomputable def leaf1431InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1431LocalValidity :
    LeafFacts leaf1431Box leaf1431Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1431Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (33554464/33553697) }) = true
      norm_num [leaf1431Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1431CertificateValid :
    WideCertificateValid leaf1431Box leaf1431Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk134ValidityFacts chi98ValidityFacts
    leaf1431LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1431CoverageChecked :
    coverageCheck (innerAD leaf1431Box) leaf1431InnerLog = true := by
  rfl'

private theorem leaf1431InnerLogValid :
    leaf1431InnerLog.Valid 8 (innerAD leaf1431Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1431CoverageChecked

private noncomputable def leaf1431InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453659/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf1431InputLogOnePlusV_eq :
    leaf1431InputLogOnePlusV = outerEnclosure 24
      (leaf1431Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1431RoundedFacts : LeafRoundedFacts 8
    leaf1431Certificate.logOnePlusV leaf1431InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1431InputLogOnePlusV_eq }

private noncomputable def leaf1431Inputs : Inputs :=
  inputsOfCaches globalInput sk134RoundedInputs
    chi98InputQChi innerPair21Input
    leaf1431InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1431LowerChecked :
    lowerCheck 24 leaf1431Box leaf1431Inputs = true := by
  rfl'

private theorem leaf1431CoversExact : CoversExact 8
    leaf1431Box leaf1431Certificate leaf1431InnerLog leaf1431Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk134RoundedFacts chi98RoundedFacts
    innerPair21RoundedFacts leaf1431RoundedFacts (by rfl)

private theorem leaf1431FlatSound : Sound leaf1431Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1431CertificateValid
    leaf1431InnerLogValid leaf1431CoversExact leaf1431LowerChecked

private noncomputable def leaf1432Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (15/128), chiHi := (1/8) }

private noncomputable def leaf1432Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435681/268435456) }, vSqrt := { lower := (65529/65536), upper := (4194308/4194207) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (362768545/268435456) }, upper := { exponent := 0, mantissa := (353/256) } }, logOuter := sk133LogOuterCertificate, logK := sk133LogKCertificate, logChi := chi99LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (8388515/8388414) } }, logDArg := sk133LogDArgCertificate }

private noncomputable def leaf1432InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf1432LocalValidity :
    LeafFacts leaf1432Box leaf1432Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1432Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4194308/4194207) }) = true
      norm_num [leaf1432Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1432CertificateValid :
    WideCertificateValid leaf1432Box leaf1432Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk133ValidityFacts chi99ValidityFacts
    leaf1432LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1432CoverageChecked :
    coverageCheck (innerAD leaf1432Box) leaf1432InnerLog = true := by
  rfl'

private theorem leaf1432InnerLogValid :
    leaf1432InnerLog.Valid 8 (innerAD leaf1432Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf1432CoverageChecked

private noncomputable def leaf1432InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629283/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1432InputLogOnePlusV_eq :
    leaf1432InputLogOnePlusV = outerEnclosure 24
      (leaf1432Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1432RoundedFacts : LeafRoundedFacts 8
    leaf1432Certificate.logOnePlusV leaf1432InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1432InputLogOnePlusV_eq }

private noncomputable def leaf1432Inputs : Inputs :=
  inputsOfCaches globalInput sk133RoundedInputs
    chi99InputQChi innerPair22Input
    leaf1432InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1432LowerChecked :
    lowerCheck 24 leaf1432Box leaf1432Inputs = true := by
  rfl'

private theorem leaf1432CoversExact : CoversExact 8
    leaf1432Box leaf1432Certificate leaf1432InnerLog leaf1432Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk133RoundedFacts chi99RoundedFacts
    innerPair22RoundedFacts leaf1432RoundedFacts (by rfl)

private theorem leaf1432FlatSound : Sound leaf1432Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1432CertificateValid
    leaf1432InnerLogValid leaf1432CoversExact leaf1432LowerChecked

private noncomputable def leaf1433Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (15/128), chiHi := (1/8) }

private noncomputable def leaf1433Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435683/268435456) }, vSqrt := { lower := (65529/65536), upper := (123362/123359) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (363751523/268435456) }, upper := { exponent := 0, mantissa := (177/128) } }, logOuter := sk134LogOuterCertificate, logK := sk134LogKCertificate, logChi := chi99LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (246721/246718) } }, logDArg := sk134LogDArgCertificate }

private noncomputable def leaf1433InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf1433LocalValidity :
    LeafFacts leaf1433Box leaf1433Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1433Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (123362/123359) }) = true
      norm_num [leaf1433Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1433CertificateValid :
    WideCertificateValid leaf1433Box leaf1433Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk134ValidityFacts chi99ValidityFacts
    leaf1433LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1433CoverageChecked :
    coverageCheck (innerAD leaf1433Box) leaf1433InnerLog = true := by
  rfl'

private theorem leaf1433InnerLogValid :
    leaf1433InnerLog.Valid 8 (innerAD leaf1433Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf1433CoverageChecked

private noncomputable def leaf1433InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629285/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1433InputLogOnePlusV_eq :
    leaf1433InputLogOnePlusV = outerEnclosure 24
      (leaf1433Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1433RoundedFacts : LeafRoundedFacts 8
    leaf1433Certificate.logOnePlusV leaf1433InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1433InputLogOnePlusV_eq }

private noncomputable def leaf1433Inputs : Inputs :=
  inputsOfCaches globalInput sk134RoundedInputs
    chi99InputQChi innerPair22Input
    leaf1433InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1433LowerChecked :
    lowerCheck 24 leaf1433Box leaf1433Inputs = true := by
  rfl'

private theorem leaf1433CoversExact : CoversExact 8
    leaf1433Box leaf1433Certificate leaf1433InnerLog leaf1433Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk134RoundedFacts chi99RoundedFacts
    innerPair22RoundedFacts leaf1433RoundedFacts (by rfl)

private theorem leaf1433FlatSound : Sound leaf1433Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1433CertificateValid
    leaf1433InnerLogValid leaf1433CoversExact leaf1433LowerChecked

private noncomputable def leaf1434Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (7/64), chiHi := (15/128) }

private noncomputable def leaf1434Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435683/268435456) }, vSqrt := { lower := (65529/65536), upper := (67108928/67107379) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (358312367/268435456) }, upper := { exponent := 0, mantissa := (5581/4096) } }, logOuter := sk135LogOuterCertificate, logK := sk135LogKCertificate, logChi := chi98LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (134216307/134214758) } }, logDArg := sk135LogDArgCertificate }

private noncomputable def leaf1434InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1434LocalValidity :
    LeafFacts leaf1434Box leaf1434Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1434Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (67108928/67107379) }) = true
      norm_num [leaf1434Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1434CertificateValid :
    WideCertificateValid leaf1434Box leaf1434Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk135ValidityFacts chi98ValidityFacts
    leaf1434LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1434CoverageChecked :
    coverageCheck (innerAD leaf1434Box) leaf1434InnerLog = true := by
  rfl'

private theorem leaf1434InnerLogValid :
    leaf1434InnerLog.Valid 8 (innerAD leaf1434Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1434CoverageChecked

private noncomputable def leaf1434InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814637/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1434InputLogOnePlusV_eq :
    leaf1434InputLogOnePlusV = outerEnclosure 24
      (leaf1434Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1434RoundedFacts : LeafRoundedFacts 8
    leaf1434Certificate.logOnePlusV leaf1434InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1434InputLogOnePlusV_eq }

private noncomputable def leaf1434Inputs : Inputs :=
  inputsOfCaches globalInput sk135RoundedInputs
    chi98InputQChi innerPair21Input
    leaf1434InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1434LowerChecked :
    lowerCheck 24 leaf1434Box leaf1434Inputs = true := by
  rfl'

private theorem leaf1434CoversExact : CoversExact 8
    leaf1434Box leaf1434Certificate leaf1434InnerLog leaf1434Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk135RoundedFacts chi98RoundedFacts
    innerPair21RoundedFacts leaf1434RoundedFacts (by rfl)

private theorem leaf1434FlatSound : Sound leaf1434Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1434CertificateValid
    leaf1434InnerLogValid leaf1434CoversExact leaf1434LowerChecked

private noncomputable def leaf1435Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (7/64), chiHi := (15/128) }

private noncomputable def leaf1435Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435685/268435456) }, vSqrt := { lower := (65529/65536), upper := (986896/986873) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (359229813/268435456) }, upper := { exponent := 0, mantissa := (1399/1024) } }, logOuter := sk136LogOuterCertificate, logK := sk136LogKCertificate, logChi := chi98LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (1973769/1973746) } }, logDArg := sk136LogDArgCertificate }

private noncomputable def leaf1435InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1435LocalValidity :
    LeafFacts leaf1435Box leaf1435Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1435Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (986896/986873) }) = true
      norm_num [leaf1435Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1435CertificateValid :
    WideCertificateValid leaf1435Box leaf1435Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk136ValidityFacts chi98ValidityFacts
    leaf1435LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1435CoverageChecked :
    coverageCheck (innerAD leaf1435Box) leaf1435InnerLog = true := by
  rfl'

private theorem leaf1435InnerLogValid :
    leaf1435InnerLog.Valid 8 (innerAD leaf1435Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1435CoverageChecked

private noncomputable def leaf1435InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907319/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1435InputLogOnePlusV_eq :
    leaf1435InputLogOnePlusV = outerEnclosure 24
      (leaf1435Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1435RoundedFacts : LeafRoundedFacts 8
    leaf1435Certificate.logOnePlusV leaf1435InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1435InputLogOnePlusV_eq }

private noncomputable def leaf1435Inputs : Inputs :=
  inputsOfCaches globalInput sk136RoundedInputs
    chi98InputQChi innerPair21Input
    leaf1435InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1435LowerChecked :
    lowerCheck 24 leaf1435Box leaf1435Inputs = true := by
  rfl'

private theorem leaf1435CoversExact : CoversExact 8
    leaf1435Box leaf1435Certificate leaf1435InnerLog leaf1435Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk136RoundedFacts chi98RoundedFacts
    innerPair21RoundedFacts leaf1435RoundedFacts (by rfl)

private theorem leaf1435FlatSound : Sound leaf1435Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1435CertificateValid
    leaf1435InnerLogValid leaf1435CoversExact leaf1435LowerChecked

private noncomputable def leaf1436Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (15/128), chiHi := (1/8) }

private noncomputable def leaf1436Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435685/268435456) }, vSqrt := { lower := (65529/65536), upper := (4194308/4194205) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (364734501/268435456) }, upper := { exponent := 0, mantissa := (355/256) } }, logOuter := sk135LogOuterCertificate, logK := sk135LogKCertificate, logChi := chi99LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (8388513/8388410) } }, logDArg := sk135LogDArgCertificate }

private noncomputable def leaf1436InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf1436LocalValidity :
    LeafFacts leaf1436Box leaf1436Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1436Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4194308/4194205) }) = true
      norm_num [leaf1436Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1436CertificateValid :
    WideCertificateValid leaf1436Box leaf1436Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk135ValidityFacts chi99ValidityFacts
    leaf1436LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1436CoverageChecked :
    coverageCheck (innerAD leaf1436Box) leaf1436InnerLog = true := by
  rfl'

private theorem leaf1436InnerLogValid :
    leaf1436InnerLog.Valid 8 (innerAD leaf1436Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf1436CoverageChecked

private noncomputable def leaf1436InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629287/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1436InputLogOnePlusV_eq :
    leaf1436InputLogOnePlusV = outerEnclosure 24
      (leaf1436Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1436RoundedFacts : LeafRoundedFacts 8
    leaf1436Certificate.logOnePlusV leaf1436InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1436InputLogOnePlusV_eq }

private noncomputable def leaf1436Inputs : Inputs :=
  inputsOfCaches globalInput sk135RoundedInputs
    chi99InputQChi innerPair22Input
    leaf1436InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1436LowerChecked :
    lowerCheck 24 leaf1436Box leaf1436Inputs = true := by
  rfl'

private theorem leaf1436CoversExact : CoversExact 8
    leaf1436Box leaf1436Certificate leaf1436InnerLog leaf1436Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk135RoundedFacts chi99RoundedFacts
    innerPair22RoundedFacts leaf1436RoundedFacts (by rfl)

private theorem leaf1436FlatSound : Sound leaf1436Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1436CertificateValid
    leaf1436InnerLogValid leaf1436CoversExact leaf1436LowerChecked

private noncomputable def leaf1437Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (15/128), chiHi := (1/8) }

private noncomputable def leaf1437Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435687/268435456) }, vSqrt := { lower := (65529/65536), upper := (1048577/1048551) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (365717479/268435456) }, upper := { exponent := 0, mantissa := (89/64) } }, logOuter := sk136LogOuterCertificate, logK := sk136LogKCertificate, logChi := chi99LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (1048564/1048551) } }, logDArg := sk136LogDArgCertificate }

private noncomputable def leaf1437InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf1437LocalValidity :
    LeafFacts leaf1437Box leaf1437Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1437Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (1048577/1048551) }) = true
      norm_num [leaf1437Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1437CertificateValid :
    WideCertificateValid leaf1437Box leaf1437Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk136ValidityFacts chi99ValidityFacts
    leaf1437LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1437CoverageChecked :
    coverageCheck (innerAD leaf1437Box) leaf1437InnerLog = true := by
  rfl'

private theorem leaf1437InnerLogValid :
    leaf1437InnerLog.Valid 8 (innerAD leaf1437Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf1437CoverageChecked

private noncomputable def leaf1437InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629289/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1437InputLogOnePlusV_eq :
    leaf1437InputLogOnePlusV = outerEnclosure 24
      (leaf1437Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1437RoundedFacts : LeafRoundedFacts 8
    leaf1437Certificate.logOnePlusV leaf1437InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1437InputLogOnePlusV_eq }

private noncomputable def leaf1437Inputs : Inputs :=
  inputsOfCaches globalInput sk136RoundedInputs
    chi99InputQChi innerPair22Input
    leaf1437InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1437LowerChecked :
    lowerCheck 24 leaf1437Box leaf1437Inputs = true := by
  rfl'

private theorem leaf1437CoversExact : CoversExact 8
    leaf1437Box leaf1437Certificate leaf1437InnerLog leaf1437Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk136RoundedFacts chi99RoundedFacts
    innerPair22RoundedFacts leaf1437RoundedFacts (by rfl)

private theorem leaf1437FlatSound : Sound leaf1437Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1437CertificateValid
    leaf1437InnerLogValid leaf1437CoversExact leaf1437LowerChecked

private noncomputable def leaf1438Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (3/32), chiHi := (25/256) }

private noncomputable def leaf1438Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435607/268435456) }, vSqrt := { lower := (65529/65536), upper := (67108992/67107589) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (347040939/268435456) }, upper := { exponent := 0, mantissa := (5371/4096) } }, logOuter := sk125LogOuterCertificate, logK := sk125LogKCertificate, logChi := chi131LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (134216581/134215178) } }, logDArg := sk125LogDArgCertificate }

private noncomputable def leaf1438InnerLog : WideLogData :=
  innerPair141Data

set_option maxRecDepth 1000000 in
private theorem leaf1438LocalValidity :
    LeafFacts leaf1438Box leaf1438Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1438Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (67108992/67107589) }) = true
      norm_num [leaf1438Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1438CertificateValid :
    WideCertificateValid leaf1438Box leaf1438Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk125ValidityFacts chi131ValidityFacts
    leaf1438LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1438CoverageChecked :
    coverageCheck (innerAD leaf1438Box) leaf1438InnerLog = true := by
  rfl'

private theorem leaf1438InnerLogValid :
    leaf1438InnerLog.Valid 8 (innerAD leaf1438Box) :=
  wideLogDataValid_of_cachedCheck endpoint35PositiveFacts
    endpoint147PositiveFacts.valid leaf1438CoverageChecked

private noncomputable def leaf1438InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453657/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf1438InputLogOnePlusV_eq :
    leaf1438InputLogOnePlusV = outerEnclosure 24
      (leaf1438Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1438RoundedFacts : LeafRoundedFacts 8
    leaf1438Certificate.logOnePlusV leaf1438InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1438InputLogOnePlusV_eq }

private noncomputable def leaf1438Inputs : Inputs :=
  inputsOfCaches globalInput sk125RoundedInputs
    chi131InputQChi innerPair141Input
    leaf1438InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1438LowerChecked :
    lowerCheck 24 leaf1438Box leaf1438Inputs = true := by
  rfl'

private theorem leaf1438CoversExact : CoversExact 8
    leaf1438Box leaf1438Certificate leaf1438InnerLog leaf1438Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk125RoundedFacts chi131RoundedFacts
    innerPair141RoundedFacts leaf1438RoundedFacts (by rfl)

private theorem leaf1438FlatSound : Sound leaf1438Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1438CertificateValid
    leaf1438InnerLogValid leaf1438CoversExact leaf1438LowerChecked

private noncomputable def leaf1439Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (25/256), chiHi := (13/128) }

private noncomputable def leaf1439Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871165/536870912) }, vSqrt := { lower := (65529/65536), upper := (3947584/3947503) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (700667893/536870912) }, upper := { exponent := 0, mantissa := (5409/4096) } }, logOuter := sk137LogOuterCertificate, logK := sk137LogKCertificate, logChi := chi132LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (7895087/7895006) } }, logDArg := sk137LogDArgCertificate }

private noncomputable def leaf1439InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf1439LocalValidity :
    LeafFacts leaf1439Box leaf1439Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1439Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (3947584/3947503) }) = true
      norm_num [leaf1439Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1439CertificateValid :
    WideCertificateValid leaf1439Box leaf1439Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk137ValidityFacts chi132ValidityFacts
    leaf1439LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1439CoverageChecked :
    coverageCheck (innerAD leaf1439Box) leaf1439InnerLog = true := by
  rfl'

private theorem leaf1439InnerLogValid :
    leaf1439InnerLog.Valid 8 (innerAD leaf1439Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf1439CoverageChecked

private noncomputable def leaf1439InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629253/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1439InputLogOnePlusV_eq :
    leaf1439InputLogOnePlusV = outerEnclosure 24
      (leaf1439Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1439RoundedFacts : LeafRoundedFacts 8
    leaf1439Certificate.logOnePlusV leaf1439InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1439InputLogOnePlusV_eq }

private noncomputable def leaf1439Inputs : Inputs :=
  inputsOfCaches globalInput sk137RoundedInputs
    chi132InputQChi innerPair17Input
    leaf1439InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1439LowerChecked :
    lowerCheck 24 leaf1439Box leaf1439Inputs = true := by
  rfl'

private theorem leaf1439CoversExact : CoversExact 8
    leaf1439Box leaf1439Certificate leaf1439InnerLog leaf1439Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk137RoundedFacts chi132RoundedFacts
    innerPair17RoundedFacts leaf1439RoundedFacts (by rfl)

private theorem leaf1439FlatSound : Sound leaf1439Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1439CertificateValid
    leaf1439InnerLogValid leaf1439CoversExact leaf1439LowerChecked

private noncomputable def leaf1440Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (25/256), chiHi := (13/128) }

private noncomputable def leaf1440Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871167/536870912) }, vSqrt := { lower := (65529/65536), upper := (33554464/33553769) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (702306191/536870912) }, upper := { exponent := 0, mantissa := (2711/2048) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi132LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (67108233/67107538) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf1440InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf1440LocalValidity :
    LeafFacts leaf1440Box leaf1440Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1440Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (33554464/33553769) }) = true
      norm_num [leaf1440Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1440CertificateValid :
    WideCertificateValid leaf1440Box leaf1440Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi132ValidityFacts
    leaf1440LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1440CoverageChecked :
    coverageCheck (innerAD leaf1440Box) leaf1440InnerLog = true := by
  rfl'

private theorem leaf1440InnerLogValid :
    leaf1440InnerLog.Valid 8 (innerAD leaf1440Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf1440CoverageChecked

private noncomputable def leaf1440InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814627/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1440InputLogOnePlusV_eq :
    leaf1440InputLogOnePlusV = outerEnclosure 24
      (leaf1440Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1440RoundedFacts : LeafRoundedFacts 8
    leaf1440Certificate.logOnePlusV leaf1440InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1440InputLogOnePlusV_eq }

private noncomputable def leaf1440Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi132InputQChi innerPair17Input
    leaf1440InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1440LowerChecked :
    lowerCheck 24 leaf1440Box leaf1440Inputs = true := by
  rfl'

private theorem leaf1440CoversExact : CoversExact 8
    leaf1440Box leaf1440Certificate leaf1440InnerLog leaf1440Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi132RoundedFacts
    innerPair17RoundedFacts leaf1440RoundedFacts (by rfl)

private theorem leaf1440FlatSound : Sound leaf1440Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1440CertificateValid
    leaf1440InnerLogValid leaf1440CoversExact leaf1440LowerChecked

private noncomputable def leaf1441Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (13/128), chiHi := (27/256) }

private noncomputable def leaf1441Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871167/536870912) }, vSqrt := { lower := (65529/65536), upper := (134217856/134215001) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (707221091/536870912) }, upper := { exponent := 0, mantissa := (10919/8192) } }, logOuter := sk137LogOuterCertificate, logK := sk137LogKCertificate, logChi := chi149LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (268432857/268430002) } }, logDArg := sk137LogDArgCertificate }

private noncomputable def leaf1441InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1441LocalValidity :
    LeafFacts leaf1441Box leaf1441Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1441Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (134217856/134215001) }) = true
      norm_num [leaf1441Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1441CertificateValid :
    WideCertificateValid leaf1441Box leaf1441Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk137ValidityFacts chi149ValidityFacts
    leaf1441LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1441CoverageChecked :
    coverageCheck (innerAD leaf1441Box) leaf1441InnerLog = true := by
  rfl'

private theorem leaf1441InnerLogValid :
    leaf1441InnerLog.Valid 8 (innerAD leaf1441Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1441CoverageChecked

private noncomputable def leaf1441InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629259/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1441InputLogOnePlusV_eq :
    leaf1441InputLogOnePlusV = outerEnclosure 24
      (leaf1441Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1441RoundedFacts : LeafRoundedFacts 8
    leaf1441Certificate.logOnePlusV leaf1441InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1441InputLogOnePlusV_eq }

private noncomputable def leaf1441Inputs : Inputs :=
  inputsOfCaches globalInput sk137RoundedInputs
    chi149InputQChi innerPair21Input
    leaf1441InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1441LowerChecked :
    lowerCheck 24 leaf1441Box leaf1441Inputs = true := by
  rfl'

private theorem leaf1441CoversExact : CoversExact 8
    leaf1441Box leaf1441Certificate leaf1441InnerLog leaf1441Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk137RoundedFacts chi149RoundedFacts
    innerPair21RoundedFacts leaf1441RoundedFacts (by rfl)

private theorem leaf1441FlatSound : Sound leaf1441Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1441CertificateValid
    leaf1441InnerLogValid leaf1441CoversExact leaf1441LowerChecked

private noncomputable def leaf1442Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (13/128), chiHi := (27/256) }

private noncomputable def leaf1442Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871169/536870912) }, vSqrt := { lower := (65529/65536), upper := (67108928/67107487) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (708924921/536870912) }, upper := { exponent := 0, mantissa := (5473/4096) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi149LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (134216415/134214974) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf1442InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1442LocalValidity :
    LeafFacts leaf1442Box leaf1442Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1442Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (67108928/67107487) }) = true
      norm_num [leaf1442Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1442CertificateValid :
    WideCertificateValid leaf1442Box leaf1442Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi149ValidityFacts
    leaf1442LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1442CoverageChecked :
    coverageCheck (innerAD leaf1442Box) leaf1442InnerLog = true := by
  rfl'

private theorem leaf1442InnerLogValid :
    leaf1442InnerLog.Valid 8 (innerAD leaf1442Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1442CoverageChecked

private noncomputable def leaf1442InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629261/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1442InputLogOnePlusV_eq :
    leaf1442InputLogOnePlusV = outerEnclosure 24
      (leaf1442Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1442RoundedFacts : LeafRoundedFacts 8
    leaf1442Certificate.logOnePlusV leaf1442InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1442InputLogOnePlusV_eq }

private noncomputable def leaf1442Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi149InputQChi innerPair21Input
    leaf1442InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1442LowerChecked :
    lowerCheck 24 leaf1442Box leaf1442Inputs = true := by
  rfl'

private theorem leaf1442CoversExact : CoversExact 8
    leaf1442Box leaf1442Certificate leaf1442InnerLog leaf1442Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi149RoundedFacts
    innerPair21RoundedFacts leaf1442RoundedFacts (by rfl)

private theorem leaf1442FlatSound : Sound leaf1442Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1442CertificateValid
    leaf1442InnerLogValid leaf1442CoversExact leaf1442LowerChecked

private noncomputable def leaf1443Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (27/256), chiHi := (7/64) }

private noncomputable def leaf1443Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871169/536870912) }, vSqrt := { lower := (65529/65536), upper := (33554464/33553725) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (713774289/536870912) }, upper := { exponent := 0, mantissa := (2755/2048) } }, logOuter := sk137LogOuterCertificate, logK := sk137LogKCertificate, logChi := chi150LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (67108189/67107450) } }, logDArg := sk137LogDArgCertificate }

private noncomputable def leaf1443InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1443LocalValidity :
    LeafFacts leaf1443Box leaf1443Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1443Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (33554464/33553725) }) = true
      norm_num [leaf1443Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1443CertificateValid :
    WideCertificateValid leaf1443Box leaf1443Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk137ValidityFacts chi150ValidityFacts
    leaf1443LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1443CoverageChecked :
    coverageCheck (innerAD leaf1443Box) leaf1443InnerLog = true := by
  rfl'

private theorem leaf1443InnerLogValid :
    leaf1443InnerLog.Valid 8 (innerAD leaf1443Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1443CoverageChecked

private noncomputable def leaf1443InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629265/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1443InputLogOnePlusV_eq :
    leaf1443InputLogOnePlusV = outerEnclosure 24
      (leaf1443Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1443RoundedFacts : LeafRoundedFacts 8
    leaf1443Certificate.logOnePlusV leaf1443InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1443InputLogOnePlusV_eq }

private noncomputable def leaf1443Inputs : Inputs :=
  inputsOfCaches globalInput sk137RoundedInputs
    chi150InputQChi innerPair21Input
    leaf1443InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1443LowerChecked :
    lowerCheck 24 leaf1443Box leaf1443Inputs = true := by
  rfl'

private theorem leaf1443CoversExact : CoversExact 8
    leaf1443Box leaf1443Certificate leaf1443InnerLog leaf1443Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk137RoundedFacts chi150RoundedFacts
    innerPair21RoundedFacts leaf1443RoundedFacts (by rfl)

private theorem leaf1443FlatSound : Sound leaf1443Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1443CertificateValid
    leaf1443InnerLogValid leaf1443CoversExact leaf1443LowerChecked

private noncomputable def leaf1444Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (27/256), chiHi := (7/64) }

private noncomputable def leaf1444Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871171/536870912) }, vSqrt := { lower := (65529/65536), upper := (16777232/16776859) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (715543651/536870912) }, upper := { exponent := 0, mantissa := (1381/1024) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi150LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (33554091/33553718) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf1444InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1444LocalValidity :
    LeafFacts leaf1444Box leaf1444Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1444Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (16777232/16776859) }) = true
      norm_num [leaf1444Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1444CertificateValid :
    WideCertificateValid leaf1444Box leaf1444Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi150ValidityFacts
    leaf1444LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1444CoverageChecked :
    coverageCheck (innerAD leaf1444Box) leaf1444InnerLog = true := by
  rfl'

private theorem leaf1444InnerLogValid :
    leaf1444InnerLog.Valid 8 (innerAD leaf1444Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1444CoverageChecked

private noncomputable def leaf1444InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629267/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1444InputLogOnePlusV_eq :
    leaf1444InputLogOnePlusV = outerEnclosure 24
      (leaf1444Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1444RoundedFacts : LeafRoundedFacts 8
    leaf1444Certificate.logOnePlusV leaf1444InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1444InputLogOnePlusV_eq }

private noncomputable def leaf1444Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi150InputQChi innerPair21Input
    leaf1444InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1444LowerChecked :
    lowerCheck 24 leaf1444Box leaf1444Inputs = true := by
  rfl'

private theorem leaf1444CoversExact : CoversExact 8
    leaf1444Box leaf1444Certificate leaf1444InnerLog leaf1444Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi150RoundedFacts
    innerPair21RoundedFacts leaf1444RoundedFacts (by rfl)

private theorem leaf1444FlatSound : Sound leaf1444Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1444CertificateValid
    leaf1444InnerLogValid leaf1444CoversExact leaf1444LowerChecked

private noncomputable def leaf1445Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (3/32), chiHi := (25/256) }

private noncomputable def leaf1445Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871167/536870912) }, vSqrt := { lower := (65529/65536), upper := (7895168/7895009) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (697260227/536870912) }, upper := { exponent := 0, mantissa := (10767/8192) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi131LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (15790177/15790018) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf1445InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf1445LocalValidity :
    LeafFacts leaf1445Box leaf1445Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1445Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (7895168/7895009) }) = true
      norm_num [leaf1445Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1445CertificateValid :
    WideCertificateValid leaf1445Box leaf1445Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi131ValidityFacts
    leaf1445LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1445CoverageChecked :
    coverageCheck (innerAD leaf1445Box) leaf1445InnerLog = true := by
  rfl'

private theorem leaf1445InnerLogValid :
    leaf1445InnerLog.Valid 8 (innerAD leaf1445Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf1445CoverageChecked

private noncomputable def leaf1445InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814625/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1445InputLogOnePlusV_eq :
    leaf1445InputLogOnePlusV = outerEnclosure 24
      (leaf1445Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1445RoundedFacts : LeafRoundedFacts 8
    leaf1445Certificate.logOnePlusV leaf1445InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1445InputLogOnePlusV_eq }

private noncomputable def leaf1445Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi131InputQChi innerPair17Input
    leaf1445InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1445LowerChecked :
    lowerCheck 24 leaf1445Box leaf1445Inputs = true := by
  rfl'

private theorem leaf1445CoversExact : CoversExact 8
    leaf1445Box leaf1445Certificate leaf1445InnerLog leaf1445Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi131RoundedFacts
    innerPair17RoundedFacts leaf1445RoundedFacts (by rfl)

private theorem leaf1445FlatSound : Sound leaf1445Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1445CertificateValid
    leaf1445InnerLogValid leaf1445CoversExact leaf1445LowerChecked

private noncomputable def leaf1446Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (3/32), chiHi := (25/256) }

private noncomputable def leaf1446Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871169/536870912) }, vSqrt := { lower := (65529/65536), upper := (16777232/16776891) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (698832993/536870912) }, upper := { exponent := 0, mantissa := (1349/1024) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi131LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (33554123/33553782) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf1446InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf1446LocalValidity :
    LeafFacts leaf1446Box leaf1446Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1446Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (16777232/16776891) }) = true
      norm_num [leaf1446Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1446CertificateValid :
    WideCertificateValid leaf1446Box leaf1446Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi131ValidityFacts
    leaf1446LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1446CoverageChecked :
    coverageCheck (innerAD leaf1446Box) leaf1446InnerLog = true := by
  rfl'

private theorem leaf1446InnerLogValid :
    leaf1446InnerLog.Valid 8 (innerAD leaf1446Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf1446CoverageChecked

private noncomputable def leaf1446InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629251/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1446InputLogOnePlusV_eq :
    leaf1446InputLogOnePlusV = outerEnclosure 24
      (leaf1446Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1446RoundedFacts : LeafRoundedFacts 8
    leaf1446Certificate.logOnePlusV leaf1446InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1446InputLogOnePlusV_eq }

private noncomputable def leaf1446Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi131InputQChi innerPair17Input
    leaf1446InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1446LowerChecked :
    lowerCheck 24 leaf1446Box leaf1446Inputs = true := by
  rfl'

private theorem leaf1446CoversExact : CoversExact 8
    leaf1446Box leaf1446Certificate leaf1446InnerLog leaf1446Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi131RoundedFacts
    innerPair17RoundedFacts leaf1446RoundedFacts (by rfl)

private theorem leaf1446FlatSound : Sound leaf1446Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1446CertificateValid
    leaf1446InnerLogValid leaf1446CoversExact leaf1446LowerChecked

private noncomputable def leaf1447Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (25/256), chiHi := (13/128) }

private noncomputable def leaf1447Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871169/536870912) }, vSqrt := { lower := (65529/65536), upper := (67108928/67107525) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (703944489/536870912) }, upper := { exponent := 0, mantissa := (5435/4096) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi132LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (134216453/134215050) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf1447InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf1447LocalValidity :
    LeafFacts leaf1447Box leaf1447Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1447Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (67108928/67107525) }) = true
      norm_num [leaf1447Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1447CertificateValid :
    WideCertificateValid leaf1447Box leaf1447Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi132ValidityFacts
    leaf1447LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1447CoverageChecked :
    coverageCheck (innerAD leaf1447Box) leaf1447InnerLog = true := by
  rfl'

private theorem leaf1447InnerLogValid :
    leaf1447InnerLog.Valid 8 (innerAD leaf1447Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf1447CoverageChecked

private noncomputable def leaf1447InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453657/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf1447InputLogOnePlusV_eq :
    leaf1447InputLogOnePlusV = outerEnclosure 24
      (leaf1447Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1447RoundedFacts : LeafRoundedFacts 8
    leaf1447Certificate.logOnePlusV leaf1447InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1447InputLogOnePlusV_eq }

private noncomputable def leaf1447Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi132InputQChi innerPair17Input
    leaf1447InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1447LowerChecked :
    lowerCheck 24 leaf1447Box leaf1447Inputs = true := by
  rfl'

private theorem leaf1447CoversExact : CoversExact 8
    leaf1447Box leaf1447Certificate leaf1447InnerLog leaf1447Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi132RoundedFacts
    innerPair17RoundedFacts leaf1447RoundedFacts (by rfl)

private theorem leaf1447FlatSound : Sound leaf1447Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1447CertificateValid
    leaf1447InnerLogValid leaf1447CoversExact leaf1447LowerChecked

private noncomputable def leaf1448Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (25/256), chiHi := (13/128) }

private noncomputable def leaf1448Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871171/536870912) }, vSqrt := { lower := (65529/65536), upper := (8388616/8388439) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (705582787/536870912) }, upper := { exponent := 0, mantissa := (681/512) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi132LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (16777055/16776878) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf1448InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1448LocalValidity :
    LeafFacts leaf1448Box leaf1448Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1448Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8388616/8388439) }) = true
      norm_num [leaf1448Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1448CertificateValid :
    WideCertificateValid leaf1448Box leaf1448Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi132ValidityFacts
    leaf1448LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1448CoverageChecked :
    coverageCheck (innerAD leaf1448Box) leaf1448InnerLog = true := by
  rfl'

private theorem leaf1448InnerLogValid :
    leaf1448InnerLog.Valid 8 (innerAD leaf1448Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1448CoverageChecked

private noncomputable def leaf1448InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814629/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1448InputLogOnePlusV_eq :
    leaf1448InputLogOnePlusV = outerEnclosure 24
      (leaf1448Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1448RoundedFacts : LeafRoundedFacts 8
    leaf1448Certificate.logOnePlusV leaf1448InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1448InputLogOnePlusV_eq }

private noncomputable def leaf1448Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi132InputQChi innerPair21Input
    leaf1448InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1448LowerChecked :
    lowerCheck 24 leaf1448Box leaf1448Inputs = true := by
  rfl'

private theorem leaf1448CoversExact : CoversExact 8
    leaf1448Box leaf1448Certificate leaf1448InnerLog leaf1448Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi132RoundedFacts
    innerPair21RoundedFacts leaf1448RoundedFacts (by rfl)

private theorem leaf1448FlatSound : Sound leaf1448Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1448CertificateValid
    leaf1448InnerLogValid leaf1448CoversExact leaf1448LowerChecked

private noncomputable def leaf1449Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (13/128), chiHi := (27/256) }

private noncomputable def leaf1449Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871171/536870912) }, vSqrt := { lower := (65529/65536), upper := (134217856/134214947) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (710628751/536870912) }, upper := { exponent := 0, mantissa := (10973/8192) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi149LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (268432803/268429894) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf1449InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1449LocalValidity :
    LeafFacts leaf1449Box leaf1449Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1449Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (134217856/134214947) }) = true
      norm_num [leaf1449Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1449CertificateValid :
    WideCertificateValid leaf1449Box leaf1449Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi149ValidityFacts
    leaf1449LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1449CoverageChecked :
    coverageCheck (innerAD leaf1449Box) leaf1449InnerLog = true := by
  rfl'

private theorem leaf1449InnerLogValid :
    leaf1449InnerLog.Valid 8 (innerAD leaf1449Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1449CoverageChecked

private noncomputable def leaf1449InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629263/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1449InputLogOnePlusV_eq :
    leaf1449InputLogOnePlusV = outerEnclosure 24
      (leaf1449Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1449RoundedFacts : LeafRoundedFacts 8
    leaf1449Certificate.logOnePlusV leaf1449InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1449InputLogOnePlusV_eq }

private noncomputable def leaf1449Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi149InputQChi innerPair21Input
    leaf1449InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1449LowerChecked :
    lowerCheck 24 leaf1449Box leaf1449Inputs = true := by
  rfl'

private theorem leaf1449CoversExact : CoversExact 8
    leaf1449Box leaf1449Certificate leaf1449InnerLog leaf1449Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi149RoundedFacts
    innerPair21RoundedFacts leaf1449RoundedFacts (by rfl)

private theorem leaf1449FlatSound : Sound leaf1449Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1449CertificateValid
    leaf1449InnerLogValid leaf1449CoversExact leaf1449LowerChecked

private noncomputable def leaf1450Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (13/128), chiHi := (27/256) }

private noncomputable def leaf1450Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871173/536870912) }, vSqrt := { lower := (65529/65536), upper := (16777232/16776865) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (712332581/536870912) }, upper := { exponent := 0, mantissa := (1375/1024) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi149LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (33554097/33553730) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf1450InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1450LocalValidity :
    LeafFacts leaf1450Box leaf1450Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1450Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (16777232/16776865) }) = true
      norm_num [leaf1450Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1450CertificateValid :
    WideCertificateValid leaf1450Box leaf1450Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi149ValidityFacts
    leaf1450LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1450CoverageChecked :
    coverageCheck (innerAD leaf1450Box) leaf1450InnerLog = true := by
  rfl'

private theorem leaf1450InnerLogValid :
    leaf1450InnerLog.Valid 8 (innerAD leaf1450Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1450CoverageChecked

private noncomputable def leaf1450InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (726829/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf1450InputLogOnePlusV_eq :
    leaf1450InputLogOnePlusV = outerEnclosure 24
      (leaf1450Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1450RoundedFacts : LeafRoundedFacts 8
    leaf1450Certificate.logOnePlusV leaf1450InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1450InputLogOnePlusV_eq }

private noncomputable def leaf1450Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi149InputQChi innerPair21Input
    leaf1450InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1450LowerChecked :
    lowerCheck 24 leaf1450Box leaf1450Inputs = true := by
  rfl'

private theorem leaf1450CoversExact : CoversExact 8
    leaf1450Box leaf1450Certificate leaf1450InnerLog leaf1450Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi149RoundedFacts
    innerPair21RoundedFacts leaf1450RoundedFacts (by rfl)

private theorem leaf1450FlatSound : Sound leaf1450Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1450CertificateValid
    leaf1450InnerLogValid leaf1450CoversExact leaf1450LowerChecked

private noncomputable def leaf1451Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (27/256), chiHi := (7/64) }

private noncomputable def leaf1451Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871173/536870912) }, vSqrt := { lower := (65529/65536), upper := (33554464/33553711) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (717313013/536870912) }, upper := { exponent := 0, mantissa := (2769/2048) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi150LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (67108175/67107422) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf1451InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1451LocalValidity :
    LeafFacts leaf1451Box leaf1451Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1451Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (33554464/33553711) }) = true
      norm_num [leaf1451Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1451CertificateValid :
    WideCertificateValid leaf1451Box leaf1451Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi150ValidityFacts
    leaf1451LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1451CoverageChecked :
    coverageCheck (innerAD leaf1451Box) leaf1451InnerLog = true := by
  rfl'

private theorem leaf1451InnerLogValid :
    leaf1451InnerLog.Valid 8 (innerAD leaf1451Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1451CoverageChecked

private noncomputable def leaf1451InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629269/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1451InputLogOnePlusV_eq :
    leaf1451InputLogOnePlusV = outerEnclosure 24
      (leaf1451Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1451RoundedFacts : LeafRoundedFacts 8
    leaf1451Certificate.logOnePlusV leaf1451InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1451InputLogOnePlusV_eq }

private noncomputable def leaf1451Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi150InputQChi innerPair21Input
    leaf1451InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1451LowerChecked :
    lowerCheck 24 leaf1451Box leaf1451Inputs = true := by
  rfl'

private theorem leaf1451CoversExact : CoversExact 8
    leaf1451Box leaf1451Certificate leaf1451InnerLog leaf1451Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi150RoundedFacts
    innerPair21RoundedFacts leaf1451RoundedFacts (by rfl)

private theorem leaf1451FlatSound : Sound leaf1451Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1451CertificateValid
    leaf1451InnerLogValid leaf1451CoversExact leaf1451LowerChecked

private noncomputable def leaf1452Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (27/256), chiHi := (7/64) }

private noncomputable def leaf1452Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871175/536870912) }, vSqrt := { lower := (65529/65536), upper := (4194308/4194213) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (719082375/536870912) }, upper := { exponent := 0, mantissa := (347/256) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi150LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (8388521/8388426) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf1452InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1452LocalValidity :
    LeafFacts leaf1452Box leaf1452Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1452Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4194308/4194213) }) = true
      norm_num [leaf1452Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1452CertificateValid :
    WideCertificateValid leaf1452Box leaf1452Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi150ValidityFacts
    leaf1452LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1452CoverageChecked :
    coverageCheck (innerAD leaf1452Box) leaf1452InnerLog = true := by
  rfl'

private theorem leaf1452InnerLogValid :
    leaf1452InnerLog.Valid 8 (innerAD leaf1452Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1452CoverageChecked

private noncomputable def leaf1452InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629271/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1452InputLogOnePlusV_eq :
    leaf1452InputLogOnePlusV = outerEnclosure 24
      (leaf1452Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1452RoundedFacts : LeafRoundedFacts 8
    leaf1452Certificate.logOnePlusV leaf1452InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1452InputLogOnePlusV_eq }

private noncomputable def leaf1452Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi150InputQChi innerPair21Input
    leaf1452InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1452LowerChecked :
    lowerCheck 24 leaf1452Box leaf1452Inputs = true := by
  rfl'

private theorem leaf1452CoversExact : CoversExact 8
    leaf1452Box leaf1452Certificate leaf1452InnerLog leaf1452Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi150RoundedFacts
    innerPair21RoundedFacts leaf1452RoundedFacts (by rfl)

private theorem leaf1452FlatSound : Sound leaf1452Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1452CertificateValid
    leaf1452InnerLogValid leaf1452CoversExact leaf1452LowerChecked

private noncomputable def leaf1453Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (7/64), chiHi := (15/128) }

private noncomputable def leaf1453Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435687/268435456) }, vSqrt := { lower := (65529/65536), upper := (67108928/67107349) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (360147259/268435456) }, upper := { exponent := 0, mantissa := (5611/4096) } }, logOuter := sk137LogOuterCertificate, logK := sk137LogKCertificate, logChi := chi98LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (134216277/134214698) } }, logDArg := sk137LogDArgCertificate }

private noncomputable def leaf1453InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1453LocalValidity :
    LeafFacts leaf1453Box leaf1453Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1453Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (67108928/67107349) }) = true
      norm_num [leaf1453Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1453CertificateValid :
    WideCertificateValid leaf1453Box leaf1453Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk137ValidityFacts chi98ValidityFacts
    leaf1453LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1453CoverageChecked :
    coverageCheck (innerAD leaf1453Box) leaf1453InnerLog = true := by
  rfl'

private theorem leaf1453InnerLogValid :
    leaf1453InnerLog.Valid 8 (innerAD leaf1453Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1453CoverageChecked

private noncomputable def leaf1453InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814639/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1453InputLogOnePlusV_eq :
    leaf1453InputLogOnePlusV = outerEnclosure 24
      (leaf1453Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1453RoundedFacts : LeafRoundedFacts 8
    leaf1453Certificate.logOnePlusV leaf1453InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1453InputLogOnePlusV_eq }

private noncomputable def leaf1453Inputs : Inputs :=
  inputsOfCaches globalInput sk137RoundedInputs
    chi98InputQChi innerPair21Input
    leaf1453InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1453LowerChecked :
    lowerCheck 24 leaf1453Box leaf1453Inputs = true := by
  rfl'

private theorem leaf1453CoversExact : CoversExact 8
    leaf1453Box leaf1453Certificate leaf1453InnerLog leaf1453Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk137RoundedFacts chi98RoundedFacts
    innerPair21RoundedFacts leaf1453RoundedFacts (by rfl)

private theorem leaf1453FlatSound : Sound leaf1453Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1453CertificateValid
    leaf1453InnerLogValid leaf1453CoversExact leaf1453LowerChecked

private noncomputable def leaf1454Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (7/64), chiHi := (15/128) }

private noncomputable def leaf1454Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435689/268435456) }, vSqrt := { lower := (65529/65536), upper := (33554464/33553667) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (361064705/268435456) }, upper := { exponent := 0, mantissa := (2813/2048) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi98LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (67108131/67107334) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf1454InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1454LocalValidity :
    LeafFacts leaf1454Box leaf1454Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1454Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (33554464/33553667) }) = true
      norm_num [leaf1454Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1454CertificateValid :
    WideCertificateValid leaf1454Box leaf1454Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi98ValidityFacts
    leaf1454LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1454CoverageChecked :
    coverageCheck (innerAD leaf1454Box) leaf1454InnerLog = true := by
  rfl'

private theorem leaf1454InnerLogValid :
    leaf1454InnerLog.Valid 8 (innerAD leaf1454Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1454CoverageChecked

private noncomputable def leaf1454InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (363415/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf1454InputLogOnePlusV_eq :
    leaf1454InputLogOnePlusV = outerEnclosure 24
      (leaf1454Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1454RoundedFacts : LeafRoundedFacts 8
    leaf1454Certificate.logOnePlusV leaf1454InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1454InputLogOnePlusV_eq }

private noncomputable def leaf1454Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi98InputQChi innerPair21Input
    leaf1454InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1454LowerChecked :
    lowerCheck 24 leaf1454Box leaf1454Inputs = true := by
  rfl'

private theorem leaf1454CoversExact : CoversExact 8
    leaf1454Box leaf1454Certificate leaf1454InnerLog leaf1454Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi98RoundedFacts
    innerPair21RoundedFacts leaf1454RoundedFacts (by rfl)

private theorem leaf1454FlatSound : Sound leaf1454Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1454CertificateValid
    leaf1454InnerLogValid leaf1454CoversExact leaf1454LowerChecked

private noncomputable def leaf1455Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (15/128), chiHi := (1/8) }

private noncomputable def leaf1455Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435689/268435456) }, vSqrt := { lower := (65529/65536), upper := (4194308/4194203) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (366700457/268435456) }, upper := { exponent := 0, mantissa := (357/256) } }, logOuter := sk137LogOuterCertificate, logK := sk137LogKCertificate, logChi := chi99LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (8388511/8388406) } }, logDArg := sk137LogDArgCertificate }

private noncomputable def leaf1455InnerLog : WideLogData :=
  innerPair133Data

set_option maxRecDepth 1000000 in
private theorem leaf1455LocalValidity :
    LeafFacts leaf1455Box leaf1455Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1455Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4194308/4194203) }) = true
      norm_num [leaf1455Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1455CertificateValid :
    WideCertificateValid leaf1455Box leaf1455Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk137ValidityFacts chi99ValidityFacts
    leaf1455LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1455CoverageChecked :
    coverageCheck (innerAD leaf1455Box) leaf1455InnerLog = true := by
  rfl'

private theorem leaf1455InnerLogValid :
    leaf1455InnerLog.Valid 8 (innerAD leaf1455Box) :=
  wideLogDataValid_of_cachedCheck endpoint30PositiveFacts
    endpoint38PositiveFacts.valid leaf1455CoverageChecked

private noncomputable def leaf1455InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629291/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1455InputLogOnePlusV_eq :
    leaf1455InputLogOnePlusV = outerEnclosure 24
      (leaf1455Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1455RoundedFacts : LeafRoundedFacts 8
    leaf1455Certificate.logOnePlusV leaf1455InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1455InputLogOnePlusV_eq }

private noncomputable def leaf1455Inputs : Inputs :=
  inputsOfCaches globalInput sk137RoundedInputs
    chi99InputQChi innerPair133Input
    leaf1455InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1455LowerChecked :
    lowerCheck 24 leaf1455Box leaf1455Inputs = true := by
  rfl'

private theorem leaf1455CoversExact : CoversExact 8
    leaf1455Box leaf1455Certificate leaf1455InnerLog leaf1455Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk137RoundedFacts chi99RoundedFacts
    innerPair133RoundedFacts leaf1455RoundedFacts (by rfl)

private theorem leaf1455FlatSound : Sound leaf1455Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1455CertificateValid
    leaf1455InnerLogValid leaf1455CoversExact leaf1455LowerChecked

private noncomputable def leaf1456Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (15/128), chiHi := (1/8) }

private noncomputable def leaf1456Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435691/268435456) }, vSqrt := { lower := (65529/65536), upper := (2097154/2097101) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (367683435/268435456) }, upper := { exponent := 0, mantissa := (179/128) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi99LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (4194255/4194202) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf1456InnerLog : WideLogData :=
  innerPair133Data

set_option maxRecDepth 1000000 in
private theorem leaf1456LocalValidity :
    LeafFacts leaf1456Box leaf1456Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1456Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (2097154/2097101) }) = true
      norm_num [leaf1456Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1456CertificateValid :
    WideCertificateValid leaf1456Box leaf1456Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi99ValidityFacts
    leaf1456LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1456CoverageChecked :
    coverageCheck (innerAD leaf1456Box) leaf1456InnerLog = true := by
  rfl'

private theorem leaf1456InnerLogValid :
    leaf1456InnerLog.Valid 8 (innerAD leaf1456Box) :=
  wideLogDataValid_of_cachedCheck endpoint30PositiveFacts
    endpoint38PositiveFacts.valid leaf1456CoverageChecked

private noncomputable def leaf1456InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629293/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1456InputLogOnePlusV_eq :
    leaf1456InputLogOnePlusV = outerEnclosure 24
      (leaf1456Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1456RoundedFacts : LeafRoundedFacts 8
    leaf1456Certificate.logOnePlusV leaf1456InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1456InputLogOnePlusV_eq }

private noncomputable def leaf1456Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi99InputQChi innerPair133Input
    leaf1456InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1456LowerChecked :
    lowerCheck 24 leaf1456Box leaf1456Inputs = true := by
  rfl'

private theorem leaf1456CoversExact : CoversExact 8
    leaf1456Box leaf1456Certificate leaf1456InnerLog leaf1456Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi99RoundedFacts
    innerPair133RoundedFacts leaf1456RoundedFacts (by rfl)

private theorem leaf1456FlatSound : Sound leaf1456Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1456CertificateValid
    leaf1456InnerLogValid leaf1456CoversExact leaf1456LowerChecked

private noncomputable def leaf1457Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (7/64), chiHi := (15/128) }

private noncomputable def leaf1457Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435691/268435456) }, vSqrt := { lower := (65529/65536), upper := (67108928/67107319) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (361982151/268435456) }, upper := { exponent := 0, mantissa := (5641/4096) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi98LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (134216247/134214638) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf1457InnerLog : WideLogData :=
  innerPair142Data

set_option maxRecDepth 1000000 in
private theorem leaf1457LocalValidity :
    LeafFacts leaf1457Box leaf1457Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1457Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (67108928/67107319) }) = true
      norm_num [leaf1457Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1457CertificateValid :
    WideCertificateValid leaf1457Box leaf1457Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi98ValidityFacts
    leaf1457LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1457CoverageChecked :
    coverageCheck (innerAD leaf1457Box) leaf1457InnerLog = true := by
  rfl'

private theorem leaf1457InnerLogValid :
    leaf1457InnerLog.Valid 8 (innerAD leaf1457Box) :=
  wideLogDataValid_of_cachedCheck endpoint37PositiveFacts
    endpoint34PositiveFacts.valid leaf1457CoverageChecked

private noncomputable def leaf1457InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814641/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1457InputLogOnePlusV_eq :
    leaf1457InputLogOnePlusV = outerEnclosure 24
      (leaf1457Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1457RoundedFacts : LeafRoundedFacts 8
    leaf1457Certificate.logOnePlusV leaf1457InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1457InputLogOnePlusV_eq }

private noncomputable def leaf1457Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi98InputQChi innerPair142Input
    leaf1457InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1457LowerChecked :
    lowerCheck 24 leaf1457Box leaf1457Inputs = true := by
  rfl'

private theorem leaf1457CoversExact : CoversExact 8
    leaf1457Box leaf1457Certificate leaf1457InnerLog leaf1457Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi98RoundedFacts
    innerPair142RoundedFacts leaf1457RoundedFacts (by rfl)

private theorem leaf1457FlatSound : Sound leaf1457Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1457CertificateValid
    leaf1457InnerLogValid leaf1457CoversExact leaf1457LowerChecked

private noncomputable def leaf1458Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (7/64), chiHi := (15/128) }

private noncomputable def leaf1458Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435693/268435456) }, vSqrt := { lower := (65529/65536), upper := (8388616/8388413) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (362899597/268435456) }, upper := { exponent := 0, mantissa := (707/512) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi98LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (16777029/16776826) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf1458InnerLog : WideLogData :=
  innerPair142Data

set_option maxRecDepth 1000000 in
private theorem leaf1458LocalValidity :
    LeafFacts leaf1458Box leaf1458Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1458Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8388616/8388413) }) = true
      norm_num [leaf1458Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1458CertificateValid :
    WideCertificateValid leaf1458Box leaf1458Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi98ValidityFacts
    leaf1458LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1458CoverageChecked :
    coverageCheck (innerAD leaf1458Box) leaf1458InnerLog = true := by
  rfl'

private theorem leaf1458InnerLogValid :
    leaf1458InnerLog.Valid 8 (innerAD leaf1458Box) :=
  wideLogDataValid_of_cachedCheck endpoint37PositiveFacts
    endpoint34PositiveFacts.valid leaf1458CoverageChecked

private noncomputable def leaf1458InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907321/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1458InputLogOnePlusV_eq :
    leaf1458InputLogOnePlusV = outerEnclosure 24
      (leaf1458Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1458RoundedFacts : LeafRoundedFacts 8
    leaf1458Certificate.logOnePlusV leaf1458InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1458InputLogOnePlusV_eq }

private noncomputable def leaf1458Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi98InputQChi innerPair142Input
    leaf1458InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1458LowerChecked :
    lowerCheck 24 leaf1458Box leaf1458Inputs = true := by
  rfl'

private theorem leaf1458CoversExact : CoversExact 8
    leaf1458Box leaf1458Certificate leaf1458InnerLog leaf1458Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi98RoundedFacts
    innerPair142RoundedFacts leaf1458RoundedFacts (by rfl)

private theorem leaf1458FlatSound : Sound leaf1458Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1458CertificateValid
    leaf1458InnerLogValid leaf1458CoversExact leaf1458LowerChecked

private noncomputable def leaf1459Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (15/128), chiHi := (1/8) }

private noncomputable def leaf1459Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435693/268435456) }, vSqrt := { lower := (65529/65536), upper := (4194308/4194201) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (368666413/268435456) }, upper := { exponent := 0, mantissa := (359/256) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi99LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (8388509/8388402) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf1459InnerLog : WideLogData :=
  innerPair133Data

set_option maxRecDepth 1000000 in
private theorem leaf1459LocalValidity :
    LeafFacts leaf1459Box leaf1459Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1459Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4194308/4194201) }) = true
      norm_num [leaf1459Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1459CertificateValid :
    WideCertificateValid leaf1459Box leaf1459Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi99ValidityFacts
    leaf1459LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1459CoverageChecked :
    coverageCheck (innerAD leaf1459Box) leaf1459InnerLog = true := by
  rfl'

private theorem leaf1459InnerLogValid :
    leaf1459InnerLog.Valid 8 (innerAD leaf1459Box) :=
  wideLogDataValid_of_cachedCheck endpoint30PositiveFacts
    endpoint38PositiveFacts.valid leaf1459CoverageChecked

private noncomputable def leaf1459InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629295/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1459InputLogOnePlusV_eq :
    leaf1459InputLogOnePlusV = outerEnclosure 24
      (leaf1459Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1459RoundedFacts : LeafRoundedFacts 8
    leaf1459Certificate.logOnePlusV leaf1459InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1459InputLogOnePlusV_eq }

private noncomputable def leaf1459Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi99InputQChi innerPair133Input
    leaf1459InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1459LowerChecked :
    lowerCheck 24 leaf1459Box leaf1459Inputs = true := by
  rfl'

private theorem leaf1459CoversExact : CoversExact 8
    leaf1459Box leaf1459Certificate leaf1459InnerLog leaf1459Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi99RoundedFacts
    innerPair133RoundedFacts leaf1459RoundedFacts (by rfl)

private theorem leaf1459FlatSound : Sound leaf1459Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1459CertificateValid
    leaf1459InnerLogValid leaf1459CoversExact leaf1459LowerChecked

private noncomputable def leaf1460Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (15/128), chiHi := (1/8) }

private noncomputable def leaf1460Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435695/268435456) }, vSqrt := { lower := (65529/65536), upper := (1048577/1048550) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (369649391/268435456) }, upper := { exponent := 0, mantissa := (45/32) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi99LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (2097127/2097100) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf1460InnerLog : WideLogData :=
  innerPair29Data

set_option maxRecDepth 1000000 in
private theorem leaf1460LocalValidity :
    LeafFacts leaf1460Box leaf1460Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1460Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (1048577/1048550) }) = true
      norm_num [leaf1460Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1460CertificateValid :
    WideCertificateValid leaf1460Box leaf1460Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi99ValidityFacts
    leaf1460LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1460CoverageChecked :
    coverageCheck (innerAD leaf1460Box) leaf1460InnerLog = true := by
  rfl'

private theorem leaf1460InnerLogValid :
    leaf1460InnerLog.Valid 8 (innerAD leaf1460Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint38PositiveFacts.valid leaf1460CoverageChecked

private noncomputable def leaf1460InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629297/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1460InputLogOnePlusV_eq :
    leaf1460InputLogOnePlusV = outerEnclosure 24
      (leaf1460Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1460RoundedFacts : LeafRoundedFacts 8
    leaf1460Certificate.logOnePlusV leaf1460InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1460InputLogOnePlusV_eq }

private noncomputable def leaf1460Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi99InputQChi innerPair29Input
    leaf1460InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1460LowerChecked :
    lowerCheck 24 leaf1460Box leaf1460Inputs = true := by
  rfl'

private theorem leaf1460CoversExact : CoversExact 8
    leaf1460Box leaf1460Certificate leaf1460InnerLog leaf1460Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi99RoundedFacts
    innerPair29RoundedFacts leaf1460RoundedFacts (by rfl)

private theorem leaf1460FlatSound : Sound leaf1460Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1460CertificateValid
    leaf1460InnerLogValid leaf1460CoversExact leaf1460LowerChecked

private noncomputable def component33Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (3/32), chiHi := (13/128) }

set_option maxRecDepth 1000000 in
private theorem component33Node0_sound : Sound component33Node0Box :=
  sound_of_literal_split component33Node0Box leaf1420Box leaf1421Box
    .chi (25/256) (by rfl) (by rfl)
    leaf1420FlatSound leaf1421FlatSound

private noncomputable def component33Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (13/128), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component33Node1_sound : Sound component33Node1Box :=
  sound_of_literal_split component33Node1Box leaf1422Box leaf1423Box
    .k (97/32) (by rfl) (by rfl)
    leaf1422FlatSound leaf1423FlatSound

private noncomputable def component33Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (3/32), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component33Node2_sound : Sound component33Node2Box :=
  sound_of_literal_split component33Node2Box component33Node0Box component33Node1Box
    .chi (13/128) (by rfl) (by rfl)
    component33Node0_sound component33Node1_sound

private noncomputable def component33Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (3/32), chiHi := (13/128) }

set_option maxRecDepth 1000000 in
private theorem component33Node3_sound : Sound component33Node3Box :=
  sound_of_literal_split component33Node3Box leaf1424Box leaf1425Box
    .chi (25/256) (by rfl) (by rfl)
    leaf1424FlatSound leaf1425FlatSound

private noncomputable def component33Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (13/128), chiHi := (27/256) }

set_option maxRecDepth 1000000 in
private theorem component33Node4_sound : Sound component33Node4Box :=
  sound_of_literal_split component33Node4Box leaf1426Box leaf1427Box
    .k (99/32) (by rfl) (by rfl)
    leaf1426FlatSound leaf1427FlatSound

private noncomputable def component33Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (27/256), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component33Node5_sound : Sound component33Node5Box :=
  sound_of_literal_split component33Node5Box leaf1428Box leaf1429Box
    .k (99/32) (by rfl) (by rfl)
    leaf1428FlatSound leaf1429FlatSound

private noncomputable def component33Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (13/128), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component33Node6_sound : Sound component33Node6Box :=
  sound_of_literal_split component33Node6Box component33Node4Box component33Node5Box
    .chi (27/256) (by rfl) (by rfl)
    component33Node4_sound component33Node5_sound

private noncomputable def component33Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (3/32), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component33Node7_sound : Sound component33Node7Box :=
  sound_of_literal_split component33Node7Box component33Node3Box component33Node6Box
    .chi (13/128) (by rfl) (by rfl)
    component33Node3_sound component33Node6_sound

private noncomputable def component33Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (3/32), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component33Node8_sound : Sound component33Node8Box :=
  sound_of_literal_split component33Node8Box component33Node2Box component33Node7Box
    .k (49/16) (by rfl) (by rfl)
    component33Node2_sound component33Node7_sound

private noncomputable def component33Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (7/64), chiHi := (15/128) }

set_option maxRecDepth 1000000 in
private theorem component33Node9_sound : Sound component33Node9Box :=
  sound_of_literal_split component33Node9Box leaf1430Box leaf1431Box
    .k (97/32) (by rfl) (by rfl)
    leaf1430FlatSound leaf1431FlatSound

private noncomputable def component33Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (15/128), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component33Node10_sound : Sound component33Node10Box :=
  sound_of_literal_split component33Node10Box leaf1432Box leaf1433Box
    .k (97/32) (by rfl) (by rfl)
    leaf1432FlatSound leaf1433FlatSound

private noncomputable def component33Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (7/64), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component33Node11_sound : Sound component33Node11Box :=
  sound_of_literal_split component33Node11Box component33Node9Box component33Node10Box
    .chi (15/128) (by rfl) (by rfl)
    component33Node9_sound component33Node10_sound

private noncomputable def component33Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (7/64), chiHi := (15/128) }

set_option maxRecDepth 1000000 in
private theorem component33Node12_sound : Sound component33Node12Box :=
  sound_of_literal_split component33Node12Box leaf1434Box leaf1435Box
    .k (99/32) (by rfl) (by rfl)
    leaf1434FlatSound leaf1435FlatSound

private noncomputable def component33Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (15/128), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component33Node13_sound : Sound component33Node13Box :=
  sound_of_literal_split component33Node13Box leaf1436Box leaf1437Box
    .k (99/32) (by rfl) (by rfl)
    leaf1436FlatSound leaf1437FlatSound

private noncomputable def component33Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (7/64), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component33Node14_sound : Sound component33Node14Box :=
  sound_of_literal_split component33Node14Box component33Node12Box component33Node13Box
    .chi (15/128) (by rfl) (by rfl)
    component33Node12_sound component33Node13_sound

private noncomputable def component33Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (7/64), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component33Node15_sound : Sound component33Node15Box :=
  sound_of_literal_split component33Node15Box component33Node11Box component33Node14Box
    .k (49/16) (by rfl) (by rfl)
    component33Node11_sound component33Node14_sound

private noncomputable def component33Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (3/32), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component33Node16_sound : Sound component33Node16Box :=
  sound_of_literal_split component33Node16Box component33Node8Box component33Node15Box
    .chi (7/64) (by rfl) (by rfl)
    component33Node8_sound component33Node15_sound

private noncomputable def component33Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (25/256), chiHi := (13/128) }

set_option maxRecDepth 1000000 in
private theorem component33Node17_sound : Sound component33Node17Box :=
  sound_of_literal_split component33Node17Box leaf1439Box leaf1440Box
    .k (101/32) (by rfl) (by rfl)
    leaf1439FlatSound leaf1440FlatSound

private noncomputable def component33Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (3/32), chiHi := (13/128) }

set_option maxRecDepth 1000000 in
private theorem component33Node18_sound : Sound component33Node18Box :=
  sound_of_literal_split component33Node18Box leaf1438Box component33Node17Box
    .chi (25/256) (by rfl) (by rfl)
    leaf1438FlatSound component33Node17_sound

private noncomputable def component33Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (13/128), chiHi := (27/256) }

set_option maxRecDepth 1000000 in
private theorem component33Node19_sound : Sound component33Node19Box :=
  sound_of_literal_split component33Node19Box leaf1441Box leaf1442Box
    .k (101/32) (by rfl) (by rfl)
    leaf1441FlatSound leaf1442FlatSound

private noncomputable def component33Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (27/256), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component33Node20_sound : Sound component33Node20Box :=
  sound_of_literal_split component33Node20Box leaf1443Box leaf1444Box
    .k (101/32) (by rfl) (by rfl)
    leaf1443FlatSound leaf1444FlatSound

private noncomputable def component33Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (13/128), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component33Node21_sound : Sound component33Node21Box :=
  sound_of_literal_split component33Node21Box component33Node19Box component33Node20Box
    .chi (27/256) (by rfl) (by rfl)
    component33Node19_sound component33Node20_sound

private noncomputable def component33Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (3/32), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component33Node22_sound : Sound component33Node22Box :=
  sound_of_literal_split component33Node22Box component33Node18Box component33Node21Box
    .chi (13/128) (by rfl) (by rfl)
    component33Node18_sound component33Node21_sound

private noncomputable def component33Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (3/32), chiHi := (25/256) }

set_option maxRecDepth 1000000 in
private theorem component33Node23_sound : Sound component33Node23Box :=
  sound_of_literal_split component33Node23Box leaf1445Box leaf1446Box
    .k (103/32) (by rfl) (by rfl)
    leaf1445FlatSound leaf1446FlatSound

private noncomputable def component33Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (25/256), chiHi := (13/128) }

set_option maxRecDepth 1000000 in
private theorem component33Node24_sound : Sound component33Node24Box :=
  sound_of_literal_split component33Node24Box leaf1447Box leaf1448Box
    .k (103/32) (by rfl) (by rfl)
    leaf1447FlatSound leaf1448FlatSound

private noncomputable def component33Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (3/32), chiHi := (13/128) }

set_option maxRecDepth 1000000 in
private theorem component33Node25_sound : Sound component33Node25Box :=
  sound_of_literal_split component33Node25Box component33Node23Box component33Node24Box
    .chi (25/256) (by rfl) (by rfl)
    component33Node23_sound component33Node24_sound

private noncomputable def component33Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (13/128), chiHi := (27/256) }

set_option maxRecDepth 1000000 in
private theorem component33Node26_sound : Sound component33Node26Box :=
  sound_of_literal_split component33Node26Box leaf1449Box leaf1450Box
    .k (103/32) (by rfl) (by rfl)
    leaf1449FlatSound leaf1450FlatSound

private noncomputable def component33Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (27/256), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component33Node27_sound : Sound component33Node27Box :=
  sound_of_literal_split component33Node27Box leaf1451Box leaf1452Box
    .k (103/32) (by rfl) (by rfl)
    leaf1451FlatSound leaf1452FlatSound

private noncomputable def component33Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (13/128), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component33Node28_sound : Sound component33Node28Box :=
  sound_of_literal_split component33Node28Box component33Node26Box component33Node27Box
    .chi (27/256) (by rfl) (by rfl)
    component33Node26_sound component33Node27_sound

private noncomputable def component33Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (3/32), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component33Node29_sound : Sound component33Node29Box :=
  sound_of_literal_split component33Node29Box component33Node25Box component33Node28Box
    .chi (13/128) (by rfl) (by rfl)
    component33Node25_sound component33Node28_sound

private noncomputable def component33Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (3/32), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component33Node30_sound : Sound component33Node30Box :=
  sound_of_literal_split component33Node30Box component33Node22Box component33Node29Box
    .k (51/16) (by rfl) (by rfl)
    component33Node22_sound component33Node29_sound

private noncomputable def component33Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (7/64), chiHi := (15/128) }

set_option maxRecDepth 1000000 in
private theorem component33Node31_sound : Sound component33Node31Box :=
  sound_of_literal_split component33Node31Box leaf1453Box leaf1454Box
    .k (101/32) (by rfl) (by rfl)
    leaf1453FlatSound leaf1454FlatSound

private noncomputable def component33Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (15/128), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component33Node32_sound : Sound component33Node32Box :=
  sound_of_literal_split component33Node32Box leaf1455Box leaf1456Box
    .k (101/32) (by rfl) (by rfl)
    leaf1455FlatSound leaf1456FlatSound

private noncomputable def component33Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (7/64), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component33Node33_sound : Sound component33Node33Box :=
  sound_of_literal_split component33Node33Box component33Node31Box component33Node32Box
    .chi (15/128) (by rfl) (by rfl)
    component33Node31_sound component33Node32_sound

private noncomputable def component33Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (7/64), chiHi := (15/128) }

set_option maxRecDepth 1000000 in
private theorem component33Node34_sound : Sound component33Node34Box :=
  sound_of_literal_split component33Node34Box leaf1457Box leaf1458Box
    .k (103/32) (by rfl) (by rfl)
    leaf1457FlatSound leaf1458FlatSound

private noncomputable def component33Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (15/128), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component33Node35_sound : Sound component33Node35Box :=
  sound_of_literal_split component33Node35Box leaf1459Box leaf1460Box
    .k (103/32) (by rfl) (by rfl)
    leaf1459FlatSound leaf1460FlatSound

private noncomputable def component33Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (7/64), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component33Node36_sound : Sound component33Node36Box :=
  sound_of_literal_split component33Node36Box component33Node34Box component33Node35Box
    .chi (15/128) (by rfl) (by rfl)
    component33Node34_sound component33Node35_sound

private noncomputable def component33Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (7/64), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component33Node37_sound : Sound component33Node37Box :=
  sound_of_literal_split component33Node37Box component33Node33Box component33Node36Box
    .k (51/16) (by rfl) (by rfl)
    component33Node33_sound component33Node36_sound

private noncomputable def component33Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (3/32), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component33Node38_sound : Sound component33Node38Box :=
  sound_of_literal_split component33Node38Box component33Node30Box component33Node37Box
    .chi (7/64) (by rfl) (by rfl)
    component33Node30_sound component33Node37_sound

noncomputable def component33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (13/4), chiLo := (3/32), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
theorem component33_sound : Sound component33Box :=
  sound_of_literal_split component33Box component33Node16Box component33Node38Box
    .k (25/8) (by rfl) (by rfl)
    component33Node16_sound component33Node38_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
