import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch7
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch8
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch9
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch12
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch13
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

private noncomputable def leaf7132Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (7/8), chiHi := (29/32) }

private noncomputable def leaf7132Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (33554587/33554432) }, vSqrt := { lower := (65529/65536), upper := (11452394153/11451305984) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (121596519/67108864) }, upper := { exponent := 1, mantissa := (1933/1024) } }, logOuter := sk123LogOuterCertificate, logK := sk123LogKCertificate, logChi := chi92LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (22903700137/22902611968) } }, logDArg := sk123LogDArgCertificate }

private noncomputable def leaf7132InnerLog : WideLogData :=
  innerPair796Data

set_option maxRecDepth 1000000 in
private theorem leaf7132LocalValidity :
    LeafFacts leaf7132Box leaf7132Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7132Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (11452394153/11451305984) }) = true
      norm_num [leaf7132Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7132CertificateValid :
    WideCertificateValid leaf7132Box leaf7132Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk123ValidityFacts chi92ValidityFacts
    leaf7132LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7132CoverageChecked :
    coverageCheck (innerAD leaf7132Box) leaf7132InnerLog = true := by
  rfl'

private theorem leaf7132InnerLogValid :
    leaf7132InnerLog.Valid 8 (innerAD leaf7132Box) :=
  wideLogDataValid_of_cachedCheck endpoint498PositiveFacts
    endpoint503PositiveFacts.valid leaf7132CoverageChecked

private noncomputable def leaf7132InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814939/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf7132InputLogOnePlusV_eq :
    leaf7132InputLogOnePlusV = outerEnclosure 24
      (leaf7132Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7132RoundedFacts : LeafRoundedFacts 8
    leaf7132Certificate.logOnePlusV leaf7132InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7132InputLogOnePlusV_eq }

private noncomputable def leaf7132Inputs : Inputs :=
  inputsOfCaches globalInput sk123RoundedInputs
    chi92InputQChi innerPair796Input
    leaf7132InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7132LowerChecked :
    lowerCheck 24 leaf7132Box leaf7132Inputs = true := by
  rfl'

private theorem leaf7132CoversExact : CoversExact 8
    leaf7132Box leaf7132Certificate leaf7132InnerLog leaf7132Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk123RoundedFacts chi92RoundedFacts
    innerPair796RoundedFacts leaf7132RoundedFacts (by rfl)

private theorem leaf7132FlatSound : Sound leaf7132Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7132CertificateValid
    leaf7132InnerLogValid leaf7132CoversExact leaf7132LowerChecked

private noncomputable def leaf7133Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (7/8), chiHi := (29/32) }

private noncomputable def leaf7133Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (33554589/33554432) }, vSqrt := { lower := (65529/65536), upper := (34357182459/34353799168) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (123431413/67108864) }, upper := { exponent := 1, mantissa := (981/512) } }, logOuter := sk124LogOuterCertificate, logK := sk124LogKCertificate, logChi := chi92LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68710981627/68707598336) } }, logDArg := sk124LogDArgCertificate }

private noncomputable def leaf7133InnerLog : WideLogData :=
  innerPair800Data

set_option maxRecDepth 1000000 in
private theorem leaf7133LocalValidity :
    LeafFacts leaf7133Box leaf7133Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7133Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34357182459/34353799168) }) = true
      norm_num [leaf7133Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7133CertificateValid :
    WideCertificateValid leaf7133Box leaf7133Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk124ValidityFacts chi92ValidityFacts
    leaf7133LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7133CoverageChecked :
    coverageCheck (innerAD leaf7133Box) leaf7133InnerLog = true := by
  rfl'

private theorem leaf7133InnerLogValid :
    leaf7133InnerLog.Valid 8 (innerAD leaf7133Box) :=
  wideLogDataValid_of_cachedCheck endpoint500PositiveFacts
    endpoint504PositiveFacts.valid leaf7133CoverageChecked

private noncomputable def leaf7133InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629907/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7133InputLogOnePlusV_eq :
    leaf7133InputLogOnePlusV = outerEnclosure 24
      (leaf7133Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7133RoundedFacts : LeafRoundedFacts 8
    leaf7133Certificate.logOnePlusV leaf7133InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7133InputLogOnePlusV_eq }

private noncomputable def leaf7133Inputs : Inputs :=
  inputsOfCaches globalInput sk124RoundedInputs
    chi92InputQChi innerPair800Input
    leaf7133InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7133LowerChecked :
    lowerCheck 24 leaf7133Box leaf7133Inputs = true := by
  rfl'

private theorem leaf7133CoversExact : CoversExact 8
    leaf7133Box leaf7133Certificate leaf7133InnerLog leaf7133Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk124RoundedFacts chi92RoundedFacts
    innerPair800RoundedFacts leaf7133RoundedFacts (by rfl)

private theorem leaf7133FlatSound : Sound leaf7133Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7133CertificateValid
    leaf7133InnerLogValid leaf7133CoversExact leaf7133LowerChecked

private noncomputable def leaf7134Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (29/32), chiHi := (15/16) }

private noncomputable def leaf7134Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (33554589/33554432) }, vSqrt := { lower := (65529/65536), upper := (34357182459/34353717248) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (124742053/67108864) }, upper := { exponent := 1, mantissa := (991/512) } }, logOuter := sk123LogOuterCertificate, logK := sk123LogKCertificate, logChi := chi93LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68710899707/68707434496) } }, logDArg := sk123LogDArgCertificate }

private noncomputable def leaf7134InnerLog : WideLogData :=
  innerPair802Data

set_option maxRecDepth 1000000 in
private theorem leaf7134LocalValidity :
    LeafFacts leaf7134Box leaf7134Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7134Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34357182459/34353717248) }) = true
      norm_num [leaf7134Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7134CertificateValid :
    WideCertificateValid leaf7134Box leaf7134Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk123ValidityFacts chi93ValidityFacts
    leaf7134LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7134CoverageChecked :
    coverageCheck (innerAD leaf7134Box) leaf7134InnerLog = true := by
  rfl'

private theorem leaf7134InnerLogValid :
    leaf7134InnerLog.Valid 8 (innerAD leaf7134Box) :=
  wideLogDataValid_of_cachedCheck endpoint501PositiveFacts
    endpoint504PositiveFacts.valid leaf7134CoverageChecked

private noncomputable def leaf7134InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629927/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7134InputLogOnePlusV_eq :
    leaf7134InputLogOnePlusV = outerEnclosure 24
      (leaf7134Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7134RoundedFacts : LeafRoundedFacts 8
    leaf7134Certificate.logOnePlusV leaf7134InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7134InputLogOnePlusV_eq }

private noncomputable def leaf7134Inputs : Inputs :=
  inputsOfCaches globalInput sk123RoundedInputs
    chi93InputQChi innerPair802Input
    leaf7134InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7134LowerChecked :
    lowerCheck 24 leaf7134Box leaf7134Inputs = true := by
  rfl'

private theorem leaf7134CoversExact : CoversExact 8
    leaf7134Box leaf7134Certificate leaf7134InnerLog leaf7134Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk123RoundedFacts chi93RoundedFacts
    innerPair802RoundedFacts leaf7134RoundedFacts (by rfl)

private theorem leaf7134FlatSound : Sound leaf7134Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7134CertificateValid
    leaf7134InnerLogValid leaf7134CoversExact leaf7134LowerChecked

private noncomputable def leaf7135Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (29/32), chiHi := (15/16) }

private noncomputable def leaf7135Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (33554591/33554432) }, vSqrt := { lower := (65529/65536), upper := (34357182459/34353594368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (126642479/67108864) }, upper := { exponent := 1, mantissa := (503/256) } }, logOuter := sk124LogOuterCertificate, logK := sk124LogKCertificate, logChi := chi93LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68710776827/68707188736) } }, logDArg := sk124LogDArgCertificate }

private noncomputable def leaf7135InnerLog : WideLogData :=
  innerPair806Data

set_option maxRecDepth 1000000 in
private theorem leaf7135LocalValidity :
    LeafFacts leaf7135Box leaf7135Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7135Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34357182459/34353594368) }) = true
      norm_num [leaf7135Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7135CertificateValid :
    WideCertificateValid leaf7135Box leaf7135Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk124ValidityFacts chi93ValidityFacts
    leaf7135LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7135CoverageChecked :
    coverageCheck (innerAD leaf7135Box) leaf7135InnerLog = true := by
  rfl'

private theorem leaf7135InnerLogValid :
    leaf7135InnerLog.Valid 8 (innerAD leaf7135Box) :=
  wideLogDataValid_of_cachedCheck endpoint502PositiveFacts
    endpoint505PositiveFacts.valid leaf7135CoverageChecked

private noncomputable def leaf7135InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629957/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7135InputLogOnePlusV_eq :
    leaf7135InputLogOnePlusV = outerEnclosure 24
      (leaf7135Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7135RoundedFacts : LeafRoundedFacts 8
    leaf7135Certificate.logOnePlusV leaf7135InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7135InputLogOnePlusV_eq }

private noncomputable def leaf7135Inputs : Inputs :=
  inputsOfCaches globalInput sk124RoundedInputs
    chi93InputQChi innerPair806Input
    leaf7135InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7135LowerChecked :
    lowerCheck 24 leaf7135Box leaf7135Inputs = true := by
  rfl'

private theorem leaf7135CoversExact : CoversExact 8
    leaf7135Box leaf7135Certificate leaf7135InnerLog leaf7135Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk124RoundedFacts chi93RoundedFacts
    innerPair806RoundedFacts leaf7135RoundedFacts (by rfl)

private theorem leaf7135FlatSound : Sound leaf7135Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7135CertificateValid
    leaf7135InnerLogValid leaf7135CoversExact leaf7135LowerChecked

private noncomputable def leaf7136Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (7/8), chiHi := (29/32) }

private noncomputable def leaf7136Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (33554591/33554432) }, vSqrt := { lower := (65529/65536), upper := (34357182459/34353680384) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (125266307/67108864) }, upper := { exponent := 1, mantissa := (1991/1024) } }, logOuter := sk125LogOuterCertificate, logK := sk125LogKCertificate, logChi := chi92LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68710862843/68707360768) } }, logDArg := sk125LogDArgCertificate }

private noncomputable def leaf7136InnerLog : WideLogData :=
  innerPair803Data

set_option maxRecDepth 1000000 in
private theorem leaf7136LocalValidity :
    LeafFacts leaf7136Box leaf7136Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7136Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34357182459/34353680384) }) = true
      norm_num [leaf7136Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7136CertificateValid :
    WideCertificateValid leaf7136Box leaf7136Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk125ValidityFacts chi92ValidityFacts
    leaf7136LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7136CoverageChecked :
    coverageCheck (innerAD leaf7136Box) leaf7136InnerLog = true := by
  rfl'

private theorem leaf7136InnerLogValid :
    leaf7136InnerLog.Valid 8 (innerAD leaf7136Box) :=
  wideLogDataValid_of_cachedCheck endpoint501PositiveFacts
    endpoint505PositiveFacts.valid leaf7136CoverageChecked

private noncomputable def leaf7136InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (726871/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf7136InputLogOnePlusV_eq :
    leaf7136InputLogOnePlusV = outerEnclosure 24
      (leaf7136Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7136RoundedFacts : LeafRoundedFacts 8
    leaf7136Certificate.logOnePlusV leaf7136InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7136InputLogOnePlusV_eq }

private noncomputable def leaf7136Inputs : Inputs :=
  inputsOfCaches globalInput sk125RoundedInputs
    chi92InputQChi innerPair803Input
    leaf7136InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7136LowerChecked :
    lowerCheck 24 leaf7136Box leaf7136Inputs = true := by
  rfl'

private theorem leaf7136CoversExact : CoversExact 8
    leaf7136Box leaf7136Certificate leaf7136InnerLog leaf7136Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk125RoundedFacts chi92RoundedFacts
    innerPair803RoundedFacts leaf7136RoundedFacts (by rfl)

private theorem leaf7136FlatSound : Sound leaf7136Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7136CertificateValid
    leaf7136InnerLogValid leaf7136CoversExact leaf7136LowerChecked

private noncomputable def leaf7137Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (7/8), chiHi := (29/32) }

private noncomputable def leaf7137Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (33554593/33554432) }, vSqrt := { lower := (65529/65536), upper := (11452394153/11451187200) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (127101201/67108864) }, upper := { exponent := 1, mantissa := (505/256) } }, logOuter := sk126LogOuterCertificate, logK := sk126LogKCertificate, logChi := chi92LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (22903581353/22902374400) } }, logDArg := sk126LogDArgCertificate }

private noncomputable def leaf7137InnerLog : WideLogData :=
  innerPair864Data

set_option maxRecDepth 1000000 in
private theorem leaf7137LocalValidity :
    LeafFacts leaf7137Box leaf7137Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7137Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (11452394153/11451187200) }) = true
      norm_num [leaf7137Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7137CertificateValid :
    WideCertificateValid leaf7137Box leaf7137Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk126ValidityFacts chi92ValidityFacts
    leaf7137LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7137CoverageChecked :
    coverageCheck (innerAD leaf7137Box) leaf7137InnerLog = true := by
  rfl'

private theorem leaf7137InnerLogValid :
    leaf7137InnerLog.Valid 8 (innerAD leaf7137Box) :=
  wideLogDataValid_of_cachedCheck endpoint574PositiveFacts
    endpoint577PositiveFacts.valid leaf7137CoverageChecked

private noncomputable def leaf7137InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629965/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7137InputLogOnePlusV_eq :
    leaf7137InputLogOnePlusV = outerEnclosure 24
      (leaf7137Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7137RoundedFacts : LeafRoundedFacts 8
    leaf7137Certificate.logOnePlusV leaf7137InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7137InputLogOnePlusV_eq }

private noncomputable def leaf7137Inputs : Inputs :=
  inputsOfCaches globalInput sk126RoundedInputs
    chi92InputQChi innerPair864Input
    leaf7137InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7137LowerChecked :
    lowerCheck 24 leaf7137Box leaf7137Inputs = true := by
  rfl'

private theorem leaf7137CoversExact : CoversExact 8
    leaf7137Box leaf7137Certificate leaf7137InnerLog leaf7137Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk126RoundedFacts chi92RoundedFacts
    innerPair864RoundedFacts leaf7137RoundedFacts (by rfl)

private theorem leaf7137FlatSound : Sound leaf7137Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7137CertificateValid
    leaf7137InnerLogValid leaf7137CoversExact leaf7137LowerChecked

private noncomputable def leaf7138Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (29/32), chiHi := (15/16) }

private noncomputable def leaf7138Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (33554593/33554432) }, vSqrt := { lower := (65529/65536), upper := (17178329085/17176735744) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (128542905/67108864) }, upper := { exponent := 1, mantissa := (1021/512) } }, logOuter := sk125LogOuterCertificate, logK := sk125LogKCertificate, logChi := chi93LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (34355064829/34353471488) } }, logDArg := sk125LogDArgCertificate }

private noncomputable def leaf7138InnerLog : WideLogData :=
  innerPair809Data

set_option maxRecDepth 1000000 in
private theorem leaf7138LocalValidity :
    LeafFacts leaf7138Box leaf7138Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7138Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (17178329085/17176735744) }) = true
      norm_num [leaf7138Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7138CertificateValid :
    WideCertificateValid leaf7138Box leaf7138Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk125ValidityFacts chi93ValidityFacts
    leaf7138LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7138CoverageChecked :
    coverageCheck (innerAD leaf7138Box) leaf7138InnerLog = true := by
  rfl'

private theorem leaf7138InnerLogValid :
    leaf7138InnerLog.Valid 8 (innerAD leaf7138Box) :=
  wideLogDataValid_of_cachedCheck endpoint503PositiveFacts
    endpoint506PositiveFacts.valid leaf7138CoverageChecked

private noncomputable def leaf7138InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629859/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7138InputLogOnePlusV_eq :
    leaf7138InputLogOnePlusV = outerEnclosure 24
      (leaf7138Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7138RoundedFacts : LeafRoundedFacts 8
    leaf7138Certificate.logOnePlusV leaf7138InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7138InputLogOnePlusV_eq }

private noncomputable def leaf7138Inputs : Inputs :=
  inputsOfCaches globalInput sk125RoundedInputs
    chi93InputQChi innerPair809Input
    leaf7138InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7138LowerChecked :
    lowerCheck 24 leaf7138Box leaf7138Inputs = true := by
  rfl'

private theorem leaf7138CoversExact : CoversExact 8
    leaf7138Box leaf7138Certificate leaf7138InnerLog leaf7138Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk125RoundedFacts chi93RoundedFacts
    innerPair809RoundedFacts leaf7138RoundedFacts (by rfl)

private theorem leaf7138FlatSound : Sound leaf7138Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7138CertificateValid
    leaf7138InnerLogValid leaf7138CoversExact leaf7138LowerChecked

private noncomputable def leaf7139Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (29/32), chiHi := (15/16) }

private noncomputable def leaf7139Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (33554595/33554432) }, vSqrt := { lower := (65529/65536), upper := (17178329085/17176674304) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (130443331/67108864) }, upper := { exponent := 2, mantissa := (259/256) } }, logOuter := sk126LogOuterCertificate, logK := sk126LogKCertificate, logChi := chi93LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (34355003389/34353348608) } }, logDArg := sk126LogDArgCertificate }

private noncomputable def leaf7139InnerLog : WideLogData :=
  innerPair812Data

set_option maxRecDepth 1000000 in
private theorem leaf7139LocalValidity :
    LeafFacts leaf7139Box leaf7139Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7139Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (17178329085/17176674304) }) = true
      norm_num [leaf7139Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7139CertificateValid :
    WideCertificateValid leaf7139Box leaf7139Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk126ValidityFacts chi93ValidityFacts
    leaf7139LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7139CoverageChecked :
    coverageCheck (innerAD leaf7139Box) leaf7139InnerLog = true := by
  rfl'

private theorem leaf7139InnerLogValid :
    leaf7139InnerLog.Valid 8 (innerAD leaf7139Box) :=
  wideLogDataValid_of_cachedCheck endpoint504PositiveFacts
    endpoint582PositiveFacts.valid leaf7139CoverageChecked

private noncomputable def leaf7139InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629889/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7139InputLogOnePlusV_eq :
    leaf7139InputLogOnePlusV = outerEnclosure 24
      (leaf7139Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7139RoundedFacts : LeafRoundedFacts 8
    leaf7139Certificate.logOnePlusV leaf7139InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7139InputLogOnePlusV_eq }

private noncomputable def leaf7139Inputs : Inputs :=
  inputsOfCaches globalInput sk126RoundedInputs
    chi93InputQChi innerPair812Input
    leaf7139InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7139LowerChecked :
    lowerCheck 24 leaf7139Box leaf7139Inputs = true := by
  rfl'

private theorem leaf7139CoversExact : CoversExact 8
    leaf7139Box leaf7139Certificate leaf7139InnerLog leaf7139Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk126RoundedFacts chi93RoundedFacts
    innerPair812RoundedFacts leaf7139RoundedFacts (by rfl)

private theorem leaf7139FlatSound : Sound leaf7139Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7139CertificateValid
    leaf7139InnerLogValid leaf7139CoversExact leaf7139LowerChecked

private noncomputable def leaf7140Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (15/16), chiHi := (31/32) }

private noncomputable def leaf7140Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (33554591/33554432) }, vSqrt := { lower := (65529/65536), upper := (34357182459/34353516544) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (127887587/67108864) }, upper := { exponent := 1, mantissa := (2031/1024) } }, logOuter := sk123LogOuterCertificate, logK := sk123LogKCertificate, logChi := chi94LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68710699003/68707033088) } }, logDArg := sk123LogDArgCertificate }

private noncomputable def leaf7140InnerLog : WideLogData :=
  innerPair807Data

set_option maxRecDepth 1000000 in
private theorem leaf7140LocalValidity :
    LeafFacts leaf7140Box leaf7140Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7140Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34357182459/34353516544) }) = true
      norm_num [leaf7140Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7140CertificateValid :
    WideCertificateValid leaf7140Box leaf7140Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk123ValidityFacts chi94ValidityFacts
    leaf7140LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7140CoverageChecked :
    coverageCheck (innerAD leaf7140Box) leaf7140InnerLog = true := by
  rfl'

private theorem leaf7140InnerLogValid :
    leaf7140InnerLog.Valid 8 (innerAD leaf7140Box) :=
  wideLogDataValid_of_cachedCheck endpoint502PositiveFacts
    endpoint506PositiveFacts.valid leaf7140CoverageChecked

private noncomputable def leaf7140InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453747/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf7140InputLogOnePlusV_eq :
    leaf7140InputLogOnePlusV = outerEnclosure 24
      (leaf7140Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7140RoundedFacts : LeafRoundedFacts 8
    leaf7140Certificate.logOnePlusV leaf7140InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7140InputLogOnePlusV_eq }

private noncomputable def leaf7140Inputs : Inputs :=
  inputsOfCaches globalInput sk123RoundedInputs
    chi94InputQChi innerPair807Input
    leaf7140InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7140LowerChecked :
    lowerCheck 24 leaf7140Box leaf7140Inputs = true := by
  rfl'

private theorem leaf7140CoversExact : CoversExact 8
    leaf7140Box leaf7140Certificate leaf7140InnerLog leaf7140Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk123RoundedFacts chi94RoundedFacts
    innerPair807RoundedFacts leaf7140RoundedFacts (by rfl)

private theorem leaf7140FlatSound : Sound leaf7140Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7140CertificateValid
    leaf7140InnerLogValid leaf7140CoversExact leaf7140LowerChecked

private noncomputable def leaf7141Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (15/16), chiHi := (31/32) }

private noncomputable def leaf7141Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (33554593/33554432) }, vSqrt := { lower := (65529/65536), upper := (5726109695/5725564928) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (129853545/67108864) }, upper := { exponent := 2, mantissa := (1031/1024) } }, logOuter := sk124LogOuterCertificate, logK := sk124LogKCertificate, logChi := chi94LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (11451674623/11451129856) } }, logDArg := sk124LogDArgCertificate }

private noncomputable def leaf7141InnerLog : WideLogData :=
  innerPair810Data

set_option maxRecDepth 1000000 in
private theorem leaf7141LocalValidity :
    LeafFacts leaf7141Box leaf7141Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7141Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (5726109695/5725564928) }) = true
      norm_num [leaf7141Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7141CertificateValid :
    WideCertificateValid leaf7141Box leaf7141Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk124ValidityFacts chi94ValidityFacts
    leaf7141LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7141CoverageChecked :
    coverageCheck (innerAD leaf7141Box) leaf7141InnerLog = true := by
  rfl'

private theorem leaf7141InnerLogValid :
    leaf7141InnerLog.Valid 8 (innerAD leaf7141Box) :=
  wideLogDataValid_of_cachedCheck endpoint503PositiveFacts
    endpoint582PositiveFacts.valid leaf7141CoverageChecked

private noncomputable def leaf7141InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629879/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7141InputLogOnePlusV_eq :
    leaf7141InputLogOnePlusV = outerEnclosure 24
      (leaf7141Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7141RoundedFacts : LeafRoundedFacts 8
    leaf7141Certificate.logOnePlusV leaf7141InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7141InputLogOnePlusV_eq }

private noncomputable def leaf7141Inputs : Inputs :=
  inputsOfCaches globalInput sk124RoundedInputs
    chi94InputQChi innerPair810Input
    leaf7141InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7141LowerChecked :
    lowerCheck 24 leaf7141Box leaf7141Inputs = true := by
  rfl'

private theorem leaf7141CoversExact : CoversExact 8
    leaf7141Box leaf7141Certificate leaf7141InnerLog leaf7141Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk124RoundedFacts chi94RoundedFacts
    innerPair810RoundedFacts leaf7141RoundedFacts (by rfl)

private theorem leaf7141FlatSound : Sound leaf7141Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7141CertificateValid
    leaf7141InnerLogValid leaf7141CoversExact leaf7141LowerChecked

private noncomputable def leaf7142Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (31/32), chiHi := (1) }

private noncomputable def leaf7142Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (33554593/33554432) }, vSqrt := { lower := (65529/65536), upper := (1145221939/1145110528) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (131033121/67108864) }, upper := { exponent := 2, mantissa := (65/64) } }, logOuter := sk123LogOuterCertificate, logK := sk123LogKCertificate, logChi := chi95LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (2290332467/2290221056) } }, logDArg := sk123LogDArgCertificate }

private noncomputable def leaf7142InnerLog : WideLogData :=
  innerPair812Data

set_option maxRecDepth 1000000 in
private theorem leaf7142LocalValidity :
    LeafFacts leaf7142Box leaf7142Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7142Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (1145221939/1145110528) }) = true
      norm_num [leaf7142Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7142CertificateValid :
    WideCertificateValid leaf7142Box leaf7142Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk123ValidityFacts chi95ValidityFacts
    leaf7142LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7142CoverageChecked :
    coverageCheck (innerAD leaf7142Box) leaf7142InnerLog = true := by
  rfl'

private theorem leaf7142InnerLogValid :
    leaf7142InnerLog.Valid 8 (innerAD leaf7142Box) :=
  wideLogDataValid_of_cachedCheck endpoint504PositiveFacts
    endpoint582PositiveFacts.valid leaf7142CoverageChecked

private noncomputable def leaf7142InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629897/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7142InputLogOnePlusV_eq :
    leaf7142InputLogOnePlusV = outerEnclosure 24
      (leaf7142Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7142RoundedFacts : LeafRoundedFacts 8
    leaf7142Certificate.logOnePlusV leaf7142InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7142InputLogOnePlusV_eq }

private noncomputable def leaf7142Inputs : Inputs :=
  inputsOfCaches globalInput sk123RoundedInputs
    chi95InputQChi innerPair812Input
    leaf7142InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7142LowerChecked :
    lowerCheck 24 leaf7142Box leaf7142Inputs = true := by
  rfl'

private theorem leaf7142CoversExact : CoversExact 8
    leaf7142Box leaf7142Certificate leaf7142InnerLog leaf7142Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk123RoundedFacts chi95RoundedFacts
    innerPair812RoundedFacts leaf7142RoundedFacts (by rfl)

private theorem leaf7142FlatSound : Sound leaf7142Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7142CertificateValid
    leaf7142InnerLogValid leaf7142CoversExact leaf7142LowerChecked

private noncomputable def leaf7143Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (31/32), chiHi := (1) }

private noncomputable def leaf7143Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (33554595/33554432) }, vSqrt := { lower := (65529/65536), upper := (17178329085/17176592384) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (133064611/67108864) }, upper := { exponent := 2, mantissa := (33/32) } }, logOuter := sk124LogOuterCertificate, logK := sk124LogKCertificate, logChi := chi95LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (34354921469/34353184768) } }, logDArg := sk124LogDArgCertificate }

private noncomputable def leaf7143InnerLog : WideLogData :=
  innerPair815Data

set_option maxRecDepth 1000000 in
private theorem leaf7143LocalValidity :
    LeafFacts leaf7143Box leaf7143Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7143Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (17178329085/17176592384) }) = true
      norm_num [leaf7143Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7143CertificateValid :
    WideCertificateValid leaf7143Box leaf7143Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk124ValidityFacts chi95ValidityFacts
    leaf7143LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7143CoverageChecked :
    coverageCheck (innerAD leaf7143Box) leaf7143InnerLog = true := by
  rfl'

private theorem leaf7143InnerLogValid :
    leaf7143InnerLog.Valid 8 (innerAD leaf7143Box) :=
  wideLogDataValid_of_cachedCheck endpoint505PositiveFacts
    endpoint583PositiveFacts.valid leaf7143CoverageChecked

private noncomputable def leaf7143InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629929/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7143InputLogOnePlusV_eq :
    leaf7143InputLogOnePlusV = outerEnclosure 24
      (leaf7143Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7143RoundedFacts : LeafRoundedFacts 8
    leaf7143Certificate.logOnePlusV leaf7143InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7143InputLogOnePlusV_eq }

private noncomputable def leaf7143Inputs : Inputs :=
  inputsOfCaches globalInput sk124RoundedInputs
    chi95InputQChi innerPair815Input
    leaf7143InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7143LowerChecked :
    lowerCheck 24 leaf7143Box leaf7143Inputs = true := by
  rfl'

private theorem leaf7143CoversExact : CoversExact 8
    leaf7143Box leaf7143Certificate leaf7143InnerLog leaf7143Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk124RoundedFacts chi95RoundedFacts
    innerPair815RoundedFacts leaf7143RoundedFacts (by rfl)

private theorem leaf7143FlatSound : Sound leaf7143Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7143CertificateValid
    leaf7143InnerLogValid leaf7143CoversExact leaf7143LowerChecked

private noncomputable def leaf7144Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (15/16), chiHi := (31/32) }

private noncomputable def leaf7144Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (33554595/33554432) }, vSqrt := { lower := (65529/65536), upper := (17178329085/17176631296) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (131819503/67108864) }, upper := { exponent := 2, mantissa := (2093/2048) } }, logOuter := sk125LogOuterCertificate, logK := sk125LogKCertificate, logChi := chi94LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (34354960381/34353262592) } }, logDArg := sk125LogDArgCertificate }

private noncomputable def leaf7144InnerLog : WideLogData :=
  innerPair813Data

set_option maxRecDepth 1000000 in
private theorem leaf7144LocalValidity :
    LeafFacts leaf7144Box leaf7144Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7144Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (17178329085/17176631296) }) = true
      norm_num [leaf7144Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7144CertificateValid :
    WideCertificateValid leaf7144Box leaf7144Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk125ValidityFacts chi94ValidityFacts
    leaf7144LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7144CoverageChecked :
    coverageCheck (innerAD leaf7144Box) leaf7144InnerLog = true := by
  rfl'

private theorem leaf7144InnerLogValid :
    leaf7144InnerLog.Valid 8 (innerAD leaf7144Box) :=
  wideLogDataValid_of_cachedCheck endpoint504PositiveFacts
    endpoint583PositiveFacts.valid leaf7144CoverageChecked

private noncomputable def leaf7144InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814955/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf7144InputLogOnePlusV_eq :
    leaf7144InputLogOnePlusV = outerEnclosure 24
      (leaf7144Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7144RoundedFacts : LeafRoundedFacts 8
    leaf7144Certificate.logOnePlusV leaf7144InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7144InputLogOnePlusV_eq }

private noncomputable def leaf7144Inputs : Inputs :=
  inputsOfCaches globalInput sk125RoundedInputs
    chi94InputQChi innerPair813Input
    leaf7144InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7144LowerChecked :
    lowerCheck 24 leaf7144Box leaf7144Inputs = true := by
  rfl'

private theorem leaf7144CoversExact : CoversExact 8
    leaf7144Box leaf7144Certificate leaf7144InnerLog leaf7144Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk125RoundedFacts chi94RoundedFacts
    innerPair813RoundedFacts leaf7144RoundedFacts (by rfl)

private theorem leaf7144FlatSound : Sound leaf7144Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7144CertificateValid
    leaf7144InnerLogValid leaf7144CoversExact leaf7144LowerChecked

private noncomputable def leaf7145Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (15/16), chiHi := (31/32) }

private noncomputable def leaf7145Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (33554597/33554432) }, vSqrt := { lower := (65529/65536), upper := (17178329085/17176567808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (133785461/67108864) }, upper := { exponent := 2, mantissa := (531/512) } }, logOuter := sk126LogOuterCertificate, logK := sk126LogKCertificate, logChi := chi94LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (34354896893/34353135616) } }, logDArg := sk126LogDArgCertificate }

private noncomputable def leaf7145InnerLog : WideLogData :=
  innerPair816Data

set_option maxRecDepth 1000000 in
private theorem leaf7145LocalValidity :
    LeafFacts leaf7145Box leaf7145Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7145Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (17178329085/17176567808) }) = true
      norm_num [leaf7145Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7145CertificateValid :
    WideCertificateValid leaf7145Box leaf7145Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk126ValidityFacts chi94ValidityFacts
    leaf7145LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7145CoverageChecked :
    coverageCheck (innerAD leaf7145Box) leaf7145InnerLog = true := by
  rfl'

private theorem leaf7145InnerLogValid :
    leaf7145InnerLog.Valid 8 (innerAD leaf7145Box) :=
  wideLogDataValid_of_cachedCheck endpoint505PositiveFacts
    endpoint584PositiveFacts.valid leaf7145CoverageChecked

private noncomputable def leaf7145InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629941/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7145InputLogOnePlusV_eq :
    leaf7145InputLogOnePlusV = outerEnclosure 24
      (leaf7145Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7145RoundedFacts : LeafRoundedFacts 8
    leaf7145Certificate.logOnePlusV leaf7145InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7145InputLogOnePlusV_eq }

private noncomputable def leaf7145Inputs : Inputs :=
  inputsOfCaches globalInput sk126RoundedInputs
    chi94InputQChi innerPair816Input
    leaf7145InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7145LowerChecked :
    lowerCheck 24 leaf7145Box leaf7145Inputs = true := by
  rfl'

private theorem leaf7145CoversExact : CoversExact 8
    leaf7145Box leaf7145Certificate leaf7145InnerLog leaf7145Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk126RoundedFacts chi94RoundedFacts
    innerPair816RoundedFacts leaf7145RoundedFacts (by rfl)

private theorem leaf7145FlatSound : Sound leaf7145Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7145CertificateValid
    leaf7145InnerLogValid leaf7145CoversExact leaf7145LowerChecked

private noncomputable def leaf7146Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (31/32), chiHi := (1) }

private noncomputable def leaf7146Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (33554597/33554432) }, vSqrt := { lower := (65529/65536), upper := (17178329085/17176526848) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (135096101/134217728) }, upper := { exponent := 2, mantissa := (67/64) } }, logOuter := sk125LogOuterCertificate, logK := sk125LogKCertificate, logChi := chi95LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (34354855933/34353053696) } }, logDArg := sk125LogDArgCertificate }

private noncomputable def leaf7146InnerLog : WideLogData :=
  innerPair818Data

set_option maxRecDepth 1000000 in
private theorem leaf7146LocalValidity :
    LeafFacts leaf7146Box leaf7146Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7146Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (17178329085/17176526848) }) = true
      norm_num [leaf7146Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7146CertificateValid :
    WideCertificateValid leaf7146Box leaf7146Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk125ValidityFacts chi95ValidityFacts
    leaf7146LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7146CoverageChecked :
    coverageCheck (innerAD leaf7146Box) leaf7146InnerLog = true := by
  rfl'

private theorem leaf7146InnerLogValid :
    leaf7146InnerLog.Valid 8 (innerAD leaf7146Box) :=
  wideLogDataValid_of_cachedCheck endpoint506PositiveFacts
    endpoint584PositiveFacts.valid leaf7146CoverageChecked

private noncomputable def leaf7146InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629961/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7146InputLogOnePlusV_eq :
    leaf7146InputLogOnePlusV = outerEnclosure 24
      (leaf7146Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7146RoundedFacts : LeafRoundedFacts 8
    leaf7146Certificate.logOnePlusV leaf7146InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7146InputLogOnePlusV_eq }

private noncomputable def leaf7146Inputs : Inputs :=
  inputsOfCaches globalInput sk125RoundedInputs
    chi95InputQChi innerPair818Input
    leaf7146InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7146LowerChecked :
    lowerCheck 24 leaf7146Box leaf7146Inputs = true := by
  rfl'

private theorem leaf7146CoversExact : CoversExact 8
    leaf7146Box leaf7146Certificate leaf7146InnerLog leaf7146Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk125RoundedFacts chi95RoundedFacts
    innerPair818RoundedFacts leaf7146RoundedFacts (by rfl)

private theorem leaf7146FlatSound : Sound leaf7146Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7146CertificateValid
    leaf7146InnerLogValid leaf7146CoversExact leaf7146LowerChecked

private noncomputable def leaf7147Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (31/32), chiHi := (1) }

private noncomputable def leaf7147Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (33554599/33554432) }, vSqrt := { lower := (65529/65536), upper := (5726109695/5725487104) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (137127591/134217728) }, upper := { exponent := 2, mantissa := (17/16) } }, logOuter := sk126LogOuterCertificate, logK := sk126LogKCertificate, logChi := chi95LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (11451596799/11450974208) } }, logDArg := sk126LogDArgCertificate }

private noncomputable def leaf7147InnerLog : WideLogData :=
  innerPair869Data

set_option maxRecDepth 1000000 in
private theorem leaf7147LocalValidity :
    LeafFacts leaf7147Box leaf7147Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7147Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (5726109695/5725487104) }) = true
      norm_num [leaf7147Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7147CertificateValid :
    WideCertificateValid leaf7147Box leaf7147Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk126ValidityFacts chi95ValidityFacts
    leaf7147LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7147CoverageChecked :
    coverageCheck (innerAD leaf7147Box) leaf7147InnerLog = true := by
  rfl'

private theorem leaf7147InnerLogValid :
    leaf7147InnerLog.Valid 8 (innerAD leaf7147Box) :=
  wideLogDataValid_of_cachedCheck endpoint582PositiveFacts
    endpoint585PositiveFacts.valid leaf7147CoverageChecked

private noncomputable def leaf7147InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629993/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7147InputLogOnePlusV_eq :
    leaf7147InputLogOnePlusV = outerEnclosure 24
      (leaf7147Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7147RoundedFacts : LeafRoundedFacts 8
    leaf7147Certificate.logOnePlusV leaf7147InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7147InputLogOnePlusV_eq }

private noncomputable def leaf7147Inputs : Inputs :=
  inputsOfCaches globalInput sk126RoundedInputs
    chi95InputQChi innerPair869Input
    leaf7147InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7147LowerChecked :
    lowerCheck 24 leaf7147Box leaf7147Inputs = true := by
  rfl'

private theorem leaf7147CoversExact : CoversExact 8
    leaf7147Box leaf7147Certificate leaf7147InnerLog leaf7147Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk126RoundedFacts chi95RoundedFacts
    innerPair869RoundedFacts leaf7147RoundedFacts (by rfl)

private theorem leaf7147FlatSound : Sound leaf7147Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7147CertificateValid
    leaf7147InnerLogValid leaf7147CoversExact leaf7147LowerChecked

private noncomputable def leaf7148Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (7/8), chiHi := (29/32) }

private noncomputable def leaf7148Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (33554595/33554432) }, vSqrt := { lower := (65529/65536), upper := (17178329085/17176721408) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (128936095/67108864) }, upper := { exponent := 2, mantissa := (2049/2048) } }, logOuter := sk131LogOuterCertificate, logK := sk131LogKCertificate, logChi := chi92LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (34355050493/34353442816) } }, logDArg := sk131LogDArgCertificate }

private noncomputable def leaf7148InnerLog : WideLogData :=
  innerPair880Data

set_option maxRecDepth 1000000 in
private theorem leaf7148LocalValidity :
    LeafFacts leaf7148Box leaf7148Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7148Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (17178329085/17176721408) }) = true
      norm_num [leaf7148Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7148CertificateValid :
    WideCertificateValid leaf7148Box leaf7148Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk131ValidityFacts chi92ValidityFacts
    leaf7148LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7148CoverageChecked :
    coverageCheck (innerAD leaf7148Box) leaf7148InnerLog = true := by
  rfl'

private theorem leaf7148InnerLogValid :
    leaf7148InnerLog.Valid 8 (innerAD leaf7148Box) :=
  wideLogDataValid_of_cachedCheck endpoint586PositiveFacts
    endpoint587PositiveFacts.valid leaf7148CoverageChecked

private noncomputable def leaf7148InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814933/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf7148InputLogOnePlusV_eq :
    leaf7148InputLogOnePlusV = outerEnclosure 24
      (leaf7148Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7148RoundedFacts : LeafRoundedFacts 8
    leaf7148Certificate.logOnePlusV leaf7148InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7148InputLogOnePlusV_eq }

private noncomputable def leaf7148Inputs : Inputs :=
  inputsOfCaches globalInput sk131RoundedInputs
    chi92InputQChi innerPair880Input
    leaf7148InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7148LowerChecked :
    lowerCheck 24 leaf7148Box leaf7148Inputs = true := by
  rfl'

private theorem leaf7148CoversExact : CoversExact 8
    leaf7148Box leaf7148Certificate leaf7148InnerLog leaf7148Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk131RoundedFacts chi92RoundedFacts
    innerPair880RoundedFacts leaf7148RoundedFacts (by rfl)

private theorem leaf7148FlatSound : Sound leaf7148Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7148CertificateValid
    leaf7148InnerLogValid leaf7148CoversExact leaf7148LowerChecked

private noncomputable def leaf7149Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (7/8), chiHi := (29/32) }

private noncomputable def leaf7149Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (33554597/33554432) }, vSqrt := { lower := (65529/65536), upper := (17178329085/17176662016) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (130770989/67108864) }, upper := { exponent := 2, mantissa := (1039/1024) } }, logOuter := sk132LogOuterCertificate, logK := sk132LogKCertificate, logChi := chi92LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (34354991101/34353324032) } }, logDArg := sk132LogDArgCertificate }

private noncomputable def leaf7149InnerLog : WideLogData :=
  innerPair812Data

set_option maxRecDepth 1000000 in
private theorem leaf7149LocalValidity :
    LeafFacts leaf7149Box leaf7149Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7149Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (17178329085/17176662016) }) = true
      norm_num [leaf7149Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7149CertificateValid :
    WideCertificateValid leaf7149Box leaf7149Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk132ValidityFacts chi92ValidityFacts
    leaf7149LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7149CoverageChecked :
    coverageCheck (innerAD leaf7149Box) leaf7149InnerLog = true := by
  rfl'

private theorem leaf7149InnerLogValid :
    leaf7149InnerLog.Valid 8 (innerAD leaf7149Box) :=
  wideLogDataValid_of_cachedCheck endpoint504PositiveFacts
    endpoint582PositiveFacts.valid leaf7149CoverageChecked

private noncomputable def leaf7149InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629895/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7149InputLogOnePlusV_eq :
    leaf7149InputLogOnePlusV = outerEnclosure 24
      (leaf7149Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7149RoundedFacts : LeafRoundedFacts 8
    leaf7149Certificate.logOnePlusV leaf7149InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7149InputLogOnePlusV_eq }

private noncomputable def leaf7149Inputs : Inputs :=
  inputsOfCaches globalInput sk132RoundedInputs
    chi92InputQChi innerPair812Input
    leaf7149InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7149LowerChecked :
    lowerCheck 24 leaf7149Box leaf7149Inputs = true := by
  rfl'

private theorem leaf7149CoversExact : CoversExact 8
    leaf7149Box leaf7149Certificate leaf7149InnerLog leaf7149Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk132RoundedFacts chi92RoundedFacts
    innerPair812RoundedFacts leaf7149RoundedFacts (by rfl)

private theorem leaf7149FlatSound : Sound leaf7149Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7149CertificateValid
    leaf7149InnerLogValid leaf7149CoversExact leaf7149LowerChecked

private noncomputable def leaf7150Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (29/32), chiHi := (15/16) }

private noncomputable def leaf7150Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (33554597/33554432) }, vSqrt := { lower := (65529/65536), upper := (17178329085/17176612864) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (132343757/67108864) }, upper := { exponent := 2, mantissa := (1051/1024) } }, logOuter := sk131LogOuterCertificate, logK := sk131LogKCertificate, logChi := chi93LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (34354941949/34353225728) } }, logDArg := sk131LogDArgCertificate }

private noncomputable def leaf7150InnerLog : WideLogData :=
  innerPair815Data

set_option maxRecDepth 1000000 in
private theorem leaf7150LocalValidity :
    LeafFacts leaf7150Box leaf7150Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7150Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (17178329085/17176612864) }) = true
      norm_num [leaf7150Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7150CertificateValid :
    WideCertificateValid leaf7150Box leaf7150Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk131ValidityFacts chi93ValidityFacts
    leaf7150LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7150CoverageChecked :
    coverageCheck (innerAD leaf7150Box) leaf7150InnerLog = true := by
  rfl'

private theorem leaf7150InnerLogValid :
    leaf7150InnerLog.Valid 8 (innerAD leaf7150Box) :=
  wideLogDataValid_of_cachedCheck endpoint505PositiveFacts
    endpoint583PositiveFacts.valid leaf7150CoverageChecked

private noncomputable def leaf7150InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629919/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7150InputLogOnePlusV_eq :
    leaf7150InputLogOnePlusV = outerEnclosure 24
      (leaf7150Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7150RoundedFacts : LeafRoundedFacts 8
    leaf7150Certificate.logOnePlusV leaf7150InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7150InputLogOnePlusV_eq }

private noncomputable def leaf7150Inputs : Inputs :=
  inputsOfCaches globalInput sk131RoundedInputs
    chi93InputQChi innerPair815Input
    leaf7150InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7150LowerChecked :
    lowerCheck 24 leaf7150Box leaf7150Inputs = true := by
  rfl'

private theorem leaf7150CoversExact : CoversExact 8
    leaf7150Box leaf7150Certificate leaf7150InnerLog leaf7150Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk131RoundedFacts chi93RoundedFacts
    innerPair815RoundedFacts leaf7150RoundedFacts (by rfl)

private theorem leaf7150FlatSound : Sound leaf7150Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7150CertificateValid
    leaf7150InnerLogValid leaf7150CoversExact leaf7150LowerChecked

private noncomputable def leaf7151Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (29/32), chiHi := (15/16) }

private noncomputable def leaf7151Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (33554599/33554432) }, vSqrt := { lower := (65529/65536), upper := (17178329085/17176551424) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (134244183/134217728) }, upper := { exponent := 2, mantissa := (533/512) } }, logOuter := sk132LogOuterCertificate, logK := sk132LogKCertificate, logChi := chi93LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (34354880509/34353102848) } }, logDArg := sk132LogDArgCertificate }

private noncomputable def leaf7151InnerLog : WideLogData :=
  innerPair818Data

set_option maxRecDepth 1000000 in
private theorem leaf7151LocalValidity :
    LeafFacts leaf7151Box leaf7151Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7151Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (17178329085/17176551424) }) = true
      norm_num [leaf7151Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7151CertificateValid :
    WideCertificateValid leaf7151Box leaf7151Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk132ValidityFacts chi93ValidityFacts
    leaf7151LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7151CoverageChecked :
    coverageCheck (innerAD leaf7151Box) leaf7151InnerLog = true := by
  rfl'

private theorem leaf7151InnerLogValid :
    leaf7151InnerLog.Valid 8 (innerAD leaf7151Box) :=
  wideLogDataValid_of_cachedCheck endpoint506PositiveFacts
    endpoint584PositiveFacts.valid leaf7151CoverageChecked

private noncomputable def leaf7151InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629949/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7151InputLogOnePlusV_eq :
    leaf7151InputLogOnePlusV = outerEnclosure 24
      (leaf7151Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7151RoundedFacts : LeafRoundedFacts 8
    leaf7151Certificate.logOnePlusV leaf7151InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7151InputLogOnePlusV_eq }

private noncomputable def leaf7151Inputs : Inputs :=
  inputsOfCaches globalInput sk132RoundedInputs
    chi93InputQChi innerPair818Input
    leaf7151InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7151LowerChecked :
    lowerCheck 24 leaf7151Box leaf7151Inputs = true := by
  rfl'

private theorem leaf7151CoversExact : CoversExact 8
    leaf7151Box leaf7151Certificate leaf7151InnerLog leaf7151Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk132RoundedFacts chi93RoundedFacts
    innerPair818RoundedFacts leaf7151RoundedFacts (by rfl)

private theorem leaf7151FlatSound : Sound leaf7151Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7151CertificateValid
    leaf7151InnerLogValid leaf7151CoversExact leaf7151LowerChecked

private noncomputable def leaf7152Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (7/8), chiHi := (29/32) }

private noncomputable def leaf7152Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (33554599/33554432) }, vSqrt := { lower := (8191/8192), upper := (5726109695/5725534208) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (132605883/67108864) }, upper := { exponent := 2, mantissa := (2107/2048) } }, logOuter := sk129LogOuterCertificate, logK := sk129LogKCertificate, logChi := chi92LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (11451643903/11451068416) } }, logDArg := sk129LogDArgCertificate }

private noncomputable def leaf7152InnerLog : WideLogData :=
  innerPair815Data

set_option maxRecDepth 1000000 in
private theorem leaf7152LocalValidity :
    LeafFacts leaf7152Box leaf7152Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7152Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5726109695/5725534208) }) = true
      norm_num [leaf7152Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7152CertificateValid :
    WideCertificateValid leaf7152Box leaf7152Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk129ValidityFacts chi92ValidityFacts
    leaf7152LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7152CoverageChecked :
    coverageCheck (innerAD leaf7152Box) leaf7152InnerLog = true := by
  rfl'

private theorem leaf7152InnerLogValid :
    leaf7152InnerLog.Valid 8 (innerAD leaf7152Box) :=
  wideLogDataValid_of_cachedCheck endpoint505PositiveFacts
    endpoint583PositiveFacts.valid leaf7152CoverageChecked

private noncomputable def leaf7152InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907481/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf7152InputLogOnePlusV_eq :
    leaf7152InputLogOnePlusV = outerEnclosure 24
      (leaf7152Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7152RoundedFacts : LeafRoundedFacts 8
    leaf7152Certificate.logOnePlusV leaf7152InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7152InputLogOnePlusV_eq }

private noncomputable def leaf7152Inputs : Inputs :=
  inputsOfCaches globalInput sk129RoundedInputs
    chi92InputQChi innerPair815Input
    leaf7152InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7152LowerChecked :
    lowerCheck 24 leaf7152Box leaf7152Inputs = true := by
  rfl'

private theorem leaf7152CoversExact : CoversExact 8
    leaf7152Box leaf7152Certificate leaf7152InnerLog leaf7152Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk129RoundedFacts chi92RoundedFacts
    innerPair815RoundedFacts leaf7152RoundedFacts (by rfl)

private theorem leaf7152FlatSound : Sound leaf7152Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7152CertificateValid
    leaf7152InnerLogValid leaf7152CoversExact leaf7152LowerChecked

private noncomputable def leaf7153Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (7/8), chiHi := (29/32) }

private noncomputable def leaf7153Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (33554601/33554432) }, vSqrt := { lower := (8191/8192), upper := (17178329085/17176543232) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (134440777/134217728) }, upper := { exponent := 2, mantissa := (267/256) } }, logOuter := sk130LogOuterCertificate, logK := sk130LogKCertificate, logChi := chi92LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34354872317/34353086464) } }, logDArg := sk130LogDArgCertificate }

private noncomputable def leaf7153InnerLog : WideLogData :=
  innerPair820Data

set_option maxRecDepth 1000000 in
private theorem leaf7153LocalValidity :
    LeafFacts leaf7153Box leaf7153Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7153Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178329085/17176543232) }) = true
      norm_num [leaf7153Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7153CertificateValid :
    WideCertificateValid leaf7153Box leaf7153Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk130ValidityFacts chi92ValidityFacts
    leaf7153LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7153CoverageChecked :
    coverageCheck (innerAD leaf7153Box) leaf7153InnerLog = true := by
  rfl'

private theorem leaf7153InnerLogValid :
    leaf7153InnerLog.Valid 8 (innerAD leaf7153Box) :=
  wideLogDataValid_of_cachedCheck endpoint506PositiveFacts
    endpoint588PositiveFacts.valid leaf7153CoverageChecked

private noncomputable def leaf7153InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629953/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7153InputLogOnePlusV_eq :
    leaf7153InputLogOnePlusV = outerEnclosure 24
      (leaf7153Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7153RoundedFacts : LeafRoundedFacts 8
    leaf7153Certificate.logOnePlusV leaf7153InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7153InputLogOnePlusV_eq }

private noncomputable def leaf7153Inputs : Inputs :=
  inputsOfCaches globalInput sk130RoundedInputs
    chi92InputQChi innerPair820Input
    leaf7153InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7153LowerChecked :
    lowerCheck 24 leaf7153Box leaf7153Inputs = true := by
  rfl'

private theorem leaf7153CoversExact : CoversExact 8
    leaf7153Box leaf7153Certificate leaf7153InnerLog leaf7153Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk130RoundedFacts chi92RoundedFacts
    innerPair820RoundedFacts leaf7153RoundedFacts (by rfl)

private theorem leaf7153FlatSound : Sound leaf7153Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7153CertificateValid
    leaf7153InnerLogValid leaf7153CoversExact leaf7153LowerChecked

private noncomputable def leaf7154Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (29/32), chiHi := (15/16) }

private noncomputable def leaf7154Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (33554601/33554432) }, vSqrt := { lower := (8191/8192), upper := (17178329085/17176489984) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (136144609/134217728) }, upper := { exponent := 2, mantissa := (1081/1024) } }, logOuter := sk129LogOuterCertificate, logK := sk129LogKCertificate, logChi := chi93LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34354819069/34352979968) } }, logDArg := sk129LogDArgCertificate }

private noncomputable def leaf7154InnerLog : WideLogData :=
  innerPair819Data

set_option maxRecDepth 1000000 in
private theorem leaf7154LocalValidity :
    LeafFacts leaf7154Box leaf7154Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7154Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178329085/17176489984) }) = true
      norm_num [leaf7154Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7154CertificateValid :
    WideCertificateValid leaf7154Box leaf7154Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk129ValidityFacts chi93ValidityFacts
    leaf7154LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7154CoverageChecked :
    coverageCheck (innerAD leaf7154Box) leaf7154InnerLog = true := by
  rfl'

private theorem leaf7154InnerLogValid :
    leaf7154InnerLog.Valid 8 (innerAD leaf7154Box) :=
  wideLogDataValid_of_cachedCheck endpoint506PositiveFacts
    endpoint585PositiveFacts.valid leaf7154CoverageChecked

private noncomputable def leaf7154InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629979/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7154InputLogOnePlusV_eq :
    leaf7154InputLogOnePlusV = outerEnclosure 24
      (leaf7154Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7154RoundedFacts : LeafRoundedFacts 8
    leaf7154Certificate.logOnePlusV leaf7154InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7154InputLogOnePlusV_eq }

private noncomputable def leaf7154Inputs : Inputs :=
  inputsOfCaches globalInput sk129RoundedInputs
    chi93InputQChi innerPair819Input
    leaf7154InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7154LowerChecked :
    lowerCheck 24 leaf7154Box leaf7154Inputs = true := by
  rfl'

private theorem leaf7154CoversExact : CoversExact 8
    leaf7154Box leaf7154Certificate leaf7154InnerLog leaf7154Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk129RoundedFacts chi93RoundedFacts
    innerPair819RoundedFacts leaf7154RoundedFacts (by rfl)

private theorem leaf7154FlatSound : Sound leaf7154Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7154CertificateValid
    leaf7154InnerLogValid leaf7154CoversExact leaf7154LowerChecked

private noncomputable def leaf7155Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (29/32), chiHi := (15/16) }

private noncomputable def leaf7155Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (33554603/33554432) }, vSqrt := { lower := (8191/8192), upper := (17178329085/17176428544) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (138045035/134217728) }, upper := { exponent := 2, mantissa := (137/128) } }, logOuter := sk130LogOuterCertificate, logK := sk130LogKCertificate, logChi := chi93LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34354757629/34352857088) } }, logDArg := sk130LogDArgCertificate }

private noncomputable def leaf7155InnerLog : WideLogData :=
  innerPair870Data

set_option maxRecDepth 1000000 in
private theorem leaf7155LocalValidity :
    LeafFacts leaf7155Box leaf7155Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7155Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178329085/17176428544) }) = true
      norm_num [leaf7155Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7155CertificateValid :
    WideCertificateValid leaf7155Box leaf7155Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk130ValidityFacts chi93ValidityFacts
    leaf7155LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7155CoverageChecked :
    coverageCheck (innerAD leaf7155Box) leaf7155InnerLog = true := by
  rfl'

private theorem leaf7155InnerLogValid :
    leaf7155InnerLog.Valid 8 (innerAD leaf7155Box) :=
  wideLogDataValid_of_cachedCheck endpoint582PositiveFacts
    endpoint589PositiveFacts.valid leaf7155CoverageChecked

private noncomputable def leaf7155InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11630009/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7155InputLogOnePlusV_eq :
    leaf7155InputLogOnePlusV = outerEnclosure 24
      (leaf7155Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7155RoundedFacts : LeafRoundedFacts 8
    leaf7155Certificate.logOnePlusV leaf7155InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7155InputLogOnePlusV_eq }

private noncomputable def leaf7155Inputs : Inputs :=
  inputsOfCaches globalInput sk130RoundedInputs
    chi93InputQChi innerPair870Input
    leaf7155InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7155LowerChecked :
    lowerCheck 24 leaf7155Box leaf7155Inputs = true := by
  rfl'

private theorem leaf7155CoversExact : CoversExact 8
    leaf7155Box leaf7155Certificate leaf7155InnerLog leaf7155Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk130RoundedFacts chi93RoundedFacts
    innerPair870RoundedFacts leaf7155RoundedFacts (by rfl)

private theorem leaf7155FlatSound : Sound leaf7155Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7155CertificateValid
    leaf7155InnerLogValid leaf7155CoversExact leaf7155LowerChecked

private noncomputable def leaf7156Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (15/16), chiHi := (31/32) }

private noncomputable def leaf7156Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (33554599/33554432) }, vSqrt := { lower := (65529/65536), upper := (1145221939/1145100288) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (135751419/134217728) }, upper := { exponent := 2, mantissa := (2155/2048) } }, logOuter := sk131LogOuterCertificate, logK := sk131LogKCertificate, logChi := chi94LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (2290322227/2290200576) } }, logDArg := sk131LogDArgCertificate }

private noncomputable def leaf7156InnerLog : WideLogData :=
  innerPair819Data

set_option maxRecDepth 1000000 in
private theorem leaf7156LocalValidity :
    LeafFacts leaf7156Box leaf7156Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7156Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (1145221939/1145100288) }) = true
      norm_num [leaf7156Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7156CertificateValid :
    WideCertificateValid leaf7156Box leaf7156Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk131ValidityFacts chi94ValidityFacts
    leaf7156LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7156CoverageChecked :
    coverageCheck (innerAD leaf7156Box) leaf7156InnerLog = true := by
  rfl'

private theorem leaf7156InnerLogValid :
    leaf7156InnerLog.Valid 8 (innerAD leaf7156Box) :=
  wideLogDataValid_of_cachedCheck endpoint506PositiveFacts
    endpoint585PositiveFacts.valid leaf7156CoverageChecked

private noncomputable def leaf7156InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907493/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf7156InputLogOnePlusV_eq :
    leaf7156InputLogOnePlusV = outerEnclosure 24
      (leaf7156Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7156RoundedFacts : LeafRoundedFacts 8
    leaf7156Certificate.logOnePlusV leaf7156InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7156InputLogOnePlusV_eq }

private noncomputable def leaf7156Inputs : Inputs :=
  inputsOfCaches globalInput sk131RoundedInputs
    chi94InputQChi innerPair819Input
    leaf7156InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7156LowerChecked :
    lowerCheck 24 leaf7156Box leaf7156Inputs = true := by
  rfl'

private theorem leaf7156CoversExact : CoversExact 8
    leaf7156Box leaf7156Certificate leaf7156InnerLog leaf7156Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk131RoundedFacts chi94RoundedFacts
    innerPair819RoundedFacts leaf7156RoundedFacts (by rfl)

private theorem leaf7156FlatSound : Sound leaf7156Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7156CertificateValid
    leaf7156InnerLogValid leaf7156CoversExact leaf7156LowerChecked

private noncomputable def leaf7157Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (15/16), chiHi := (31/32) }

private noncomputable def leaf7157Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (33554601/33554432) }, vSqrt := { lower := (65529/65536), upper := (17178329085/17176440832) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (137717377/134217728) }, upper := { exponent := 2, mantissa := (1093/1024) } }, logOuter := sk132LogOuterCertificate, logK := sk132LogKCertificate, logChi := chi94LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (34354769917/34352881664) } }, logDArg := sk132LogDArgCertificate }

private noncomputable def leaf7157InnerLog : WideLogData :=
  innerPair870Data

set_option maxRecDepth 1000000 in
private theorem leaf7157LocalValidity :
    LeafFacts leaf7157Box leaf7157Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7157Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (17178329085/17176440832) }) = true
      norm_num [leaf7157Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7157CertificateValid :
    WideCertificateValid leaf7157Box leaf7157Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk132ValidityFacts chi94ValidityFacts
    leaf7157LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7157CoverageChecked :
    coverageCheck (innerAD leaf7157Box) leaf7157InnerLog = true := by
  rfl'

private theorem leaf7157InnerLogValid :
    leaf7157InnerLog.Valid 8 (innerAD leaf7157Box) :=
  wideLogDataValid_of_cachedCheck endpoint582PositiveFacts
    endpoint589PositiveFacts.valid leaf7157CoverageChecked

private noncomputable def leaf7157InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11630003/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7157InputLogOnePlusV_eq :
    leaf7157InputLogOnePlusV = outerEnclosure 24
      (leaf7157Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7157RoundedFacts : LeafRoundedFacts 8
    leaf7157Certificate.logOnePlusV leaf7157InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7157InputLogOnePlusV_eq }

private noncomputable def leaf7157Inputs : Inputs :=
  inputsOfCaches globalInput sk132RoundedInputs
    chi94InputQChi innerPair870Input
    leaf7157InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7157LowerChecked :
    lowerCheck 24 leaf7157Box leaf7157Inputs = true := by
  rfl'

private theorem leaf7157CoversExact : CoversExact 8
    leaf7157Box leaf7157Certificate leaf7157InnerLog leaf7157Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk132RoundedFacts chi94RoundedFacts
    innerPair870RoundedFacts leaf7157RoundedFacts (by rfl)

private theorem leaf7157FlatSound : Sound leaf7157Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7157CertificateValid
    leaf7157InnerLogValid leaf7157CoversExact leaf7157LowerChecked

private noncomputable def leaf7158Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (31/32), chiHi := (1) }

private noncomputable def leaf7158Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (33554601/33554432) }, vSqrt := { lower := (65529/65536), upper := (17178329085/17176395776) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (139159081/134217728) }, upper := { exponent := 2, mantissa := (69/64) } }, logOuter := sk131LogOuterCertificate, logK := sk131LogKCertificate, logChi := chi95LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (34354724861/34352791552) } }, logDArg := sk131LogDArgCertificate }

private noncomputable def leaf7158InnerLog : WideLogData :=
  innerPair872Data

set_option maxRecDepth 1000000 in
private theorem leaf7158LocalValidity :
    LeafFacts leaf7158Box leaf7158Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7158Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (17178329085/17176395776) }) = true
      norm_num [leaf7158Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7158CertificateValid :
    WideCertificateValid leaf7158Box leaf7158Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk131ValidityFacts chi95ValidityFacts
    leaf7158LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7158CoverageChecked :
    coverageCheck (innerAD leaf7158Box) leaf7158InnerLog = true := by
  rfl'

private theorem leaf7158InnerLogValid :
    leaf7158InnerLog.Valid 8 (innerAD leaf7158Box) :=
  wideLogDataValid_of_cachedCheck endpoint583PositiveFacts
    endpoint589PositiveFacts.valid leaf7158CoverageChecked

private noncomputable def leaf7158InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11630025/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7158InputLogOnePlusV_eq :
    leaf7158InputLogOnePlusV = outerEnclosure 24
      (leaf7158Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7158RoundedFacts : LeafRoundedFacts 8
    leaf7158Certificate.logOnePlusV leaf7158InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7158InputLogOnePlusV_eq }

private noncomputable def leaf7158Inputs : Inputs :=
  inputsOfCaches globalInput sk131RoundedInputs
    chi95InputQChi innerPair872Input
    leaf7158InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7158LowerChecked :
    lowerCheck 24 leaf7158Box leaf7158Inputs = true := by
  rfl'

private theorem leaf7158CoversExact : CoversExact 8
    leaf7158Box leaf7158Certificate leaf7158InnerLog leaf7158Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk131RoundedFacts chi95RoundedFacts
    innerPair872RoundedFacts leaf7158RoundedFacts (by rfl)

private theorem leaf7158FlatSound : Sound leaf7158Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7158CertificateValid
    leaf7158InnerLogValid leaf7158CoversExact leaf7158LowerChecked

private noncomputable def leaf7159Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (31/32), chiHi := (1) }

private noncomputable def leaf7159Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (33554603/33554432) }, vSqrt := { lower := (65529/65536), upper := (3435665817/3435266048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (141190571/134217728) }, upper := { exponent := 2, mantissa := (35/32) } }, logOuter := sk132LogOuterCertificate, logK := sk132LogKCertificate, logChi := chi95LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (6870931865/6870532096) } }, logDArg := sk132LogDArgCertificate }

private noncomputable def leaf7159InnerLog : WideLogData :=
  innerPair875Data

set_option maxRecDepth 1000000 in
private theorem leaf7159LocalValidity :
    LeafFacts leaf7159Box leaf7159Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7159Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (3435665817/3435266048) }) = true
      norm_num [leaf7159Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7159CertificateValid :
    WideCertificateValid leaf7159Box leaf7159Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk132ValidityFacts chi95ValidityFacts
    leaf7159LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7159CoverageChecked :
    coverageCheck (innerAD leaf7159Box) leaf7159InnerLog = true := by
  rfl'

private theorem leaf7159InnerLogValid :
    leaf7159InnerLog.Valid 8 (innerAD leaf7159Box) :=
  wideLogDataValid_of_cachedCheck endpoint584PositiveFacts
    endpoint590PositiveFacts.valid leaf7159CoverageChecked

private noncomputable def leaf7159InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11630057/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7159InputLogOnePlusV_eq :
    leaf7159InputLogOnePlusV = outerEnclosure 24
      (leaf7159Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7159RoundedFacts : LeafRoundedFacts 8
    leaf7159Certificate.logOnePlusV leaf7159InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7159InputLogOnePlusV_eq }

private noncomputable def leaf7159Inputs : Inputs :=
  inputsOfCaches globalInput sk132RoundedInputs
    chi95InputQChi innerPair875Input
    leaf7159InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7159LowerChecked :
    lowerCheck 24 leaf7159Box leaf7159Inputs = true := by
  rfl'

private theorem leaf7159CoversExact : CoversExact 8
    leaf7159Box leaf7159Certificate leaf7159InnerLog leaf7159Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk132RoundedFacts chi95RoundedFacts
    innerPair875RoundedFacts leaf7159RoundedFacts (by rfl)

private theorem leaf7159FlatSound : Sound leaf7159Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7159CertificateValid
    leaf7159InnerLogValid leaf7159CoversExact leaf7159LowerChecked

private noncomputable def leaf7160Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (15/16), chiHi := (31/32) }

private noncomputable def leaf7160Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (33554603/33554432) }, vSqrt := { lower := (8191/8192), upper := (17178329085/17176377344) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (139683335/134217728) }, upper := { exponent := 2, mantissa := (2217/2048) } }, logOuter := sk129LogOuterCertificate, logK := sk129LogKCertificate, logChi := chi94LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34354706429/34352754688) } }, logDArg := sk129LogDArgCertificate }

private noncomputable def leaf7160InnerLog : WideLogData :=
  innerPair873Data

set_option maxRecDepth 1000000 in
private theorem leaf7160LocalValidity :
    LeafFacts leaf7160Box leaf7160Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7160Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178329085/17176377344) }) = true
      norm_num [leaf7160Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7160CertificateValid :
    WideCertificateValid leaf7160Box leaf7160Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk129ValidityFacts chi94ValidityFacts
    leaf7160LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7160CoverageChecked :
    coverageCheck (innerAD leaf7160Box) leaf7160InnerLog = true := by
  rfl'

private theorem leaf7160InnerLogValid :
    leaf7160InnerLog.Valid 8 (innerAD leaf7160Box) :=
  wideLogDataValid_of_cachedCheck endpoint583PositiveFacts
    endpoint590PositiveFacts.valid leaf7160CoverageChecked

private noncomputable def leaf7160InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5815017/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf7160InputLogOnePlusV_eq :
    leaf7160InputLogOnePlusV = outerEnclosure 24
      (leaf7160Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7160RoundedFacts : LeafRoundedFacts 8
    leaf7160Certificate.logOnePlusV leaf7160InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7160InputLogOnePlusV_eq }

private noncomputable def leaf7160Inputs : Inputs :=
  inputsOfCaches globalInput sk129RoundedInputs
    chi94InputQChi innerPair873Input
    leaf7160InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7160LowerChecked :
    lowerCheck 24 leaf7160Box leaf7160Inputs = true := by
  rfl'

private theorem leaf7160CoversExact : CoversExact 8
    leaf7160Box leaf7160Certificate leaf7160InnerLog leaf7160Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk129RoundedFacts chi94RoundedFacts
    innerPair873RoundedFacts leaf7160RoundedFacts (by rfl)

private theorem leaf7160FlatSound : Sound leaf7160Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7160CertificateValid
    leaf7160InnerLogValid leaf7160CoversExact leaf7160LowerChecked

private noncomputable def leaf7161Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (15/16), chiHi := (31/32) }

private noncomputable def leaf7161Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (33554605/33554432) }, vSqrt := { lower := (8191/8192), upper := (5726109695/5725437952) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (141649293/134217728) }, upper := { exponent := 2, mantissa := (281/256) } }, logOuter := sk130LogOuterCertificate, logK := sk130LogKCertificate, logChi := chi94LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (11451547647/11450875904) } }, logDArg := sk130LogDArgCertificate }

private noncomputable def leaf7161InnerLog : WideLogData :=
  innerPair876Data

set_option maxRecDepth 1000000 in
private theorem leaf7161LocalValidity :
    LeafFacts leaf7161Box leaf7161Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7161Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5726109695/5725437952) }) = true
      norm_num [leaf7161Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7161CertificateValid :
    WideCertificateValid leaf7161Box leaf7161Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk130ValidityFacts chi94ValidityFacts
    leaf7161LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7161CoverageChecked :
    coverageCheck (innerAD leaf7161Box) leaf7161InnerLog = true := by
  rfl'

private theorem leaf7161InnerLogValid :
    leaf7161InnerLog.Valid 8 (innerAD leaf7161Box) :=
  wideLogDataValid_of_cachedCheck endpoint584PositiveFacts
    endpoint591PositiveFacts.valid leaf7161CoverageChecked

private noncomputable def leaf7161InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11630065/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7161InputLogOnePlusV_eq :
    leaf7161InputLogOnePlusV = outerEnclosure 24
      (leaf7161Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7161RoundedFacts : LeafRoundedFacts 8
    leaf7161Certificate.logOnePlusV leaf7161InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7161InputLogOnePlusV_eq }

private noncomputable def leaf7161Inputs : Inputs :=
  inputsOfCaches globalInput sk130RoundedInputs
    chi94InputQChi innerPair876Input
    leaf7161InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7161LowerChecked :
    lowerCheck 24 leaf7161Box leaf7161Inputs = true := by
  rfl'

private theorem leaf7161CoversExact : CoversExact 8
    leaf7161Box leaf7161Certificate leaf7161InnerLog leaf7161Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk130RoundedFacts chi94RoundedFacts
    innerPair876RoundedFacts leaf7161RoundedFacts (by rfl)

private theorem leaf7161FlatSound : Sound leaf7161Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7161CertificateValid
    leaf7161InnerLogValid leaf7161CoversExact leaf7161LowerChecked

private noncomputable def leaf7162Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (31/32), chiHi := (1) }

private noncomputable def leaf7162Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (33554605/33554432) }, vSqrt := { lower := (8191/8192), upper := (5726109695/5725421568) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (143222061/134217728) }, upper := { exponent := 2, mantissa := (71/64) } }, logOuter := sk129LogOuterCertificate, logK := sk129LogKCertificate, logChi := chi95LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (11451531263/11450843136) } }, logDArg := sk129LogDArgCertificate }

private noncomputable def leaf7162InnerLog : WideLogData :=
  innerPair878Data

set_option maxRecDepth 1000000 in
private theorem leaf7162LocalValidity :
    LeafFacts leaf7162Box leaf7162Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7162Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5726109695/5725421568) }) = true
      norm_num [leaf7162Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7162CertificateValid :
    WideCertificateValid leaf7162Box leaf7162Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk129ValidityFacts chi95ValidityFacts
    leaf7162LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7162CoverageChecked :
    coverageCheck (innerAD leaf7162Box) leaf7162InnerLog = true := by
  rfl'

private theorem leaf7162InnerLogValid :
    leaf7162InnerLog.Valid 8 (innerAD leaf7162Box) :=
  wideLogDataValid_of_cachedCheck endpoint585PositiveFacts
    endpoint591PositiveFacts.valid leaf7162CoverageChecked

private noncomputable def leaf7162InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11630089/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7162InputLogOnePlusV_eq :
    leaf7162InputLogOnePlusV = outerEnclosure 24
      (leaf7162Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7162RoundedFacts : LeafRoundedFacts 8
    leaf7162Certificate.logOnePlusV leaf7162InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7162InputLogOnePlusV_eq }

private noncomputable def leaf7162Inputs : Inputs :=
  inputsOfCaches globalInput sk129RoundedInputs
    chi95InputQChi innerPair878Input
    leaf7162InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7162LowerChecked :
    lowerCheck 24 leaf7162Box leaf7162Inputs = true := by
  rfl'

private theorem leaf7162CoversExact : CoversExact 8
    leaf7162Box leaf7162Certificate leaf7162InnerLog leaf7162Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk129RoundedFacts chi95RoundedFacts
    innerPair878RoundedFacts leaf7162RoundedFacts (by rfl)

private theorem leaf7162FlatSound : Sound leaf7162Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7162CertificateValid
    leaf7162InnerLogValid leaf7162CoversExact leaf7162LowerChecked

private noncomputable def leaf7163Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (31/32), chiHi := (1) }

private noncomputable def leaf7163Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (8191/8192), upper := (33554607/33554432) }, vSqrt := { lower := (8191/8192), upper := (34356133881/34352398336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (145253551/134217728) }, upper := { exponent := 2, mantissa := (9/8) } }, logOuter := sk130LogOuterCertificate, logK := sk130LogKCertificate, logChi := chi95LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68708532217/68704796672) } }, logDArg := sk130LogDArgCertificate }

private noncomputable def leaf7163InnerLog : WideLogData :=
  innerPair882Data

set_option maxRecDepth 1000000 in
private theorem leaf7163LocalValidity :
    LeafFacts leaf7163Box leaf7163Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7163Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34356133881/34352398336) }) = true
      norm_num [leaf7163Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7163CertificateValid :
    WideCertificateValid leaf7163Box leaf7163Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk130ValidityFacts chi95ValidityFacts
    leaf7163LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7163CoverageChecked :
    coverageCheck (innerAD leaf7163Box) leaf7163InnerLog = true := by
  rfl'

private theorem leaf7163InnerLogValid :
    leaf7163InnerLog.Valid 8 (innerAD leaf7163Box) :=
  wideLogDataValid_of_cachedCheck endpoint589PositiveFacts
    endpoint592PositiveFacts.valid leaf7163CoverageChecked

private noncomputable def leaf7163InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629993/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7163InputLogOnePlusV_eq :
    leaf7163InputLogOnePlusV = outerEnclosure 24
      (leaf7163Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7163RoundedFacts : LeafRoundedFacts 8
    leaf7163Certificate.logOnePlusV leaf7163InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7163InputLogOnePlusV_eq }

private noncomputable def leaf7163Inputs : Inputs :=
  inputsOfCaches globalInput sk130RoundedInputs
    chi95InputQChi innerPair882Input
    leaf7163InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7163LowerChecked :
    lowerCheck 24 leaf7163Box leaf7163Inputs = true := by
  rfl'

private theorem leaf7163CoversExact : CoversExact 8
    leaf7163Box leaf7163Certificate leaf7163InnerLog leaf7163Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk130RoundedFacts chi95RoundedFacts
    innerPair882RoundedFacts leaf7163RoundedFacts (by rfl)

private theorem leaf7163FlatSound : Sound leaf7163Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7163CertificateValid
    leaf7163InnerLogValid leaf7163CoversExact leaf7163LowerChecked

private noncomputable def component145Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (7/8), chiHi := (29/32) }

set_option maxRecDepth 1000000 in
private theorem component145Node0_sound : Sound component145Node0Box :=
  sound_of_literal_split component145Node0Box leaf7132Box leaf7133Box
    .k (49/16) (by rfl) (by rfl)
    leaf7132FlatSound leaf7133FlatSound

private noncomputable def component145Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (29/32), chiHi := (15/16) }

set_option maxRecDepth 1000000 in
private theorem component145Node1_sound : Sound component145Node1Box :=
  sound_of_literal_split component145Node1Box leaf7134Box leaf7135Box
    .k (49/16) (by rfl) (by rfl)
    leaf7134FlatSound leaf7135FlatSound

private noncomputable def component145Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (7/8), chiHi := (15/16) }

set_option maxRecDepth 1000000 in
private theorem component145Node2_sound : Sound component145Node2Box :=
  sound_of_literal_split component145Node2Box component145Node0Box component145Node1Box
    .chi (29/32) (by rfl) (by rfl)
    component145Node0_sound component145Node1_sound

private noncomputable def component145Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (7/8), chiHi := (29/32) }

set_option maxRecDepth 1000000 in
private theorem component145Node3_sound : Sound component145Node3Box :=
  sound_of_literal_split component145Node3Box leaf7136Box leaf7137Box
    .k (51/16) (by rfl) (by rfl)
    leaf7136FlatSound leaf7137FlatSound

private noncomputable def component145Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (29/32), chiHi := (15/16) }

set_option maxRecDepth 1000000 in
private theorem component145Node4_sound : Sound component145Node4Box :=
  sound_of_literal_split component145Node4Box leaf7138Box leaf7139Box
    .k (51/16) (by rfl) (by rfl)
    leaf7138FlatSound leaf7139FlatSound

private noncomputable def component145Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (7/8), chiHi := (15/16) }

set_option maxRecDepth 1000000 in
private theorem component145Node5_sound : Sound component145Node5Box :=
  sound_of_literal_split component145Node5Box component145Node3Box component145Node4Box
    .chi (29/32) (by rfl) (by rfl)
    component145Node3_sound component145Node4_sound

private noncomputable def component145Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (13/4), chiLo := (7/8), chiHi := (15/16) }

set_option maxRecDepth 1000000 in
private theorem component145Node6_sound : Sound component145Node6Box :=
  sound_of_literal_split component145Node6Box component145Node2Box component145Node5Box
    .k (25/8) (by rfl) (by rfl)
    component145Node2_sound component145Node5_sound

private noncomputable def component145Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (15/16), chiHi := (31/32) }

set_option maxRecDepth 1000000 in
private theorem component145Node7_sound : Sound component145Node7Box :=
  sound_of_literal_split component145Node7Box leaf7140Box leaf7141Box
    .k (49/16) (by rfl) (by rfl)
    leaf7140FlatSound leaf7141FlatSound

private noncomputable def component145Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (31/32), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component145Node8_sound : Sound component145Node8Box :=
  sound_of_literal_split component145Node8Box leaf7142Box leaf7143Box
    .k (49/16) (by rfl) (by rfl)
    leaf7142FlatSound leaf7143FlatSound

private noncomputable def component145Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (15/16), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component145Node9_sound : Sound component145Node9Box :=
  sound_of_literal_split component145Node9Box component145Node7Box component145Node8Box
    .chi (31/32) (by rfl) (by rfl)
    component145Node7_sound component145Node8_sound

private noncomputable def component145Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (15/16), chiHi := (31/32) }

set_option maxRecDepth 1000000 in
private theorem component145Node10_sound : Sound component145Node10Box :=
  sound_of_literal_split component145Node10Box leaf7144Box leaf7145Box
    .k (51/16) (by rfl) (by rfl)
    leaf7144FlatSound leaf7145FlatSound

private noncomputable def component145Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (31/32), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component145Node11_sound : Sound component145Node11Box :=
  sound_of_literal_split component145Node11Box leaf7146Box leaf7147Box
    .k (51/16) (by rfl) (by rfl)
    leaf7146FlatSound leaf7147FlatSound

private noncomputable def component145Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (15/16), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component145Node12_sound : Sound component145Node12Box :=
  sound_of_literal_split component145Node12Box component145Node10Box component145Node11Box
    .chi (31/32) (by rfl) (by rfl)
    component145Node10_sound component145Node11_sound

private noncomputable def component145Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (13/4), chiLo := (15/16), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component145Node13_sound : Sound component145Node13Box :=
  sound_of_literal_split component145Node13Box component145Node9Box component145Node12Box
    .k (25/8) (by rfl) (by rfl)
    component145Node9_sound component145Node12_sound

private noncomputable def component145Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (13/4), chiLo := (7/8), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component145Node14_sound : Sound component145Node14Box :=
  sound_of_literal_split component145Node14Box component145Node6Box component145Node13Box
    .chi (15/16) (by rfl) (by rfl)
    component145Node6_sound component145Node13_sound

private noncomputable def component145Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (7/8), chiHi := (29/32) }

set_option maxRecDepth 1000000 in
private theorem component145Node15_sound : Sound component145Node15Box :=
  sound_of_literal_split component145Node15Box leaf7148Box leaf7149Box
    .k (53/16) (by rfl) (by rfl)
    leaf7148FlatSound leaf7149FlatSound

private noncomputable def component145Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (29/32), chiHi := (15/16) }

set_option maxRecDepth 1000000 in
private theorem component145Node16_sound : Sound component145Node16Box :=
  sound_of_literal_split component145Node16Box leaf7150Box leaf7151Box
    .k (53/16) (by rfl) (by rfl)
    leaf7150FlatSound leaf7151FlatSound

private noncomputable def component145Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (7/8), chiHi := (15/16) }

set_option maxRecDepth 1000000 in
private theorem component145Node17_sound : Sound component145Node17Box :=
  sound_of_literal_split component145Node17Box component145Node15Box component145Node16Box
    .chi (29/32) (by rfl) (by rfl)
    component145Node15_sound component145Node16_sound

private noncomputable def component145Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (7/8), chiHi := (29/32) }

set_option maxRecDepth 1000000 in
private theorem component145Node18_sound : Sound component145Node18Box :=
  sound_of_literal_split component145Node18Box leaf7152Box leaf7153Box
    .k (55/16) (by rfl) (by rfl)
    leaf7152FlatSound leaf7153FlatSound

private noncomputable def component145Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (29/32), chiHi := (15/16) }

set_option maxRecDepth 1000000 in
private theorem component145Node19_sound : Sound component145Node19Box :=
  sound_of_literal_split component145Node19Box leaf7154Box leaf7155Box
    .k (55/16) (by rfl) (by rfl)
    leaf7154FlatSound leaf7155FlatSound

private noncomputable def component145Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (7/8), chiHi := (15/16) }

set_option maxRecDepth 1000000 in
private theorem component145Node20_sound : Sound component145Node20Box :=
  sound_of_literal_split component145Node20Box component145Node18Box component145Node19Box
    .chi (29/32) (by rfl) (by rfl)
    component145Node18_sound component145Node19_sound

private noncomputable def component145Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (7/2), chiLo := (7/8), chiHi := (15/16) }

set_option maxRecDepth 1000000 in
private theorem component145Node21_sound : Sound component145Node21Box :=
  sound_of_literal_split component145Node21Box component145Node17Box component145Node20Box
    .k (27/8) (by rfl) (by rfl)
    component145Node17_sound component145Node20_sound

private noncomputable def component145Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (15/16), chiHi := (31/32) }

set_option maxRecDepth 1000000 in
private theorem component145Node22_sound : Sound component145Node22Box :=
  sound_of_literal_split component145Node22Box leaf7156Box leaf7157Box
    .k (53/16) (by rfl) (by rfl)
    leaf7156FlatSound leaf7157FlatSound

private noncomputable def component145Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (31/32), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component145Node23_sound : Sound component145Node23Box :=
  sound_of_literal_split component145Node23Box leaf7158Box leaf7159Box
    .k (53/16) (by rfl) (by rfl)
    leaf7158FlatSound leaf7159FlatSound

private noncomputable def component145Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (15/16), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component145Node24_sound : Sound component145Node24Box :=
  sound_of_literal_split component145Node24Box component145Node22Box component145Node23Box
    .chi (31/32) (by rfl) (by rfl)
    component145Node22_sound component145Node23_sound

private noncomputable def component145Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (15/16), chiHi := (31/32) }

set_option maxRecDepth 1000000 in
private theorem component145Node25_sound : Sound component145Node25Box :=
  sound_of_literal_split component145Node25Box leaf7160Box leaf7161Box
    .k (55/16) (by rfl) (by rfl)
    leaf7160FlatSound leaf7161FlatSound

private noncomputable def component145Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (31/32), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component145Node26_sound : Sound component145Node26Box :=
  sound_of_literal_split component145Node26Box leaf7162Box leaf7163Box
    .k (55/16) (by rfl) (by rfl)
    leaf7162FlatSound leaf7163FlatSound

private noncomputable def component145Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (15/16), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component145Node27_sound : Sound component145Node27Box :=
  sound_of_literal_split component145Node27Box component145Node25Box component145Node26Box
    .chi (31/32) (by rfl) (by rfl)
    component145Node25_sound component145Node26_sound

private noncomputable def component145Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (7/2), chiLo := (15/16), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component145Node28_sound : Sound component145Node28Box :=
  sound_of_literal_split component145Node28Box component145Node24Box component145Node27Box
    .k (27/8) (by rfl) (by rfl)
    component145Node24_sound component145Node27_sound

private noncomputable def component145Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (7/2), chiLo := (7/8), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component145Node29_sound : Sound component145Node29Box :=
  sound_of_literal_split component145Node29Box component145Node21Box component145Node28Box
    .chi (15/16) (by rfl) (by rfl)
    component145Node21_sound component145Node28_sound

noncomputable def component145Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (7/2), chiLo := (7/8), chiHi := (1) }

set_option maxRecDepth 1000000 in
theorem component145_sound : Sound component145Box :=
  sound_of_literal_split component145Box component145Node14Box component145Node29Box
    .k (13/4) (by rfl) (by rfl)
    component145Node14_sound component145Node29_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
