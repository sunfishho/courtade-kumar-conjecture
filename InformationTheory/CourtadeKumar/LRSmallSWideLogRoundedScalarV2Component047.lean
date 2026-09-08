import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch6
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch7
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

private noncomputable def leaf2133Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (5/32), chiHi := (41/256) }

private noncomputable def leaf2133Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871211/536870912) }, vSqrt := { lower := (65529/65536), upper := (22906164565/22905729536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (819936087/536870912) }, upper := { exponent := 0, mantissa := (12661/8192) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi183LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (45811894101/45811459072) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf2133InnerLog : WideLogData :=
  innerPair177Data

set_option maxRecDepth 1000000 in
private theorem leaf2133LocalValidity :
    LeafFacts leaf2133Box leaf2133Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2133Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22906164565/22905729536) }) = true
      norm_num [leaf2133Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2133CertificateValid :
    WideCertificateValid leaf2133Box leaf2133Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi183ValidityFacts
    leaf2133LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2133CoverageChecked :
    coverageCheck (innerAD leaf2133Box) leaf2133InnerLog = true := by
  rfl'

private theorem leaf2133InnerLogValid :
    leaf2133InnerLog.Valid 8 (innerAD leaf2133Box) :=
  wideLogDataValid_of_cachedCheck endpoint49PositiveFacts
    endpoint43PositiveFacts.valid leaf2133CoverageChecked

private noncomputable def leaf2133InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453655/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf2133InputLogOnePlusV_eq :
    leaf2133InputLogOnePlusV = outerEnclosure 24
      (leaf2133Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2133RoundedFacts : LeafRoundedFacts 8
    leaf2133Certificate.logOnePlusV leaf2133InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2133InputLogOnePlusV_eq }

private noncomputable def leaf2133Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi183InputQChi innerPair177Input
    leaf2133InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2133LowerChecked :
    lowerCheck 24 leaf2133Box leaf2133Inputs = true := by
  rfl'

private theorem leaf2133CoversExact : CoversExact 8
    leaf2133Box leaf2133Certificate leaf2133InnerLog leaf2133Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi183RoundedFacts
    innerPair177RoundedFacts leaf2133RoundedFacts (by rfl)

private theorem leaf2133FlatSound : Sound leaf2133Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2133CertificateValid
    leaf2133InnerLogValid leaf2133CoversExact leaf2133LowerChecked

private noncomputable def leaf2134Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (41/256), chiHi := (21/128) }

private noncomputable def leaf2134Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871213/536870912) }, vSqrt := { lower := (65529/65536), upper := (13743698739/13743426560) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (827013541/536870912) }, upper := { exponent := 0, mantissa := (6385/4096) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi184LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (27487125299/27486853120) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf2134InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2134LocalValidity :
    LeafFacts leaf2134Box leaf2134Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2134Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (13743698739/13743426560) }) = true
      norm_num [leaf2134Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2134CertificateValid :
    WideCertificateValid leaf2134Box leaf2134Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi184ValidityFacts
    leaf2134LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2134CoverageChecked :
    coverageCheck (innerAD leaf2134Box) leaf2134InnerLog = true := by
  rfl'

private theorem leaf2134InnerLogValid :
    leaf2134InnerLog.Valid 8 (innerAD leaf2134Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2134CoverageChecked

private noncomputable def leaf2134InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629247/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2134InputLogOnePlusV_eq :
    leaf2134InputLogOnePlusV = outerEnclosure 24
      (leaf2134Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2134RoundedFacts : LeafRoundedFacts 8
    leaf2134Certificate.logOnePlusV leaf2134InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2134InputLogOnePlusV_eq }

private noncomputable def leaf2134Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi184InputQChi innerPair40Input
    leaf2134InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2134LowerChecked :
    lowerCheck 24 leaf2134Box leaf2134Inputs = true := by
  rfl'

private theorem leaf2134CoversExact : CoversExact 8
    leaf2134Box leaf2134Certificate leaf2134InnerLog leaf2134Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi184RoundedFacts
    innerPair40RoundedFacts leaf2134RoundedFacts (by rfl)

private theorem leaf2134FlatSound : Sound leaf2134Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2134CertificateValid
    leaf2134InnerLogValid leaf2134CoversExact leaf2134LowerChecked

private noncomputable def leaf2135Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (5/32), chiHi := (41/256) }

private noncomputable def leaf2135Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871213/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717167616) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (822557365/536870912) }, upper := { exponent := 0, mantissa := (6351/4096) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi183LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435661311/137434335232) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf2135InnerLog : WideLogData :=
  innerPair88Data

set_option maxRecDepth 1000000 in
private theorem leaf2135LocalValidity :
    LeafFacts leaf2135Box leaf2135Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2135Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717167616) }) = true
      norm_num [leaf2135Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2135CertificateValid :
    WideCertificateValid leaf2135Box leaf2135Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi183ValidityFacts
    leaf2135LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2135CoverageChecked :
    coverageCheck (innerAD leaf2135Box) leaf2135InnerLog = true := by
  rfl'

private theorem leaf2135InnerLogValid :
    leaf2135InnerLog.Valid 8 (innerAD leaf2135Box) :=
  wideLogDataValid_of_cachedCheck endpoint19PositiveFacts
    endpoint122PositiveFacts.valid leaf2135CoverageChecked

private noncomputable def leaf2135InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629243/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2135InputLogOnePlusV_eq :
    leaf2135InputLogOnePlusV = outerEnclosure 24
      (leaf2135Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2135RoundedFacts : LeafRoundedFacts 8
    leaf2135Certificate.logOnePlusV leaf2135InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2135InputLogOnePlusV_eq }

private noncomputable def leaf2135Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi183InputQChi innerPair88Input
    leaf2135InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2135LowerChecked :
    lowerCheck 24 leaf2135Box leaf2135Inputs = true := by
  rfl'

private theorem leaf2135CoversExact : CoversExact 8
    leaf2135Box leaf2135Certificate leaf2135InnerLog leaf2135Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi183RoundedFacts
    innerPair88RoundedFacts leaf2135RoundedFacts (by rfl)

private theorem leaf2135FlatSound : Sound leaf2135Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2135CertificateValid
    leaf2135InnerLogValid leaf2135CoversExact leaf2135LowerChecked

private noncomputable def leaf2136Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (41/256), chiHi := (21/128) }

private noncomputable def leaf2136Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871215/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717111296) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (829700351/536870912) }, upper := { exponent := 0, mantissa := (3203/2048) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi184LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435604991/137434222592) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf2136InnerLog : WideLogData :=
  innerPair182Data

set_option maxRecDepth 1000000 in
private theorem leaf2136LocalValidity :
    LeafFacts leaf2136Box leaf2136Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2136Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717111296) }) = true
      norm_num [leaf2136Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2136CertificateValid :
    WideCertificateValid leaf2136Box leaf2136Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi184ValidityFacts
    leaf2136LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2136CoverageChecked :
    coverageCheck (innerAD leaf2136Box) leaf2136InnerLog = true := by
  rfl'

private theorem leaf2136InnerLogValid :
    leaf2136InnerLog.Valid 8 (innerAD leaf2136Box) :=
  wideLogDataValid_of_cachedCheck endpoint53PositiveFacts
    endpoint52PositiveFacts.valid leaf2136CoverageChecked

private noncomputable def leaf2136InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629249/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2136InputLogOnePlusV_eq :
    leaf2136InputLogOnePlusV = outerEnclosure 24
      (leaf2136Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2136RoundedFacts : LeafRoundedFacts 8
    leaf2136Certificate.logOnePlusV leaf2136InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2136InputLogOnePlusV_eq }

private noncomputable def leaf2136Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi184InputQChi innerPair182Input
    leaf2136InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2136LowerChecked :
    lowerCheck 24 leaf2136Box leaf2136Inputs = true := by
  rfl'

private theorem leaf2136CoversExact : CoversExact 8
    leaf2136Box leaf2136Certificate leaf2136InnerLog leaf2136Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi184RoundedFacts
    innerPair182RoundedFacts leaf2136RoundedFacts (by rfl)

private theorem leaf2136FlatSound : Sound leaf2136Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2136CertificateValid
    leaf2136InnerLogValid leaf2136CoversExact leaf2136LowerChecked

private noncomputable def leaf2137Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (21/128), chiHi := (43/256) }

private noncomputable def leaf2137Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871215/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717076992) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (834090995/536870912) }, upper := { exponent := 0, mantissa := (12879/8192) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi185LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435570687/137434153984) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf2137InnerLog : WideLogData :=
  innerPair156Data

set_option maxRecDepth 1000000 in
private theorem leaf2137LocalValidity :
    LeafFacts leaf2137Box leaf2137Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2137Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717076992) }) = true
      norm_num [leaf2137Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2137CertificateValid :
    WideCertificateValid leaf2137Box leaf2137Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi185ValidityFacts
    leaf2137LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2137CoverageChecked :
    coverageCheck (innerAD leaf2137Box) leaf2137InnerLog = true := by
  rfl'

private theorem leaf2137InnerLogValid :
    leaf2137InnerLog.Valid 8 (innerAD leaf2137Box) :=
  wideLogDataValid_of_cachedCheck endpoint43PositiveFacts
    endpoint47PositiveFacts.valid leaf2137CoverageChecked

private noncomputable def leaf2137InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814627/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2137InputLogOnePlusV_eq :
    leaf2137InputLogOnePlusV = outerEnclosure 24
      (leaf2137Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2137RoundedFacts : LeafRoundedFacts 8
    leaf2137Certificate.logOnePlusV leaf2137InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2137InputLogOnePlusV_eq }

private noncomputable def leaf2137Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi185InputQChi innerPair156Input
    leaf2137InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2137LowerChecked :
    lowerCheck 24 leaf2137Box leaf2137Inputs = true := by
  rfl'

private theorem leaf2137CoversExact : CoversExact 8
    leaf2137Box leaf2137Certificate leaf2137InnerLog leaf2137Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi185RoundedFacts
    innerPair156RoundedFacts leaf2137RoundedFacts (by rfl)

private theorem leaf2137FlatSound : Sound leaf2137Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2137CertificateValid
    leaf2137InnerLogValid leaf2137CoversExact leaf2137LowerChecked

private noncomputable def leaf2138Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (43/256), chiHi := (11/64) }

private noncomputable def leaf2138Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871217/536870912) }, vSqrt := { lower := (65529/65536), upper := (22906164565/22905673728) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (841168449/536870912) }, upper := { exponent := 0, mantissa := (3247/2048) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi186LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (45811838293/45811347456) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf2138InnerLog : WideLogData :=
  innerPair181Data

set_option maxRecDepth 1000000 in
private theorem leaf2138LocalValidity :
    LeafFacts leaf2138Box leaf2138Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2138Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22906164565/22905673728) }) = true
      norm_num [leaf2138Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2138CertificateValid :
    WideCertificateValid leaf2138Box leaf2138Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi186ValidityFacts
    leaf2138LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2138CoverageChecked :
    coverageCheck (innerAD leaf2138Box) leaf2138InnerLog = true := by
  rfl'

private theorem leaf2138InnerLogValid :
    leaf2138InnerLog.Valid 8 (innerAD leaf2138Box) :=
  wideLogDataValid_of_cachedCheck endpoint52PositiveFacts
    endpoint168PositiveFacts.valid leaf2138CoverageChecked

private noncomputable def leaf2138InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907315/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2138InputLogOnePlusV_eq :
    leaf2138InputLogOnePlusV = outerEnclosure 24
      (leaf2138Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2138RoundedFacts : LeafRoundedFacts 8
    leaf2138Certificate.logOnePlusV leaf2138InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2138InputLogOnePlusV_eq }

private noncomputable def leaf2138Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi186InputQChi innerPair181Input
    leaf2138InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2138LowerChecked :
    lowerCheck 24 leaf2138Box leaf2138Inputs = true := by
  rfl'

private theorem leaf2138CoversExact : CoversExact 8
    leaf2138Box leaf2138Certificate leaf2138InnerLog leaf2138Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi186RoundedFacts
    innerPair181RoundedFacts leaf2138RoundedFacts (by rfl)

private theorem leaf2138FlatSound : Sound leaf2138Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2138CertificateValid
    leaf2138InnerLogValid leaf2138CoversExact leaf2138LowerChecked

private noncomputable def leaf2139Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (21/128), chiHi := (43/256) }

private noncomputable def leaf2139Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871217/536870912) }, vSqrt := { lower := (65529/65536), upper := (22906164565/22905684992) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (836843337/536870912) }, upper := { exponent := 0, mantissa := (6461/4096) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi185LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (45811849557/45811369984) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf2139InnerLog : WideLogData :=
  innerPair156Data

set_option maxRecDepth 1000000 in
private theorem leaf2139LocalValidity :
    LeafFacts leaf2139Box leaf2139Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2139Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22906164565/22905684992) }) = true
      norm_num [leaf2139Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2139CertificateValid :
    WideCertificateValid leaf2139Box leaf2139Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi185ValidityFacts
    leaf2139LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2139CoverageChecked :
    coverageCheck (innerAD leaf2139Box) leaf2139InnerLog = true := by
  rfl'

private theorem leaf2139InnerLogValid :
    leaf2139InnerLog.Valid 8 (innerAD leaf2139Box) :=
  wideLogDataValid_of_cachedCheck endpoint43PositiveFacts
    endpoint47PositiveFacts.valid leaf2139CoverageChecked

private noncomputable def leaf2139InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453657/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf2139InputLogOnePlusV_eq :
    leaf2139InputLogOnePlusV = outerEnclosure 24
      (leaf2139Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2139RoundedFacts : LeafRoundedFacts 8
    leaf2139Certificate.logOnePlusV leaf2139InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2139InputLogOnePlusV_eq }

private noncomputable def leaf2139Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi185InputQChi innerPair156Input
    leaf2139InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2139LowerChecked :
    lowerCheck 24 leaf2139Box leaf2139Inputs = true := by
  rfl'

private theorem leaf2139CoversExact : CoversExact 8
    leaf2139Box leaf2139Certificate leaf2139InnerLog leaf2139Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi185RoundedFacts
    innerPair156RoundedFacts leaf2139RoundedFacts (by rfl)

private theorem leaf2139FlatSound : Sound leaf2139Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2139CertificateValid
    leaf2139InnerLogValid leaf2139CoversExact leaf2139LowerChecked

private noncomputable def leaf2140Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (219/64), chiLo := (43/256), chiHi := (11/64) }

private noncomputable def leaf2140Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742349/1073741824) }, vSqrt := { lower := (65529/65536), upper := (27487384371/27486803968) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1688005501/1073741824) }, upper := { exponent := 0, mantissa := (6505/4096) } }, logOuter := sk177LogOuterCertificate, logK := sk177LogKCertificate, logChi := chi186LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (54974188339/54973607936) } }, logDArg := sk177LogDArgCertificate }

private noncomputable def leaf2140InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2140LocalValidity :
    LeafFacts leaf2140Box leaf2140Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2140Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (27487384371/27486803968) }) = true
      norm_num [leaf2140Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2140CertificateValid :
    WideCertificateValid leaf2140Box leaf2140Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk177ValidityFacts chi186ValidityFacts
    leaf2140LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2140CoverageChecked :
    coverageCheck (innerAD leaf2140Box) leaf2140InnerLog = true := by
  rfl'

private theorem leaf2140InnerLogValid :
    leaf2140InnerLog.Valid 8 (innerAD leaf2140Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2140CoverageChecked

private noncomputable def leaf2140InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814629/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2140InputLogOnePlusV_eq :
    leaf2140InputLogOnePlusV = outerEnclosure 24
      (leaf2140Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2140RoundedFacts : LeafRoundedFacts 8
    leaf2140Certificate.logOnePlusV leaf2140InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2140InputLogOnePlusV_eq }

private noncomputable def leaf2140Inputs : Inputs :=
  inputsOfCaches globalInput sk177RoundedInputs
    chi186InputQChi innerPair50Input
    leaf2140InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2140LowerChecked :
    lowerCheck 24 leaf2140Box leaf2140Inputs = true := by
  rfl'

private theorem leaf2140CoversExact : CoversExact 8
    leaf2140Box leaf2140Certificate leaf2140InnerLog leaf2140Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk177RoundedFacts chi186RoundedFacts
    innerPair50RoundedFacts leaf2140RoundedFacts (by rfl)

private theorem leaf2140FlatSound : Sound leaf2140Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2140CertificateValid
    leaf2140InnerLogValid leaf2140CoversExact leaf2140LowerChecked

private noncomputable def leaf2141Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (219/64), kHi := (55/16), chiLo := (43/256), chiHi := (11/64) }

private noncomputable def leaf2141Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742351/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433997312) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1690823375/1073741824) }, upper := { exponent := 0, mantissa := (1629/1024) } }, logOuter := sk178LogOuterCertificate, logK := sk178LogKCertificate, logChi := chi186LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870919167/274867994624) } }, logDArg := sk178LogDArgCertificate }

private noncomputable def leaf2141InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2141LocalValidity :
    LeafFacts leaf2141Box leaf2141Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2141Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433997312) }) = true
      norm_num [leaf2141Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2141CertificateValid :
    WideCertificateValid leaf2141Box leaf2141Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk178ValidityFacts chi186ValidityFacts
    leaf2141LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2141CoverageChecked :
    coverageCheck (innerAD leaf2141Box) leaf2141InnerLog = true := by
  rfl'

private theorem leaf2141InnerLogValid :
    leaf2141InnerLog.Valid 8 (innerAD leaf2141Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2141CoverageChecked

private noncomputable def leaf2141InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629259/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2141InputLogOnePlusV_eq :
    leaf2141InputLogOnePlusV = outerEnclosure 24
      (leaf2141Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2141RoundedFacts : LeafRoundedFacts 8
    leaf2141Certificate.logOnePlusV leaf2141InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2141InputLogOnePlusV_eq }

private noncomputable def leaf2141Inputs : Inputs :=
  inputsOfCaches globalInput sk178RoundedInputs
    chi186InputQChi innerPair50Input
    leaf2141InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2141LowerChecked :
    lowerCheck 24 leaf2141Box leaf2141Inputs = true := by
  rfl'

private theorem leaf2141CoversExact : CoversExact 8
    leaf2141Box leaf2141Certificate leaf2141InnerLog leaf2141Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk178RoundedFacts chi186RoundedFacts
    innerPair50RoundedFacts leaf2141RoundedFacts (by rfl)

private theorem leaf2141FlatSound : Sound leaf2141Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2141CertificateValid
    leaf2141InnerLogValid leaf2141CoversExact leaf2141LowerChecked

private noncomputable def leaf2142Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (5/32), chiHi := (41/256) }

private noncomputable def leaf2142Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871215/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717146624) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (825178643/536870912) }, upper := { exponent := 0, mantissa := (12743/8192) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi183LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435640319/137434293248) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf2142InnerLog : WideLogData :=
  innerPair415Data

set_option maxRecDepth 1000000 in
private theorem leaf2142LocalValidity :
    LeafFacts leaf2142Box leaf2142Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2142Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717146624) }) = true
      norm_num [leaf2142Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2142CertificateValid :
    WideCertificateValid leaf2142Box leaf2142Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi183ValidityFacts
    leaf2142LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2142CoverageChecked :
    coverageCheck (innerAD leaf2142Box) leaf2142InnerLog = true := by
  rfl'

private theorem leaf2142InnerLogValid :
    leaf2142InnerLog.Valid 8 (innerAD leaf2142Box) :=
  wideLogDataValid_of_cachedCheck endpoint124PositiveFacts
    endpoint165PositiveFacts.valid leaf2142CoverageChecked

private noncomputable def leaf2142InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629245/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2142InputLogOnePlusV_eq :
    leaf2142InputLogOnePlusV = outerEnclosure 24
      (leaf2142Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2142RoundedFacts : LeafRoundedFacts 8
    leaf2142Certificate.logOnePlusV leaf2142InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2142InputLogOnePlusV_eq }

private noncomputable def leaf2142Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi183InputQChi innerPair415Input
    leaf2142InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2142LowerChecked :
    lowerCheck 24 leaf2142Box leaf2142Inputs = true := by
  rfl'

private theorem leaf2142CoversExact : CoversExact 8
    leaf2142Box leaf2142Certificate leaf2142InnerLog leaf2142Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi183RoundedFacts
    innerPair415RoundedFacts leaf2142RoundedFacts (by rfl)

private theorem leaf2142FlatSound : Sound leaf2142Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2142CertificateValid
    leaf2142InnerLogValid leaf2142CoversExact leaf2142LowerChecked

private noncomputable def leaf2143Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (221/64), chiLo := (41/256), chiHi := (21/128) }

private noncomputable def leaf2143Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742349/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137434201088) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1664807173/1073741824) }, upper := { exponent := 0, mantissa := (12833/8192) } }, logOuter := sk179LogOuterCertificate, logK := sk179LogKCertificate, logChi := chi184LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274871122943/274868402176) } }, logDArg := sk179LogDArgCertificate }

private noncomputable def leaf2143InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf2143LocalValidity :
    LeafFacts leaf2143Box leaf2143Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2143Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137434201088) }) = true
      norm_num [leaf2143Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2143CertificateValid :
    WideCertificateValid leaf2143Box leaf2143Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk179ValidityFacts chi184ValidityFacts
    leaf2143LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2143CoverageChecked :
    coverageCheck (innerAD leaf2143Box) leaf2143InnerLog = true := by
  rfl'

private theorem leaf2143InnerLogValid :
    leaf2143InnerLog.Valid 8 (innerAD leaf2143Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf2143CoverageChecked

private noncomputable def leaf2143InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629247/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2143InputLogOnePlusV_eq :
    leaf2143InputLogOnePlusV = outerEnclosure 24
      (leaf2143Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2143RoundedFacts : LeafRoundedFacts 8
    leaf2143Certificate.logOnePlusV leaf2143InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2143InputLogOnePlusV_eq }

private noncomputable def leaf2143Inputs : Inputs :=
  inputsOfCaches globalInput sk179RoundedInputs
    chi184InputQChi innerPair41Input
    leaf2143InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2143LowerChecked :
    lowerCheck 24 leaf2143Box leaf2143Inputs = true := by
  rfl'

private theorem leaf2143CoversExact : CoversExact 8
    leaf2143Box leaf2143Certificate leaf2143InnerLog leaf2143Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk179RoundedFacts chi184RoundedFacts
    innerPair41RoundedFacts leaf2143RoundedFacts (by rfl)

private theorem leaf2143FlatSound : Sound leaf2143Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2143CertificateValid
    leaf2143InnerLogValid leaf2143CoversExact leaf2143LowerChecked

private noncomputable def leaf2144Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (221/64), kHi := (111/32), chiLo := (41/256), chiHi := (21/128) }

private noncomputable def leaf2144Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742351/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137434179584) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1667493983/1073741824) }, upper := { exponent := 0, mantissa := (6427/4096) } }, logOuter := sk180LogOuterCertificate, logK := sk180LogKCertificate, logChi := chi184LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274871101439/274868359168) } }, logDArg := sk180LogDArgCertificate }

private noncomputable def leaf2144InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf2144LocalValidity :
    LeafFacts leaf2144Box leaf2144Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2144Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137434179584) }) = true
      norm_num [leaf2144Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2144CertificateValid :
    WideCertificateValid leaf2144Box leaf2144Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk180ValidityFacts chi184ValidityFacts
    leaf2144LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2144CoverageChecked :
    coverageCheck (innerAD leaf2144Box) leaf2144InnerLog = true := by
  rfl'

private theorem leaf2144InnerLogValid :
    leaf2144InnerLog.Valid 8 (innerAD leaf2144Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf2144CoverageChecked

private noncomputable def leaf2144InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (181707/262144) }

set_option maxRecDepth 1000000 in
private theorem leaf2144InputLogOnePlusV_eq :
    leaf2144InputLogOnePlusV = outerEnclosure 24
      (leaf2144Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2144RoundedFacts : LeafRoundedFacts 8
    leaf2144Certificate.logOnePlusV leaf2144InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2144InputLogOnePlusV_eq }

private noncomputable def leaf2144Inputs : Inputs :=
  inputsOfCaches globalInput sk180RoundedInputs
    chi184InputQChi innerPair41Input
    leaf2144InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2144LowerChecked :
    lowerCheck 24 leaf2144Box leaf2144Inputs = true := by
  rfl'

private theorem leaf2144CoversExact : CoversExact 8
    leaf2144Box leaf2144Certificate leaf2144InnerLog leaf2144Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk180RoundedFacts chi184RoundedFacts
    innerPair41RoundedFacts leaf2144RoundedFacts (by rfl)

private theorem leaf2144FlatSound : Sound leaf2144Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2144CertificateValid
    leaf2144InnerLogValid leaf2144CoversExact leaf2144LowerChecked

private noncomputable def leaf2145Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (223/64), chiLo := (5/32), chiHi := (41/256) }

private noncomputable def leaf2145Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742351/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137434272256) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1655632691/1073741824) }, upper := { exponent := 0, mantissa := (25527/16384) } }, logOuter := sk181LogOuterCertificate, logK := sk181LogKCertificate, logChi := chi183LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274871194111/274868544512) } }, logDArg := sk181LogDArgCertificate }

private noncomputable def leaf2145InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2145LocalValidity :
    LeafFacts leaf2145Box leaf2145Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2145Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137434272256) }) = true
      norm_num [leaf2145Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2145CertificateValid :
    WideCertificateValid leaf2145Box leaf2145Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk181ValidityFacts chi183ValidityFacts
    leaf2145LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2145CoverageChecked :
    coverageCheck (innerAD leaf2145Box) leaf2145InnerLog = true := by
  rfl'

private theorem leaf2145InnerLogValid :
    leaf2145InnerLog.Valid 8 (innerAD leaf2145Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2145CoverageChecked

private noncomputable def leaf2145InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814621/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2145InputLogOnePlusV_eq :
    leaf2145InputLogOnePlusV = outerEnclosure 24
      (leaf2145Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2145RoundedFacts : LeafRoundedFacts 8
    leaf2145Certificate.logOnePlusV leaf2145InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2145InputLogOnePlusV_eq }

private noncomputable def leaf2145Inputs : Inputs :=
  inputsOfCaches globalInput sk181RoundedInputs
    chi183InputQChi innerPair40Input
    leaf2145InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2145LowerChecked :
    lowerCheck 24 leaf2145Box leaf2145Inputs = true := by
  rfl'

private theorem leaf2145CoversExact : CoversExact 8
    leaf2145Box leaf2145Certificate leaf2145InnerLog leaf2145Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk181RoundedFacts chi183RoundedFacts
    innerPair40RoundedFacts leaf2145RoundedFacts (by rfl)

private theorem leaf2145FlatSound : Sound leaf2145Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2145CertificateValid
    leaf2145InnerLogValid leaf2145CoversExact leaf2145LowerChecked

private noncomputable def leaf2146Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (223/64), kHi := (7/2), chiLo := (5/32), chiHi := (41/256) }

private noncomputable def leaf2146Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742353/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45811417088) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1658253969/1073741824) }, upper := { exponent := 0, mantissa := (799/512) } }, logOuter := sk182LogOuterCertificate, logK := sk182LogKCertificate, logChi := chi183LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623724373/91622834176) } }, logDArg := sk182LogDArgCertificate }

private noncomputable def leaf2146InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2146LocalValidity :
    LeafFacts leaf2146Box leaf2146Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2146Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45811417088) }) = true
      norm_num [leaf2146Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2146CertificateValid :
    WideCertificateValid leaf2146Box leaf2146Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk182ValidityFacts chi183ValidityFacts
    leaf2146LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2146CoverageChecked :
    coverageCheck (innerAD leaf2146Box) leaf2146InnerLog = true := by
  rfl'

private theorem leaf2146InnerLogValid :
    leaf2146InnerLog.Valid 8 (innerAD leaf2146Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2146CoverageChecked

private noncomputable def leaf2146InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907311/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2146InputLogOnePlusV_eq :
    leaf2146InputLogOnePlusV = outerEnclosure 24
      (leaf2146Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2146RoundedFacts : LeafRoundedFacts 8
    leaf2146Certificate.logOnePlusV leaf2146InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2146InputLogOnePlusV_eq }

private noncomputable def leaf2146Inputs : Inputs :=
  inputsOfCaches globalInput sk182RoundedInputs
    chi183InputQChi innerPair40Input
    leaf2146InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2146LowerChecked :
    lowerCheck 24 leaf2146Box leaf2146Inputs = true := by
  rfl'

private theorem leaf2146CoversExact : CoversExact 8
    leaf2146Box leaf2146Certificate leaf2146InnerLog leaf2146Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk182RoundedFacts chi183RoundedFacts
    innerPair40RoundedFacts leaf2146RoundedFacts (by rfl)

private theorem leaf2146FlatSound : Sound leaf2146Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2146CertificateValid
    leaf2146InnerLogValid leaf2146CoversExact leaf2146LowerChecked

private noncomputable def leaf2147Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (223/64), chiLo := (41/256), chiHi := (21/128) }

private noncomputable def leaf2147Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742353/1073741824) }, vSqrt := { lower := (65529/65536), upper := (1616904963/1616872448) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1670180793/1073741824) }, upper := { exponent := 0, mantissa := (12875/8192) } }, logOuter := sk181LogOuterCertificate, logK := sk181LogKCertificate, logChi := chi184LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (3233777411/3233744896) } }, logDArg := sk181LogDArgCertificate }

private noncomputable def leaf2147InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf2147LocalValidity :
    LeafFacts leaf2147Box leaf2147Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2147Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (1616904963/1616872448) }) = true
      norm_num [leaf2147Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2147CertificateValid :
    WideCertificateValid leaf2147Box leaf2147Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk181ValidityFacts chi184ValidityFacts
    leaf2147LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2147CoverageChecked :
    coverageCheck (innerAD leaf2147Box) leaf2147InnerLog = true := by
  rfl'

private theorem leaf2147InnerLogValid :
    leaf2147InnerLog.Valid 8 (innerAD leaf2147Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf2147CoverageChecked

private noncomputable def leaf2147InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629249/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2147InputLogOnePlusV_eq :
    leaf2147InputLogOnePlusV = outerEnclosure 24
      (leaf2147Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2147RoundedFacts : LeafRoundedFacts 8
    leaf2147Certificate.logOnePlusV leaf2147InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2147InputLogOnePlusV_eq }

private noncomputable def leaf2147Inputs : Inputs :=
  inputsOfCaches globalInput sk181RoundedInputs
    chi184InputQChi innerPair41Input
    leaf2147InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2147LowerChecked :
    lowerCheck 24 leaf2147Box leaf2147Inputs = true := by
  rfl'

private theorem leaf2147CoversExact : CoversExact 8
    leaf2147Box leaf2147Certificate leaf2147InnerLog leaf2147Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk181RoundedFacts chi184RoundedFacts
    innerPair41RoundedFacts leaf2147RoundedFacts (by rfl)

private theorem leaf2147FlatSound : Sound leaf2147Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2147CertificateValid
    leaf2147InnerLogValid leaf2147CoversExact leaf2147LowerChecked

private noncomputable def leaf2148Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (223/64), kHi := (7/2), chiLo := (41/256), chiHi := (21/128) }

private noncomputable def leaf2148Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742355/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434136576) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1672867603/1073741824) }, upper := { exponent := 0, mantissa := (403/256) } }, logOuter := sk182LogOuterCertificate, logK := sk182LogKCertificate, logChi := chi184LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871058431/274868273152) } }, logDArg := sk182LogDArgCertificate }

private noncomputable def leaf2148InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf2148LocalValidity :
    LeafFacts leaf2148Box leaf2148Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2148Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434136576) }) = true
      norm_num [leaf2148Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2148CertificateValid :
    WideCertificateValid leaf2148Box leaf2148Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk182ValidityFacts chi184ValidityFacts
    leaf2148LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2148CoverageChecked :
    coverageCheck (innerAD leaf2148Box) leaf2148InnerLog = true := by
  rfl'

private theorem leaf2148InnerLogValid :
    leaf2148InnerLog.Valid 8 (innerAD leaf2148Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf2148CoverageChecked

private noncomputable def leaf2148InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629251/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2148InputLogOnePlusV_eq :
    leaf2148InputLogOnePlusV = outerEnclosure 24
      (leaf2148Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2148RoundedFacts : LeafRoundedFacts 8
    leaf2148Certificate.logOnePlusV leaf2148InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2148InputLogOnePlusV_eq }

private noncomputable def leaf2148Inputs : Inputs :=
  inputsOfCaches globalInput sk182RoundedInputs
    chi184InputQChi innerPair41Input
    leaf2148InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2148LowerChecked :
    lowerCheck 24 leaf2148Box leaf2148Inputs = true := by
  rfl'

private theorem leaf2148CoversExact : CoversExact 8
    leaf2148Box leaf2148Certificate leaf2148InnerLog leaf2148Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk182RoundedFacts chi184RoundedFacts
    innerPair41RoundedFacts leaf2148RoundedFacts (by rfl)

private theorem leaf2148FlatSound : Sound leaf2148Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2148CertificateValid
    leaf2148InnerLogValid leaf2148CoversExact leaf2148LowerChecked

private noncomputable def leaf2149Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (221/64), chiLo := (21/128), chiHi := (43/256) }

private noncomputable def leaf2149Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742351/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137434087936) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1679224211/1073741824) }, upper := { exponent := 0, mantissa := (25887/16384) } }, logOuter := sk179LogOuterCertificate, logK := sk179LogKCertificate, logChi := chi185LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274871009791/274868175872) } }, logDArg := sk179LogDArgCertificate }

private noncomputable def leaf2149InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2149LocalValidity :
    LeafFacts leaf2149Box leaf2149Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2149Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137434087936) }) = true
      norm_num [leaf2149Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2149CertificateValid :
    WideCertificateValid leaf2149Box leaf2149Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk179ValidityFacts chi185ValidityFacts
    leaf2149LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2149CoverageChecked :
    coverageCheck (innerAD leaf2149Box) leaf2149InnerLog = true := by
  rfl'

private theorem leaf2149InnerLogValid :
    leaf2149InnerLog.Valid 8 (innerAD leaf2149Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2149CoverageChecked

private noncomputable def leaf2149InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814627/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2149InputLogOnePlusV_eq :
    leaf2149InputLogOnePlusV = outerEnclosure 24
      (leaf2149Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2149RoundedFacts : LeafRoundedFacts 8
    leaf2149Certificate.logOnePlusV leaf2149InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2149InputLogOnePlusV_eq }

private noncomputable def leaf2149Inputs : Inputs :=
  inputsOfCaches globalInput sk179RoundedInputs
    chi185InputQChi innerPair50Input
    leaf2149InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2149LowerChecked :
    lowerCheck 24 leaf2149Box leaf2149Inputs = true := by
  rfl'

private theorem leaf2149CoversExact : CoversExact 8
    leaf2149Box leaf2149Certificate leaf2149InnerLog leaf2149Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk179RoundedFacts chi185RoundedFacts
    innerPair50RoundedFacts leaf2149RoundedFacts (by rfl)

private theorem leaf2149FlatSound : Sound leaf2149Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2149CertificateValid
    leaf2149InnerLogValid leaf2149CoversExact leaf2149LowerChecked

private noncomputable def leaf2150Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (221/64), kHi := (111/32), chiLo := (21/128), chiHi := (43/256) }

private noncomputable def leaf2150Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742353/1073741824) }, vSqrt := { lower := (65529/65536), upper := (27487384371/27486813184) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1681976553/1073741824) }, upper := { exponent := 0, mantissa := (12965/8192) } }, logOuter := sk180LogOuterCertificate, logK := sk180LogKCertificate, logChi := chi185LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (54974197555/54973626368) } }, logDArg := sk180LogDArgCertificate }

private noncomputable def leaf2150InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2150LocalValidity :
    LeafFacts leaf2150Box leaf2150Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2150Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (27487384371/27486813184) }) = true
      norm_num [leaf2150Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2150CertificateValid :
    WideCertificateValid leaf2150Box leaf2150Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk180ValidityFacts chi185ValidityFacts
    leaf2150LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2150CoverageChecked :
    coverageCheck (innerAD leaf2150Box) leaf2150InnerLog = true := by
  rfl'

private theorem leaf2150InnerLogValid :
    leaf2150InnerLog.Valid 8 (innerAD leaf2150Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2150CoverageChecked

private noncomputable def leaf2150InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629255/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2150InputLogOnePlusV_eq :
    leaf2150InputLogOnePlusV = outerEnclosure 24
      (leaf2150Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2150RoundedFacts : LeafRoundedFacts 8
    leaf2150Certificate.logOnePlusV leaf2150InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2150InputLogOnePlusV_eq }

private noncomputable def leaf2150Inputs : Inputs :=
  inputsOfCaches globalInput sk180RoundedInputs
    chi185InputQChi innerPair50Input
    leaf2150InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2150LowerChecked :
    lowerCheck 24 leaf2150Box leaf2150Inputs = true := by
  rfl'

private theorem leaf2150CoversExact : CoversExact 8
    leaf2150Box leaf2150Certificate leaf2150InnerLog leaf2150Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk180RoundedFacts chi185RoundedFacts
    innerPair50RoundedFacts leaf2150RoundedFacts (by rfl)

private theorem leaf2150FlatSound : Sound leaf2150Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2150CertificateValid
    leaf2150InnerLogValid leaf2150CoversExact leaf2150LowerChecked

private noncomputable def leaf2151Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (221/64), chiLo := (43/256), chiHi := (11/64) }

private noncomputable def leaf2151Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742353/1073741824) }, vSqrt := { lower := (65529/65536), upper := (45812307285/45811324928) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1693641249/1073741824) }, upper := { exponent := 0, mantissa := (6527/4096) } }, logOuter := sk179LogOuterCertificate, logK := sk179LogKCertificate, logChi := chi186LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (91623632213/91622649856) } }, logDArg := sk179LogDArgCertificate }

private noncomputable def leaf2151InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2151LocalValidity :
    LeafFacts leaf2151Box leaf2151Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2151Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (45812307285/45811324928) }) = true
      norm_num [leaf2151Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2151CertificateValid :
    WideCertificateValid leaf2151Box leaf2151Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk179ValidityFacts chi186ValidityFacts
    leaf2151LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2151CoverageChecked :
    coverageCheck (innerAD leaf2151Box) leaf2151InnerLog = true := by
  rfl'

private theorem leaf2151InnerLogValid :
    leaf2151InnerLog.Valid 8 (innerAD leaf2151Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2151CoverageChecked

private noncomputable def leaf2151InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629261/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2151InputLogOnePlusV_eq :
    leaf2151InputLogOnePlusV = outerEnclosure 24
      (leaf2151Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2151RoundedFacts : LeafRoundedFacts 8
    leaf2151Certificate.logOnePlusV leaf2151InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2151InputLogOnePlusV_eq }

private noncomputable def leaf2151Inputs : Inputs :=
  inputsOfCaches globalInput sk179RoundedInputs
    chi186InputQChi innerPair50Input
    leaf2151InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2151LowerChecked :
    lowerCheck 24 leaf2151Box leaf2151Inputs = true := by
  rfl'

private theorem leaf2151CoversExact : CoversExact 8
    leaf2151Box leaf2151Certificate leaf2151InnerLog leaf2151Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk179RoundedFacts chi186RoundedFacts
    innerPair50RoundedFacts leaf2151RoundedFacts (by rfl)

private theorem leaf2151FlatSound : Sound leaf2151Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2151CertificateValid
    leaf2151InnerLogValid leaf2151CoversExact leaf2151LowerChecked

private noncomputable def leaf2152Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (221/64), kHi := (111/32), chiLo := (43/256), chiHi := (11/64) }

private noncomputable def leaf2152Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742355/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433952256) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1696459123/1073741824) }, upper := { exponent := 0, mantissa := (3269/2048) } }, logOuter := sk180LogOuterCertificate, logK := sk180LogKCertificate, logChi := chi186LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870874111/274867904512) } }, logDArg := sk180LogDArgCertificate }

private noncomputable def leaf2152InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2152LocalValidity :
    LeafFacts leaf2152Box leaf2152Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2152Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433952256) }) = true
      norm_num [leaf2152Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2152CertificateValid :
    WideCertificateValid leaf2152Box leaf2152Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk180ValidityFacts chi186ValidityFacts
    leaf2152LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2152CoverageChecked :
    coverageCheck (innerAD leaf2152Box) leaf2152InnerLog = true := by
  rfl'

private theorem leaf2152InnerLogValid :
    leaf2152InnerLog.Valid 8 (innerAD leaf2152Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2152CoverageChecked

private noncomputable def leaf2152InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814631/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2152InputLogOnePlusV_eq :
    leaf2152InputLogOnePlusV = outerEnclosure 24
      (leaf2152Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2152RoundedFacts : LeafRoundedFacts 8
    leaf2152Certificate.logOnePlusV leaf2152InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2152InputLogOnePlusV_eq }

private noncomputable def leaf2152Inputs : Inputs :=
  inputsOfCaches globalInput sk180RoundedInputs
    chi186InputQChi innerPair50Input
    leaf2152InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2152LowerChecked :
    lowerCheck 24 leaf2152Box leaf2152Inputs = true := by
  rfl'

private theorem leaf2152CoversExact : CoversExact 8
    leaf2152Box leaf2152Certificate leaf2152InnerLog leaf2152Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk180RoundedFacts chi186RoundedFacts
    innerPair50RoundedFacts leaf2152RoundedFacts (by rfl)

private theorem leaf2152FlatSound : Sound leaf2152Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2152CertificateValid
    leaf2152InnerLogValid leaf2152CoversExact leaf2152LowerChecked

private noncomputable def leaf2153Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (223/64), chiLo := (21/128), chiHi := (43/256) }

private noncomputable def leaf2153Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742355/1073741824) }, vSqrt := { lower := (65529/65536), upper := (45812307285/45811347968) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1684728895/1073741824) }, upper := { exponent := 0, mantissa := (25973/16384) } }, logOuter := sk181LogOuterCertificate, logK := sk181LogKCertificate, logChi := chi185LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (91623655253/91622695936) } }, logDArg := sk181LogDArgCertificate }

private noncomputable def leaf2153InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2153LocalValidity :
    LeafFacts leaf2153Box leaf2153Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2153Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (45812307285/45811347968) }) = true
      norm_num [leaf2153Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2153CertificateValid :
    WideCertificateValid leaf2153Box leaf2153Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk181ValidityFacts chi185ValidityFacts
    leaf2153LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2153CoverageChecked :
    coverageCheck (innerAD leaf2153Box) leaf2153InnerLog = true := by
  rfl'

private theorem leaf2153InnerLogValid :
    leaf2153InnerLog.Valid 8 (innerAD leaf2153Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2153CoverageChecked

private noncomputable def leaf2153InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453657/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf2153InputLogOnePlusV_eq :
    leaf2153InputLogOnePlusV = outerEnclosure 24
      (leaf2153Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2153RoundedFacts : LeafRoundedFacts 8
    leaf2153Certificate.logOnePlusV leaf2153InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2153InputLogOnePlusV_eq }

private noncomputable def leaf2153Inputs : Inputs :=
  inputsOfCaches globalInput sk181RoundedInputs
    chi185InputQChi innerPair50Input
    leaf2153InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2153LowerChecked :
    lowerCheck 24 leaf2153Box leaf2153Inputs = true := by
  rfl'

private theorem leaf2153CoversExact : CoversExact 8
    leaf2153Box leaf2153Certificate leaf2153InnerLog leaf2153Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk181RoundedFacts chi185RoundedFacts
    innerPair50RoundedFacts leaf2153RoundedFacts (by rfl)

private theorem leaf2153FlatSound : Sound leaf2153Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2153CertificateValid
    leaf2153InnerLogValid leaf2153CoversExact leaf2153LowerChecked

private noncomputable def leaf2154Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (223/64), kHi := (7/2), chiLo := (21/128), chiHi := (43/256) }

private noncomputable def leaf2154Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742357/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434021888) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1687481237/1073741824) }, upper := { exponent := 0, mantissa := (813/512) } }, logOuter := sk182LogOuterCertificate, logK := sk182LogKCertificate, logChi := chi185LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870943743/274868043776) } }, logDArg := sk182LogDArgCertificate }

private noncomputable def leaf2154InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2154LocalValidity :
    LeafFacts leaf2154Box leaf2154Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2154Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434021888) }) = true
      norm_num [leaf2154Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2154CertificateValid :
    WideCertificateValid leaf2154Box leaf2154Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk182ValidityFacts chi185ValidityFacts
    leaf2154LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2154CoverageChecked :
    coverageCheck (innerAD leaf2154Box) leaf2154InnerLog = true := by
  rfl'

private theorem leaf2154InnerLogValid :
    leaf2154InnerLog.Valid 8 (innerAD leaf2154Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2154CoverageChecked

private noncomputable def leaf2154InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814629/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2154InputLogOnePlusV_eq :
    leaf2154InputLogOnePlusV = outerEnclosure 24
      (leaf2154Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2154RoundedFacts : LeafRoundedFacts 8
    leaf2154Certificate.logOnePlusV leaf2154InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2154InputLogOnePlusV_eq }

private noncomputable def leaf2154Inputs : Inputs :=
  inputsOfCaches globalInput sk182RoundedInputs
    chi185InputQChi innerPair50Input
    leaf2154InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2154LowerChecked :
    lowerCheck 24 leaf2154Box leaf2154Inputs = true := by
  rfl'

private theorem leaf2154CoversExact : CoversExact 8
    leaf2154Box leaf2154Certificate leaf2154InnerLog leaf2154Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk182RoundedFacts chi185RoundedFacts
    innerPair50RoundedFacts leaf2154RoundedFacts (by rfl)

private theorem leaf2154FlatSound : Sound leaf2154Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2154CertificateValid
    leaf2154InnerLogValid leaf2154CoversExact leaf2154LowerChecked

private noncomputable def leaf2155Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (223/64), chiLo := (43/256), chiHi := (11/64) }

private noncomputable def leaf2155Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742357/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433929728) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1699276997/1073741824) }, upper := { exponent := 0, mantissa := (6549/4096) } }, logOuter := sk181LogOuterCertificate, logK := sk181LogKCertificate, logChi := chi186LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870851583/274867859456) } }, logDArg := sk181LogDArgCertificate }

private noncomputable def leaf2155InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2155LocalValidity :
    LeafFacts leaf2155Box leaf2155Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2155Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433929728) }) = true
      norm_num [leaf2155Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2155CertificateValid :
    WideCertificateValid leaf2155Box leaf2155Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk181ValidityFacts chi186ValidityFacts
    leaf2155LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2155CoverageChecked :
    coverageCheck (innerAD leaf2155Box) leaf2155InnerLog = true := by
  rfl'

private theorem leaf2155InnerLogValid :
    leaf2155InnerLog.Valid 8 (innerAD leaf2155Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2155CoverageChecked

private noncomputable def leaf2155InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629263/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2155InputLogOnePlusV_eq :
    leaf2155InputLogOnePlusV = outerEnclosure 24
      (leaf2155Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2155RoundedFacts : LeafRoundedFacts 8
    leaf2155Certificate.logOnePlusV leaf2155InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2155InputLogOnePlusV_eq }

private noncomputable def leaf2155Inputs : Inputs :=
  inputsOfCaches globalInput sk181RoundedInputs
    chi186InputQChi innerPair50Input
    leaf2155InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2155LowerChecked :
    lowerCheck 24 leaf2155Box leaf2155Inputs = true := by
  rfl'

private theorem leaf2155CoversExact : CoversExact 8
    leaf2155Box leaf2155Certificate leaf2155InnerLog leaf2155Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk181RoundedFacts chi186RoundedFacts
    innerPair50RoundedFacts leaf2155RoundedFacts (by rfl)

private theorem leaf2155FlatSound : Sound leaf2155Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2155CertificateValid
    leaf2155InnerLogValid leaf2155CoversExact leaf2155LowerChecked

private noncomputable def leaf2156Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (223/64), kHi := (7/2), chiLo := (43/256), chiHi := (11/64) }

private noncomputable def leaf2156Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742359/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9162461457/9162260480) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1702094871/1073741824) }, upper := { exponent := 0, mantissa := (205/128) } }, logOuter := sk182LogOuterCertificate, logK := sk182LogKCertificate, logChi := chi186LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (18324721937/18324520960) } }, logDArg := sk182LogDArgCertificate }

private noncomputable def leaf2156InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2156LocalValidity :
    LeafFacts leaf2156Box leaf2156Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2156Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9162461457/9162260480) }) = true
      norm_num [leaf2156Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2156CertificateValid :
    WideCertificateValid leaf2156Box leaf2156Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk182ValidityFacts chi186ValidityFacts
    leaf2156LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2156CoverageChecked :
    coverageCheck (innerAD leaf2156Box) leaf2156InnerLog = true := by
  rfl'

private theorem leaf2156InnerLogValid :
    leaf2156InnerLog.Valid 8 (innerAD leaf2156Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2156CoverageChecked

private noncomputable def leaf2156InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629265/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2156InputLogOnePlusV_eq :
    leaf2156InputLogOnePlusV = outerEnclosure 24
      (leaf2156Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2156RoundedFacts : LeafRoundedFacts 8
    leaf2156Certificate.logOnePlusV leaf2156InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2156InputLogOnePlusV_eq }

private noncomputable def leaf2156Inputs : Inputs :=
  inputsOfCaches globalInput sk182RoundedInputs
    chi186InputQChi innerPair50Input
    leaf2156InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2156LowerChecked :
    lowerCheck 24 leaf2156Box leaf2156Inputs = true := by
  rfl'

private theorem leaf2156CoversExact : CoversExact 8
    leaf2156Box leaf2156Certificate leaf2156InnerLog leaf2156Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk182RoundedFacts chi186RoundedFacts
    innerPair50RoundedFacts leaf2156RoundedFacts (by rfl)

private theorem leaf2156FlatSound : Sound leaf2156Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2156CertificateValid
    leaf2156InnerLogValid leaf2156CoversExact leaf2156LowerChecked

private noncomputable def leaf2157Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (11/64), chiHi := (45/256) }

private noncomputable def leaf2157Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871219/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68716965376) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (848245903/536870912) }, upper := { exponent := 0, mantissa := (13097/8192) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi133LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435459071/137433930752) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf2157InnerLog : WideLogData :=
  innerPair451Data

set_option maxRecDepth 1000000 in
private theorem leaf2157LocalValidity :
    LeafFacts leaf2157Box leaf2157Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2157Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68716965376) }) = true
      norm_num [leaf2157Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2157CertificateValid :
    WideCertificateValid leaf2157Box leaf2157Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi133ValidityFacts
    leaf2157LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2157CoverageChecked :
    coverageCheck (innerAD leaf2157Box) leaf2157InnerLog = true := by
  rfl'

private theorem leaf2157InnerLogValid :
    leaf2157InnerLog.Valid 8 (innerAD leaf2157Box) :=
  wideLogDataValid_of_cachedCheck endpoint169PositiveFacts
    endpoint170PositiveFacts.valid leaf2157CoverageChecked

private noncomputable def leaf2157InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629267/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2157InputLogOnePlusV_eq :
    leaf2157InputLogOnePlusV = outerEnclosure 24
      (leaf2157Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2157RoundedFacts : LeafRoundedFacts 8
    leaf2157Certificate.logOnePlusV leaf2157InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2157InputLogOnePlusV_eq }

private noncomputable def leaf2157Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi133InputQChi innerPair451Input
    leaf2157InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2157LowerChecked :
    lowerCheck 24 leaf2157Box leaf2157Inputs = true := by
  rfl'

private theorem leaf2157CoversExact : CoversExact 8
    leaf2157Box leaf2157Certificate leaf2157InnerLog leaf2157Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi133RoundedFacts
    innerPair451RoundedFacts leaf2157RoundedFacts (by rfl)

private theorem leaf2157FlatSound : Sound leaf2157Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2157CertificateValid
    leaf2157InnerLogValid leaf2157CoversExact leaf2157LowerChecked

private noncomputable def leaf2158Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (217/64), chiLo := (45/256), chiHi := (23/128) }

private noncomputable def leaf2158Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742349/1073741824) }, vSqrt := { lower := (65529/65536), upper := (45812307285/45811280896) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1710679573/1073741824) }, upper := { exponent := 0, mantissa := (13183/8192) } }, logOuter := sk183LogOuterCertificate, logK := sk183LogKCertificate, logChi := chi134LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (91623588181/91622561792) } }, logDArg := sk183LogDArgCertificate }

private noncomputable def leaf2158InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2158LocalValidity :
    LeafFacts leaf2158Box leaf2158Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2158Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (45812307285/45811280896) }) = true
      norm_num [leaf2158Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2158CertificateValid :
    WideCertificateValid leaf2158Box leaf2158Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk183ValidityFacts chi134ValidityFacts
    leaf2158LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2158CoverageChecked :
    coverageCheck (innerAD leaf2158Box) leaf2158InnerLog = true := by
  rfl'

private theorem leaf2158InnerLogValid :
    leaf2158InnerLog.Valid 8 (innerAD leaf2158Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2158CoverageChecked

private noncomputable def leaf2158InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629269/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2158InputLogOnePlusV_eq :
    leaf2158InputLogOnePlusV = outerEnclosure 24
      (leaf2158Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2158RoundedFacts : LeafRoundedFacts 8
    leaf2158Certificate.logOnePlusV leaf2158InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2158InputLogOnePlusV_eq }

private noncomputable def leaf2158Inputs : Inputs :=
  inputsOfCaches globalInput sk183RoundedInputs
    chi134InputQChi innerPair50Input
    leaf2158InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2158LowerChecked :
    lowerCheck 24 leaf2158Box leaf2158Inputs = true := by
  rfl'

private theorem leaf2158CoversExact : CoversExact 8
    leaf2158Box leaf2158Certificate leaf2158InnerLog leaf2158Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk183RoundedFacts chi134RoundedFacts
    innerPair50RoundedFacts leaf2158RoundedFacts (by rfl)

private theorem leaf2158FlatSound : Sound leaf2158Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2158CertificateValid
    leaf2158InnerLogValid leaf2158CoversExact leaf2158LowerChecked

private noncomputable def leaf2159Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (217/64), kHi := (109/32), chiLo := (45/256), chiHi := (23/128) }

private noncomputable def leaf2159Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742351/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433819136) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1713628511/1073741824) }, upper := { exponent := 0, mantissa := (6603/4096) } }, logOuter := sk184LogOuterCertificate, logK := sk184LogKCertificate, logChi := chi134LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870740991/274867638272) } }, logDArg := sk184LogDArgCertificate }

private noncomputable def leaf2159InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2159LocalValidity :
    LeafFacts leaf2159Box leaf2159Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2159Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433819136) }) = true
      norm_num [leaf2159Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2159CertificateValid :
    WideCertificateValid leaf2159Box leaf2159Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk184ValidityFacts chi134ValidityFacts
    leaf2159LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2159CoverageChecked :
    coverageCheck (innerAD leaf2159Box) leaf2159InnerLog = true := by
  rfl'

private theorem leaf2159InnerLogValid :
    leaf2159InnerLog.Valid 8 (innerAD leaf2159Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2159CoverageChecked

private noncomputable def leaf2159InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814635/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2159InputLogOnePlusV_eq :
    leaf2159InputLogOnePlusV = outerEnclosure 24
      (leaf2159Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2159RoundedFacts : LeafRoundedFacts 8
    leaf2159Certificate.logOnePlusV leaf2159InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2159InputLogOnePlusV_eq }

private noncomputable def leaf2159Inputs : Inputs :=
  inputsOfCaches globalInput sk184RoundedInputs
    chi134InputQChi innerPair50Input
    leaf2159InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2159LowerChecked :
    lowerCheck 24 leaf2159Box leaf2159Inputs = true := by
  rfl'

private theorem leaf2159CoversExact : CoversExact 8
    leaf2159Box leaf2159Certificate leaf2159InnerLog leaf2159Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk184RoundedFacts chi134RoundedFacts
    innerPair50RoundedFacts leaf2159RoundedFacts (by rfl)

private theorem leaf2159FlatSound : Sound leaf2159Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2159CertificateValid
    leaf2159InnerLogValid leaf2159CoversExact leaf2159LowerChecked

private noncomputable def leaf2160Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (219/64), chiLo := (11/64), chiHi := (45/256) }

private noncomputable def leaf2160Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742351/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433907712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1702291475/1073741824) }, upper := { exponent := 0, mantissa := (26239/16384) } }, logOuter := sk177LogOuterCertificate, logK := sk177LogKCertificate, logChi := chi133LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870829567/274867815424) } }, logDArg := sk177LogDArgCertificate }

private noncomputable def leaf2160InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2160LocalValidity :
    LeafFacts leaf2160Box leaf2160Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2160Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433907712) }) = true
      norm_num [leaf2160Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2160CertificateValid :
    WideCertificateValid leaf2160Box leaf2160Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk177ValidityFacts chi133ValidityFacts
    leaf2160LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2160CoverageChecked :
    coverageCheck (innerAD leaf2160Box) leaf2160InnerLog = true := by
  rfl'

private theorem leaf2160InnerLogValid :
    leaf2160InnerLog.Valid 8 (innerAD leaf2160Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2160CoverageChecked

private noncomputable def leaf2160InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629265/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2160InputLogOnePlusV_eq :
    leaf2160InputLogOnePlusV = outerEnclosure 24
      (leaf2160Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2160RoundedFacts : LeafRoundedFacts 8
    leaf2160Certificate.logOnePlusV leaf2160InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2160InputLogOnePlusV_eq }

private noncomputable def leaf2160Inputs : Inputs :=
  inputsOfCaches globalInput sk177RoundedInputs
    chi133InputQChi innerPair50Input
    leaf2160InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2160LowerChecked :
    lowerCheck 24 leaf2160Box leaf2160Inputs = true := by
  rfl'

private theorem leaf2160CoversExact : CoversExact 8
    leaf2160Box leaf2160Certificate leaf2160InnerLog leaf2160Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk177RoundedFacts chi133RoundedFacts
    innerPair50RoundedFacts leaf2160RoundedFacts (by rfl)

private theorem leaf2160FlatSound : Sound leaf2160Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2160CertificateValid
    leaf2160InnerLogValid leaf2160CoversExact leaf2160LowerChecked

private noncomputable def leaf2161Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (219/64), kHi := (55/16), chiLo := (11/64), chiHi := (45/256) }

private noncomputable def leaf2161Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742353/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433884672) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1705174881/1073741824) }, upper := { exponent := 0, mantissa := (6571/4096) } }, logOuter := sk178LogOuterCertificate, logK := sk178LogKCertificate, logChi := chi133LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870806527/274867769344) } }, logDArg := sk178LogDArgCertificate }

private noncomputable def leaf2161InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2161LocalValidity :
    LeafFacts leaf2161Box leaf2161Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2161Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433884672) }) = true
      norm_num [leaf2161Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2161CertificateValid :
    WideCertificateValid leaf2161Box leaf2161Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk178ValidityFacts chi133ValidityFacts
    leaf2161LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2161CoverageChecked :
    coverageCheck (innerAD leaf2161Box) leaf2161InnerLog = true := by
  rfl'

private theorem leaf2161InnerLogValid :
    leaf2161InnerLog.Valid 8 (innerAD leaf2161Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2161CoverageChecked

private noncomputable def leaf2161InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814633/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2161InputLogOnePlusV_eq :
    leaf2161InputLogOnePlusV = outerEnclosure 24
      (leaf2161Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2161RoundedFacts : LeafRoundedFacts 8
    leaf2161Certificate.logOnePlusV leaf2161InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2161InputLogOnePlusV_eq }

private noncomputable def leaf2161Inputs : Inputs :=
  inputsOfCaches globalInput sk178RoundedInputs
    chi133InputQChi innerPair50Input
    leaf2161InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2161LowerChecked :
    lowerCheck 24 leaf2161Box leaf2161Inputs = true := by
  rfl'

private theorem leaf2161CoversExact : CoversExact 8
    leaf2161Box leaf2161Certificate leaf2161InnerLog leaf2161Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk178RoundedFacts chi133RoundedFacts
    innerPair50RoundedFacts leaf2161RoundedFacts (by rfl)

private theorem leaf2161FlatSound : Sound leaf2161Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2161CertificateValid
    leaf2161InnerLogValid leaf2161CoversExact leaf2161LowerChecked

private noncomputable def leaf2162Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (219/64), chiLo := (45/256), chiHi := (23/128) }

private noncomputable def leaf2162Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742353/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433795584) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1716577449/1073741824) }, upper := { exponent := 0, mantissa := (13229/8192) } }, logOuter := sk177LogOuterCertificate, logK := sk177LogKCertificate, logChi := chi134LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870717439/274867591168) } }, logDArg := sk177LogDArgCertificate }

private noncomputable def leaf2162InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2162LocalValidity :
    LeafFacts leaf2162Box leaf2162Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2162Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433795584) }) = true
      norm_num [leaf2162Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2162CertificateValid :
    WideCertificateValid leaf2162Box leaf2162Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk177ValidityFacts chi134ValidityFacts
    leaf2162LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2162CoverageChecked :
    coverageCheck (innerAD leaf2162Box) leaf2162InnerLog = true := by
  rfl'

private theorem leaf2162InnerLogValid :
    leaf2162InnerLog.Valid 8 (innerAD leaf2162Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2162CoverageChecked

private noncomputable def leaf2162InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453659/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf2162InputLogOnePlusV_eq :
    leaf2162InputLogOnePlusV = outerEnclosure 24
      (leaf2162Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2162RoundedFacts : LeafRoundedFacts 8
    leaf2162Certificate.logOnePlusV leaf2162InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2162InputLogOnePlusV_eq }

private noncomputable def leaf2162Inputs : Inputs :=
  inputsOfCaches globalInput sk177RoundedInputs
    chi134InputQChi innerPair50Input
    leaf2162InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2162LowerChecked :
    lowerCheck 24 leaf2162Box leaf2162Inputs = true := by
  rfl'

private theorem leaf2162CoversExact : CoversExact 8
    leaf2162Box leaf2162Certificate leaf2162InnerLog leaf2162Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk177RoundedFacts chi134RoundedFacts
    innerPair50RoundedFacts leaf2162RoundedFacts (by rfl)

private theorem leaf2162FlatSound : Sound leaf2162Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2162CertificateValid
    leaf2162InnerLogValid leaf2162CoversExact leaf2162LowerChecked

private noncomputable def leaf2163Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (219/64), kHi := (55/16), chiLo := (45/256), chiHi := (23/128) }

private noncomputable def leaf2163Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742355/1073741824) }, vSqrt := { lower := (65529/65536), upper := (45812307285/45811257344) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1719526387/1073741824) }, upper := { exponent := 0, mantissa := (3313/2048) } }, logOuter := sk178LogOuterCertificate, logK := sk178LogKCertificate, logChi := chi134LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (91623564629/91622514688) } }, logDArg := sk178LogDArgCertificate }

private noncomputable def leaf2163InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2163LocalValidity :
    LeafFacts leaf2163Box leaf2163Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2163Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (45812307285/45811257344) }) = true
      norm_num [leaf2163Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2163CertificateValid :
    WideCertificateValid leaf2163Box leaf2163Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk178ValidityFacts chi134ValidityFacts
    leaf2163LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2163CoverageChecked :
    coverageCheck (innerAD leaf2163Box) leaf2163InnerLog = true := by
  rfl'

private theorem leaf2163InnerLogValid :
    leaf2163InnerLog.Valid 8 (innerAD leaf2163Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2163CoverageChecked

private noncomputable def leaf2163InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629273/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2163InputLogOnePlusV_eq :
    leaf2163InputLogOnePlusV = outerEnclosure 24
      (leaf2163Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2163RoundedFacts : LeafRoundedFacts 8
    leaf2163Certificate.logOnePlusV leaf2163InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2163InputLogOnePlusV_eq }

private noncomputable def leaf2163Inputs : Inputs :=
  inputsOfCaches globalInput sk178RoundedInputs
    chi134InputQChi innerPair50Input
    leaf2163InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2163LowerChecked :
    lowerCheck 24 leaf2163Box leaf2163Inputs = true := by
  rfl'

private theorem leaf2163CoversExact : CoversExact 8
    leaf2163Box leaf2163Certificate leaf2163InnerLog leaf2163Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk178RoundedFacts chi134RoundedFacts
    innerPair50RoundedFacts leaf2163RoundedFacts (by rfl)

private theorem leaf2163FlatSound : Sound leaf2163Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2163CertificateValid
    leaf2163InnerLogValid leaf2163CoversExact leaf2163LowerChecked

private noncomputable def leaf2164Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (217/64), chiLo := (23/128), chiHi := (47/256) }

private noncomputable def leaf2164Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742351/1073741824) }, vSqrt := { lower := (65529/65536), upper := (8084524815/8084337152) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1724834483/1073741824) }, upper := { exponent := 0, mantissa := (26583/16384) } }, logOuter := sk183LogOuterCertificate, logK := sk183LogKCertificate, logChi := chi135LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (16168861967/16168674304) } }, logDArg := sk183LogDArgCertificate }

private noncomputable def leaf2164InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2164LocalValidity :
    LeafFacts leaf2164Box leaf2164Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2164Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8084524815/8084337152) }) = true
      norm_num [leaf2164Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2164CertificateValid :
    WideCertificateValid leaf2164Box leaf2164Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk183ValidityFacts chi135ValidityFacts
    leaf2164LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2164CoverageChecked :
    coverageCheck (innerAD leaf2164Box) leaf2164InnerLog = true := by
  rfl'

private theorem leaf2164InnerLogValid :
    leaf2164InnerLog.Valid 8 (innerAD leaf2164Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2164CoverageChecked

private noncomputable def leaf2164InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629275/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2164InputLogOnePlusV_eq :
    leaf2164InputLogOnePlusV = outerEnclosure 24
      (leaf2164Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2164RoundedFacts : LeafRoundedFacts 8
    leaf2164Certificate.logOnePlusV leaf2164InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2164InputLogOnePlusV_eq }

private noncomputable def leaf2164Inputs : Inputs :=
  inputsOfCaches globalInput sk183RoundedInputs
    chi135InputQChi innerPair50Input
    leaf2164InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2164LowerChecked :
    lowerCheck 24 leaf2164Box leaf2164Inputs = true := by
  rfl'

private theorem leaf2164CoversExact : CoversExact 8
    leaf2164Box leaf2164Certificate leaf2164InnerLog leaf2164Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk183RoundedFacts chi135RoundedFacts
    innerPair50RoundedFacts leaf2164RoundedFacts (by rfl)

private theorem leaf2164FlatSound : Sound leaf2164Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2164CertificateValid
    leaf2164InnerLogValid leaf2164CoversExact leaf2164LowerChecked

private noncomputable def leaf2165Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (217/64), kHi := (109/32), chiLo := (23/128), chiHi := (47/256) }

private noncomputable def leaf2165Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742353/1073741824) }, vSqrt := { lower := (65529/65536), upper := (9162461457/9162247168) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1727848953/1073741824) }, upper := { exponent := 0, mantissa := (13315/8192) } }, logOuter := sk184LogOuterCertificate, logK := sk184LogKCertificate, logChi := chi135LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (18324708625/18324494336) } }, logDArg := sk184LogDArgCertificate }

private noncomputable def leaf2165InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf2165LocalValidity :
    LeafFacts leaf2165Box leaf2165Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2165Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (9162461457/9162247168) }) = true
      norm_num [leaf2165Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2165CertificateValid :
    WideCertificateValid leaf2165Box leaf2165Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk184ValidityFacts chi135ValidityFacts
    leaf2165LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2165CoverageChecked :
    coverageCheck (innerAD leaf2165Box) leaf2165InnerLog = true := by
  rfl'

private theorem leaf2165InnerLogValid :
    leaf2165InnerLog.Valid 8 (innerAD leaf2165Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf2165CoverageChecked

private noncomputable def leaf2165InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629277/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2165InputLogOnePlusV_eq :
    leaf2165InputLogOnePlusV = outerEnclosure 24
      (leaf2165Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2165RoundedFacts : LeafRoundedFacts 8
    leaf2165Certificate.logOnePlusV leaf2165InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2165InputLogOnePlusV_eq }

private noncomputable def leaf2165Inputs : Inputs :=
  inputsOfCaches globalInput sk184RoundedInputs
    chi135InputQChi innerPair51Input
    leaf2165InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2165LowerChecked :
    lowerCheck 24 leaf2165Box leaf2165Inputs = true := by
  rfl'

private theorem leaf2165CoversExact : CoversExact 8
    leaf2165Box leaf2165Certificate leaf2165InnerLog leaf2165Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk184RoundedFacts chi135RoundedFacts
    innerPair51RoundedFacts leaf2165RoundedFacts (by rfl)

private theorem leaf2165FlatSound : Sound leaf2165Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2165CertificateValid
    leaf2165InnerLogValid leaf2165CoversExact leaf2165LowerChecked

private noncomputable def leaf2166Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (217/64), chiLo := (47/256), chiHi := (3/16) }

private noncomputable def leaf2166Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742353/1073741824) }, vSqrt := { lower := (65529/65536), upper := (27487384371/27486724096) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1738989393/1073741824) }, upper := { exponent := 0, mantissa := (1675/1024) } }, logOuter := sk183LogOuterCertificate, logK := sk183LogKCertificate, logChi := chi136LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (54974108467/54973448192) } }, logDArg := sk183LogDArgCertificate }

private noncomputable def leaf2166InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf2166LocalValidity :
    LeafFacts leaf2166Box leaf2166Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2166Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (27487384371/27486724096) }) = true
      norm_num [leaf2166Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2166CertificateValid :
    WideCertificateValid leaf2166Box leaf2166Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk183ValidityFacts chi136ValidityFacts
    leaf2166LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2166CoverageChecked :
    coverageCheck (innerAD leaf2166Box) leaf2166InnerLog = true := by
  rfl'

private theorem leaf2166InnerLogValid :
    leaf2166InnerLog.Valid 8 (innerAD leaf2166Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf2166CoverageChecked

private noncomputable def leaf2166InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814641/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2166InputLogOnePlusV_eq :
    leaf2166InputLogOnePlusV = outerEnclosure 24
      (leaf2166Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2166RoundedFacts : LeafRoundedFacts 8
    leaf2166Certificate.logOnePlusV leaf2166InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2166InputLogOnePlusV_eq }

private noncomputable def leaf2166Inputs : Inputs :=
  inputsOfCaches globalInput sk183RoundedInputs
    chi136InputQChi innerPair51Input
    leaf2166InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2166LowerChecked :
    lowerCheck 24 leaf2166Box leaf2166Inputs = true := by
  rfl'

private theorem leaf2166CoversExact : CoversExact 8
    leaf2166Box leaf2166Certificate leaf2166InnerLog leaf2166Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk183RoundedFacts chi136RoundedFacts
    innerPair51RoundedFacts leaf2166RoundedFacts (by rfl)

private theorem leaf2166FlatSound : Sound leaf2166Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2166CertificateValid
    leaf2166InnerLogValid leaf2166CoversExact leaf2166LowerChecked

private noncomputable def leaf2167Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (217/64), kHi := (109/32), chiLo := (47/256), chiHi := (3/16) }

private noncomputable def leaf2167Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742355/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433595904) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1742069395/1073741824) }, upper := { exponent := 0, mantissa := (839/512) } }, logOuter := sk184LogOuterCertificate, logK := sk184LogKCertificate, logChi := chi136LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870517759/274867191808) } }, logDArg := sk184LogDArgCertificate }

private noncomputable def leaf2167InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf2167LocalValidity :
    LeafFacts leaf2167Box leaf2167Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2167Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433595904) }) = true
      norm_num [leaf2167Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2167CertificateValid :
    WideCertificateValid leaf2167Box leaf2167Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk184ValidityFacts chi136ValidityFacts
    leaf2167LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2167CoverageChecked :
    coverageCheck (innerAD leaf2167Box) leaf2167InnerLog = true := by
  rfl'

private theorem leaf2167InnerLogValid :
    leaf2167InnerLog.Valid 8 (innerAD leaf2167Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf2167CoverageChecked

private noncomputable def leaf2167InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907321/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2167InputLogOnePlusV_eq :
    leaf2167InputLogOnePlusV = outerEnclosure 24
      (leaf2167Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2167RoundedFacts : LeafRoundedFacts 8
    leaf2167Certificate.logOnePlusV leaf2167InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2167InputLogOnePlusV_eq }

private noncomputable def leaf2167Inputs : Inputs :=
  inputsOfCaches globalInput sk184RoundedInputs
    chi136InputQChi innerPair51Input
    leaf2167InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2167LowerChecked :
    lowerCheck 24 leaf2167Box leaf2167Inputs = true := by
  rfl'

private theorem leaf2167CoversExact : CoversExact 8
    leaf2167Box leaf2167Certificate leaf2167InnerLog leaf2167Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk184RoundedFacts chi136RoundedFacts
    innerPair51RoundedFacts leaf2167RoundedFacts (by rfl)

private theorem leaf2167FlatSound : Sound leaf2167Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2167CertificateValid
    leaf2167InnerLogValid leaf2167CoversExact leaf2167LowerChecked

private noncomputable def leaf2168Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (219/64), chiLo := (23/128), chiHi := (47/256) }

private noncomputable def leaf2168Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742355/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433683456) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1730863423/1073741824) }, upper := { exponent := 0, mantissa := (26677/16384) } }, logOuter := sk177LogOuterCertificate, logK := sk177LogKCertificate, logChi := chi135LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870605311/274867366912) } }, logDArg := sk177LogDArgCertificate }

private noncomputable def leaf2168InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf2168LocalValidity :
    LeafFacts leaf2168Box leaf2168Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2168Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433683456) }) = true
      norm_num [leaf2168Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2168CertificateValid :
    WideCertificateValid leaf2168Box leaf2168Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk177ValidityFacts chi135ValidityFacts
    leaf2168LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2168CoverageChecked :
    coverageCheck (innerAD leaf2168Box) leaf2168InnerLog = true := by
  rfl'

private theorem leaf2168InnerLogValid :
    leaf2168InnerLog.Valid 8 (innerAD leaf2168Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf2168CoverageChecked

private noncomputable def leaf2168InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814639/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2168InputLogOnePlusV_eq :
    leaf2168InputLogOnePlusV = outerEnclosure 24
      (leaf2168Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2168RoundedFacts : LeafRoundedFacts 8
    leaf2168Certificate.logOnePlusV leaf2168InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2168InputLogOnePlusV_eq }

private noncomputable def leaf2168Inputs : Inputs :=
  inputsOfCaches globalInput sk177RoundedInputs
    chi135InputQChi innerPair51Input
    leaf2168InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2168LowerChecked :
    lowerCheck 24 leaf2168Box leaf2168Inputs = true := by
  rfl'

private theorem leaf2168CoversExact : CoversExact 8
    leaf2168Box leaf2168Certificate leaf2168InnerLog leaf2168Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk177RoundedFacts chi135RoundedFacts
    innerPair51RoundedFacts leaf2168RoundedFacts (by rfl)

private theorem leaf2168FlatSound : Sound leaf2168Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2168CertificateValid
    leaf2168InnerLogValid leaf2168CoversExact leaf2168LowerChecked

private noncomputable def leaf2169Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (219/64), kHi := (55/16), chiLo := (23/128), chiHi := (47/256) }

private noncomputable def leaf2169Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742357/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433659392) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1733877893/1073741824) }, upper := { exponent := 0, mantissa := (6681/4096) } }, logOuter := sk178LogOuterCertificate, logK := sk178LogKCertificate, logChi := chi135LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870581247/274867318784) } }, logDArg := sk178LogDArgCertificate }

private noncomputable def leaf2169InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf2169LocalValidity :
    LeafFacts leaf2169Box leaf2169Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2169Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433659392) }) = true
      norm_num [leaf2169Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2169CertificateValid :
    WideCertificateValid leaf2169Box leaf2169Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk178ValidityFacts chi135ValidityFacts
    leaf2169LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2169CoverageChecked :
    coverageCheck (innerAD leaf2169Box) leaf2169InnerLog = true := by
  rfl'

private theorem leaf2169InnerLogValid :
    leaf2169InnerLog.Valid 8 (innerAD leaf2169Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf2169CoverageChecked

private noncomputable def leaf2169InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (363415/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf2169InputLogOnePlusV_eq :
    leaf2169InputLogOnePlusV = outerEnclosure 24
      (leaf2169Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2169RoundedFacts : LeafRoundedFacts 8
    leaf2169Certificate.logOnePlusV leaf2169InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2169InputLogOnePlusV_eq }

private noncomputable def leaf2169Inputs : Inputs :=
  inputsOfCaches globalInput sk178RoundedInputs
    chi135InputQChi innerPair51Input
    leaf2169InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2169LowerChecked :
    lowerCheck 24 leaf2169Box leaf2169Inputs = true := by
  rfl'

private theorem leaf2169CoversExact : CoversExact 8
    leaf2169Box leaf2169Certificate leaf2169InnerLog leaf2169Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk178RoundedFacts chi135RoundedFacts
    innerPair51RoundedFacts leaf2169RoundedFacts (by rfl)

private theorem leaf2169FlatSound : Sound leaf2169Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2169CertificateValid
    leaf2169InnerLogValid leaf2169CoversExact leaf2169LowerChecked

private noncomputable def leaf2170Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (219/64), chiLo := (47/256), chiHi := (3/16) }

private noncomputable def leaf2170Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742357/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433571328) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1745149397/1073741824) }, upper := { exponent := 0, mantissa := (1681/1024) } }, logOuter := sk177LogOuterCertificate, logK := sk177LogKCertificate, logChi := chi136LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870493183/274867142656) } }, logDArg := sk177LogDArgCertificate }

private noncomputable def leaf2170InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2170LocalValidity :
    LeafFacts leaf2170Box leaf2170Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2170Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433571328) }) = true
      norm_num [leaf2170Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2170CertificateValid :
    WideCertificateValid leaf2170Box leaf2170Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk177ValidityFacts chi136ValidityFacts
    leaf2170LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2170CoverageChecked :
    coverageCheck (innerAD leaf2170Box) leaf2170InnerLog = true := by
  rfl'

private theorem leaf2170InnerLogValid :
    leaf2170InnerLog.Valid 8 (innerAD leaf2170Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2170CoverageChecked

private noncomputable def leaf2170InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629285/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2170InputLogOnePlusV_eq :
    leaf2170InputLogOnePlusV = outerEnclosure 24
      (leaf2170Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2170RoundedFacts : LeafRoundedFacts 8
    leaf2170Certificate.logOnePlusV leaf2170InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2170InputLogOnePlusV_eq }

private noncomputable def leaf2170Inputs : Inputs :=
  inputsOfCaches globalInput sk177RoundedInputs
    chi136InputQChi innerPair56Input
    leaf2170InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2170LowerChecked :
    lowerCheck 24 leaf2170Box leaf2170Inputs = true := by
  rfl'

private theorem leaf2170CoversExact : CoversExact 8
    leaf2170Box leaf2170Certificate leaf2170InnerLog leaf2170Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk177RoundedFacts chi136RoundedFacts
    innerPair56RoundedFacts leaf2170RoundedFacts (by rfl)

private theorem leaf2170FlatSound : Sound leaf2170Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2170CertificateValid
    leaf2170InnerLogValid leaf2170CoversExact leaf2170LowerChecked

private noncomputable def leaf2171Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (219/64), kHi := (55/16), chiLo := (47/256), chiHi := (3/16) }

private noncomputable def leaf2171Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742359/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433546752) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1748229399/1073741824) }, upper := { exponent := 0, mantissa := (421/256) } }, logOuter := sk178LogOuterCertificate, logK := sk178LogKCertificate, logChi := chi136LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870468607/274867093504) } }, logDArg := sk178LogDArgCertificate }

private noncomputable def leaf2171InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2171LocalValidity :
    LeafFacts leaf2171Box leaf2171Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2171Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433546752) }) = true
      norm_num [leaf2171Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2171CertificateValid :
    WideCertificateValid leaf2171Box leaf2171Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk178ValidityFacts chi136ValidityFacts
    leaf2171LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2171CoverageChecked :
    coverageCheck (innerAD leaf2171Box) leaf2171InnerLog = true := by
  rfl'

private theorem leaf2171InnerLogValid :
    leaf2171InnerLog.Valid 8 (innerAD leaf2171Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2171CoverageChecked

private noncomputable def leaf2171InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629287/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2171InputLogOnePlusV_eq :
    leaf2171InputLogOnePlusV = outerEnclosure 24
      (leaf2171Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2171RoundedFacts : LeafRoundedFacts 8
    leaf2171Certificate.logOnePlusV leaf2171InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2171InputLogOnePlusV_eq }

private noncomputable def leaf2171Inputs : Inputs :=
  inputsOfCaches globalInput sk178RoundedInputs
    chi136InputQChi innerPair56Input
    leaf2171InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2171LowerChecked :
    lowerCheck 24 leaf2171Box leaf2171Inputs = true := by
  rfl'

private theorem leaf2171CoversExact : CoversExact 8
    leaf2171Box leaf2171Certificate leaf2171InnerLog leaf2171Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk178RoundedFacts chi136RoundedFacts
    innerPair56RoundedFacts leaf2171RoundedFacts (by rfl)

private theorem leaf2171FlatSound : Sound leaf2171Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2171CertificateValid
    leaf2171InnerLogValid leaf2171CoversExact leaf2171LowerChecked

private noncomputable def leaf2172Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (221/64), chiLo := (11/64), chiHi := (45/256) }

private noncomputable def leaf2172Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742355/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433861632) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1708058287/1073741824) }, upper := { exponent := 0, mantissa := (26329/16384) } }, logOuter := sk179LogOuterCertificate, logK := sk179LogKCertificate, logChi := chi133LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870783487/274867723264) } }, logDArg := sk179LogDArgCertificate }

private noncomputable def leaf2172InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2172LocalValidity :
    LeafFacts leaf2172Box leaf2172Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2172Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433861632) }) = true
      norm_num [leaf2172Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2172CertificateValid :
    WideCertificateValid leaf2172Box leaf2172Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk179ValidityFacts chi133ValidityFacts
    leaf2172LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2172CoverageChecked :
    coverageCheck (innerAD leaf2172Box) leaf2172InnerLog = true := by
  rfl'

private theorem leaf2172InnerLogValid :
    leaf2172InnerLog.Valid 8 (innerAD leaf2172Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2172CoverageChecked

private noncomputable def leaf2172InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907317/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2172InputLogOnePlusV_eq :
    leaf2172InputLogOnePlusV = outerEnclosure 24
      (leaf2172Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2172RoundedFacts : LeafRoundedFacts 8
    leaf2172Certificate.logOnePlusV leaf2172InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2172InputLogOnePlusV_eq }

private noncomputable def leaf2172Inputs : Inputs :=
  inputsOfCaches globalInput sk179RoundedInputs
    chi133InputQChi innerPair50Input
    leaf2172InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2172LowerChecked :
    lowerCheck 24 leaf2172Box leaf2172Inputs = true := by
  rfl'

private theorem leaf2172CoversExact : CoversExact 8
    leaf2172Box leaf2172Certificate leaf2172InnerLog leaf2172Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk179RoundedFacts chi133RoundedFacts
    innerPair50RoundedFacts leaf2172RoundedFacts (by rfl)

private theorem leaf2172FlatSound : Sound leaf2172Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2172CertificateValid
    leaf2172InnerLogValid leaf2172CoversExact leaf2172LowerChecked

private noncomputable def leaf2173Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (221/64), kHi := (111/32), chiLo := (11/64), chiHi := (45/256) }

private noncomputable def leaf2173Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742357/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433838592) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1710941693/1073741824) }, upper := { exponent := 0, mantissa := (13187/8192) } }, logOuter := sk180LogOuterCertificate, logK := sk180LogKCertificate, logChi := chi133LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870760447/274867677184) } }, logDArg := sk180LogDArgCertificate }

private noncomputable def leaf2173InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2173LocalValidity :
    LeafFacts leaf2173Box leaf2173Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2173Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433838592) }) = true
      norm_num [leaf2173Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2173CertificateValid :
    WideCertificateValid leaf2173Box leaf2173Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk180ValidityFacts chi133ValidityFacts
    leaf2173LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2173CoverageChecked :
    coverageCheck (innerAD leaf2173Box) leaf2173InnerLog = true := by
  rfl'

private theorem leaf2173InnerLogValid :
    leaf2173InnerLog.Valid 8 (innerAD leaf2173Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2173CoverageChecked

private noncomputable def leaf2173InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629269/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2173InputLogOnePlusV_eq :
    leaf2173InputLogOnePlusV = outerEnclosure 24
      (leaf2173Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2173RoundedFacts : LeafRoundedFacts 8
    leaf2173Certificate.logOnePlusV leaf2173InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2173InputLogOnePlusV_eq }

private noncomputable def leaf2173Inputs : Inputs :=
  inputsOfCaches globalInput sk180RoundedInputs
    chi133InputQChi innerPair50Input
    leaf2173InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2173LowerChecked :
    lowerCheck 24 leaf2173Box leaf2173Inputs = true := by
  rfl'

private theorem leaf2173CoversExact : CoversExact 8
    leaf2173Box leaf2173Certificate leaf2173InnerLog leaf2173Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk180RoundedFacts chi133RoundedFacts
    innerPair50RoundedFacts leaf2173RoundedFacts (by rfl)

private theorem leaf2173FlatSound : Sound leaf2173Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2173CertificateValid
    leaf2173InnerLogValid leaf2173CoversExact leaf2173LowerChecked

private noncomputable def leaf2174Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (221/64), chiLo := (45/256), chiHi := (23/128) }

private noncomputable def leaf2174Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742357/1073741824) }, vSqrt := { lower := (65529/65536), upper := (27487384371/27486749696) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1722475325/1073741824) }, upper := { exponent := 0, mantissa := (13275/8192) } }, logOuter := sk179LogOuterCertificate, logK := sk179LogKCertificate, logChi := chi134LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (54974134067/54973499392) } }, logDArg := sk179LogDArgCertificate }

private noncomputable def leaf2174InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2174LocalValidity :
    LeafFacts leaf2174Box leaf2174Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2174Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (27487384371/27486749696) }) = true
      norm_num [leaf2174Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2174CertificateValid :
    WideCertificateValid leaf2174Box leaf2174Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk179ValidityFacts chi134ValidityFacts
    leaf2174LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2174CoverageChecked :
    coverageCheck (innerAD leaf2174Box) leaf2174InnerLog = true := by
  rfl'

private theorem leaf2174InnerLogValid :
    leaf2174InnerLog.Valid 8 (innerAD leaf2174Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2174CoverageChecked

private noncomputable def leaf2174InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814637/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2174InputLogOnePlusV_eq :
    leaf2174InputLogOnePlusV = outerEnclosure 24
      (leaf2174Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2174RoundedFacts : LeafRoundedFacts 8
    leaf2174Certificate.logOnePlusV leaf2174InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2174InputLogOnePlusV_eq }

private noncomputable def leaf2174Inputs : Inputs :=
  inputsOfCaches globalInput sk179RoundedInputs
    chi134InputQChi innerPair50Input
    leaf2174InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2174LowerChecked :
    lowerCheck 24 leaf2174Box leaf2174Inputs = true := by
  rfl'

private theorem leaf2174CoversExact : CoversExact 8
    leaf2174Box leaf2174Certificate leaf2174InnerLog leaf2174Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk179RoundedFacts chi134RoundedFacts
    innerPair50RoundedFacts leaf2174RoundedFacts (by rfl)

private theorem leaf2174FlatSound : Sound leaf2174Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2174CertificateValid
    leaf2174InnerLogValid leaf2174CoversExact leaf2174LowerChecked

private noncomputable def leaf2175Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (221/64), kHi := (111/32), chiLo := (45/256), chiHi := (23/128) }

private noncomputable def leaf2175Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742359/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433724928) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1725424263/1073741824) }, upper := { exponent := 0, mantissa := (6649/4096) } }, logOuter := sk180LogOuterCertificate, logK := sk180LogKCertificate, logChi := chi134LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870646783/274867449856) } }, logDArg := sk180LogDArgCertificate }

private noncomputable def leaf2175InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2175LocalValidity :
    LeafFacts leaf2175Box leaf2175Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2175Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433724928) }) = true
      norm_num [leaf2175Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2175CertificateValid :
    WideCertificateValid leaf2175Box leaf2175Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk180ValidityFacts chi134ValidityFacts
    leaf2175LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2175CoverageChecked :
    coverageCheck (innerAD leaf2175Box) leaf2175InnerLog = true := by
  rfl'

private theorem leaf2175InnerLogValid :
    leaf2175InnerLog.Valid 8 (innerAD leaf2175Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2175CoverageChecked

private noncomputable def leaf2175InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907319/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2175InputLogOnePlusV_eq :
    leaf2175InputLogOnePlusV = outerEnclosure 24
      (leaf2175Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2175RoundedFacts : LeafRoundedFacts 8
    leaf2175Certificate.logOnePlusV leaf2175InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2175InputLogOnePlusV_eq }

private noncomputable def leaf2175Inputs : Inputs :=
  inputsOfCaches globalInput sk180RoundedInputs
    chi134InputQChi innerPair50Input
    leaf2175InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2175LowerChecked :
    lowerCheck 24 leaf2175Box leaf2175Inputs = true := by
  rfl'

private theorem leaf2175CoversExact : CoversExact 8
    leaf2175Box leaf2175Certificate leaf2175InnerLog leaf2175Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk180RoundedFacts chi134RoundedFacts
    innerPair50RoundedFacts leaf2175RoundedFacts (by rfl)

private theorem leaf2175FlatSound : Sound leaf2175Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2175CertificateValid
    leaf2175InnerLogValid leaf2175CoversExact leaf2175LowerChecked

private noncomputable def leaf2176Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (223/64), chiLo := (11/64), chiHi := (45/256) }

private noncomputable def leaf2176Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742359/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433815552) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1713825099/1073741824) }, upper := { exponent := 0, mantissa := (26419/16384) } }, logOuter := sk181LogOuterCertificate, logK := sk181LogKCertificate, logChi := chi133LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870737407/274867631104) } }, logDArg := sk181LogDArgCertificate }

private noncomputable def leaf2176InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2176LocalValidity :
    LeafFacts leaf2176Box leaf2176Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2176Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433815552) }) = true
      norm_num [leaf2176Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2176CertificateValid :
    WideCertificateValid leaf2176Box leaf2176Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk181ValidityFacts chi133ValidityFacts
    leaf2176LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2176CoverageChecked :
    coverageCheck (innerAD leaf2176Box) leaf2176InnerLog = true := by
  rfl'

private theorem leaf2176InnerLogValid :
    leaf2176InnerLog.Valid 8 (innerAD leaf2176Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2176CoverageChecked

private noncomputable def leaf2176InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814635/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2176InputLogOnePlusV_eq :
    leaf2176InputLogOnePlusV = outerEnclosure 24
      (leaf2176Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2176RoundedFacts : LeafRoundedFacts 8
    leaf2176Certificate.logOnePlusV leaf2176InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2176InputLogOnePlusV_eq }

private noncomputable def leaf2176Inputs : Inputs :=
  inputsOfCaches globalInput sk181RoundedInputs
    chi133InputQChi innerPair50Input
    leaf2176InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2176LowerChecked :
    lowerCheck 24 leaf2176Box leaf2176Inputs = true := by
  rfl'

private theorem leaf2176CoversExact : CoversExact 8
    leaf2176Box leaf2176Certificate leaf2176InnerLog leaf2176Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk181RoundedFacts chi133RoundedFacts
    innerPair50RoundedFacts leaf2176RoundedFacts (by rfl)

private theorem leaf2176FlatSound : Sound leaf2176Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2176CertificateValid
    leaf2176InnerLogValid leaf2176CoversExact leaf2176LowerChecked

private noncomputable def leaf2177Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (223/64), kHi := (7/2), chiLo := (11/64), chiHi := (45/256) }

private noncomputable def leaf2177Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742361/1073741824) }, vSqrt := { lower := (8191/8192), upper := (8084524815/8084340736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1716708505/1073741824) }, upper := { exponent := 0, mantissa := (827/512) } }, logOuter := sk182LogOuterCertificate, logK := sk182LogKCertificate, logChi := chi133LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16168865551/16168681472) } }, logDArg := sk182LogDArgCertificate }

private noncomputable def leaf2177InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2177LocalValidity :
    LeafFacts leaf2177Box leaf2177Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2177Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8084524815/8084340736) }) = true
      norm_num [leaf2177Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2177CertificateValid :
    WideCertificateValid leaf2177Box leaf2177Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk182ValidityFacts chi133ValidityFacts
    leaf2177LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2177CoverageChecked :
    coverageCheck (innerAD leaf2177Box) leaf2177InnerLog = true := by
  rfl'

private theorem leaf2177InnerLogValid :
    leaf2177InnerLog.Valid 8 (innerAD leaf2177Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2177CoverageChecked

private noncomputable def leaf2177InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453659/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf2177InputLogOnePlusV_eq :
    leaf2177InputLogOnePlusV = outerEnclosure 24
      (leaf2177Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2177RoundedFacts : LeafRoundedFacts 8
    leaf2177Certificate.logOnePlusV leaf2177InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2177InputLogOnePlusV_eq }

private noncomputable def leaf2177Inputs : Inputs :=
  inputsOfCaches globalInput sk182RoundedInputs
    chi133InputQChi innerPair50Input
    leaf2177InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2177LowerChecked :
    lowerCheck 24 leaf2177Box leaf2177Inputs = true := by
  rfl'

private theorem leaf2177CoversExact : CoversExact 8
    leaf2177Box leaf2177Certificate leaf2177InnerLog leaf2177Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk182RoundedFacts chi133RoundedFacts
    innerPair50RoundedFacts leaf2177RoundedFacts (by rfl)

private theorem leaf2177FlatSound : Sound leaf2177Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2177CertificateValid
    leaf2177InnerLogValid leaf2177CoversExact leaf2177LowerChecked

private noncomputable def leaf2178Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (223/64), chiLo := (45/256), chiHi := (23/128) }

private noncomputable def leaf2178Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742361/1073741824) }, vSqrt := { lower := (65529/65536), upper := (5090256365/5090137088) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1728373201/1073741824) }, upper := { exponent := 0, mantissa := (13321/8192) } }, logOuter := sk181LogOuterCertificate, logK := sk181LogKCertificate, logChi := chi134LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (10180393453/10180274176) } }, logDArg := sk181LogDArgCertificate }

private noncomputable def leaf2178InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf2178LocalValidity :
    LeafFacts leaf2178Box leaf2178Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2178Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (5090256365/5090137088) }) = true
      norm_num [leaf2178Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2178CertificateValid :
    WideCertificateValid leaf2178Box leaf2178Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk181ValidityFacts chi134ValidityFacts
    leaf2178LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2178CoverageChecked :
    coverageCheck (innerAD leaf2178Box) leaf2178InnerLog = true := by
  rfl'

private theorem leaf2178InnerLogValid :
    leaf2178InnerLog.Valid 8 (innerAD leaf2178Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf2178CoverageChecked

private noncomputable def leaf2178InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629277/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2178InputLogOnePlusV_eq :
    leaf2178InputLogOnePlusV = outerEnclosure 24
      (leaf2178Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2178RoundedFacts : LeafRoundedFacts 8
    leaf2178Certificate.logOnePlusV leaf2178InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2178InputLogOnePlusV_eq }

private noncomputable def leaf2178Inputs : Inputs :=
  inputsOfCaches globalInput sk181RoundedInputs
    chi134InputQChi innerPair51Input
    leaf2178InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2178LowerChecked :
    lowerCheck 24 leaf2178Box leaf2178Inputs = true := by
  rfl'

private theorem leaf2178CoversExact : CoversExact 8
    leaf2178Box leaf2178Certificate leaf2178InnerLog leaf2178Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk181RoundedFacts chi134RoundedFacts
    innerPair51RoundedFacts leaf2178RoundedFacts (by rfl)

private theorem leaf2178FlatSound : Sound leaf2178Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2178CertificateValid
    leaf2178InnerLogValid leaf2178CoversExact leaf2178LowerChecked

private noncomputable def leaf2179Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (223/64), kHi := (7/2), chiLo := (45/256), chiHi := (23/128) }

private noncomputable def leaf2179Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742363/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433677824) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1731322139/1073741824) }, upper := { exponent := 0, mantissa := (417/256) } }, logOuter := sk182LogOuterCertificate, logK := sk182LogKCertificate, logChi := chi134LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870599679/274867355648) } }, logDArg := sk182LogDArgCertificate }

private noncomputable def leaf2179InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf2179LocalValidity :
    LeafFacts leaf2179Box leaf2179Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2179Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433677824) }) = true
      norm_num [leaf2179Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2179CertificateValid :
    WideCertificateValid leaf2179Box leaf2179Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk182ValidityFacts chi134ValidityFacts
    leaf2179LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2179CoverageChecked :
    coverageCheck (innerAD leaf2179Box) leaf2179InnerLog = true := by
  rfl'

private theorem leaf2179InnerLogValid :
    leaf2179InnerLog.Valid 8 (innerAD leaf2179Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf2179CoverageChecked

private noncomputable def leaf2179InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629279/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2179InputLogOnePlusV_eq :
    leaf2179InputLogOnePlusV = outerEnclosure 24
      (leaf2179Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2179RoundedFacts : LeafRoundedFacts 8
    leaf2179Certificate.logOnePlusV leaf2179InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2179InputLogOnePlusV_eq }

private noncomputable def leaf2179Inputs : Inputs :=
  inputsOfCaches globalInput sk182RoundedInputs
    chi134InputQChi innerPair51Input
    leaf2179InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2179LowerChecked :
    lowerCheck 24 leaf2179Box leaf2179Inputs = true := by
  rfl'

private theorem leaf2179CoversExact : CoversExact 8
    leaf2179Box leaf2179Certificate leaf2179InnerLog leaf2179Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk182RoundedFacts chi134RoundedFacts
    innerPair51RoundedFacts leaf2179RoundedFacts (by rfl)

private theorem leaf2179FlatSound : Sound leaf2179Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2179CertificateValid
    leaf2179InnerLogValid leaf2179CoversExact leaf2179LowerChecked

private noncomputable def leaf2180Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (221/64), chiLo := (23/128), chiHi := (47/256) }

private noncomputable def leaf2180Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742359/1073741824) }, vSqrt := { lower := (65529/65536), upper := (45812307285/45811211776) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1736892363/1073741824) }, upper := { exponent := 0, mantissa := (26771/16384) } }, logOuter := sk179LogOuterCertificate, logK := sk179LogKCertificate, logChi := chi135LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (91623519061/91622423552) } }, logDArg := sk179LogDArgCertificate }

private noncomputable def leaf2180InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf2180LocalValidity :
    LeafFacts leaf2180Box leaf2180Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2180Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (45812307285/45811211776) }) = true
      norm_num [leaf2180Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2180CertificateValid :
    WideCertificateValid leaf2180Box leaf2180Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk179ValidityFacts chi135ValidityFacts
    leaf2180LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2180CoverageChecked :
    coverageCheck (innerAD leaf2180Box) leaf2180InnerLog = true := by
  rfl'

private theorem leaf2180InnerLogValid :
    leaf2180InnerLog.Valid 8 (innerAD leaf2180Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf2180CoverageChecked

private noncomputable def leaf2180InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629281/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2180InputLogOnePlusV_eq :
    leaf2180InputLogOnePlusV = outerEnclosure 24
      (leaf2180Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2180RoundedFacts : LeafRoundedFacts 8
    leaf2180Certificate.logOnePlusV leaf2180InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2180InputLogOnePlusV_eq }

private noncomputable def leaf2180Inputs : Inputs :=
  inputsOfCaches globalInput sk179RoundedInputs
    chi135InputQChi innerPair51Input
    leaf2180InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2180LowerChecked :
    lowerCheck 24 leaf2180Box leaf2180Inputs = true := by
  rfl'

private theorem leaf2180CoversExact : CoversExact 8
    leaf2180Box leaf2180Certificate leaf2180InnerLog leaf2180Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk179RoundedFacts chi135RoundedFacts
    innerPair51RoundedFacts leaf2180RoundedFacts (by rfl)

private theorem leaf2180FlatSound : Sound leaf2180Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2180CertificateValid
    leaf2180InnerLogValid leaf2180CoversExact leaf2180LowerChecked

private noncomputable def leaf2181Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (221/64), kHi := (111/32), chiLo := (23/128), chiHi := (47/256) }

private noncomputable def leaf2181Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742361/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433611264) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1739906833/1073741824) }, upper := { exponent := 0, mantissa := (13409/8192) } }, logOuter := sk180LogOuterCertificate, logK := sk180LogKCertificate, logChi := chi135LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870533119/274867222528) } }, logDArg := sk180LogDArgCertificate }

private noncomputable def leaf2181InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf2181LocalValidity :
    LeafFacts leaf2181Box leaf2181Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2181Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433611264) }) = true
      norm_num [leaf2181Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2181CertificateValid :
    WideCertificateValid leaf2181Box leaf2181Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk180ValidityFacts chi135ValidityFacts
    leaf2181LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2181CoverageChecked :
    coverageCheck (innerAD leaf2181Box) leaf2181InnerLog = true := by
  rfl'

private theorem leaf2181InnerLogValid :
    leaf2181InnerLog.Valid 8 (innerAD leaf2181Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf2181CoverageChecked

private noncomputable def leaf2181InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629283/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2181InputLogOnePlusV_eq :
    leaf2181InputLogOnePlusV = outerEnclosure 24
      (leaf2181Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2181RoundedFacts : LeafRoundedFacts 8
    leaf2181Certificate.logOnePlusV leaf2181InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2181InputLogOnePlusV_eq }

private noncomputable def leaf2181Inputs : Inputs :=
  inputsOfCaches globalInput sk180RoundedInputs
    chi135InputQChi innerPair51Input
    leaf2181InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2181LowerChecked :
    lowerCheck 24 leaf2181Box leaf2181Inputs = true := by
  rfl'

private theorem leaf2181CoversExact : CoversExact 8
    leaf2181Box leaf2181Certificate leaf2181InnerLog leaf2181Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk180RoundedFacts chi135RoundedFacts
    innerPair51RoundedFacts leaf2181RoundedFacts (by rfl)

private theorem leaf2181FlatSound : Sound leaf2181Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2181CertificateValid
    leaf2181InnerLogValid leaf2181CoversExact leaf2181LowerChecked

private noncomputable def leaf2182Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (221/64), chiLo := (47/256), chiHi := (3/16) }

private noncomputable def leaf2182Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742361/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433522176) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1751309401/1073741824) }, upper := { exponent := 0, mantissa := (1687/1024) } }, logOuter := sk179LogOuterCertificate, logK := sk179LogKCertificate, logChi := chi136LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870444031/274867044352) } }, logDArg := sk179LogDArgCertificate }

private noncomputable def leaf2182InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2182LocalValidity :
    LeafFacts leaf2182Box leaf2182Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2182Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433522176) }) = true
      norm_num [leaf2182Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2182CertificateValid :
    WideCertificateValid leaf2182Box leaf2182Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk179ValidityFacts chi136ValidityFacts
    leaf2182LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2182CoverageChecked :
    coverageCheck (innerAD leaf2182Box) leaf2182InnerLog = true := by
  rfl'

private theorem leaf2182InnerLogValid :
    leaf2182InnerLog.Valid 8 (innerAD leaf2182Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2182CoverageChecked

private noncomputable def leaf2182InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453661/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf2182InputLogOnePlusV_eq :
    leaf2182InputLogOnePlusV = outerEnclosure 24
      (leaf2182Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2182RoundedFacts : LeafRoundedFacts 8
    leaf2182Certificate.logOnePlusV leaf2182InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2182InputLogOnePlusV_eq }

private noncomputable def leaf2182Inputs : Inputs :=
  inputsOfCaches globalInput sk179RoundedInputs
    chi136InputQChi innerPair56Input
    leaf2182InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2182LowerChecked :
    lowerCheck 24 leaf2182Box leaf2182Inputs = true := by
  rfl'

private theorem leaf2182CoversExact : CoversExact 8
    leaf2182Box leaf2182Certificate leaf2182InnerLog leaf2182Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk179RoundedFacts chi136RoundedFacts
    innerPair56RoundedFacts leaf2182RoundedFacts (by rfl)

private theorem leaf2182FlatSound : Sound leaf2182Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2182CertificateValid
    leaf2182InnerLogValid leaf2182CoversExact leaf2182LowerChecked

private noncomputable def leaf2183Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (221/64), kHi := (111/32), chiLo := (47/256), chiHi := (3/16) }

private noncomputable def leaf2183Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742363/1073741824) }, vSqrt := { lower := (65529/65536), upper := (27487384371/27486699520) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1754389403/1073741824) }, upper := { exponent := 0, mantissa := (845/512) } }, logOuter := sk180LogOuterCertificate, logK := sk180LogKCertificate, logChi := chi136LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (54974083891/54973399040) } }, logDArg := sk180LogDArgCertificate }

private noncomputable def leaf2183InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2183LocalValidity :
    LeafFacts leaf2183Box leaf2183Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2183Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (27487384371/27486699520) }) = true
      norm_num [leaf2183Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2183CertificateValid :
    WideCertificateValid leaf2183Box leaf2183Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk180ValidityFacts chi136ValidityFacts
    leaf2183LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2183CoverageChecked :
    coverageCheck (innerAD leaf2183Box) leaf2183InnerLog = true := by
  rfl'

private theorem leaf2183InnerLogValid :
    leaf2183InnerLog.Valid 8 (innerAD leaf2183Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2183CoverageChecked

private noncomputable def leaf2183InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814645/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2183InputLogOnePlusV_eq :
    leaf2183InputLogOnePlusV = outerEnclosure 24
      (leaf2183Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2183RoundedFacts : LeafRoundedFacts 8
    leaf2183Certificate.logOnePlusV leaf2183InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2183InputLogOnePlusV_eq }

private noncomputable def leaf2183Inputs : Inputs :=
  inputsOfCaches globalInput sk180RoundedInputs
    chi136InputQChi innerPair56Input
    leaf2183InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2183LowerChecked :
    lowerCheck 24 leaf2183Box leaf2183Inputs = true := by
  rfl'

private theorem leaf2183CoversExact : CoversExact 8
    leaf2183Box leaf2183Certificate leaf2183InnerLog leaf2183Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk180RoundedFacts chi136RoundedFacts
    innerPair56RoundedFacts leaf2183RoundedFacts (by rfl)

private theorem leaf2183FlatSound : Sound leaf2183Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2183CertificateValid
    leaf2183InnerLogValid leaf2183CoversExact leaf2183LowerChecked

private noncomputable def leaf2184Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (223/64), chiLo := (23/128), chiHi := (47/256) }

private noncomputable def leaf2184Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742363/1073741824) }, vSqrt := { lower := (65529/65536), upper := (27487384371/27486717440) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1742921303/1073741824) }, upper := { exponent := 0, mantissa := (26865/16384) } }, logOuter := sk181LogOuterCertificate, logK := sk181LogKCertificate, logChi := chi135LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (54974101811/54973434880) } }, logDArg := sk181LogDArgCertificate }

private noncomputable def leaf2184InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf2184LocalValidity :
    LeafFacts leaf2184Box leaf2184Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2184Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (27487384371/27486717440) }) = true
      norm_num [leaf2184Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2184CertificateValid :
    WideCertificateValid leaf2184Box leaf2184Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk181ValidityFacts chi135ValidityFacts
    leaf2184LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2184CoverageChecked :
    coverageCheck (innerAD leaf2184Box) leaf2184InnerLog = true := by
  rfl'

private theorem leaf2184InnerLogValid :
    leaf2184InnerLog.Valid 8 (innerAD leaf2184Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf2184CoverageChecked

private noncomputable def leaf2184InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907321/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2184InputLogOnePlusV_eq :
    leaf2184InputLogOnePlusV = outerEnclosure 24
      (leaf2184Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2184RoundedFacts : LeafRoundedFacts 8
    leaf2184Certificate.logOnePlusV leaf2184InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2184InputLogOnePlusV_eq }

private noncomputable def leaf2184Inputs : Inputs :=
  inputsOfCaches globalInput sk181RoundedInputs
    chi135InputQChi innerPair51Input
    leaf2184InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2184LowerChecked :
    lowerCheck 24 leaf2184Box leaf2184Inputs = true := by
  rfl'

private theorem leaf2184CoversExact : CoversExact 8
    leaf2184Box leaf2184Certificate leaf2184InnerLog leaf2184Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk181RoundedFacts chi135RoundedFacts
    innerPair51RoundedFacts leaf2184RoundedFacts (by rfl)

private theorem leaf2184FlatSound : Sound leaf2184Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2184CertificateValid
    leaf2184InnerLogValid leaf2184CoversExact leaf2184LowerChecked

private noncomputable def leaf2185Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (223/64), kHi := (7/2), chiLo := (23/128), chiHi := (47/256) }

private noncomputable def leaf2185Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742365/1073741824) }, vSqrt := { lower := (8191/8192), upper := (5090256365/5090131968) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1745935773/1073741824) }, upper := { exponent := 0, mantissa := (841/512) } }, logOuter := sk182LogOuterCertificate, logK := sk182LogKCertificate, logChi := chi135LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (10180388333/10180263936) } }, logDArg := sk182LogDArgCertificate }

private noncomputable def leaf2185InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2185LocalValidity :
    LeafFacts leaf2185Box leaf2185Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2185Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5090256365/5090131968) }) = true
      norm_num [leaf2185Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2185CertificateValid :
    WideCertificateValid leaf2185Box leaf2185Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk182ValidityFacts chi135ValidityFacts
    leaf2185LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2185CoverageChecked :
    coverageCheck (innerAD leaf2185Box) leaf2185InnerLog = true := by
  rfl'

private theorem leaf2185InnerLogValid :
    leaf2185InnerLog.Valid 8 (innerAD leaf2185Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2185CoverageChecked

private noncomputable def leaf2185InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814643/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2185InputLogOnePlusV_eq :
    leaf2185InputLogOnePlusV = outerEnclosure 24
      (leaf2185Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2185RoundedFacts : LeafRoundedFacts 8
    leaf2185Certificate.logOnePlusV leaf2185InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2185InputLogOnePlusV_eq }

private noncomputable def leaf2185Inputs : Inputs :=
  inputsOfCaches globalInput sk182RoundedInputs
    chi135InputQChi innerPair56Input
    leaf2185InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2185LowerChecked :
    lowerCheck 24 leaf2185Box leaf2185Inputs = true := by
  rfl'

private theorem leaf2185CoversExact : CoversExact 8
    leaf2185Box leaf2185Certificate leaf2185InnerLog leaf2185Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk182RoundedFacts chi135RoundedFacts
    innerPair56RoundedFacts leaf2185RoundedFacts (by rfl)

private theorem leaf2185FlatSound : Sound leaf2185Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2185CertificateValid
    leaf2185InnerLogValid leaf2185CoversExact leaf2185LowerChecked

private noncomputable def leaf2186Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (223/64), chiLo := (47/256), chiHi := (3/16) }

private noncomputable def leaf2186Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742365/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433473024) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1757469405/1073741824) }, upper := { exponent := 0, mantissa := (1693/1024) } }, logOuter := sk181LogOuterCertificate, logK := sk181LogKCertificate, logChi := chi136LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870394879/274866946048) } }, logDArg := sk181LogDArgCertificate }

private noncomputable def leaf2186InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2186LocalValidity :
    LeafFacts leaf2186Box leaf2186Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2186Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433473024) }) = true
      norm_num [leaf2186Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2186CertificateValid :
    WideCertificateValid leaf2186Box leaf2186Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk181ValidityFacts chi136ValidityFacts
    leaf2186LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2186CoverageChecked :
    coverageCheck (innerAD leaf2186Box) leaf2186InnerLog = true := by
  rfl'

private theorem leaf2186InnerLogValid :
    leaf2186InnerLog.Valid 8 (innerAD leaf2186Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2186CoverageChecked

private noncomputable def leaf2186InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629291/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2186InputLogOnePlusV_eq :
    leaf2186InputLogOnePlusV = outerEnclosure 24
      (leaf2186Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2186RoundedFacts : LeafRoundedFacts 8
    leaf2186Certificate.logOnePlusV leaf2186InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2186InputLogOnePlusV_eq }

private noncomputable def leaf2186Inputs : Inputs :=
  inputsOfCaches globalInput sk181RoundedInputs
    chi136InputQChi innerPair56Input
    leaf2186InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2186LowerChecked :
    lowerCheck 24 leaf2186Box leaf2186Inputs = true := by
  rfl'

private theorem leaf2186CoversExact : CoversExact 8
    leaf2186Box leaf2186Certificate leaf2186InnerLog leaf2186Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk181RoundedFacts chi136RoundedFacts
    innerPair56RoundedFacts leaf2186RoundedFacts (by rfl)

private theorem leaf2186FlatSound : Sound leaf2186Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2186CertificateValid
    leaf2186InnerLogValid leaf2186CoversExact leaf2186LowerChecked

private noncomputable def leaf2187Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (223/64), kHi := (7/2), chiLo := (47/256), chiHi := (3/16) }

private noncomputable def leaf2187Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742367/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433448448) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1760549407/1073741824) }, upper := { exponent := 0, mantissa := (53/32) } }, logOuter := sk182LogOuterCertificate, logK := sk182LogKCertificate, logChi := chi136LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870370303/274866896896) } }, logDArg := sk182LogDArgCertificate }

private noncomputable def leaf2187InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2187LocalValidity :
    LeafFacts leaf2187Box leaf2187Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2187Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433448448) }) = true
      norm_num [leaf2187Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2187CertificateValid :
    WideCertificateValid leaf2187Box leaf2187Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk182ValidityFacts chi136ValidityFacts
    leaf2187LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2187CoverageChecked :
    coverageCheck (innerAD leaf2187Box) leaf2187InnerLog = true := by
  rfl'

private theorem leaf2187InnerLogValid :
    leaf2187InnerLog.Valid 8 (innerAD leaf2187Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2187CoverageChecked

private noncomputable def leaf2187InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629293/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2187InputLogOnePlusV_eq :
    leaf2187InputLogOnePlusV = outerEnclosure 24
      (leaf2187Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2187RoundedFacts : LeafRoundedFacts 8
    leaf2187Certificate.logOnePlusV leaf2187InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2187InputLogOnePlusV_eq }

private noncomputable def leaf2187Inputs : Inputs :=
  inputsOfCaches globalInput sk182RoundedInputs
    chi136InputQChi innerPair56Input
    leaf2187InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2187LowerChecked :
    lowerCheck 24 leaf2187Box leaf2187Inputs = true := by
  rfl'

private theorem leaf2187CoversExact : CoversExact 8
    leaf2187Box leaf2187Certificate leaf2187InnerLog leaf2187Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk182RoundedFacts chi136RoundedFacts
    innerPair56RoundedFacts leaf2187RoundedFacts (by rfl)

private theorem leaf2187FlatSound : Sound leaf2187Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2187CertificateValid
    leaf2187InnerLogValid leaf2187CoversExact leaf2187LowerChecked

private noncomputable def component47Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (5/32), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component47Node0_sound : Sound component47Node0Box :=
  sound_of_literal_split component47Node0Box leaf2133Box leaf2134Box
    .chi (41/256) (by rfl) (by rfl)
    leaf2133FlatSound leaf2134FlatSound

private noncomputable def component47Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (5/32), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component47Node1_sound : Sound component47Node1Box :=
  sound_of_literal_split component47Node1Box leaf2135Box leaf2136Box
    .chi (41/256) (by rfl) (by rfl)
    leaf2135FlatSound leaf2136FlatSound

private noncomputable def component47Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (5/32), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component47Node2_sound : Sound component47Node2Box :=
  sound_of_literal_split component47Node2Box component47Node0Box component47Node1Box
    .k (109/32) (by rfl) (by rfl)
    component47Node0_sound component47Node1_sound

private noncomputable def component47Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (21/128), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component47Node3_sound : Sound component47Node3Box :=
  sound_of_literal_split component47Node3Box leaf2137Box leaf2138Box
    .chi (43/256) (by rfl) (by rfl)
    leaf2137FlatSound leaf2138FlatSound

private noncomputable def component47Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (43/256), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component47Node4_sound : Sound component47Node4Box :=
  sound_of_literal_split component47Node4Box leaf2140Box leaf2141Box
    .k (219/64) (by rfl) (by rfl)
    leaf2140FlatSound leaf2141FlatSound

private noncomputable def component47Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (21/128), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component47Node5_sound : Sound component47Node5Box :=
  sound_of_literal_split component47Node5Box leaf2139Box component47Node4Box
    .chi (43/256) (by rfl) (by rfl)
    leaf2139FlatSound component47Node4_sound

private noncomputable def component47Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (21/128), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component47Node6_sound : Sound component47Node6Box :=
  sound_of_literal_split component47Node6Box component47Node3Box component47Node5Box
    .k (109/32) (by rfl) (by rfl)
    component47Node3_sound component47Node5_sound

private noncomputable def component47Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (5/32), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component47Node7_sound : Sound component47Node7Box :=
  sound_of_literal_split component47Node7Box component47Node2Box component47Node6Box
    .chi (21/128) (by rfl) (by rfl)
    component47Node2_sound component47Node6_sound

private noncomputable def component47Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (41/256), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component47Node8_sound : Sound component47Node8Box :=
  sound_of_literal_split component47Node8Box leaf2143Box leaf2144Box
    .k (221/64) (by rfl) (by rfl)
    leaf2143FlatSound leaf2144FlatSound

private noncomputable def component47Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (5/32), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component47Node9_sound : Sound component47Node9Box :=
  sound_of_literal_split component47Node9Box leaf2142Box component47Node8Box
    .chi (41/256) (by rfl) (by rfl)
    leaf2142FlatSound component47Node8_sound

private noncomputable def component47Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (5/32), chiHi := (41/256) }

set_option maxRecDepth 1000000 in
private theorem component47Node10_sound : Sound component47Node10Box :=
  sound_of_literal_split component47Node10Box leaf2145Box leaf2146Box
    .k (223/64) (by rfl) (by rfl)
    leaf2145FlatSound leaf2146FlatSound

private noncomputable def component47Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (41/256), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component47Node11_sound : Sound component47Node11Box :=
  sound_of_literal_split component47Node11Box leaf2147Box leaf2148Box
    .k (223/64) (by rfl) (by rfl)
    leaf2147FlatSound leaf2148FlatSound

private noncomputable def component47Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (5/32), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component47Node12_sound : Sound component47Node12Box :=
  sound_of_literal_split component47Node12Box component47Node10Box component47Node11Box
    .chi (41/256) (by rfl) (by rfl)
    component47Node10_sound component47Node11_sound

private noncomputable def component47Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (5/32), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component47Node13_sound : Sound component47Node13Box :=
  sound_of_literal_split component47Node13Box component47Node9Box component47Node12Box
    .k (111/32) (by rfl) (by rfl)
    component47Node9_sound component47Node12_sound

private noncomputable def component47Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (21/128), chiHi := (43/256) }

set_option maxRecDepth 1000000 in
private theorem component47Node14_sound : Sound component47Node14Box :=
  sound_of_literal_split component47Node14Box leaf2149Box leaf2150Box
    .k (221/64) (by rfl) (by rfl)
    leaf2149FlatSound leaf2150FlatSound

private noncomputable def component47Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (43/256), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component47Node15_sound : Sound component47Node15Box :=
  sound_of_literal_split component47Node15Box leaf2151Box leaf2152Box
    .k (221/64) (by rfl) (by rfl)
    leaf2151FlatSound leaf2152FlatSound

private noncomputable def component47Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (21/128), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component47Node16_sound : Sound component47Node16Box :=
  sound_of_literal_split component47Node16Box component47Node14Box component47Node15Box
    .chi (43/256) (by rfl) (by rfl)
    component47Node14_sound component47Node15_sound

private noncomputable def component47Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (21/128), chiHi := (43/256) }

set_option maxRecDepth 1000000 in
private theorem component47Node17_sound : Sound component47Node17Box :=
  sound_of_literal_split component47Node17Box leaf2153Box leaf2154Box
    .k (223/64) (by rfl) (by rfl)
    leaf2153FlatSound leaf2154FlatSound

private noncomputable def component47Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (43/256), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component47Node18_sound : Sound component47Node18Box :=
  sound_of_literal_split component47Node18Box leaf2155Box leaf2156Box
    .k (223/64) (by rfl) (by rfl)
    leaf2155FlatSound leaf2156FlatSound

private noncomputable def component47Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (21/128), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component47Node19_sound : Sound component47Node19Box :=
  sound_of_literal_split component47Node19Box component47Node17Box component47Node18Box
    .chi (43/256) (by rfl) (by rfl)
    component47Node17_sound component47Node18_sound

private noncomputable def component47Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (21/128), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component47Node20_sound : Sound component47Node20Box :=
  sound_of_literal_split component47Node20Box component47Node16Box component47Node19Box
    .k (111/32) (by rfl) (by rfl)
    component47Node16_sound component47Node19_sound

private noncomputable def component47Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (5/32), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component47Node21_sound : Sound component47Node21Box :=
  sound_of_literal_split component47Node21Box component47Node13Box component47Node20Box
    .chi (21/128) (by rfl) (by rfl)
    component47Node13_sound component47Node20_sound

private noncomputable def component47Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (5/32), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component47Node22_sound : Sound component47Node22Box :=
  sound_of_literal_split component47Node22Box component47Node7Box component47Node21Box
    .k (55/16) (by rfl) (by rfl)
    component47Node7_sound component47Node21_sound

private noncomputable def component47Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (45/256), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component47Node23_sound : Sound component47Node23Box :=
  sound_of_literal_split component47Node23Box leaf2158Box leaf2159Box
    .k (217/64) (by rfl) (by rfl)
    leaf2158FlatSound leaf2159FlatSound

private noncomputable def component47Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (11/64), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component47Node24_sound : Sound component47Node24Box :=
  sound_of_literal_split component47Node24Box leaf2157Box component47Node23Box
    .chi (45/256) (by rfl) (by rfl)
    leaf2157FlatSound component47Node23_sound

private noncomputable def component47Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (11/64), chiHi := (45/256) }

set_option maxRecDepth 1000000 in
private theorem component47Node25_sound : Sound component47Node25Box :=
  sound_of_literal_split component47Node25Box leaf2160Box leaf2161Box
    .k (219/64) (by rfl) (by rfl)
    leaf2160FlatSound leaf2161FlatSound

private noncomputable def component47Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (45/256), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component47Node26_sound : Sound component47Node26Box :=
  sound_of_literal_split component47Node26Box leaf2162Box leaf2163Box
    .k (219/64) (by rfl) (by rfl)
    leaf2162FlatSound leaf2163FlatSound

private noncomputable def component47Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (11/64), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component47Node27_sound : Sound component47Node27Box :=
  sound_of_literal_split component47Node27Box component47Node25Box component47Node26Box
    .chi (45/256) (by rfl) (by rfl)
    component47Node25_sound component47Node26_sound

private noncomputable def component47Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (11/64), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component47Node28_sound : Sound component47Node28Box :=
  sound_of_literal_split component47Node28Box component47Node24Box component47Node27Box
    .k (109/32) (by rfl) (by rfl)
    component47Node24_sound component47Node27_sound

private noncomputable def component47Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (23/128), chiHi := (47/256) }

set_option maxRecDepth 1000000 in
private theorem component47Node29_sound : Sound component47Node29Box :=
  sound_of_literal_split component47Node29Box leaf2164Box leaf2165Box
    .k (217/64) (by rfl) (by rfl)
    leaf2164FlatSound leaf2165FlatSound

private noncomputable def component47Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (47/256), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component47Node30_sound : Sound component47Node30Box :=
  sound_of_literal_split component47Node30Box leaf2166Box leaf2167Box
    .k (217/64) (by rfl) (by rfl)
    leaf2166FlatSound leaf2167FlatSound

private noncomputable def component47Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (23/128), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component47Node31_sound : Sound component47Node31Box :=
  sound_of_literal_split component47Node31Box component47Node29Box component47Node30Box
    .chi (47/256) (by rfl) (by rfl)
    component47Node29_sound component47Node30_sound

private noncomputable def component47Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (23/128), chiHi := (47/256) }

set_option maxRecDepth 1000000 in
private theorem component47Node32_sound : Sound component47Node32Box :=
  sound_of_literal_split component47Node32Box leaf2168Box leaf2169Box
    .k (219/64) (by rfl) (by rfl)
    leaf2168FlatSound leaf2169FlatSound

private noncomputable def component47Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (47/256), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component47Node33_sound : Sound component47Node33Box :=
  sound_of_literal_split component47Node33Box leaf2170Box leaf2171Box
    .k (219/64) (by rfl) (by rfl)
    leaf2170FlatSound leaf2171FlatSound

private noncomputable def component47Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (23/128), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component47Node34_sound : Sound component47Node34Box :=
  sound_of_literal_split component47Node34Box component47Node32Box component47Node33Box
    .chi (47/256) (by rfl) (by rfl)
    component47Node32_sound component47Node33_sound

private noncomputable def component47Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (23/128), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component47Node35_sound : Sound component47Node35Box :=
  sound_of_literal_split component47Node35Box component47Node31Box component47Node34Box
    .k (109/32) (by rfl) (by rfl)
    component47Node31_sound component47Node34_sound

private noncomputable def component47Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (11/64), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component47Node36_sound : Sound component47Node36Box :=
  sound_of_literal_split component47Node36Box component47Node28Box component47Node35Box
    .chi (23/128) (by rfl) (by rfl)
    component47Node28_sound component47Node35_sound

private noncomputable def component47Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (11/64), chiHi := (45/256) }

set_option maxRecDepth 1000000 in
private theorem component47Node37_sound : Sound component47Node37Box :=
  sound_of_literal_split component47Node37Box leaf2172Box leaf2173Box
    .k (221/64) (by rfl) (by rfl)
    leaf2172FlatSound leaf2173FlatSound

private noncomputable def component47Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (45/256), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component47Node38_sound : Sound component47Node38Box :=
  sound_of_literal_split component47Node38Box leaf2174Box leaf2175Box
    .k (221/64) (by rfl) (by rfl)
    leaf2174FlatSound leaf2175FlatSound

private noncomputable def component47Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (11/64), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component47Node39_sound : Sound component47Node39Box :=
  sound_of_literal_split component47Node39Box component47Node37Box component47Node38Box
    .chi (45/256) (by rfl) (by rfl)
    component47Node37_sound component47Node38_sound

private noncomputable def component47Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (11/64), chiHi := (45/256) }

set_option maxRecDepth 1000000 in
private theorem component47Node40_sound : Sound component47Node40Box :=
  sound_of_literal_split component47Node40Box leaf2176Box leaf2177Box
    .k (223/64) (by rfl) (by rfl)
    leaf2176FlatSound leaf2177FlatSound

private noncomputable def component47Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (45/256), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component47Node41_sound : Sound component47Node41Box :=
  sound_of_literal_split component47Node41Box leaf2178Box leaf2179Box
    .k (223/64) (by rfl) (by rfl)
    leaf2178FlatSound leaf2179FlatSound

private noncomputable def component47Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (11/64), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component47Node42_sound : Sound component47Node42Box :=
  sound_of_literal_split component47Node42Box component47Node40Box component47Node41Box
    .chi (45/256) (by rfl) (by rfl)
    component47Node40_sound component47Node41_sound

private noncomputable def component47Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (11/64), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component47Node43_sound : Sound component47Node43Box :=
  sound_of_literal_split component47Node43Box component47Node39Box component47Node42Box
    .k (111/32) (by rfl) (by rfl)
    component47Node39_sound component47Node42_sound

private noncomputable def component47Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (23/128), chiHi := (47/256) }

set_option maxRecDepth 1000000 in
private theorem component47Node44_sound : Sound component47Node44Box :=
  sound_of_literal_split component47Node44Box leaf2180Box leaf2181Box
    .k (221/64) (by rfl) (by rfl)
    leaf2180FlatSound leaf2181FlatSound

private noncomputable def component47Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (47/256), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component47Node45_sound : Sound component47Node45Box :=
  sound_of_literal_split component47Node45Box leaf2182Box leaf2183Box
    .k (221/64) (by rfl) (by rfl)
    leaf2182FlatSound leaf2183FlatSound

private noncomputable def component47Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (23/128), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component47Node46_sound : Sound component47Node46Box :=
  sound_of_literal_split component47Node46Box component47Node44Box component47Node45Box
    .chi (47/256) (by rfl) (by rfl)
    component47Node44_sound component47Node45_sound

private noncomputable def component47Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (23/128), chiHi := (47/256) }

set_option maxRecDepth 1000000 in
private theorem component47Node47_sound : Sound component47Node47Box :=
  sound_of_literal_split component47Node47Box leaf2184Box leaf2185Box
    .k (223/64) (by rfl) (by rfl)
    leaf2184FlatSound leaf2185FlatSound

private noncomputable def component47Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (47/256), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component47Node48_sound : Sound component47Node48Box :=
  sound_of_literal_split component47Node48Box leaf2186Box leaf2187Box
    .k (223/64) (by rfl) (by rfl)
    leaf2186FlatSound leaf2187FlatSound

private noncomputable def component47Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (23/128), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component47Node49_sound : Sound component47Node49Box :=
  sound_of_literal_split component47Node49Box component47Node47Box component47Node48Box
    .chi (47/256) (by rfl) (by rfl)
    component47Node47_sound component47Node48_sound

private noncomputable def component47Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (23/128), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component47Node50_sound : Sound component47Node50Box :=
  sound_of_literal_split component47Node50Box component47Node46Box component47Node49Box
    .k (111/32) (by rfl) (by rfl)
    component47Node46_sound component47Node49_sound

private noncomputable def component47Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (11/64), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component47Node51_sound : Sound component47Node51Box :=
  sound_of_literal_split component47Node51Box component47Node43Box component47Node50Box
    .chi (23/128) (by rfl) (by rfl)
    component47Node43_sound component47Node50_sound

private noncomputable def component47Node52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (11/64), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component47Node52_sound : Sound component47Node52Box :=
  sound_of_literal_split component47Node52Box component47Node36Box component47Node51Box
    .k (55/16) (by rfl) (by rfl)
    component47Node36_sound component47Node51_sound

noncomputable def component47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (5/32), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
theorem component47_sound : Sound component47Box :=
  sound_of_literal_split component47Box component47Node22Box component47Node52Box
    .chi (11/64) (by rfl) (by rfl)
    component47Node22_sound component47Node52_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
