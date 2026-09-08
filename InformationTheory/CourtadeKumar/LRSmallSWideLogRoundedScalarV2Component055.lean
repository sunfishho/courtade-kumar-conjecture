import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch6
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch7
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheSKBatch2
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

private noncomputable def leaf2562Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (1/8), chiHi := (33/256) }

private noncomputable def leaf2562Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871211/536870912) }, vSqrt := { lower := (8191/8192), upper := (134217856/134213867) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (780092631/536870912) }, upper := { exponent := 0, mantissa := (12053/8192) } }, logOuter := sk163LogOuterCertificate, logK := sk163LogKCertificate, logChi := chi181LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268431723/268427734) } }, logDArg := sk163LogDArgCertificate }

private noncomputable def leaf2562InnerLog : WideLogData :=
  innerPair447Data

set_option maxRecDepth 1000000 in
private theorem leaf2562LocalValidity :
    LeafFacts leaf2562Box leaf2562Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2562Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217856/134213867) }) = true
      norm_num [leaf2562Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2562CertificateValid :
    WideCertificateValid leaf2562Box leaf2562Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk163ValidityFacts chi181ValidityFacts
    leaf2562LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2562CoverageChecked :
    coverageCheck (innerAD leaf2562Box) leaf2562InnerLog = true := by
  rfl'

private theorem leaf2562InnerLogValid :
    leaf2562InnerLog.Valid 8 (innerAD leaf2562Box) :=
  wideLogDataValid_of_cachedCheck endpoint161PositiveFacts
    endpoint194PositiveFacts.valid leaf2562CoverageChecked

private noncomputable def leaf2562InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814665/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2562InputLogOnePlusV_eq :
    leaf2562InputLogOnePlusV = outerEnclosure 24
      (leaf2562Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2562RoundedFacts : LeafRoundedFacts 8
    leaf2562Certificate.logOnePlusV leaf2562InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2562InputLogOnePlusV_eq }

private noncomputable def leaf2562Inputs : Inputs :=
  inputsOfCaches globalInput sk163RoundedInputs
    chi181InputQChi innerPair447Input
    leaf2562InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2562LowerChecked :
    lowerCheck 24 leaf2562Box leaf2562Inputs = true := by
  rfl'

private theorem leaf2562CoversExact : CoversExact 8
    leaf2562Box leaf2562Certificate leaf2562InnerLog leaf2562Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk163RoundedFacts chi181RoundedFacts
    innerPair447RoundedFacts leaf2562RoundedFacts (by rfl)

private theorem leaf2562FlatSound : Sound leaf2562Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2562CertificateValid
    leaf2562InnerLogValid leaf2562CoversExact leaf2562LowerChecked

private noncomputable def leaf2563Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (33/256), chiHi := (17/128) }

private noncomputable def leaf2563Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871213/536870912) }, vSqrt := { lower := (8191/8192), upper := (13743698739/13743488000) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (787694341/536870912) }, upper := { exponent := 0, mantissa := (6085/4096) } }, logOuter := sk163LogOuterCertificate, logK := sk163LogKCertificate, logChi := chi182LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (27487186739/27486976000) } }, logDArg := sk163LogDArgCertificate }

private noncomputable def leaf2563InnerLog : WideLogData :=
  innerPair474Data

set_option maxRecDepth 1000000 in
private theorem leaf2563LocalValidity :
    LeafFacts leaf2563Box leaf2563Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2563Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (13743698739/13743488000) }) = true
      norm_num [leaf2563Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2563CertificateValid :
    WideCertificateValid leaf2563Box leaf2563Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk163ValidityFacts chi182ValidityFacts
    leaf2563LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2563CoverageChecked :
    coverageCheck (innerAD leaf2563Box) leaf2563InnerLog = true := by
  rfl'

private theorem leaf2563InnerLogValid :
    leaf2563InnerLog.Valid 8 (innerAD leaf2563Box) :=
  wideLogDataValid_of_cachedCheck endpoint195PositiveFacts
    endpoint196PositiveFacts.valid leaf2563CoverageChecked

private noncomputable def leaf2563InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629209/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2563InputLogOnePlusV_eq :
    leaf2563InputLogOnePlusV = outerEnclosure 24
      (leaf2563Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2563RoundedFacts : LeafRoundedFacts 8
    leaf2563Certificate.logOnePlusV leaf2563InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2563InputLogOnePlusV_eq }

private noncomputable def leaf2563Inputs : Inputs :=
  inputsOfCaches globalInput sk163RoundedInputs
    chi182InputQChi innerPair474Input
    leaf2563InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2563LowerChecked :
    lowerCheck 24 leaf2563Box leaf2563Inputs = true := by
  rfl'

private theorem leaf2563CoversExact : CoversExact 8
    leaf2563Box leaf2563Certificate leaf2563InnerLog leaf2563Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk163RoundedFacts chi182RoundedFacts
    innerPair474RoundedFacts leaf2563RoundedFacts (by rfl)

private theorem leaf2563FlatSound : Sound leaf2563Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2563CertificateValid
    leaf2563InnerLogValid leaf2563CoversExact leaf2563LowerChecked

private noncomputable def leaf2564Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (1/8), chiHi := (33/256) }

private noncomputable def leaf2564Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871213/536870912) }, vSqrt := { lower := (8191/8192), upper := (67108928/67106917) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (782189653/536870912) }, upper := { exponent := 0, mantissa := (6043/4096) } }, logOuter := sk164LogOuterCertificate, logK := sk164LogKCertificate, logChi := chi181LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134215845/134213834) } }, logDArg := sk164LogDArgCertificate }

private noncomputable def leaf2564InnerLog : WideLogData :=
  innerPair150Data

set_option maxRecDepth 1000000 in
private theorem leaf2564LocalValidity :
    LeafFacts leaf2564Box leaf2564Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2564Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108928/67106917) }) = true
      norm_num [leaf2564Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2564CertificateValid :
    WideCertificateValid leaf2564Box leaf2564Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk164ValidityFacts chi181ValidityFacts
    leaf2564LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2564CoverageChecked :
    coverageCheck (innerAD leaf2564Box) leaf2564InnerLog = true := by
  rfl'

private theorem leaf2564InnerLogValid :
    leaf2564InnerLog.Valid 8 (innerAD leaf2564Box) :=
  wideLogDataValid_of_cachedCheck endpoint41PositiveFacts
    endpoint190PositiveFacts.valid leaf2564CoverageChecked

private noncomputable def leaf2564InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907333/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2564InputLogOnePlusV_eq :
    leaf2564InputLogOnePlusV = outerEnclosure 24
      (leaf2564Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2564RoundedFacts : LeafRoundedFacts 8
    leaf2564Certificate.logOnePlusV leaf2564InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2564InputLogOnePlusV_eq }

private noncomputable def leaf2564Inputs : Inputs :=
  inputsOfCaches globalInput sk164RoundedInputs
    chi181InputQChi innerPair150Input
    leaf2564InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2564LowerChecked :
    lowerCheck 24 leaf2564Box leaf2564Inputs = true := by
  rfl'

private theorem leaf2564CoversExact : CoversExact 8
    leaf2564Box leaf2564Certificate leaf2564InnerLog leaf2564Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk164RoundedFacts chi181RoundedFacts
    innerPair150RoundedFacts leaf2564RoundedFacts (by rfl)

private theorem leaf2564FlatSound : Sound leaf2564Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2564CertificateValid
    leaf2564InnerLogValid leaf2564CoversExact leaf2564LowerChecked

private noncomputable def leaf2565Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (33/256), chiHi := (67/512) }

private noncomputable def leaf2565Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742193/1073741824) }, vSqrt := { lower := (8191/8192), upper := (134217856/134213775) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1579746793/1073741824) }, upper := { exponent := 0, mantissa := (12145/8192) } }, logOuter := sk164LogOuterCertificate, logK := sk164LogKCertificate, logChi := chi203LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268431631/268427550) } }, logDArg := sk164LogDArgCertificate }

private noncomputable def leaf2565InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf2565LocalValidity :
    LeafFacts leaf2565Box leaf2565Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2565Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217856/134213775) }) = true
      norm_num [leaf2565Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2565CertificateValid :
    WideCertificateValid leaf2565Box leaf2565Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk164ValidityFacts chi203ValidityFacts
    leaf2565LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2565CoverageChecked :
    coverageCheck (innerAD leaf2565Box) leaf2565InnerLog = true := by
  rfl'

private theorem leaf2565InnerLogValid :
    leaf2565InnerLog.Valid 8 (innerAD leaf2565Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf2565CoverageChecked

private noncomputable def leaf2565InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453667/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf2565InputLogOnePlusV_eq :
    leaf2565InputLogOnePlusV = outerEnclosure 24
      (leaf2565Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2565RoundedFacts : LeafRoundedFacts 8
    leaf2565Certificate.logOnePlusV leaf2565InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2565InputLogOnePlusV_eq }

private noncomputable def leaf2565Inputs : Inputs :=
  inputsOfCaches globalInput sk164RoundedInputs
    chi203InputQChi innerPair34Input
    leaf2565InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2565LowerChecked :
    lowerCheck 24 leaf2565Box leaf2565Inputs = true := by
  rfl'

private theorem leaf2565CoversExact : CoversExact 8
    leaf2565Box leaf2565Certificate leaf2565InnerLog leaf2565Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk164RoundedFacts chi203RoundedFacts
    innerPair34RoundedFacts leaf2565RoundedFacts (by rfl)

private theorem leaf2565FlatSound : Sound leaf2565Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2565CertificateValid
    leaf2565InnerLogValid leaf2565CoversExact leaf2565LowerChecked

private noncomputable def leaf2566Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (67/512), chiHi := (17/128) }

private noncomputable def leaf2566Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742195/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68718493695/68717422592) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1587414035/1073741824) }, upper := { exponent := 0, mantissa := (3051/2048) } }, logOuter := sk164LogOuterCertificate, logK := sk164LogKCertificate, logChi := chi204LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137435916287/137434845184) } }, logDArg := sk164LogDArgCertificate }

private noncomputable def leaf2566InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf2566LocalValidity :
    LeafFacts leaf2566Box leaf2566Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2566Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68718493695/68717422592) }) = true
      norm_num [leaf2566Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2566CertificateValid :
    WideCertificateValid leaf2566Box leaf2566Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk164ValidityFacts chi204ValidityFacts
    leaf2566LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2566CoverageChecked :
    coverageCheck (innerAD leaf2566Box) leaf2566InnerLog = true := by
  rfl'

private theorem leaf2566InnerLogValid :
    leaf2566InnerLog.Valid 8 (innerAD leaf2566Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf2566CoverageChecked

private noncomputable def leaf2566InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629211/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2566InputLogOnePlusV_eq :
    leaf2566InputLogOnePlusV = outerEnclosure 24
      (leaf2566Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2566RoundedFacts : LeafRoundedFacts 8
    leaf2566Certificate.logOnePlusV leaf2566InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2566InputLogOnePlusV_eq }

private noncomputable def leaf2566Inputs : Inputs :=
  inputsOfCaches globalInput sk164RoundedInputs
    chi204InputQChi innerPair34Input
    leaf2566InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2566LowerChecked :
    lowerCheck 24 leaf2566Box leaf2566Inputs = true := by
  rfl'

private theorem leaf2566CoversExact : CoversExact 8
    leaf2566Box leaf2566Certificate leaf2566InnerLog leaf2566Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk164RoundedFacts chi204RoundedFacts
    innerPair34RoundedFacts leaf2566RoundedFacts (by rfl)

private theorem leaf2566FlatSound : Sound leaf2566Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2566CertificateValid
    leaf2566InnerLogValid leaf2566CoversExact leaf2566LowerChecked

private noncomputable def leaf2567Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (233/64), chiLo := (17/128), chiHi := (35/256) }

private noncomputable def leaf2567Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742359/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45811592704) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1590624939/1073741824) }, upper := { exponent := 0, mantissa := (24539/16384) } }, logOuter := sk217LogOuterCertificate, logK := sk217LogKCertificate, logChi := chi179LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623899989/91623185408) } }, logDArg := sk217LogDArgCertificate }

private noncomputable def leaf2567InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf2567LocalValidity :
    LeafFacts leaf2567Box leaf2567Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2567Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45811592704) }) = true
      norm_num [leaf2567Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2567CertificateValid :
    WideCertificateValid leaf2567Box leaf2567Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk217ValidityFacts chi179ValidityFacts
    leaf2567LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2567CoverageChecked :
    coverageCheck (innerAD leaf2567Box) leaf2567InnerLog = true := by
  rfl'

private theorem leaf2567InnerLogValid :
    leaf2567InnerLog.Valid 8 (innerAD leaf2567Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf2567CoverageChecked

private noncomputable def leaf2567InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907303/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2567InputLogOnePlusV_eq :
    leaf2567InputLogOnePlusV = outerEnclosure 24
      (leaf2567Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2567RoundedFacts : LeafRoundedFacts 8
    leaf2567Certificate.logOnePlusV leaf2567InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2567InputLogOnePlusV_eq }

private noncomputable def leaf2567Inputs : Inputs :=
  inputsOfCaches globalInput sk217RoundedInputs
    chi179InputQChi innerPair34Input
    leaf2567InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2567LowerChecked :
    lowerCheck 24 leaf2567Box leaf2567Inputs = true := by
  rfl'

private theorem leaf2567CoversExact : CoversExact 8
    leaf2567Box leaf2567Certificate leaf2567InnerLog leaf2567Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk217RoundedFacts chi179RoundedFacts
    innerPair34RoundedFacts leaf2567RoundedFacts (by rfl)

private theorem leaf2567FlatSound : Sound leaf2567Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2567CertificateValid
    leaf2567InnerLogValid leaf2567CoversExact leaf2567LowerChecked

private noncomputable def leaf2568Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (233/64), kHi := (117/32), chiLo := (17/128), chiHi := (35/256) }

private noncomputable def leaf2568Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742361/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434760192) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1592853025/1073741824) }, upper := { exponent := 0, mantissa := (12287/8192) } }, logOuter := sk218LogOuterCertificate, logK := sk218LogKCertificate, logChi := chi179LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871682047/274869520384) } }, logDArg := sk218LogDArgCertificate }

private noncomputable def leaf2568InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf2568LocalValidity :
    LeafFacts leaf2568Box leaf2568Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2568Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434760192) }) = true
      norm_num [leaf2568Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2568CertificateValid :
    WideCertificateValid leaf2568Box leaf2568Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk218ValidityFacts chi179ValidityFacts
    leaf2568LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2568CoverageChecked :
    coverageCheck (innerAD leaf2568Box) leaf2568InnerLog = true := by
  rfl'

private theorem leaf2568InnerLogValid :
    leaf2568InnerLog.Valid 8 (innerAD leaf2568Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf2568CoverageChecked

private noncomputable def leaf2568InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629213/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2568InputLogOnePlusV_eq :
    leaf2568InputLogOnePlusV = outerEnclosure 24
      (leaf2568Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2568RoundedFacts : LeafRoundedFacts 8
    leaf2568Certificate.logOnePlusV leaf2568InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2568InputLogOnePlusV_eq }

private noncomputable def leaf2568Inputs : Inputs :=
  inputsOfCaches globalInput sk218RoundedInputs
    chi179InputQChi innerPair34Input
    leaf2568InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2568LowerChecked :
    lowerCheck 24 leaf2568Box leaf2568Inputs = true := by
  rfl'

private theorem leaf2568CoversExact : CoversExact 8
    leaf2568Box leaf2568Certificate leaf2568InnerLog leaf2568Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk218RoundedFacts chi179RoundedFacts
    innerPair34RoundedFacts leaf2568RoundedFacts (by rfl)

private theorem leaf2568FlatSound : Sound leaf2568Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2568CertificateValid
    leaf2568InnerLogValid leaf2568CoversExact leaf2568LowerChecked

private noncomputable def leaf2569Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (233/64), chiLo := (35/256), chiHi := (9/64) }

private noncomputable def leaf2569Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742361/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434658816) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1605828361/1073741824) }, upper := { exponent := 0, mantissa := (6193/4096) } }, logOuter := sk217LogOuterCertificate, logK := sk217LogKCertificate, logChi := chi180LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871580671/274869317632) } }, logDArg := sk217LogDArgCertificate }

private noncomputable def leaf2569InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf2569LocalValidity :
    LeafFacts leaf2569Box leaf2569Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2569Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434658816) }) = true
      norm_num [leaf2569Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2569CertificateValid :
    WideCertificateValid leaf2569Box leaf2569Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk217ValidityFacts chi180ValidityFacts
    leaf2569LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2569CoverageChecked :
    coverageCheck (innerAD leaf2569Box) leaf2569InnerLog = true := by
  rfl'

private theorem leaf2569InnerLogValid :
    leaf2569InnerLog.Valid 8 (innerAD leaf2569Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf2569CoverageChecked

private noncomputable def leaf2569InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629219/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2569InputLogOnePlusV_eq :
    leaf2569InputLogOnePlusV = outerEnclosure 24
      (leaf2569Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2569RoundedFacts : LeafRoundedFacts 8
    leaf2569Certificate.logOnePlusV leaf2569InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2569InputLogOnePlusV_eq }

private noncomputable def leaf2569Inputs : Inputs :=
  inputsOfCaches globalInput sk217RoundedInputs
    chi180InputQChi innerPair35Input
    leaf2569InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2569LowerChecked :
    lowerCheck 24 leaf2569Box leaf2569Inputs = true := by
  rfl'

private theorem leaf2569CoversExact : CoversExact 8
    leaf2569Box leaf2569Certificate leaf2569InnerLog leaf2569Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk217RoundedFacts chi180RoundedFacts
    innerPair35RoundedFacts leaf2569RoundedFacts (by rfl)

private theorem leaf2569FlatSound : Sound leaf2569Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2569CertificateValid
    leaf2569InnerLogValid leaf2569CoversExact leaf2569LowerChecked

private noncomputable def leaf2570Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (233/64), kHi := (117/32), chiLo := (35/256), chiHi := (9/64) }

private noncomputable def leaf2570Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742363/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434640384) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1608121979/1073741824) }, upper := { exponent := 0, mantissa := (3101/2048) } }, logOuter := sk218LogOuterCertificate, logK := sk218LogKCertificate, logChi := chi180LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871562239/274869280768) } }, logDArg := sk218LogDArgCertificate }

private noncomputable def leaf2570InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf2570LocalValidity :
    LeafFacts leaf2570Box leaf2570Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2570Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434640384) }) = true
      norm_num [leaf2570Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2570CertificateValid :
    WideCertificateValid leaf2570Box leaf2570Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk218ValidityFacts chi180ValidityFacts
    leaf2570LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2570CoverageChecked :
    coverageCheck (innerAD leaf2570Box) leaf2570InnerLog = true := by
  rfl'

private theorem leaf2570InnerLogValid :
    leaf2570InnerLog.Valid 8 (innerAD leaf2570Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf2570CoverageChecked

private noncomputable def leaf2570InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907305/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2570InputLogOnePlusV_eq :
    leaf2570InputLogOnePlusV = outerEnclosure 24
      (leaf2570Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2570RoundedFacts : LeafRoundedFacts 8
    leaf2570Certificate.logOnePlusV leaf2570InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2570InputLogOnePlusV_eq }

private noncomputable def leaf2570Inputs : Inputs :=
  inputsOfCaches globalInput sk218RoundedInputs
    chi180InputQChi innerPair35Input
    leaf2570InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2570LowerChecked :
    lowerCheck 24 leaf2570Box leaf2570Inputs = true := by
  rfl'

private theorem leaf2570CoversExact : CoversExact 8
    leaf2570Box leaf2570Certificate leaf2570InnerLog leaf2570Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk218RoundedFacts chi180RoundedFacts
    innerPair35RoundedFacts leaf2570RoundedFacts (by rfl)

private theorem leaf2570FlatSound : Sound leaf2570Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2570CertificateValid
    leaf2570InnerLogValid leaf2570CoversExact leaf2570LowerChecked

private noncomputable def leaf2571Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (235/64), chiLo := (17/128), chiHi := (35/256) }

private noncomputable def leaf2571Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742363/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434742272) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1595081111/1073741824) }, upper := { exponent := 0, mantissa := (24609/16384) } }, logOuter := sk219LogOuterCertificate, logK := sk219LogKCertificate, logChi := chi179LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871664127/274869484544) } }, logDArg := sk219LogDArgCertificate }

private noncomputable def leaf2571InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf2571LocalValidity :
    LeafFacts leaf2571Box leaf2571Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2571Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434742272) }) = true
      norm_num [leaf2571Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2571CertificateValid :
    WideCertificateValid leaf2571Box leaf2571Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk219ValidityFacts chi179ValidityFacts
    leaf2571LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2571CoverageChecked :
    coverageCheck (innerAD leaf2571Box) leaf2571InnerLog = true := by
  rfl'

private theorem leaf2571InnerLogValid :
    leaf2571InnerLog.Valid 8 (innerAD leaf2571Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf2571CoverageChecked

private noncomputable def leaf2571InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814607/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2571InputLogOnePlusV_eq :
    leaf2571InputLogOnePlusV = outerEnclosure 24
      (leaf2571Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2571RoundedFacts : LeafRoundedFacts 8
    leaf2571Certificate.logOnePlusV leaf2571InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2571InputLogOnePlusV_eq }

private noncomputable def leaf2571Inputs : Inputs :=
  inputsOfCaches globalInput sk219RoundedInputs
    chi179InputQChi innerPair35Input
    leaf2571InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2571LowerChecked :
    lowerCheck 24 leaf2571Box leaf2571Inputs = true := by
  rfl'

private theorem leaf2571CoversExact : CoversExact 8
    leaf2571Box leaf2571Certificate leaf2571InnerLog leaf2571Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk219RoundedFacts chi179RoundedFacts
    innerPair35RoundedFacts leaf2571RoundedFacts (by rfl)

private theorem leaf2571FlatSound : Sound leaf2571Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2571CertificateValid
    leaf2571InnerLogValid leaf2571CoversExact leaf2571LowerChecked

private noncomputable def leaf2572Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (235/64), kHi := (59/16), chiLo := (17/128), chiHi := (35/256) }

private noncomputable def leaf2572Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742365/1073741824) }, vSqrt := { lower := (8191/8192), upper := (5090256365/5090174976) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1597309197/1073741824) }, upper := { exponent := 0, mantissa := (6161/4096) } }, logOuter := sk220LogOuterCertificate, logK := sk220LogKCertificate, logChi := chi179LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (10180431341/10180349952) } }, logDArg := sk220LogDArgCertificate }

private noncomputable def leaf2572InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf2572LocalValidity :
    LeafFacts leaf2572Box leaf2572Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2572Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5090256365/5090174976) }) = true
      norm_num [leaf2572Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2572CertificateValid :
    WideCertificateValid leaf2572Box leaf2572Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk220ValidityFacts chi179ValidityFacts
    leaf2572LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2572CoverageChecked :
    coverageCheck (innerAD leaf2572Box) leaf2572InnerLog = true := by
  rfl'

private theorem leaf2572InnerLogValid :
    leaf2572InnerLog.Valid 8 (innerAD leaf2572Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf2572CoverageChecked

private noncomputable def leaf2572InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629215/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2572InputLogOnePlusV_eq :
    leaf2572InputLogOnePlusV = outerEnclosure 24
      (leaf2572Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2572RoundedFacts : LeafRoundedFacts 8
    leaf2572Certificate.logOnePlusV leaf2572InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2572InputLogOnePlusV_eq }

private noncomputable def leaf2572Inputs : Inputs :=
  inputsOfCaches globalInput sk220RoundedInputs
    chi179InputQChi innerPair35Input
    leaf2572InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2572LowerChecked :
    lowerCheck 24 leaf2572Box leaf2572Inputs = true := by
  rfl'

private theorem leaf2572CoversExact : CoversExact 8
    leaf2572Box leaf2572Certificate leaf2572InnerLog leaf2572Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk220RoundedFacts chi179RoundedFacts
    innerPair35RoundedFacts leaf2572RoundedFacts (by rfl)

private theorem leaf2572FlatSound : Sound leaf2572Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2572CertificateValid
    leaf2572InnerLogValid leaf2572CoversExact leaf2572LowerChecked

private noncomputable def leaf2573Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (235/64), chiLo := (35/256), chiHi := (9/64) }

private noncomputable def leaf2573Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742365/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434621952) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1610415597/1073741824) }, upper := { exponent := 0, mantissa := (6211/4096) } }, logOuter := sk219LogOuterCertificate, logK := sk219LogKCertificate, logChi := chi180LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871543807/274869243904) } }, logDArg := sk219LogDArgCertificate }

private noncomputable def leaf2573InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf2573LocalValidity :
    LeafFacts leaf2573Box leaf2573Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2573Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434621952) }) = true
      norm_num [leaf2573Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2573CertificateValid :
    WideCertificateValid leaf2573Box leaf2573Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk219ValidityFacts chi180ValidityFacts
    leaf2573LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2573CoverageChecked :
    coverageCheck (innerAD leaf2573Box) leaf2573InnerLog = true := by
  rfl'

private theorem leaf2573InnerLogValid :
    leaf2573InnerLog.Valid 8 (innerAD leaf2573Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf2573CoverageChecked

private noncomputable def leaf2573InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629221/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2573InputLogOnePlusV_eq :
    leaf2573InputLogOnePlusV = outerEnclosure 24
      (leaf2573Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2573RoundedFacts : LeafRoundedFacts 8
    leaf2573Certificate.logOnePlusV leaf2573InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2573InputLogOnePlusV_eq }

private noncomputable def leaf2573Inputs : Inputs :=
  inputsOfCaches globalInput sk219RoundedInputs
    chi180InputQChi innerPair35Input
    leaf2573InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2573LowerChecked :
    lowerCheck 24 leaf2573Box leaf2573Inputs = true := by
  rfl'

private theorem leaf2573CoversExact : CoversExact 8
    leaf2573Box leaf2573Certificate leaf2573InnerLog leaf2573Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk219RoundedFacts chi180RoundedFacts
    innerPair35RoundedFacts leaf2573RoundedFacts (by rfl)

private theorem leaf2573FlatSound : Sound leaf2573Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2573CertificateValid
    leaf2573InnerLogValid leaf2573CoversExact leaf2573LowerChecked

private noncomputable def leaf2574Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (235/64), kHi := (59/16), chiLo := (35/256), chiHi := (9/64) }

private noncomputable def leaf2574Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742367/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486920704) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1612709215/1073741824) }, upper := { exponent := 0, mantissa := (1555/1024) } }, logOuter := sk220LogOuterCertificate, logK := sk220LogKCertificate, logChi := chi180LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54974305075/54973841408) } }, logDArg := sk220LogDArgCertificate }

private noncomputable def leaf2574InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2574LocalValidity :
    LeafFacts leaf2574Box leaf2574Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2574Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486920704) }) = true
      norm_num [leaf2574Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2574CertificateValid :
    WideCertificateValid leaf2574Box leaf2574Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk220ValidityFacts chi180ValidityFacts
    leaf2574LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2574CoverageChecked :
    coverageCheck (innerAD leaf2574Box) leaf2574InnerLog = true := by
  rfl'

private theorem leaf2574InnerLogValid :
    leaf2574InnerLog.Valid 8 (innerAD leaf2574Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2574CoverageChecked

private noncomputable def leaf2574InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814611/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2574InputLogOnePlusV_eq :
    leaf2574InputLogOnePlusV = outerEnclosure 24
      (leaf2574Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2574RoundedFacts : LeafRoundedFacts 8
    leaf2574Certificate.logOnePlusV leaf2574InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2574InputLogOnePlusV_eq }

private noncomputable def leaf2574Inputs : Inputs :=
  inputsOfCaches globalInput sk220RoundedInputs
    chi180InputQChi innerPair40Input
    leaf2574InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2574LowerChecked :
    lowerCheck 24 leaf2574Box leaf2574Inputs = true := by
  rfl'

private theorem leaf2574CoversExact : CoversExact 8
    leaf2574Box leaf2574Certificate leaf2574InnerLog leaf2574Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk220RoundedFacts chi180RoundedFacts
    innerPair40RoundedFacts leaf2574RoundedFacts (by rfl)

private theorem leaf2574FlatSound : Sound leaf2574Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2574CertificateValid
    leaf2574InnerLogValid leaf2574CoversExact leaf2574LowerChecked

private noncomputable def leaf2575Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (1/8), chiHi := (65/512) }

private noncomputable def leaf2575Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742191/1073741824) }, vSqrt := { lower := (8191/8192), upper := (268435712/268427721) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1568606355/1073741824) }, upper := { exponent := 0, mantissa := (24119/16384) } }, logOuter := sk165LogOuterCertificate, logK := sk165LogKCertificate, logChi := chi205LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (536863433/536855442) } }, logDArg := sk165LogDArgCertificate }

private noncomputable def leaf2575InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf2575LocalValidity :
    LeafFacts leaf2575Box leaf2575Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2575Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (268435712/268427721) }) = true
      norm_num [leaf2575Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2575CertificateValid :
    WideCertificateValid leaf2575Box leaf2575Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk165ValidityFacts chi205ValidityFacts
    leaf2575LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2575CoverageChecked :
    coverageCheck (innerAD leaf2575Box) leaf2575InnerLog = true := by
  rfl'

private theorem leaf2575InnerLogValid :
    leaf2575InnerLog.Valid 8 (innerAD leaf2575Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf2575CoverageChecked

private noncomputable def leaf2575InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814665/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2575InputLogOnePlusV_eq :
    leaf2575InputLogOnePlusV = outerEnclosure 24
      (leaf2575Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2575RoundedFacts : LeafRoundedFacts 8
    leaf2575Certificate.logOnePlusV leaf2575InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2575InputLogOnePlusV_eq }

private noncomputable def leaf2575Inputs : Inputs :=
  inputsOfCaches globalInput sk165RoundedInputs
    chi205InputQChi innerPair34Input
    leaf2575InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2575LowerChecked :
    lowerCheck 24 leaf2575Box leaf2575Inputs = true := by
  rfl'

private theorem leaf2575CoversExact : CoversExact 8
    leaf2575Box leaf2575Certificate leaf2575InnerLog leaf2575Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk165RoundedFacts chi205RoundedFacts
    innerPair34RoundedFacts leaf2575RoundedFacts (by rfl)

private theorem leaf2575FlatSound : Sound leaf2575Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2575CertificateValid
    leaf2575InnerLogValid leaf2575CoversExact leaf2575LowerChecked

private noncomputable def leaf2576Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (65/512), chiHi := (33/256) }

private noncomputable def leaf2576Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742193/1073741824) }, vSqrt := { lower := (8191/8192), upper := (134217856/134213801) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1576339129/1073741824) }, upper := { exponent := 0, mantissa := (12119/8192) } }, logOuter := sk165LogOuterCertificate, logK := sk165LogKCertificate, logChi := chi206LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268431657/268427602) } }, logDArg := sk165LogDArgCertificate }

private noncomputable def leaf2576InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf2576LocalValidity :
    LeafFacts leaf2576Box leaf2576Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2576Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217856/134213801) }) = true
      norm_num [leaf2576Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2576CertificateValid :
    WideCertificateValid leaf2576Box leaf2576Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk165ValidityFacts chi206ValidityFacts
    leaf2576LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2576CoverageChecked :
    coverageCheck (innerAD leaf2576Box) leaf2576InnerLog = true := by
  rfl'

private theorem leaf2576InnerLogValid :
    leaf2576InnerLog.Valid 8 (innerAD leaf2576Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf2576CoverageChecked

private noncomputable def leaf2576InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814667/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2576InputLogOnePlusV_eq :
    leaf2576InputLogOnePlusV = outerEnclosure 24
      (leaf2576Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2576RoundedFacts : LeafRoundedFacts 8
    leaf2576Certificate.logOnePlusV leaf2576InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2576InputLogOnePlusV_eq }

private noncomputable def leaf2576Inputs : Inputs :=
  inputsOfCaches globalInput sk165RoundedInputs
    chi206InputQChi innerPair34Input
    leaf2576InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2576LowerChecked :
    lowerCheck 24 leaf2576Box leaf2576Inputs = true := by
  rfl'

private theorem leaf2576CoversExact : CoversExact 8
    leaf2576Box leaf2576Certificate leaf2576InnerLog leaf2576Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk165RoundedFacts chi206RoundedFacts
    innerPair34RoundedFacts leaf2576RoundedFacts (by rfl)

private theorem leaf2576FlatSound : Sound leaf2576Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2576CertificateValid
    leaf2576InnerLogValid leaf2576CoversExact leaf2576LowerChecked

private noncomputable def leaf2577Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (33/256), chiHi := (67/512) }

private noncomputable def leaf2577Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742195/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68718493695/68717435648) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1584071903/1073741824) }, upper := { exponent := 0, mantissa := (24357/16384) } }, logOuter := sk165LogOuterCertificate, logK := sk165LogKCertificate, logChi := chi203LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137435929343/137434871296) } }, logDArg := sk165LogDArgCertificate }

private noncomputable def leaf2577InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf2577LocalValidity :
    LeafFacts leaf2577Box leaf2577Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2577Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68718493695/68717435648) }) = true
      norm_num [leaf2577Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2577CertificateValid :
    WideCertificateValid leaf2577Box leaf2577Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk165ValidityFacts chi203ValidityFacts
    leaf2577LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2577CoverageChecked :
    coverageCheck (innerAD leaf2577Box) leaf2577InnerLog = true := by
  rfl'

private theorem leaf2577InnerLogValid :
    leaf2577InnerLog.Valid 8 (innerAD leaf2577Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf2577CoverageChecked

private noncomputable def leaf2577InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814605/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2577InputLogOnePlusV_eq :
    leaf2577InputLogOnePlusV = outerEnclosure 24
      (leaf2577Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2577RoundedFacts : LeafRoundedFacts 8
    leaf2577Certificate.logOnePlusV leaf2577InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2577InputLogOnePlusV_eq }

private noncomputable def leaf2577Inputs : Inputs :=
  inputsOfCaches globalInput sk165RoundedInputs
    chi203InputQChi innerPair34Input
    leaf2577InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2577LowerChecked :
    lowerCheck 24 leaf2577Box leaf2577Inputs = true := by
  rfl'

private theorem leaf2577CoversExact : CoversExact 8
    leaf2577Box leaf2577Certificate leaf2577InnerLog leaf2577Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk165RoundedFacts chi203RoundedFacts
    innerPair34RoundedFacts leaf2577RoundedFacts (by rfl)

private theorem leaf2577FlatSound : Sound leaf2577Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2577CertificateValid
    leaf2577InnerLogValid leaf2577CoversExact leaf2577LowerChecked

private noncomputable def leaf2578Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (67/512), chiHi := (17/128) }

private noncomputable def leaf2578Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742197/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22906164565/22905801728) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1591804677/1073741824) }, upper := { exponent := 0, mantissa := (6119/4096) } }, logOuter := sk165LogOuterCertificate, logK := sk165LogKCertificate, logChi := chi204LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45811966293/45811603456) } }, logDArg := sk165LogDArgCertificate }

private noncomputable def leaf2578InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf2578LocalValidity :
    LeafFacts leaf2578Box leaf2578Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2578Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22906164565/22905801728) }) = true
      norm_num [leaf2578Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2578CertificateValid :
    WideCertificateValid leaf2578Box leaf2578Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk165ValidityFacts chi204ValidityFacts
    leaf2578LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2578CoverageChecked :
    coverageCheck (innerAD leaf2578Box) leaf2578InnerLog = true := by
  rfl'

private theorem leaf2578InnerLogValid :
    leaf2578InnerLog.Valid 8 (innerAD leaf2578Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf2578CoverageChecked

private noncomputable def leaf2578InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814607/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2578InputLogOnePlusV_eq :
    leaf2578InputLogOnePlusV = outerEnclosure 24
      (leaf2578Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2578RoundedFacts : LeafRoundedFacts 8
    leaf2578Certificate.logOnePlusV leaf2578InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2578InputLogOnePlusV_eq }

private noncomputable def leaf2578Inputs : Inputs :=
  inputsOfCaches globalInput sk165RoundedInputs
    chi204InputQChi innerPair34Input
    leaf2578InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2578LowerChecked :
    lowerCheck 24 leaf2578Box leaf2578Inputs = true := by
  rfl'

private theorem leaf2578CoversExact : CoversExact 8
    leaf2578Box leaf2578Certificate leaf2578InnerLog leaf2578Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk165RoundedFacts chi204RoundedFacts
    innerPair34RoundedFacts leaf2578RoundedFacts (by rfl)

private theorem leaf2578FlatSound : Sound leaf2578Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2578CertificateValid
    leaf2578InnerLogValid leaf2578CoversExact leaf2578LowerChecked

private noncomputable def leaf2579Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (1/8), chiHi := (65/512) }

private noncomputable def leaf2579Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742193/1073741824) }, vSqrt := { lower := (8191/8192), upper := (33554464/33553457) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1572800401/1073741824) }, upper := { exponent := 0, mantissa := (3023/2048) } }, logOuter := sk166LogOuterCertificate, logK := sk166LogKCertificate, logChi := chi205LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (67107921/67106914) } }, logDArg := sk166LogDArgCertificate }

private noncomputable def leaf2579InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf2579LocalValidity :
    LeafFacts leaf2579Box leaf2579Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2579Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (33554464/33553457) }) = true
      norm_num [leaf2579Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2579CertificateValid :
    WideCertificateValid leaf2579Box leaf2579Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk166ValidityFacts chi205ValidityFacts
    leaf2579LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2579CoverageChecked :
    coverageCheck (innerAD leaf2579Box) leaf2579InnerLog = true := by
  rfl'

private theorem leaf2579InnerLogValid :
    leaf2579InnerLog.Valid 8 (innerAD leaf2579Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf2579CoverageChecked

private noncomputable def leaf2579InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907333/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2579InputLogOnePlusV_eq :
    leaf2579InputLogOnePlusV = outerEnclosure 24
      (leaf2579Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2579RoundedFacts : LeafRoundedFacts 8
    leaf2579Certificate.logOnePlusV leaf2579InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2579InputLogOnePlusV_eq }

private noncomputable def leaf2579Inputs : Inputs :=
  inputsOfCaches globalInput sk166RoundedInputs
    chi205InputQChi innerPair34Input
    leaf2579InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2579LowerChecked :
    lowerCheck 24 leaf2579Box leaf2579Inputs = true := by
  rfl'

private theorem leaf2579CoversExact : CoversExact 8
    leaf2579Box leaf2579Certificate leaf2579InnerLog leaf2579Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk166RoundedFacts chi205RoundedFacts
    innerPair34RoundedFacts leaf2579RoundedFacts (by rfl)

private theorem leaf2579FlatSound : Sound leaf2579Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2579CertificateValid
    leaf2579InnerLogValid leaf2579CoversExact leaf2579LowerChecked

private noncomputable def leaf2580Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (65/512), chiHi := (33/256) }

private noncomputable def leaf2580Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742195/1073741824) }, vSqrt := { lower := (8191/8192), upper := (16777232/16776721) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1580598707/1073741824) }, upper := { exponent := 0, mantissa := (1519/1024) } }, logOuter := sk166LogOuterCertificate, logK := sk166LogKCertificate, logChi := chi206LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (33553953/33553442) } }, logDArg := sk166LogDArgCertificate }

private noncomputable def leaf2580InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf2580LocalValidity :
    LeafFacts leaf2580Box leaf2580Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2580Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (16777232/16776721) }) = true
      norm_num [leaf2580Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2580CertificateValid :
    WideCertificateValid leaf2580Box leaf2580Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk166ValidityFacts chi206ValidityFacts
    leaf2580LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2580CoverageChecked :
    coverageCheck (innerAD leaf2580Box) leaf2580InnerLog = true := by
  rfl'

private theorem leaf2580InnerLogValid :
    leaf2580InnerLog.Valid 8 (innerAD leaf2580Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf2580CoverageChecked

private noncomputable def leaf2580InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453667/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf2580InputLogOnePlusV_eq :
    leaf2580InputLogOnePlusV = outerEnclosure 24
      (leaf2580Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2580RoundedFacts : LeafRoundedFacts 8
    leaf2580Certificate.logOnePlusV leaf2580InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2580InputLogOnePlusV_eq }

private noncomputable def leaf2580Inputs : Inputs :=
  inputsOfCaches globalInput sk166RoundedInputs
    chi206InputQChi innerPair34Input
    leaf2580InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2580LowerChecked :
    lowerCheck 24 leaf2580Box leaf2580Inputs = true := by
  rfl'

private theorem leaf2580CoversExact : CoversExact 8
    leaf2580Box leaf2580Certificate leaf2580InnerLog leaf2580Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk166RoundedFacts chi206RoundedFacts
    innerPair34RoundedFacts leaf2580RoundedFacts (by rfl)

private theorem leaf2580FlatSound : Sound leaf2580Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2580CertificateValid
    leaf2580InnerLogValid leaf2580CoversExact leaf2580LowerChecked

private noncomputable def leaf2581Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (33/256), chiHi := (67/512) }

private noncomputable def leaf2581Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742197/1073741824) }, vSqrt := { lower := (8191/8192), upper := (4042264335/4042201088) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1588397013/1073741824) }, upper := { exponent := 0, mantissa := (3053/2048) } }, logOuter := sk166LogOuterCertificate, logK := sk166LogKCertificate, logChi := chi203LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (8084465423/8084402176) } }, logDArg := sk166LogDArgCertificate }

private noncomputable def leaf2581InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf2581LocalValidity :
    LeafFacts leaf2581Box leaf2581Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2581Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4042264335/4042201088) }) = true
      norm_num [leaf2581Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2581CertificateValid :
    WideCertificateValid leaf2581Box leaf2581Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk166ValidityFacts chi203ValidityFacts
    leaf2581LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2581CoverageChecked :
    coverageCheck (innerAD leaf2581Box) leaf2581InnerLog = true := by
  rfl'

private theorem leaf2581InnerLogValid :
    leaf2581InnerLog.Valid 8 (innerAD leaf2581Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf2581CoverageChecked

private noncomputable def leaf2581InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907303/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2581InputLogOnePlusV_eq :
    leaf2581InputLogOnePlusV = outerEnclosure 24
      (leaf2581Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2581RoundedFacts : LeafRoundedFacts 8
    leaf2581Certificate.logOnePlusV leaf2581InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2581InputLogOnePlusV_eq }

private noncomputable def leaf2581Inputs : Inputs :=
  inputsOfCaches globalInput sk166RoundedInputs
    chi203InputQChi innerPair34Input
    leaf2581InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2581LowerChecked :
    lowerCheck 24 leaf2581Box leaf2581Inputs = true := by
  rfl'

private theorem leaf2581CoversExact : CoversExact 8
    leaf2581Box leaf2581Certificate leaf2581InnerLog leaf2581Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk166RoundedFacts chi203RoundedFacts
    innerPair34RoundedFacts leaf2581RoundedFacts (by rfl)

private theorem leaf2581FlatSound : Sound leaf2581Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2581CertificateValid
    leaf2581InnerLogValid leaf2581CoversExact leaf2581LowerChecked

private noncomputable def leaf2582Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (67/512), chiHi := (17/128) }

private noncomputable def leaf2582Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742199/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68718493695/68717387776) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1596195319/1073741824) }, upper := { exponent := 0, mantissa := (767/512) } }, logOuter := sk166LogOuterCertificate, logK := sk166LogKCertificate, logChi := chi204LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137435881471/137434775552) } }, logDArg := sk166LogDArgCertificate }

private noncomputable def leaf2582InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf2582LocalValidity :
    LeafFacts leaf2582Box leaf2582Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2582Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68718493695/68717387776) }) = true
      norm_num [leaf2582Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2582CertificateValid :
    WideCertificateValid leaf2582Box leaf2582Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk166ValidityFacts chi204ValidityFacts
    leaf2582LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2582CoverageChecked :
    coverageCheck (innerAD leaf2582Box) leaf2582InnerLog = true := by
  rfl'

private theorem leaf2582InnerLogValid :
    leaf2582InnerLog.Valid 8 (innerAD leaf2582Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf2582CoverageChecked

private noncomputable def leaf2582InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (363413/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf2582InputLogOnePlusV_eq :
    leaf2582InputLogOnePlusV = outerEnclosure 24
      (leaf2582Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2582RoundedFacts : LeafRoundedFacts 8
    leaf2582Certificate.logOnePlusV leaf2582InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2582InputLogOnePlusV_eq }

private noncomputable def leaf2582Inputs : Inputs :=
  inputsOfCaches globalInput sk166RoundedInputs
    chi204InputQChi innerPair34Input
    leaf2582InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2582LowerChecked :
    lowerCheck 24 leaf2582Box leaf2582Inputs = true := by
  rfl'

private theorem leaf2582CoversExact : CoversExact 8
    leaf2582Box leaf2582Certificate leaf2582InnerLog leaf2582Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk166RoundedFacts chi204RoundedFacts
    innerPair34RoundedFacts leaf2582RoundedFacts (by rfl)

private theorem leaf2582FlatSound : Sound leaf2582Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2582CertificateValid
    leaf2582InnerLogValid leaf2582CoversExact leaf2582LowerChecked

private noncomputable def leaf2583Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (237/64), chiLo := (17/128), chiHi := (35/256) }

private noncomputable def leaf2583Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742367/1073741824) }, vSqrt := { lower := (8191/8192), upper := (8084524815/8084394496) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1599537283/1073741824) }, upper := { exponent := 0, mantissa := (24679/16384) } }, logOuter := sk221LogOuterCertificate, logK := sk221LogKCertificate, logChi := chi179LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16168919311/16168788992) } }, logDArg := sk221LogDArgCertificate }

private noncomputable def leaf2583InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf2583LocalValidity :
    LeafFacts leaf2583Box leaf2583Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2583Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8084524815/8084394496) }) = true
      norm_num [leaf2583Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2583CertificateValid :
    WideCertificateValid leaf2583Box leaf2583Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk221ValidityFacts chi179ValidityFacts
    leaf2583LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2583CoverageChecked :
    coverageCheck (innerAD leaf2583Box) leaf2583InnerLog = true := by
  rfl'

private theorem leaf2583InnerLogValid :
    leaf2583InnerLog.Valid 8 (innerAD leaf2583Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf2583CoverageChecked

private noncomputable def leaf2583InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (363413/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf2583InputLogOnePlusV_eq :
    leaf2583InputLogOnePlusV = outerEnclosure 24
      (leaf2583Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2583RoundedFacts : LeafRoundedFacts 8
    leaf2583Certificate.logOnePlusV leaf2583InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2583InputLogOnePlusV_eq }

private noncomputable def leaf2583Inputs : Inputs :=
  inputsOfCaches globalInput sk221RoundedInputs
    chi179InputQChi innerPair35Input
    leaf2583InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2583LowerChecked :
    lowerCheck 24 leaf2583Box leaf2583Inputs = true := by
  rfl'

private theorem leaf2583CoversExact : CoversExact 8
    leaf2583Box leaf2583Certificate leaf2583InnerLog leaf2583Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk221RoundedFacts chi179RoundedFacts
    innerPair35RoundedFacts leaf2583RoundedFacts (by rfl)

private theorem leaf2583FlatSound : Sound leaf2583Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2583CertificateValid
    leaf2583InnerLogValid leaf2583CoversExact leaf2583LowerChecked

private noncomputable def leaf2584Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (237/64), kHi := (119/32), chiLo := (17/128), chiHi := (35/256) }

private noncomputable def leaf2584Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742369/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434688512) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1601765369/1073741824) }, upper := { exponent := 0, mantissa := (12357/8192) } }, logOuter := sk222LogOuterCertificate, logK := sk222LogKCertificate, logChi := chi179LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871610367/274869377024) } }, logDArg := sk222LogDArgCertificate }

private noncomputable def leaf2584InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf2584LocalValidity :
    LeafFacts leaf2584Box leaf2584Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2584Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434688512) }) = true
      norm_num [leaf2584Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2584CertificateValid :
    WideCertificateValid leaf2584Box leaf2584Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk222ValidityFacts chi179ValidityFacts
    leaf2584LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2584CoverageChecked :
    coverageCheck (innerAD leaf2584Box) leaf2584InnerLog = true := by
  rfl'

private theorem leaf2584InnerLogValid :
    leaf2584InnerLog.Valid 8 (innerAD leaf2584Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf2584CoverageChecked

private noncomputable def leaf2584InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629217/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2584InputLogOnePlusV_eq :
    leaf2584InputLogOnePlusV = outerEnclosure 24
      (leaf2584Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2584RoundedFacts : LeafRoundedFacts 8
    leaf2584Certificate.logOnePlusV leaf2584InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2584InputLogOnePlusV_eq }

private noncomputable def leaf2584Inputs : Inputs :=
  inputsOfCaches globalInput sk222RoundedInputs
    chi179InputQChi innerPair35Input
    leaf2584InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2584LowerChecked :
    lowerCheck 24 leaf2584Box leaf2584Inputs = true := by
  rfl'

private theorem leaf2584CoversExact : CoversExact 8
    leaf2584Box leaf2584Certificate leaf2584InnerLog leaf2584Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk222RoundedFacts chi179RoundedFacts
    innerPair35RoundedFacts leaf2584RoundedFacts (by rfl)

private theorem leaf2584FlatSound : Sound leaf2584Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2584CertificateValid
    leaf2584InnerLogValid leaf2584CoversExact leaf2584LowerChecked

private noncomputable def leaf2585Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (237/64), chiLo := (35/256), chiHi := (9/64) }

private noncomputable def leaf2585Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742369/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434585088) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1615002833/1073741824) }, upper := { exponent := 0, mantissa := (6229/4096) } }, logOuter := sk221LogOuterCertificate, logK := sk221LogKCertificate, logChi := chi180LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871506943/274869170176) } }, logDArg := sk221LogDArgCertificate }

private noncomputable def leaf2585InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2585LocalValidity :
    LeafFacts leaf2585Box leaf2585Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2585Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434585088) }) = true
      norm_num [leaf2585Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2585CertificateValid :
    WideCertificateValid leaf2585Box leaf2585Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk221ValidityFacts chi180ValidityFacts
    leaf2585LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2585CoverageChecked :
    coverageCheck (innerAD leaf2585Box) leaf2585InnerLog = true := by
  rfl'

private theorem leaf2585InnerLogValid :
    leaf2585InnerLog.Valid 8 (innerAD leaf2585Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2585CoverageChecked

private noncomputable def leaf2585InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629223/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2585InputLogOnePlusV_eq :
    leaf2585InputLogOnePlusV = outerEnclosure 24
      (leaf2585Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2585RoundedFacts : LeafRoundedFacts 8
    leaf2585Certificate.logOnePlusV leaf2585InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2585InputLogOnePlusV_eq }

private noncomputable def leaf2585Inputs : Inputs :=
  inputsOfCaches globalInput sk221RoundedInputs
    chi180InputQChi innerPair40Input
    leaf2585InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2585LowerChecked :
    lowerCheck 24 leaf2585Box leaf2585Inputs = true := by
  rfl'

private theorem leaf2585CoversExact : CoversExact 8
    leaf2585Box leaf2585Certificate leaf2585InnerLog leaf2585Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk221RoundedFacts chi180RoundedFacts
    innerPair40RoundedFacts leaf2585RoundedFacts (by rfl)

private theorem leaf2585FlatSound : Sound leaf2585Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2585CertificateValid
    leaf2585InnerLogValid leaf2585CoversExact leaf2585LowerChecked

private noncomputable def leaf2586Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (237/64), kHi := (119/32), chiLo := (35/256), chiHi := (9/64) }

private noncomputable def leaf2586Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742371/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434566656) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1617296451/1073741824) }, upper := { exponent := 0, mantissa := (3119/2048) } }, logOuter := sk222LogOuterCertificate, logK := sk222LogKCertificate, logChi := chi180LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871488511/274869133312) } }, logDArg := sk222LogDArgCertificate }

private noncomputable def leaf2586InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2586LocalValidity :
    LeafFacts leaf2586Box leaf2586Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2586Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434566656) }) = true
      norm_num [leaf2586Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2586CertificateValid :
    WideCertificateValid leaf2586Box leaf2586Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk222ValidityFacts chi180ValidityFacts
    leaf2586LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2586CoverageChecked :
    coverageCheck (innerAD leaf2586Box) leaf2586InnerLog = true := by
  rfl'

private theorem leaf2586InnerLogValid :
    leaf2586InnerLog.Valid 8 (innerAD leaf2586Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2586CoverageChecked

private noncomputable def leaf2586InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453653/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf2586InputLogOnePlusV_eq :
    leaf2586InputLogOnePlusV = outerEnclosure 24
      (leaf2586Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2586RoundedFacts : LeafRoundedFacts 8
    leaf2586Certificate.logOnePlusV leaf2586InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2586InputLogOnePlusV_eq }

private noncomputable def leaf2586Inputs : Inputs :=
  inputsOfCaches globalInput sk222RoundedInputs
    chi180InputQChi innerPair40Input
    leaf2586InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2586LowerChecked :
    lowerCheck 24 leaf2586Box leaf2586Inputs = true := by
  rfl'

private theorem leaf2586CoversExact : CoversExact 8
    leaf2586Box leaf2586Certificate leaf2586InnerLog leaf2586Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk222RoundedFacts chi180RoundedFacts
    innerPair40RoundedFacts leaf2586RoundedFacts (by rfl)

private theorem leaf2586FlatSound : Sound leaf2586Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2586CertificateValid
    leaf2586InnerLogValid leaf2586CoversExact leaf2586LowerChecked

private noncomputable def leaf2587Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (239/64), chiLo := (17/128), chiHi := (35/256) }

private noncomputable def leaf2587Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742371/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45811556864) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1603993455/1073741824) }, upper := { exponent := 0, mantissa := (24749/16384) } }, logOuter := sk223LogOuterCertificate, logK := sk223LogKCertificate, logChi := chi179LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623864149/91623113728) } }, logDArg := sk223LogDArgCertificate }

private noncomputable def leaf2587InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf2587LocalValidity :
    LeafFacts leaf2587Box leaf2587Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2587Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45811556864) }) = true
      norm_num [leaf2587Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2587CertificateValid :
    WideCertificateValid leaf2587Box leaf2587Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk223ValidityFacts chi179ValidityFacts
    leaf2587LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2587CoverageChecked :
    coverageCheck (innerAD leaf2587Box) leaf2587InnerLog = true := by
  rfl'

private theorem leaf2587InnerLogValid :
    leaf2587InnerLog.Valid 8 (innerAD leaf2587Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf2587CoverageChecked

private noncomputable def leaf2587InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814609/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2587InputLogOnePlusV_eq :
    leaf2587InputLogOnePlusV = outerEnclosure 24
      (leaf2587Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2587RoundedFacts : LeafRoundedFacts 8
    leaf2587Certificate.logOnePlusV leaf2587InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2587InputLogOnePlusV_eq }

private noncomputable def leaf2587Inputs : Inputs :=
  inputsOfCaches globalInput sk223RoundedInputs
    chi179InputQChi innerPair35Input
    leaf2587InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2587LowerChecked :
    lowerCheck 24 leaf2587Box leaf2587Inputs = true := by
  rfl'

private theorem leaf2587CoversExact : CoversExact 8
    leaf2587Box leaf2587Certificate leaf2587InnerLog leaf2587Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk223RoundedFacts chi179RoundedFacts
    innerPair35RoundedFacts leaf2587RoundedFacts (by rfl)

private theorem leaf2587FlatSound : Sound leaf2587Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2587CertificateValid
    leaf2587InnerLogValid leaf2587CoversExact leaf2587LowerChecked

private noncomputable def leaf2588Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (239/64), kHi := (15/4), chiLo := (17/128), chiHi := (35/256) }

private noncomputable def leaf2588Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742373/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434652672) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1606221541/1073741824) }, upper := { exponent := 0, mantissa := (1549/1024) } }, logOuter := sk224LogOuterCertificate, logK := sk224LogKCertificate, logChi := chi179LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871574527/274869305344) } }, logDArg := sk224LogDArgCertificate }

private noncomputable def leaf2588InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf2588LocalValidity :
    LeafFacts leaf2588Box leaf2588Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2588Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434652672) }) = true
      norm_num [leaf2588Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2588CertificateValid :
    WideCertificateValid leaf2588Box leaf2588Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk224ValidityFacts chi179ValidityFacts
    leaf2588LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2588CoverageChecked :
    coverageCheck (innerAD leaf2588Box) leaf2588InnerLog = true := by
  rfl'

private theorem leaf2588InnerLogValid :
    leaf2588InnerLog.Valid 8 (innerAD leaf2588Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf2588CoverageChecked

private noncomputable def leaf2588InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629219/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2588InputLogOnePlusV_eq :
    leaf2588InputLogOnePlusV = outerEnclosure 24
      (leaf2588Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2588RoundedFacts : LeafRoundedFacts 8
    leaf2588Certificate.logOnePlusV leaf2588InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2588InputLogOnePlusV_eq }

private noncomputable def leaf2588Inputs : Inputs :=
  inputsOfCaches globalInput sk224RoundedInputs
    chi179InputQChi innerPair35Input
    leaf2588InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2588LowerChecked :
    lowerCheck 24 leaf2588Box leaf2588Inputs = true := by
  rfl'

private theorem leaf2588CoversExact : CoversExact 8
    leaf2588Box leaf2588Certificate leaf2588InnerLog leaf2588Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk224RoundedFacts chi179RoundedFacts
    innerPair35RoundedFacts leaf2588RoundedFacts (by rfl)

private theorem leaf2588FlatSound : Sound leaf2588Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2588CertificateValid
    leaf2588InnerLogValid leaf2588CoversExact leaf2588LowerChecked

private noncomputable def leaf2589Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (239/64), chiLo := (35/256), chiHi := (9/64) }

private noncomputable def leaf2589Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742373/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434548224) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1619590069/1073741824) }, upper := { exponent := 0, mantissa := (6247/4096) } }, logOuter := sk223LogOuterCertificate, logK := sk223LogKCertificate, logChi := chi180LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871470079/274869096448) } }, logDArg := sk223LogDArgCertificate }

private noncomputable def leaf2589InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2589LocalValidity :
    LeafFacts leaf2589Box leaf2589Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2589Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434548224) }) = true
      norm_num [leaf2589Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2589CertificateValid :
    WideCertificateValid leaf2589Box leaf2589Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk223ValidityFacts chi180ValidityFacts
    leaf2589LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2589CoverageChecked :
    coverageCheck (innerAD leaf2589Box) leaf2589InnerLog = true := by
  rfl'

private theorem leaf2589InnerLogValid :
    leaf2589InnerLog.Valid 8 (innerAD leaf2589Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2589CoverageChecked

private noncomputable def leaf2589InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814613/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2589InputLogOnePlusV_eq :
    leaf2589InputLogOnePlusV = outerEnclosure 24
      (leaf2589Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2589RoundedFacts : LeafRoundedFacts 8
    leaf2589Certificate.logOnePlusV leaf2589InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2589InputLogOnePlusV_eq }

private noncomputable def leaf2589Inputs : Inputs :=
  inputsOfCaches globalInput sk223RoundedInputs
    chi180InputQChi innerPair40Input
    leaf2589InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2589LowerChecked :
    lowerCheck 24 leaf2589Box leaf2589Inputs = true := by
  rfl'

private theorem leaf2589CoversExact : CoversExact 8
    leaf2589Box leaf2589Certificate leaf2589InnerLog leaf2589Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk223RoundedFacts chi180RoundedFacts
    innerPair40RoundedFacts leaf2589RoundedFacts (by rfl)

private theorem leaf2589FlatSound : Sound leaf2589Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2589CertificateValid
    leaf2589InnerLogValid leaf2589CoversExact leaf2589LowerChecked

private noncomputable def leaf2590Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (239/64), kHi := (15/4), chiLo := (35/256), chiHi := (9/64) }

private noncomputable def leaf2590Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742375/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434529792) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1621883687/1073741824) }, upper := { exponent := 0, mantissa := (391/256) } }, logOuter := sk224LogOuterCertificate, logK := sk224LogKCertificate, logChi := chi180LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871451647/274869059584) } }, logDArg := sk224LogDArgCertificate }

private noncomputable def leaf2590InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2590LocalValidity :
    LeafFacts leaf2590Box leaf2590Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2590Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434529792) }) = true
      norm_num [leaf2590Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2590CertificateValid :
    WideCertificateValid leaf2590Box leaf2590Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk224ValidityFacts chi180ValidityFacts
    leaf2590LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2590CoverageChecked :
    coverageCheck (innerAD leaf2590Box) leaf2590InnerLog = true := by
  rfl'

private theorem leaf2590InnerLogValid :
    leaf2590InnerLog.Valid 8 (innerAD leaf2590Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2590CoverageChecked

private noncomputable def leaf2590InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629227/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2590InputLogOnePlusV_eq :
    leaf2590InputLogOnePlusV = outerEnclosure 24
      (leaf2590Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2590RoundedFacts : LeafRoundedFacts 8
    leaf2590Certificate.logOnePlusV leaf2590InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2590InputLogOnePlusV_eq }

private noncomputable def leaf2590Inputs : Inputs :=
  inputsOfCaches globalInput sk224RoundedInputs
    chi180InputQChi innerPair40Input
    leaf2590InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2590LowerChecked :
    lowerCheck 24 leaf2590Box leaf2590Inputs = true := by
  rfl'

private theorem leaf2590CoversExact : CoversExact 8
    leaf2590Box leaf2590Certificate leaf2590InnerLog leaf2590Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk224RoundedFacts chi180RoundedFacts
    innerPair40RoundedFacts leaf2590RoundedFacts (by rfl)

private theorem leaf2590FlatSound : Sound leaf2590Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2590CertificateValid
    leaf2590InnerLogValid leaf2590CoversExact leaf2590LowerChecked

private noncomputable def leaf2591Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (233/64), chiLo := (9/64), chiHi := (37/256) }

private noncomputable def leaf2591Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742363/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486907904) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1621031783/1073741824) }, upper := { exponent := 0, mantissa := (25005/16384) } }, logOuter := sk217LogOuterCertificate, logK := sk217LogKCertificate, logChi := chi175LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54974292275/54973815808) } }, logDArg := sk217LogDArgCertificate }

private noncomputable def leaf2591InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2591LocalValidity :
    LeafFacts leaf2591Box leaf2591Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2591Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486907904) }) = true
      norm_num [leaf2591Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2591CertificateValid :
    WideCertificateValid leaf2591Box leaf2591Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk217ValidityFacts chi175ValidityFacts
    leaf2591LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2591CoverageChecked :
    coverageCheck (innerAD leaf2591Box) leaf2591InnerLog = true := by
  rfl'

private theorem leaf2591InnerLogValid :
    leaf2591InnerLog.Valid 8 (innerAD leaf2591Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2591CoverageChecked

private noncomputable def leaf2591InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814613/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2591InputLogOnePlusV_eq :
    leaf2591InputLogOnePlusV = outerEnclosure 24
      (leaf2591Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2591RoundedFacts : LeafRoundedFacts 8
    leaf2591Certificate.logOnePlusV leaf2591InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2591InputLogOnePlusV_eq }

private noncomputable def leaf2591Inputs : Inputs :=
  inputsOfCaches globalInput sk217RoundedInputs
    chi175InputQChi innerPair40Input
    leaf2591InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2591LowerChecked :
    lowerCheck 24 leaf2591Box leaf2591Inputs = true := by
  rfl'

private theorem leaf2591CoversExact : CoversExact 8
    leaf2591Box leaf2591Certificate leaf2591InnerLog leaf2591Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk217RoundedFacts chi175RoundedFacts
    innerPair40RoundedFacts leaf2591RoundedFacts (by rfl)

private theorem leaf2591FlatSound : Sound leaf2591Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2591CertificateValid
    leaf2591InnerLogValid leaf2591CoversExact leaf2591LowerChecked

private noncomputable def leaf2592Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (233/64), kHi := (117/32), chiLo := (9/64), chiHi := (37/256) }

private noncomputable def leaf2592Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742365/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434520576) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1623390933/1073741824) }, upper := { exponent := 0, mantissa := (12521/8192) } }, logOuter := sk218LogOuterCertificate, logK := sk218LogKCertificate, logChi := chi175LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871442431/274869041152) } }, logDArg := sk218LogDArgCertificate }

private noncomputable def leaf2592InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2592LocalValidity :
    LeafFacts leaf2592Box leaf2592Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2592Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434520576) }) = true
      norm_num [leaf2592Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2592CertificateValid :
    WideCertificateValid leaf2592Box leaf2592Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk218ValidityFacts chi175ValidityFacts
    leaf2592LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2592CoverageChecked :
    coverageCheck (innerAD leaf2592Box) leaf2592InnerLog = true := by
  rfl'

private theorem leaf2592InnerLogValid :
    leaf2592InnerLog.Valid 8 (innerAD leaf2592Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2592CoverageChecked

private noncomputable def leaf2592InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629227/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2592InputLogOnePlusV_eq :
    leaf2592InputLogOnePlusV = outerEnclosure 24
      (leaf2592Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2592RoundedFacts : LeafRoundedFacts 8
    leaf2592Certificate.logOnePlusV leaf2592InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2592InputLogOnePlusV_eq }

private noncomputable def leaf2592Inputs : Inputs :=
  inputsOfCaches globalInput sk218RoundedInputs
    chi175InputQChi innerPair40Input
    leaf2592InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2592LowerChecked :
    lowerCheck 24 leaf2592Box leaf2592Inputs = true := by
  rfl'

private theorem leaf2592CoversExact : CoversExact 8
    leaf2592Box leaf2592Certificate leaf2592InnerLog leaf2592Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk218RoundedFacts chi175RoundedFacts
    innerPair40RoundedFacts leaf2592RoundedFacts (by rfl)

private theorem leaf2592FlatSound : Sound leaf2592Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2592CertificateValid
    leaf2592InnerLogValid leaf2592CoversExact leaf2592LowerChecked

private noncomputable def leaf2593Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (233/64), chiLo := (37/256), chiHi := (19/128) }

private noncomputable def leaf2593Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742365/1073741824) }, vSqrt := { lower := (8191/8192), upper := (5090256365/5090163712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1636235205/1073741824) }, upper := { exponent := 0, mantissa := (12619/8192) } }, logOuter := sk217LogOuterCertificate, logK := sk217LogKCertificate, logChi := chi176LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (10180420077/10180327424) } }, logDArg := sk217LogDArgCertificate }

private noncomputable def leaf2593InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2593LocalValidity :
    LeafFacts leaf2593Box leaf2593Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2593Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5090256365/5090163712) }) = true
      norm_num [leaf2593Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2593CertificateValid :
    WideCertificateValid leaf2593Box leaf2593Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk217ValidityFacts chi176ValidityFacts
    leaf2593LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2593CoverageChecked :
    coverageCheck (innerAD leaf2593Box) leaf2593InnerLog = true := by
  rfl'

private theorem leaf2593InnerLogValid :
    leaf2593InnerLog.Valid 8 (innerAD leaf2593Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2593CoverageChecked

private noncomputable def leaf2593InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629233/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2593InputLogOnePlusV_eq :
    leaf2593InputLogOnePlusV = outerEnclosure 24
      (leaf2593Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2593RoundedFacts : LeafRoundedFacts 8
    leaf2593Certificate.logOnePlusV leaf2593InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2593InputLogOnePlusV_eq }

private noncomputable def leaf2593Inputs : Inputs :=
  inputsOfCaches globalInput sk217RoundedInputs
    chi176InputQChi innerPair40Input
    leaf2593InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2593LowerChecked :
    lowerCheck 24 leaf2593Box leaf2593Inputs = true := by
  rfl'

private theorem leaf2593CoversExact : CoversExact 8
    leaf2593Box leaf2593Certificate leaf2593InnerLog leaf2593Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk217RoundedFacts chi176RoundedFacts
    innerPair40RoundedFacts leaf2593RoundedFacts (by rfl)

private theorem leaf2593FlatSound : Sound leaf2593Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2593CertificateValid
    leaf2593InnerLogValid leaf2593CoversExact leaf2593LowerChecked

private noncomputable def leaf2594Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (233/64), kHi := (117/32), chiLo := (37/256), chiHi := (19/128) }

private noncomputable def leaf2594Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742367/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434400768) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1638659887/1073741824) }, upper := { exponent := 0, mantissa := (6319/4096) } }, logOuter := sk218LogOuterCertificate, logK := sk218LogKCertificate, logChi := chi176LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871322623/274868801536) } }, logDArg := sk218LogDArgCertificate }

private noncomputable def leaf2594InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2594LocalValidity :
    LeafFacts leaf2594Box leaf2594Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2594Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434400768) }) = true
      norm_num [leaf2594Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2594CertificateValid :
    WideCertificateValid leaf2594Box leaf2594Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk218ValidityFacts chi176ValidityFacts
    leaf2594LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2594CoverageChecked :
    coverageCheck (innerAD leaf2594Box) leaf2594InnerLog = true := by
  rfl'

private theorem leaf2594InnerLogValid :
    leaf2594InnerLog.Valid 8 (innerAD leaf2594Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2594CoverageChecked

private noncomputable def leaf2594InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629235/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2594InputLogOnePlusV_eq :
    leaf2594InputLogOnePlusV = outerEnclosure 24
      (leaf2594Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2594RoundedFacts : LeafRoundedFacts 8
    leaf2594Certificate.logOnePlusV leaf2594InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2594InputLogOnePlusV_eq }

private noncomputable def leaf2594Inputs : Inputs :=
  inputsOfCaches globalInput sk218RoundedInputs
    chi176InputQChi innerPair40Input
    leaf2594InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2594LowerChecked :
    lowerCheck 24 leaf2594Box leaf2594Inputs = true := by
  rfl'

private theorem leaf2594CoversExact : CoversExact 8
    leaf2594Box leaf2594Certificate leaf2594InnerLog leaf2594Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk218RoundedFacts chi176RoundedFacts
    innerPair40RoundedFacts leaf2594RoundedFacts (by rfl)

private theorem leaf2594FlatSound : Sound leaf2594Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2594CertificateValid
    leaf2594InnerLogValid leaf2594CoversExact leaf2594LowerChecked

private noncomputable def leaf2595Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (235/64), chiLo := (9/64), chiHi := (37/256) }

private noncomputable def leaf2595Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742367/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45811500544) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1625750083/1073741824) }, upper := { exponent := 0, mantissa := (25079/16384) } }, logOuter := sk219LogOuterCertificate, logK := sk219LogKCertificate, logChi := chi175LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623807829/91623001088) } }, logDArg := sk219LogDArgCertificate }

private noncomputable def leaf2595InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2595LocalValidity :
    LeafFacts leaf2595Box leaf2595Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2595Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45811500544) }) = true
      norm_num [leaf2595Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2595CertificateValid :
    WideCertificateValid leaf2595Box leaf2595Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk219ValidityFacts chi175ValidityFacts
    leaf2595LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2595CoverageChecked :
    coverageCheck (innerAD leaf2595Box) leaf2595InnerLog = true := by
  rfl'

private theorem leaf2595InnerLogValid :
    leaf2595InnerLog.Valid 8 (innerAD leaf2595Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2595CoverageChecked

private noncomputable def leaf2595InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907307/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2595InputLogOnePlusV_eq :
    leaf2595InputLogOnePlusV = outerEnclosure 24
      (leaf2595Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2595RoundedFacts : LeafRoundedFacts 8
    leaf2595Certificate.logOnePlusV leaf2595InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2595InputLogOnePlusV_eq }

private noncomputable def leaf2595Inputs : Inputs :=
  inputsOfCaches globalInput sk219RoundedInputs
    chi175InputQChi innerPair40Input
    leaf2595InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2595LowerChecked :
    lowerCheck 24 leaf2595Box leaf2595Inputs = true := by
  rfl'

private theorem leaf2595CoversExact : CoversExact 8
    leaf2595Box leaf2595Certificate leaf2595InnerLog leaf2595Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk219RoundedFacts chi175RoundedFacts
    innerPair40RoundedFacts leaf2595RoundedFacts (by rfl)

private theorem leaf2595FlatSound : Sound leaf2595Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2595CertificateValid
    leaf2595InnerLogValid leaf2595CoversExact leaf2595LowerChecked

private noncomputable def leaf2596Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (235/64), kHi := (59/16), chiLo := (9/64), chiHi := (37/256) }

private noncomputable def leaf2596Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742369/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434482688) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1628109233/1073741824) }, upper := { exponent := 0, mantissa := (6279/4096) } }, logOuter := sk220LogOuterCertificate, logK := sk220LogKCertificate, logChi := chi175LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871404543/274868965376) } }, logDArg := sk220LogDArgCertificate }

private noncomputable def leaf2596InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2596LocalValidity :
    LeafFacts leaf2596Box leaf2596Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2596Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434482688) }) = true
      norm_num [leaf2596Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2596CertificateValid :
    WideCertificateValid leaf2596Box leaf2596Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk220ValidityFacts chi175ValidityFacts
    leaf2596LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2596CoverageChecked :
    coverageCheck (innerAD leaf2596Box) leaf2596InnerLog = true := by
  rfl'

private theorem leaf2596InnerLogValid :
    leaf2596InnerLog.Valid 8 (innerAD leaf2596Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2596CoverageChecked

private noncomputable def leaf2596InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814615/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2596InputLogOnePlusV_eq :
    leaf2596InputLogOnePlusV = outerEnclosure 24
      (leaf2596Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2596RoundedFacts : LeafRoundedFacts 8
    leaf2596Certificate.logOnePlusV leaf2596InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2596InputLogOnePlusV_eq }

private noncomputable def leaf2596Inputs : Inputs :=
  inputsOfCaches globalInput sk220RoundedInputs
    chi175InputQChi innerPair40Input
    leaf2596InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2596LowerChecked :
    lowerCheck 24 leaf2596Box leaf2596Inputs = true := by
  rfl'

private theorem leaf2596CoversExact : CoversExact 8
    leaf2596Box leaf2596Certificate leaf2596InnerLog leaf2596Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk220RoundedFacts chi175RoundedFacts
    innerPair40RoundedFacts leaf2596RoundedFacts (by rfl)

private theorem leaf2596FlatSound : Sound leaf2596Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2596CertificateValid
    leaf2596InnerLogValid leaf2596CoversExact leaf2596LowerChecked

private noncomputable def leaf2597Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (235/64), chiLo := (37/256), chiHi := (19/128) }

private noncomputable def leaf2597Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742369/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434381312) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1641084569/1073741824) }, upper := { exponent := 0, mantissa := (12657/8192) } }, logOuter := sk219LogOuterCertificate, logK := sk219LogKCertificate, logChi := chi176LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871303167/274868762624) } }, logDArg := sk219LogDArgCertificate }

private noncomputable def leaf2597InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2597LocalValidity :
    LeafFacts leaf2597Box leaf2597Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2597Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434381312) }) = true
      norm_num [leaf2597Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2597CertificateValid :
    WideCertificateValid leaf2597Box leaf2597Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk219ValidityFacts chi176ValidityFacts
    leaf2597LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2597CoverageChecked :
    coverageCheck (innerAD leaf2597Box) leaf2597InnerLog = true := by
  rfl'

private theorem leaf2597InnerLogValid :
    leaf2597InnerLog.Valid 8 (innerAD leaf2597Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2597CoverageChecked

private noncomputable def leaf2597InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907309/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2597InputLogOnePlusV_eq :
    leaf2597InputLogOnePlusV = outerEnclosure 24
      (leaf2597Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2597RoundedFacts : LeafRoundedFacts 8
    leaf2597Certificate.logOnePlusV leaf2597InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2597InputLogOnePlusV_eq }

private noncomputable def leaf2597Inputs : Inputs :=
  inputsOfCaches globalInput sk219RoundedInputs
    chi176InputQChi innerPair40Input
    leaf2597InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2597LowerChecked :
    lowerCheck 24 leaf2597Box leaf2597Inputs = true := by
  rfl'

private theorem leaf2597CoversExact : CoversExact 8
    leaf2597Box leaf2597Certificate leaf2597InnerLog leaf2597Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk219RoundedFacts chi176RoundedFacts
    innerPair40RoundedFacts leaf2597RoundedFacts (by rfl)

private theorem leaf2597FlatSound : Sound leaf2597Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2597CertificateValid
    leaf2597InnerLogValid leaf2597CoversExact leaf2597LowerChecked

private noncomputable def leaf2598Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (235/64), kHi := (59/16), chiLo := (37/256), chiHi := (19/128) }

private noncomputable def leaf2598Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742371/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45811453952) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1643509251/1073741824) }, upper := { exponent := 0, mantissa := (3169/2048) } }, logOuter := sk220LogOuterCertificate, logK := sk220LogKCertificate, logChi := chi176LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623761237/91622907904) } }, logDArg := sk220LogDArgCertificate }

private noncomputable def leaf2598InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2598LocalValidity :
    LeafFacts leaf2598Box leaf2598Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2598Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45811453952) }) = true
      norm_num [leaf2598Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2598CertificateValid :
    WideCertificateValid leaf2598Box leaf2598Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk220ValidityFacts chi176ValidityFacts
    leaf2598LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2598CoverageChecked :
    coverageCheck (innerAD leaf2598Box) leaf2598InnerLog = true := by
  rfl'

private theorem leaf2598InnerLogValid :
    leaf2598InnerLog.Valid 8 (innerAD leaf2598Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2598CoverageChecked

private noncomputable def leaf2598InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629237/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2598InputLogOnePlusV_eq :
    leaf2598InputLogOnePlusV = outerEnclosure 24
      (leaf2598Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2598RoundedFacts : LeafRoundedFacts 8
    leaf2598Certificate.logOnePlusV leaf2598InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2598InputLogOnePlusV_eq }

private noncomputable def leaf2598Inputs : Inputs :=
  inputsOfCaches globalInput sk220RoundedInputs
    chi176InputQChi innerPair40Input
    leaf2598InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2598LowerChecked :
    lowerCheck 24 leaf2598Box leaf2598Inputs = true := by
  rfl'

private theorem leaf2598CoversExact : CoversExact 8
    leaf2598Box leaf2598Certificate leaf2598InnerLog leaf2598Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk220RoundedFacts chi176RoundedFacts
    innerPair40RoundedFacts leaf2598RoundedFacts (by rfl)

private theorem leaf2598FlatSound : Sound leaf2598Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2598CertificateValid
    leaf2598InnerLogValid leaf2598CoversExact leaf2598LowerChecked

private noncomputable def leaf2599Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (233/64), chiLo := (19/128), chiHi := (39/256) }

private noncomputable def leaf2599Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742367/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434300928) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1651438627/1073741824) }, upper := { exponent := 0, mantissa := (25471/16384) } }, logOuter := sk217LogOuterCertificate, logK := sk217LogKCertificate, logChi := chi177LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871222783/274868601856) } }, logDArg := sk217LogDArgCertificate }

private noncomputable def leaf2599InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2599LocalValidity :
    LeafFacts leaf2599Box leaf2599Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2599Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434300928) }) = true
      norm_num [leaf2599Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2599CertificateValid :
    WideCertificateValid leaf2599Box leaf2599Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk217ValidityFacts chi177ValidityFacts
    leaf2599LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2599CoverageChecked :
    coverageCheck (innerAD leaf2599Box) leaf2599InnerLog = true := by
  rfl'

private theorem leaf2599InnerLogValid :
    leaf2599InnerLog.Valid 8 (innerAD leaf2599Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2599CoverageChecked

private noncomputable def leaf2599InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629241/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2599InputLogOnePlusV_eq :
    leaf2599InputLogOnePlusV = outerEnclosure 24
      (leaf2599Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2599RoundedFacts : LeafRoundedFacts 8
    leaf2599Certificate.logOnePlusV leaf2599InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2599InputLogOnePlusV_eq }

private noncomputable def leaf2599Inputs : Inputs :=
  inputsOfCaches globalInput sk217RoundedInputs
    chi177InputQChi innerPair40Input
    leaf2599InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2599LowerChecked :
    lowerCheck 24 leaf2599Box leaf2599Inputs = true := by
  rfl'

private theorem leaf2599CoversExact : CoversExact 8
    leaf2599Box leaf2599Certificate leaf2599InnerLog leaf2599Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk217RoundedFacts chi177RoundedFacts
    innerPair40RoundedFacts leaf2599RoundedFacts (by rfl)

private theorem leaf2599FlatSound : Sound leaf2599Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2599CertificateValid
    leaf2599InnerLogValid leaf2599CoversExact leaf2599LowerChecked

private noncomputable def leaf2600Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (233/64), kHi := (117/32), chiLo := (19/128), chiHi := (39/256) }

private noncomputable def leaf2600Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742369/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486856192) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1653928841/1073741824) }, upper := { exponent := 0, mantissa := (12755/8192) } }, logOuter := sk218LogOuterCertificate, logK := sk218LogKCertificate, logChi := chi177LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54974240563/54973712384) } }, logDArg := sk218LogDArgCertificate }

private noncomputable def leaf2600InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2600LocalValidity :
    LeafFacts leaf2600Box leaf2600Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2600Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486856192) }) = true
      norm_num [leaf2600Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2600CertificateValid :
    WideCertificateValid leaf2600Box leaf2600Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk218ValidityFacts chi177ValidityFacts
    leaf2600LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2600CoverageChecked :
    coverageCheck (innerAD leaf2600Box) leaf2600InnerLog = true := by
  rfl'

private theorem leaf2600InnerLogValid :
    leaf2600InnerLog.Valid 8 (innerAD leaf2600Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2600CoverageChecked

private noncomputable def leaf2600InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814621/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2600InputLogOnePlusV_eq :
    leaf2600InputLogOnePlusV = outerEnclosure 24
      (leaf2600Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2600RoundedFacts : LeafRoundedFacts 8
    leaf2600Certificate.logOnePlusV leaf2600InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2600InputLogOnePlusV_eq }

private noncomputable def leaf2600Inputs : Inputs :=
  inputsOfCaches globalInput sk218RoundedInputs
    chi177InputQChi innerPair40Input
    leaf2600InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2600LowerChecked :
    lowerCheck 24 leaf2600Box leaf2600Inputs = true := by
  rfl'

private theorem leaf2600CoversExact : CoversExact 8
    leaf2600Box leaf2600Certificate leaf2600InnerLog leaf2600Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk218RoundedFacts chi177RoundedFacts
    innerPair40RoundedFacts leaf2600RoundedFacts (by rfl)

private theorem leaf2600FlatSound : Sound leaf2600Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2600CertificateValid
    leaf2600InnerLogValid leaf2600CoversExact leaf2600LowerChecked

private noncomputable def leaf2601Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (233/64), chiLo := (39/256), chiHi := (5/32) }

private noncomputable def leaf2601Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742369/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434181632) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1666642049/1073741824) }, upper := { exponent := 0, mantissa := (3213/2048) } }, logOuter := sk217LogOuterCertificate, logK := sk217LogKCertificate, logChi := chi178LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871103487/274868363264) } }, logDArg := sk217LogDArgCertificate }

private noncomputable def leaf2601InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf2601LocalValidity :
    LeafFacts leaf2601Box leaf2601Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2601Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434181632) }) = true
      norm_num [leaf2601Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2601CertificateValid :
    WideCertificateValid leaf2601Box leaf2601Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk217ValidityFacts chi178ValidityFacts
    leaf2601LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2601CoverageChecked :
    coverageCheck (innerAD leaf2601Box) leaf2601InnerLog = true := by
  rfl'

private theorem leaf2601InnerLogValid :
    leaf2601InnerLog.Valid 8 (innerAD leaf2601Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf2601CoverageChecked

private noncomputable def leaf2601InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (181707/262144) }

set_option maxRecDepth 1000000 in
private theorem leaf2601InputLogOnePlusV_eq :
    leaf2601InputLogOnePlusV = outerEnclosure 24
      (leaf2601Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2601RoundedFacts : LeafRoundedFacts 8
    leaf2601Certificate.logOnePlusV leaf2601InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2601InputLogOnePlusV_eq }

private noncomputable def leaf2601Inputs : Inputs :=
  inputsOfCaches globalInput sk217RoundedInputs
    chi178InputQChi innerPair41Input
    leaf2601InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2601LowerChecked :
    lowerCheck 24 leaf2601Box leaf2601Inputs = true := by
  rfl'

private theorem leaf2601CoversExact : CoversExact 8
    leaf2601Box leaf2601Certificate leaf2601InnerLog leaf2601Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk217RoundedFacts chi178RoundedFacts
    innerPair41RoundedFacts leaf2601RoundedFacts (by rfl)

private theorem leaf2601FlatSound : Sound leaf2601Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2601CertificateValid
    leaf2601InnerLogValid leaf2601CoversExact leaf2601LowerChecked

private noncomputable def leaf2602Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (233/64), kHi := (117/32), chiLo := (39/256), chiHi := (5/32) }

private noncomputable def leaf2602Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742371/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434161152) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1669197795/1073741824) }, upper := { exponent := 0, mantissa := (1609/1024) } }, logOuter := sk218LogOuterCertificate, logK := sk218LogKCertificate, logChi := chi178LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871083007/274868322304) } }, logDArg := sk218LogDArgCertificate }

private noncomputable def leaf2602InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf2602LocalValidity :
    LeafFacts leaf2602Box leaf2602Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2602Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434161152) }) = true
      norm_num [leaf2602Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2602CertificateValid :
    WideCertificateValid leaf2602Box leaf2602Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk218ValidityFacts chi178ValidityFacts
    leaf2602LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2602CoverageChecked :
    coverageCheck (innerAD leaf2602Box) leaf2602InnerLog = true := by
  rfl'

private theorem leaf2602InnerLogValid :
    leaf2602InnerLog.Valid 8 (innerAD leaf2602Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf2602CoverageChecked

private noncomputable def leaf2602InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629249/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2602InputLogOnePlusV_eq :
    leaf2602InputLogOnePlusV = outerEnclosure 24
      (leaf2602Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2602RoundedFacts : LeafRoundedFacts 8
    leaf2602Certificate.logOnePlusV leaf2602InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2602InputLogOnePlusV_eq }

private noncomputable def leaf2602Inputs : Inputs :=
  inputsOfCaches globalInput sk218RoundedInputs
    chi178InputQChi innerPair41Input
    leaf2602InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2602LowerChecked :
    lowerCheck 24 leaf2602Box leaf2602Inputs = true := by
  rfl'

private theorem leaf2602CoversExact : CoversExact 8
    leaf2602Box leaf2602Certificate leaf2602InnerLog leaf2602Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk218RoundedFacts chi178RoundedFacts
    innerPair41RoundedFacts leaf2602RoundedFacts (by rfl)

private theorem leaf2602FlatSound : Sound leaf2602Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2602CertificateValid
    leaf2602InnerLogValid leaf2602CoversExact leaf2602LowerChecked

private noncomputable def leaf2603Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (235/64), chiLo := (19/128), chiHi := (39/256) }

private noncomputable def leaf2603Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742371/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434260992) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1656419055/1073741824) }, upper := { exponent := 0, mantissa := (25549/16384) } }, logOuter := sk219LogOuterCertificate, logK := sk219LogKCertificate, logChi := chi177LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871182847/274868521984) } }, logDArg := sk219LogDArgCertificate }

private noncomputable def leaf2603InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2603LocalValidity :
    LeafFacts leaf2603Box leaf2603Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2603Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434260992) }) = true
      norm_num [leaf2603Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2603CertificateValid :
    WideCertificateValid leaf2603Box leaf2603Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk219ValidityFacts chi177ValidityFacts
    leaf2603LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2603CoverageChecked :
    coverageCheck (innerAD leaf2603Box) leaf2603InnerLog = true := by
  rfl'

private theorem leaf2603InnerLogValid :
    leaf2603InnerLog.Valid 8 (innerAD leaf2603Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2603CoverageChecked

private noncomputable def leaf2603InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629243/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2603InputLogOnePlusV_eq :
    leaf2603InputLogOnePlusV = outerEnclosure 24
      (leaf2603Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2603RoundedFacts : LeafRoundedFacts 8
    leaf2603Certificate.logOnePlusV leaf2603InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2603InputLogOnePlusV_eq }

private noncomputable def leaf2603Inputs : Inputs :=
  inputsOfCaches globalInput sk219RoundedInputs
    chi177InputQChi innerPair40Input
    leaf2603InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2603LowerChecked :
    lowerCheck 24 leaf2603Box leaf2603Inputs = true := by
  rfl'

private theorem leaf2603CoversExact : CoversExact 8
    leaf2603Box leaf2603Certificate leaf2603InnerLog leaf2603Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk219RoundedFacts chi177RoundedFacts
    innerPair40RoundedFacts leaf2603RoundedFacts (by rfl)

private theorem leaf2603FlatSound : Sound leaf2603Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2603CertificateValid
    leaf2603InnerLogValid leaf2603CoversExact leaf2603LowerChecked

private noncomputable def leaf2604Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (235/64), kHi := (59/16), chiLo := (19/128), chiHi := (39/256) }

private noncomputable def leaf2604Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742373/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434241024) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1658909269/1073741824) }, upper := { exponent := 0, mantissa := (6397/4096) } }, logOuter := sk220LogOuterCertificate, logK := sk220LogKCertificate, logChi := chi177LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871162879/274868482048) } }, logDArg := sk220LogDArgCertificate }

private noncomputable def leaf2604InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2604LocalValidity :
    LeafFacts leaf2604Box leaf2604Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2604Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434241024) }) = true
      norm_num [leaf2604Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2604CertificateValid :
    WideCertificateValid leaf2604Box leaf2604Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk220ValidityFacts chi177ValidityFacts
    leaf2604LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2604CoverageChecked :
    coverageCheck (innerAD leaf2604Box) leaf2604InnerLog = true := by
  rfl'

private theorem leaf2604InnerLogValid :
    leaf2604InnerLog.Valid 8 (innerAD leaf2604Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2604CoverageChecked

private noncomputable def leaf2604InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907311/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2604InputLogOnePlusV_eq :
    leaf2604InputLogOnePlusV = outerEnclosure 24
      (leaf2604Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2604RoundedFacts : LeafRoundedFacts 8
    leaf2604Certificate.logOnePlusV leaf2604InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2604InputLogOnePlusV_eq }

private noncomputable def leaf2604Inputs : Inputs :=
  inputsOfCaches globalInput sk220RoundedInputs
    chi177InputQChi innerPair40Input
    leaf2604InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2604LowerChecked :
    lowerCheck 24 leaf2604Box leaf2604Inputs = true := by
  rfl'

private theorem leaf2604CoversExact : CoversExact 8
    leaf2604Box leaf2604Certificate leaf2604InnerLog leaf2604Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk220RoundedFacts chi177RoundedFacts
    innerPair40RoundedFacts leaf2604RoundedFacts (by rfl)

private theorem leaf2604FlatSound : Sound leaf2604Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2604CertificateValid
    leaf2604InnerLogValid leaf2604CoversExact leaf2604LowerChecked

private noncomputable def leaf2605Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (235/64), chiLo := (39/256), chiHi := (5/32) }

private noncomputable def leaf2605Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742373/1073741824) }, vSqrt := { lower := (8191/8192), upper := (2694841605/2694787072) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1671753541/1073741824) }, upper := { exponent := 0, mantissa := (3223/2048) } }, logOuter := sk219LogOuterCertificate, logK := sk219LogKCertificate, logChi := chi178LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (5389628677/5389574144) } }, logDArg := sk219LogDArgCertificate }

private noncomputable def leaf2605InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf2605LocalValidity :
    LeafFacts leaf2605Box leaf2605Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2605Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (2694841605/2694787072) }) = true
      norm_num [leaf2605Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2605CertificateValid :
    WideCertificateValid leaf2605Box leaf2605Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk219ValidityFacts chi178ValidityFacts
    leaf2605LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2605CoverageChecked :
    coverageCheck (innerAD leaf2605Box) leaf2605InnerLog = true := by
  rfl'

private theorem leaf2605InnerLogValid :
    leaf2605InnerLog.Valid 8 (innerAD leaf2605Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf2605CoverageChecked

private noncomputable def leaf2605InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814625/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2605InputLogOnePlusV_eq :
    leaf2605InputLogOnePlusV = outerEnclosure 24
      (leaf2605Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2605RoundedFacts : LeafRoundedFacts 8
    leaf2605Certificate.logOnePlusV leaf2605InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2605InputLogOnePlusV_eq }

private noncomputable def leaf2605Inputs : Inputs :=
  inputsOfCaches globalInput sk219RoundedInputs
    chi178InputQChi innerPair41Input
    leaf2605InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2605LowerChecked :
    lowerCheck 24 leaf2605Box leaf2605Inputs = true := by
  rfl'

private theorem leaf2605CoversExact : CoversExact 8
    leaf2605Box leaf2605Certificate leaf2605InnerLog leaf2605Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk219RoundedFacts chi178RoundedFacts
    innerPair41RoundedFacts leaf2605RoundedFacts (by rfl)

private theorem leaf2605FlatSound : Sound leaf2605Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2605CertificateValid
    leaf2605InnerLogValid leaf2605CoversExact leaf2605LowerChecked

private noncomputable def leaf2606Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (235/64), kHi := (59/16), chiLo := (39/256), chiHi := (5/32) }

private noncomputable def leaf2606Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742375/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434120192) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1674309287/1073741824) }, upper := { exponent := 0, mantissa := (807/512) } }, logOuter := sk220LogOuterCertificate, logK := sk220LogKCertificate, logChi := chi178LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871042047/274868240384) } }, logDArg := sk220LogDArgCertificate }

private noncomputable def leaf2606InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf2606LocalValidity :
    LeafFacts leaf2606Box leaf2606Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2606Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434120192) }) = true
      norm_num [leaf2606Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2606CertificateValid :
    WideCertificateValid leaf2606Box leaf2606Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk220ValidityFacts chi178ValidityFacts
    leaf2606LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2606CoverageChecked :
    coverageCheck (innerAD leaf2606Box) leaf2606InnerLog = true := by
  rfl'

private theorem leaf2606InnerLogValid :
    leaf2606InnerLog.Valid 8 (innerAD leaf2606Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf2606CoverageChecked

private noncomputable def leaf2606InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907313/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2606InputLogOnePlusV_eq :
    leaf2606InputLogOnePlusV = outerEnclosure 24
      (leaf2606Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2606RoundedFacts : LeafRoundedFacts 8
    leaf2606Certificate.logOnePlusV leaf2606InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2606InputLogOnePlusV_eq }

private noncomputable def leaf2606Inputs : Inputs :=
  inputsOfCaches globalInput sk220RoundedInputs
    chi178InputQChi innerPair41Input
    leaf2606InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2606LowerChecked :
    lowerCheck 24 leaf2606Box leaf2606Inputs = true := by
  rfl'

private theorem leaf2606CoversExact : CoversExact 8
    leaf2606Box leaf2606Certificate leaf2606InnerLog leaf2606Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk220RoundedFacts chi178RoundedFacts
    innerPair41RoundedFacts leaf2606RoundedFacts (by rfl)

private theorem leaf2606FlatSound : Sound leaf2606Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2606CertificateValid
    leaf2606InnerLogValid leaf2606CoversExact leaf2606LowerChecked

private noncomputable def leaf2607Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (237/64), chiLo := (9/64), chiHi := (37/256) }

private noncomputable def leaf2607Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742371/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434463744) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1630468383/1073741824) }, upper := { exponent := 0, mantissa := (25153/16384) } }, logOuter := sk221LogOuterCertificate, logK := sk221LogKCertificate, logChi := chi175LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871385599/274868927488) } }, logDArg := sk221LogDArgCertificate }

private noncomputable def leaf2607InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2607LocalValidity :
    LeafFacts leaf2607Box leaf2607Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2607Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434463744) }) = true
      norm_num [leaf2607Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2607CertificateValid :
    WideCertificateValid leaf2607Box leaf2607Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk221ValidityFacts chi175ValidityFacts
    leaf2607LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2607CoverageChecked :
    coverageCheck (innerAD leaf2607Box) leaf2607InnerLog = true := by
  rfl'

private theorem leaf2607InnerLogValid :
    leaf2607InnerLog.Valid 8 (innerAD leaf2607Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2607CoverageChecked

private noncomputable def leaf2607InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629231/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2607InputLogOnePlusV_eq :
    leaf2607InputLogOnePlusV = outerEnclosure 24
      (leaf2607Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2607RoundedFacts : LeafRoundedFacts 8
    leaf2607Certificate.logOnePlusV leaf2607InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2607InputLogOnePlusV_eq }

private noncomputable def leaf2607Inputs : Inputs :=
  inputsOfCaches globalInput sk221RoundedInputs
    chi175InputQChi innerPair40Input
    leaf2607InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2607LowerChecked :
    lowerCheck 24 leaf2607Box leaf2607Inputs = true := by
  rfl'

private theorem leaf2607CoversExact : CoversExact 8
    leaf2607Box leaf2607Certificate leaf2607InnerLog leaf2607Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk221RoundedFacts chi175RoundedFacts
    innerPair40RoundedFacts leaf2607RoundedFacts (by rfl)

private theorem leaf2607FlatSound : Sound leaf2607Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2607CertificateValid
    leaf2607InnerLogValid leaf2607CoversExact leaf2607LowerChecked

private noncomputable def leaf2608Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (237/64), kHi := (119/32), chiLo := (9/64), chiHi := (37/256) }

private noncomputable def leaf2608Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742373/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9162461457/9162296320) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1632827533/1073741824) }, upper := { exponent := 0, mantissa := (12595/8192) } }, logOuter := sk222LogOuterCertificate, logK := sk222LogKCertificate, logChi := chi175LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (18324757777/18324592640) } }, logDArg := sk222LogDArgCertificate }

private noncomputable def leaf2608InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2608LocalValidity :
    LeafFacts leaf2608Box leaf2608Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2608Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9162461457/9162296320) }) = true
      norm_num [leaf2608Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2608CertificateValid :
    WideCertificateValid leaf2608Box leaf2608Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk222ValidityFacts chi175ValidityFacts
    leaf2608LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2608CoverageChecked :
    coverageCheck (innerAD leaf2608Box) leaf2608InnerLog = true := by
  rfl'

private theorem leaf2608InnerLogValid :
    leaf2608InnerLog.Valid 8 (innerAD leaf2608Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2608CoverageChecked

private noncomputable def leaf2608InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726827/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf2608InputLogOnePlusV_eq :
    leaf2608InputLogOnePlusV = outerEnclosure 24
      (leaf2608Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2608RoundedFacts : LeafRoundedFacts 8
    leaf2608Certificate.logOnePlusV leaf2608InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2608InputLogOnePlusV_eq }

private noncomputable def leaf2608Inputs : Inputs :=
  inputsOfCaches globalInput sk222RoundedInputs
    chi175InputQChi innerPair40Input
    leaf2608InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2608LowerChecked :
    lowerCheck 24 leaf2608Box leaf2608Inputs = true := by
  rfl'

private theorem leaf2608CoversExact : CoversExact 8
    leaf2608Box leaf2608Certificate leaf2608InnerLog leaf2608Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk222RoundedFacts chi175RoundedFacts
    innerPair40RoundedFacts leaf2608RoundedFacts (by rfl)

private theorem leaf2608FlatSound : Sound leaf2608Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2608CertificateValid
    leaf2608InnerLogValid leaf2608CoversExact leaf2608LowerChecked

private noncomputable def leaf2609Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (237/64), chiLo := (37/256), chiHi := (19/128) }

private noncomputable def leaf2609Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742373/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486868480) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1645933933/1073741824) }, upper := { exponent := 0, mantissa := (12695/8192) } }, logOuter := sk221LogOuterCertificate, logK := sk221LogKCertificate, logChi := chi176LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54974252851/54973736960) } }, logDArg := sk221LogDArgCertificate }

private noncomputable def leaf2609InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2609LocalValidity :
    LeafFacts leaf2609Box leaf2609Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2609Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486868480) }) = true
      norm_num [leaf2609Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2609CertificateValid :
    WideCertificateValid leaf2609Box leaf2609Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk221ValidityFacts chi176ValidityFacts
    leaf2609LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2609CoverageChecked :
    coverageCheck (innerAD leaf2609Box) leaf2609InnerLog = true := by
  rfl'

private theorem leaf2609InnerLogValid :
    leaf2609InnerLog.Valid 8 (innerAD leaf2609Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2609CoverageChecked

private noncomputable def leaf2609InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814619/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2609InputLogOnePlusV_eq :
    leaf2609InputLogOnePlusV = outerEnclosure 24
      (leaf2609Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2609RoundedFacts : LeafRoundedFacts 8
    leaf2609Certificate.logOnePlusV leaf2609InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2609InputLogOnePlusV_eq }

private noncomputable def leaf2609Inputs : Inputs :=
  inputsOfCaches globalInput sk221RoundedInputs
    chi176InputQChi innerPair40Input
    leaf2609InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2609LowerChecked :
    lowerCheck 24 leaf2609Box leaf2609Inputs = true := by
  rfl'

private theorem leaf2609CoversExact : CoversExact 8
    leaf2609Box leaf2609Certificate leaf2609InnerLog leaf2609Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk221RoundedFacts chi176RoundedFacts
    innerPair40RoundedFacts leaf2609RoundedFacts (by rfl)

private theorem leaf2609FlatSound : Sound leaf2609Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2609CertificateValid
    leaf2609InnerLogValid leaf2609CoversExact leaf2609LowerChecked

private noncomputable def leaf2610Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (237/64), kHi := (119/32), chiLo := (37/256), chiHi := (19/128) }

private noncomputable def leaf2610Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742375/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434322944) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1648358615/1073741824) }, upper := { exponent := 0, mantissa := (6357/4096) } }, logOuter := sk222LogOuterCertificate, logK := sk222LogKCertificate, logChi := chi176LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871244799/274868645888) } }, logDArg := sk222LogDArgCertificate }

private noncomputable def leaf2610InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2610LocalValidity :
    LeafFacts leaf2610Box leaf2610Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2610Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434322944) }) = true
      norm_num [leaf2610Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2610CertificateValid :
    WideCertificateValid leaf2610Box leaf2610Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk222ValidityFacts chi176ValidityFacts
    leaf2610LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2610CoverageChecked :
    coverageCheck (innerAD leaf2610Box) leaf2610InnerLog = true := by
  rfl'

private theorem leaf2610InnerLogValid :
    leaf2610InnerLog.Valid 8 (innerAD leaf2610Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2610CoverageChecked

private noncomputable def leaf2610InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629239/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2610InputLogOnePlusV_eq :
    leaf2610InputLogOnePlusV = outerEnclosure 24
      (leaf2610Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2610RoundedFacts : LeafRoundedFacts 8
    leaf2610Certificate.logOnePlusV leaf2610InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2610InputLogOnePlusV_eq }

private noncomputable def leaf2610Inputs : Inputs :=
  inputsOfCaches globalInput sk222RoundedInputs
    chi176InputQChi innerPair40Input
    leaf2610InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2610LowerChecked :
    lowerCheck 24 leaf2610Box leaf2610Inputs = true := by
  rfl'

private theorem leaf2610CoversExact : CoversExact 8
    leaf2610Box leaf2610Certificate leaf2610InnerLog leaf2610Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk222RoundedFacts chi176RoundedFacts
    innerPair40RoundedFacts leaf2610RoundedFacts (by rfl)

private theorem leaf2610FlatSound : Sound leaf2610Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2610CertificateValid
    leaf2610InnerLogValid leaf2610CoversExact leaf2610LowerChecked

private noncomputable def leaf2611Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (239/64), chiLo := (9/64), chiHi := (37/256) }

private noncomputable def leaf2611Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742375/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434425856) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1635186683/1073741824) }, upper := { exponent := 0, mantissa := (25227/16384) } }, logOuter := sk223LogOuterCertificate, logK := sk223LogKCertificate, logChi := chi175LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871347711/274868851712) } }, logDArg := sk223LogDArgCertificate }

private noncomputable def leaf2611InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2611LocalValidity :
    LeafFacts leaf2611Box leaf2611Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2611Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434425856) }) = true
      norm_num [leaf2611Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2611CertificateValid :
    WideCertificateValid leaf2611Box leaf2611Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk223ValidityFacts chi175ValidityFacts
    leaf2611LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2611CoverageChecked :
    coverageCheck (innerAD leaf2611Box) leaf2611InnerLog = true := by
  rfl'

private theorem leaf2611InnerLogValid :
    leaf2611InnerLog.Valid 8 (innerAD leaf2611Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2611CoverageChecked

private noncomputable def leaf2611InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629233/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2611InputLogOnePlusV_eq :
    leaf2611InputLogOnePlusV = outerEnclosure 24
      (leaf2611Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2611RoundedFacts : LeafRoundedFacts 8
    leaf2611Certificate.logOnePlusV leaf2611InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2611InputLogOnePlusV_eq }

private noncomputable def leaf2611Inputs : Inputs :=
  inputsOfCaches globalInput sk223RoundedInputs
    chi175InputQChi innerPair40Input
    leaf2611InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2611LowerChecked :
    lowerCheck 24 leaf2611Box leaf2611Inputs = true := by
  rfl'

private theorem leaf2611CoversExact : CoversExact 8
    leaf2611Box leaf2611Certificate leaf2611InnerLog leaf2611Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk223RoundedFacts chi175RoundedFacts
    innerPair40RoundedFacts leaf2611RoundedFacts (by rfl)

private theorem leaf2611FlatSound : Sound leaf2611Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2611CertificateValid
    leaf2611InnerLogValid leaf2611CoversExact leaf2611LowerChecked

private noncomputable def leaf2612Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (239/64), kHi := (15/4), chiLo := (9/64), chiHi := (37/256) }

private noncomputable def leaf2612Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742377/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434406912) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1637545833/1073741824) }, upper := { exponent := 0, mantissa := (1579/1024) } }, logOuter := sk224LogOuterCertificate, logK := sk224LogKCertificate, logChi := chi175LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871328767/274868813824) } }, logDArg := sk224LogDArgCertificate }

private noncomputable def leaf2612InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2612LocalValidity :
    LeafFacts leaf2612Box leaf2612Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2612Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434406912) }) = true
      norm_num [leaf2612Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2612CertificateValid :
    WideCertificateValid leaf2612Box leaf2612Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk224ValidityFacts chi175ValidityFacts
    leaf2612LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2612CoverageChecked :
    coverageCheck (innerAD leaf2612Box) leaf2612InnerLog = true := by
  rfl'

private theorem leaf2612InnerLogValid :
    leaf2612InnerLog.Valid 8 (innerAD leaf2612Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2612CoverageChecked

private noncomputable def leaf2612InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814617/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2612InputLogOnePlusV_eq :
    leaf2612InputLogOnePlusV = outerEnclosure 24
      (leaf2612Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2612RoundedFacts : LeafRoundedFacts 8
    leaf2612Certificate.logOnePlusV leaf2612InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2612InputLogOnePlusV_eq }

private noncomputable def leaf2612Inputs : Inputs :=
  inputsOfCaches globalInput sk224RoundedInputs
    chi175InputQChi innerPair40Input
    leaf2612InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2612LowerChecked :
    lowerCheck 24 leaf2612Box leaf2612Inputs = true := by
  rfl'

private theorem leaf2612CoversExact : CoversExact 8
    leaf2612Box leaf2612Certificate leaf2612InnerLog leaf2612Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk224RoundedFacts chi175RoundedFacts
    innerPair40RoundedFacts leaf2612RoundedFacts (by rfl)

private theorem leaf2612FlatSound : Sound leaf2612Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2612CertificateValid
    leaf2612InnerLogValid leaf2612CoversExact leaf2612LowerChecked

private noncomputable def leaf2613Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (239/64), chiLo := (37/256), chiHi := (19/128) }

private noncomputable def leaf2613Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742377/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45811434496) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1650783297/1073741824) }, upper := { exponent := 0, mantissa := (12733/8192) } }, logOuter := sk223LogOuterCertificate, logK := sk223LogKCertificate, logChi := chi176LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623741781/91622868992) } }, logDArg := sk223LogDArgCertificate }

private noncomputable def leaf2613InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2613LocalValidity :
    LeafFacts leaf2613Box leaf2613Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2613Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45811434496) }) = true
      norm_num [leaf2613Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2613CertificateValid :
    WideCertificateValid leaf2613Box leaf2613Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk223ValidityFacts chi176ValidityFacts
    leaf2613LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2613CoverageChecked :
    coverageCheck (innerAD leaf2613Box) leaf2613InnerLog = true := by
  rfl'

private theorem leaf2613InnerLogValid :
    leaf2613InnerLog.Valid 8 (innerAD leaf2613Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2613CoverageChecked

private noncomputable def leaf2613InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629241/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2613InputLogOnePlusV_eq :
    leaf2613InputLogOnePlusV = outerEnclosure 24
      (leaf2613Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2613RoundedFacts : LeafRoundedFacts 8
    leaf2613Certificate.logOnePlusV leaf2613InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2613InputLogOnePlusV_eq }

private noncomputable def leaf2613Inputs : Inputs :=
  inputsOfCaches globalInput sk223RoundedInputs
    chi176InputQChi innerPair40Input
    leaf2613InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2613LowerChecked :
    lowerCheck 24 leaf2613Box leaf2613Inputs = true := by
  rfl'

private theorem leaf2613CoversExact : CoversExact 8
    leaf2613Box leaf2613Certificate leaf2613InnerLog leaf2613Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk223RoundedFacts chi176RoundedFacts
    innerPair40RoundedFacts leaf2613RoundedFacts (by rfl)

private theorem leaf2613FlatSound : Sound leaf2613Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2613CertificateValid
    leaf2613InnerLogValid leaf2613CoversExact leaf2613LowerChecked

private noncomputable def leaf2614Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (239/64), kHi := (15/4), chiLo := (37/256), chiHi := (19/128) }

private noncomputable def leaf2614Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742379/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434284032) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1653207979/1073741824) }, upper := { exponent := 0, mantissa := (797/512) } }, logOuter := sk224LogOuterCertificate, logK := sk224LogKCertificate, logChi := chi176LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871205887/274868568064) } }, logDArg := sk224LogDArgCertificate }

private noncomputable def leaf2614InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2614LocalValidity :
    LeafFacts leaf2614Box leaf2614Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2614Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434284032) }) = true
      norm_num [leaf2614Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2614CertificateValid :
    WideCertificateValid leaf2614Box leaf2614Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk224ValidityFacts chi176ValidityFacts
    leaf2614LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2614CoverageChecked :
    coverageCheck (innerAD leaf2614Box) leaf2614InnerLog = true := by
  rfl'

private theorem leaf2614InnerLogValid :
    leaf2614InnerLog.Valid 8 (innerAD leaf2614Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2614CoverageChecked

private noncomputable def leaf2614InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814621/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2614InputLogOnePlusV_eq :
    leaf2614InputLogOnePlusV = outerEnclosure 24
      (leaf2614Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2614RoundedFacts : LeafRoundedFacts 8
    leaf2614Certificate.logOnePlusV leaf2614InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2614InputLogOnePlusV_eq }

private noncomputable def leaf2614Inputs : Inputs :=
  inputsOfCaches globalInput sk224RoundedInputs
    chi176InputQChi innerPair40Input
    leaf2614InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2614LowerChecked :
    lowerCheck 24 leaf2614Box leaf2614Inputs = true := by
  rfl'

private theorem leaf2614CoversExact : CoversExact 8
    leaf2614Box leaf2614Certificate leaf2614InnerLog leaf2614Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk224RoundedFacts chi176RoundedFacts
    innerPair40RoundedFacts leaf2614RoundedFacts (by rfl)

private theorem leaf2614FlatSound : Sound leaf2614Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2614CertificateValid
    leaf2614InnerLogValid leaf2614CoversExact leaf2614LowerChecked

private noncomputable def leaf2615Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (237/64), chiLo := (19/128), chiHi := (39/256) }

private noncomputable def leaf2615Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742375/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434221056) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1661399483/1073741824) }, upper := { exponent := 0, mantissa := (25627/16384) } }, logOuter := sk221LogOuterCertificate, logK := sk221LogKCertificate, logChi := chi177LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871142911/274868442112) } }, logDArg := sk221LogDArgCertificate }

private noncomputable def leaf2615InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf2615LocalValidity :
    LeafFacts leaf2615Box leaf2615Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2615Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434221056) }) = true
      norm_num [leaf2615Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2615CertificateValid :
    WideCertificateValid leaf2615Box leaf2615Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk221ValidityFacts chi177ValidityFacts
    leaf2615LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2615CoverageChecked :
    coverageCheck (innerAD leaf2615Box) leaf2615InnerLog = true := by
  rfl'

private theorem leaf2615InnerLogValid :
    leaf2615InnerLog.Valid 8 (innerAD leaf2615Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf2615CoverageChecked

private noncomputable def leaf2615InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814623/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2615InputLogOnePlusV_eq :
    leaf2615InputLogOnePlusV = outerEnclosure 24
      (leaf2615Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2615RoundedFacts : LeafRoundedFacts 8
    leaf2615Certificate.logOnePlusV leaf2615InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2615InputLogOnePlusV_eq }

private noncomputable def leaf2615Inputs : Inputs :=
  inputsOfCaches globalInput sk221RoundedInputs
    chi177InputQChi innerPair41Input
    leaf2615InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2615LowerChecked :
    lowerCheck 24 leaf2615Box leaf2615Inputs = true := by
  rfl'

private theorem leaf2615CoversExact : CoversExact 8
    leaf2615Box leaf2615Certificate leaf2615InnerLog leaf2615Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk221RoundedFacts chi177RoundedFacts
    innerPair41RoundedFacts leaf2615RoundedFacts (by rfl)

private theorem leaf2615FlatSound : Sound leaf2615Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2615CertificateValid
    leaf2615InnerLogValid leaf2615CoversExact leaf2615LowerChecked

private noncomputable def leaf2616Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (237/64), kHi := (119/32), chiLo := (19/128), chiHi := (39/256) }

private noncomputable def leaf2616Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742377/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434201088) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1663889697/1073741824) }, upper := { exponent := 0, mantissa := (12833/8192) } }, logOuter := sk222LogOuterCertificate, logK := sk222LogKCertificate, logChi := chi177LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871122943/274868402176) } }, logDArg := sk222LogDArgCertificate }

private noncomputable def leaf2616InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf2616LocalValidity :
    LeafFacts leaf2616Box leaf2616Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2616Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434201088) }) = true
      norm_num [leaf2616Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2616CertificateValid :
    WideCertificateValid leaf2616Box leaf2616Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk222ValidityFacts chi177ValidityFacts
    leaf2616LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2616CoverageChecked :
    coverageCheck (innerAD leaf2616Box) leaf2616InnerLog = true := by
  rfl'

private theorem leaf2616InnerLogValid :
    leaf2616InnerLog.Valid 8 (innerAD leaf2616Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf2616CoverageChecked

private noncomputable def leaf2616InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629247/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2616InputLogOnePlusV_eq :
    leaf2616InputLogOnePlusV = outerEnclosure 24
      (leaf2616Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2616RoundedFacts : LeafRoundedFacts 8
    leaf2616Certificate.logOnePlusV leaf2616InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2616InputLogOnePlusV_eq }

private noncomputable def leaf2616Inputs : Inputs :=
  inputsOfCaches globalInput sk222RoundedInputs
    chi177InputQChi innerPair41Input
    leaf2616InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2616LowerChecked :
    lowerCheck 24 leaf2616Box leaf2616Inputs = true := by
  rfl'

private theorem leaf2616CoversExact : CoversExact 8
    leaf2616Box leaf2616Certificate leaf2616InnerLog leaf2616Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk222RoundedFacts chi177RoundedFacts
    innerPair41RoundedFacts leaf2616RoundedFacts (by rfl)

private theorem leaf2616FlatSound : Sound leaf2616Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2616CertificateValid
    leaf2616InnerLogValid leaf2616CoversExact leaf2616LowerChecked

private noncomputable def leaf2617Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (237/64), chiLo := (39/256), chiHi := (5/32) }

private noncomputable def leaf2617Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742377/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434099712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1676865033/1073741824) }, upper := { exponent := 0, mantissa := (3233/2048) } }, logOuter := sk221LogOuterCertificate, logK := sk221LogKCertificate, logChi := chi178LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871021567/274868199424) } }, logDArg := sk221LogDArgCertificate }

private noncomputable def leaf2617InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf2617LocalValidity :
    LeafFacts leaf2617Box leaf2617Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2617Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434099712) }) = true
      norm_num [leaf2617Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2617CertificateValid :
    WideCertificateValid leaf2617Box leaf2617Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk221ValidityFacts chi178ValidityFacts
    leaf2617LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2617CoverageChecked :
    coverageCheck (innerAD leaf2617Box) leaf2617InnerLog = true := by
  rfl'

private theorem leaf2617InnerLogValid :
    leaf2617InnerLog.Valid 8 (innerAD leaf2617Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf2617CoverageChecked

private noncomputable def leaf2617InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629253/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2617InputLogOnePlusV_eq :
    leaf2617InputLogOnePlusV = outerEnclosure 24
      (leaf2617Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2617RoundedFacts : LeafRoundedFacts 8
    leaf2617Certificate.logOnePlusV leaf2617InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2617InputLogOnePlusV_eq }

private noncomputable def leaf2617Inputs : Inputs :=
  inputsOfCaches globalInput sk221RoundedInputs
    chi178InputQChi innerPair41Input
    leaf2617InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2617LowerChecked :
    lowerCheck 24 leaf2617Box leaf2617Inputs = true := by
  rfl'

private theorem leaf2617CoversExact : CoversExact 8
    leaf2617Box leaf2617Certificate leaf2617InnerLog leaf2617Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk221RoundedFacts chi178RoundedFacts
    innerPair41RoundedFacts leaf2617RoundedFacts (by rfl)

private theorem leaf2617FlatSound : Sound leaf2617Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2617CertificateValid
    leaf2617InnerLogValid leaf2617CoversExact leaf2617LowerChecked

private noncomputable def leaf2618Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (237/64), kHi := (119/32), chiLo := (39/256), chiHi := (5/32) }

private noncomputable def leaf2618Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742379/1073741824) }, vSqrt := { lower := (8191/8192), upper := (15270769095/15270453248) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1679420779/1073741824) }, upper := { exponent := 0, mantissa := (1619/1024) } }, logOuter := sk222LogOuterCertificate, logK := sk222LogKCertificate, logChi := chi178LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (30541222343/30540906496) } }, logDArg := sk222LogDArgCertificate }

private noncomputable def leaf2618InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2618LocalValidity :
    LeafFacts leaf2618Box leaf2618Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2618Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (15270769095/15270453248) }) = true
      norm_num [leaf2618Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2618CertificateValid :
    WideCertificateValid leaf2618Box leaf2618Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk222ValidityFacts chi178ValidityFacts
    leaf2618LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2618CoverageChecked :
    coverageCheck (innerAD leaf2618Box) leaf2618InnerLog = true := by
  rfl'

private theorem leaf2618InnerLogValid :
    leaf2618InnerLog.Valid 8 (innerAD leaf2618Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2618CoverageChecked

private noncomputable def leaf2618InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814627/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2618InputLogOnePlusV_eq :
    leaf2618InputLogOnePlusV = outerEnclosure 24
      (leaf2618Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2618RoundedFacts : LeafRoundedFacts 8
    leaf2618Certificate.logOnePlusV leaf2618InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2618InputLogOnePlusV_eq }

private noncomputable def leaf2618Inputs : Inputs :=
  inputsOfCaches globalInput sk222RoundedInputs
    chi178InputQChi innerPair50Input
    leaf2618InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2618LowerChecked :
    lowerCheck 24 leaf2618Box leaf2618Inputs = true := by
  rfl'

private theorem leaf2618CoversExact : CoversExact 8
    leaf2618Box leaf2618Certificate leaf2618InnerLog leaf2618Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk222RoundedFacts chi178RoundedFacts
    innerPair50RoundedFacts leaf2618RoundedFacts (by rfl)

private theorem leaf2618FlatSound : Sound leaf2618Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2618CertificateValid
    leaf2618InnerLogValid leaf2618CoversExact leaf2618LowerChecked

private noncomputable def leaf2619Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (239/64), chiLo := (19/128), chiHi := (39/256) }

private noncomputable def leaf2619Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742379/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486836224) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1666379911/1073741824) }, upper := { exponent := 0, mantissa := (25705/16384) } }, logOuter := sk223LogOuterCertificate, logK := sk223LogKCertificate, logChi := chi177LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54974220595/54973672448) } }, logDArg := sk223LogDArgCertificate }

private noncomputable def leaf2619InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf2619LocalValidity :
    LeafFacts leaf2619Box leaf2619Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2619Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486836224) }) = true
      norm_num [leaf2619Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2619CertificateValid :
    WideCertificateValid leaf2619Box leaf2619Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk223ValidityFacts chi177ValidityFacts
    leaf2619LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2619CoverageChecked :
    coverageCheck (innerAD leaf2619Box) leaf2619InnerLog = true := by
  rfl'

private theorem leaf2619InnerLogValid :
    leaf2619InnerLog.Valid 8 (innerAD leaf2619Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf2619CoverageChecked

private noncomputable def leaf2619InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (181707/262144) }

set_option maxRecDepth 1000000 in
private theorem leaf2619InputLogOnePlusV_eq :
    leaf2619InputLogOnePlusV = outerEnclosure 24
      (leaf2619Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2619RoundedFacts : LeafRoundedFacts 8
    leaf2619Certificate.logOnePlusV leaf2619InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2619InputLogOnePlusV_eq }

private noncomputable def leaf2619Inputs : Inputs :=
  inputsOfCaches globalInput sk223RoundedInputs
    chi177InputQChi innerPair41Input
    leaf2619InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2619LowerChecked :
    lowerCheck 24 leaf2619Box leaf2619Inputs = true := by
  rfl'

private theorem leaf2619CoversExact : CoversExact 8
    leaf2619Box leaf2619Certificate leaf2619InnerLog leaf2619Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk223RoundedFacts chi177RoundedFacts
    innerPair41RoundedFacts leaf2619RoundedFacts (by rfl)

private theorem leaf2619FlatSound : Sound leaf2619Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2619CertificateValid
    leaf2619InnerLogValid leaf2619CoversExact leaf2619LowerChecked

private noncomputable def leaf2620Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (239/64), kHi := (15/4), chiLo := (19/128), chiHi := (39/256) }

private noncomputable def leaf2620Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742381/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434161152) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1668870125/1073741824) }, upper := { exponent := 0, mantissa := (1609/1024) } }, logOuter := sk224LogOuterCertificate, logK := sk224LogKCertificate, logChi := chi177LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871083007/274868322304) } }, logDArg := sk224LogDArgCertificate }

private noncomputable def leaf2620InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf2620LocalValidity :
    LeafFacts leaf2620Box leaf2620Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2620Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434161152) }) = true
      norm_num [leaf2620Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2620CertificateValid :
    WideCertificateValid leaf2620Box leaf2620Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk224ValidityFacts chi177ValidityFacts
    leaf2620LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2620CoverageChecked :
    coverageCheck (innerAD leaf2620Box) leaf2620InnerLog = true := by
  rfl'

private theorem leaf2620InnerLogValid :
    leaf2620InnerLog.Valid 8 (innerAD leaf2620Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf2620CoverageChecked

private noncomputable def leaf2620InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629249/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2620InputLogOnePlusV_eq :
    leaf2620InputLogOnePlusV = outerEnclosure 24
      (leaf2620Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2620RoundedFacts : LeafRoundedFacts 8
    leaf2620Certificate.logOnePlusV leaf2620InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2620InputLogOnePlusV_eq }

private noncomputable def leaf2620Inputs : Inputs :=
  inputsOfCaches globalInput sk224RoundedInputs
    chi177InputQChi innerPair41Input
    leaf2620InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2620LowerChecked :
    lowerCheck 24 leaf2620Box leaf2620Inputs = true := by
  rfl'

private theorem leaf2620CoversExact : CoversExact 8
    leaf2620Box leaf2620Certificate leaf2620InnerLog leaf2620Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk224RoundedFacts chi177RoundedFacts
    innerPair41RoundedFacts leaf2620RoundedFacts (by rfl)

private theorem leaf2620FlatSound : Sound leaf2620Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2620CertificateValid
    leaf2620InnerLogValid leaf2620CoversExact leaf2620LowerChecked

private noncomputable def leaf2621Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (239/64), chiLo := (39/256), chiHi := (5/32) }

private noncomputable def leaf2621Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742381/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434058752) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1681976525/1073741824) }, upper := { exponent := 0, mantissa := (3243/2048) } }, logOuter := sk223LogOuterCertificate, logK := sk223LogKCertificate, logChi := chi178LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870980607/274868117504) } }, logDArg := sk223LogDArgCertificate }

private noncomputable def leaf2621InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2621LocalValidity :
    LeafFacts leaf2621Box leaf2621Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2621Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434058752) }) = true
      norm_num [leaf2621Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2621CertificateValid :
    WideCertificateValid leaf2621Box leaf2621Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk223ValidityFacts chi178ValidityFacts
    leaf2621LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2621CoverageChecked :
    coverageCheck (innerAD leaf2621Box) leaf2621InnerLog = true := by
  rfl'

private theorem leaf2621InnerLogValid :
    leaf2621InnerLog.Valid 8 (innerAD leaf2621Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2621CoverageChecked

private noncomputable def leaf2621InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629255/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2621InputLogOnePlusV_eq :
    leaf2621InputLogOnePlusV = outerEnclosure 24
      (leaf2621Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2621RoundedFacts : LeafRoundedFacts 8
    leaf2621Certificate.logOnePlusV leaf2621InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2621InputLogOnePlusV_eq }

private noncomputable def leaf2621Inputs : Inputs :=
  inputsOfCaches globalInput sk223RoundedInputs
    chi178InputQChi innerPair50Input
    leaf2621InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2621LowerChecked :
    lowerCheck 24 leaf2621Box leaf2621Inputs = true := by
  rfl'

private theorem leaf2621CoversExact : CoversExact 8
    leaf2621Box leaf2621Certificate leaf2621InnerLog leaf2621Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk223RoundedFacts chi178RoundedFacts
    innerPair50RoundedFacts leaf2621RoundedFacts (by rfl)

private theorem leaf2621FlatSound : Sound leaf2621Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2621CertificateValid
    leaf2621InnerLogValid leaf2621CoversExact leaf2621LowerChecked

private noncomputable def leaf2622Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (239/64), kHi := (15/4), chiLo := (39/256), chiHi := (5/32) }

private noncomputable def leaf2622Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742383/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434038272) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1684532271/1073741824) }, upper := { exponent := 0, mantissa := (203/128) } }, logOuter := sk224LogOuterCertificate, logK := sk224LogKCertificate, logChi := chi178LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870960127/274868076544) } }, logDArg := sk224LogDArgCertificate }

private noncomputable def leaf2622InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2622LocalValidity :
    LeafFacts leaf2622Box leaf2622Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2622Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434038272) }) = true
      norm_num [leaf2622Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2622CertificateValid :
    WideCertificateValid leaf2622Box leaf2622Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk224ValidityFacts chi178ValidityFacts
    leaf2622LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2622CoverageChecked :
    coverageCheck (innerAD leaf2622Box) leaf2622InnerLog = true := by
  rfl'

private theorem leaf2622InnerLogValid :
    leaf2622InnerLog.Valid 8 (innerAD leaf2622Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2622CoverageChecked

private noncomputable def leaf2622InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629257/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2622InputLogOnePlusV_eq :
    leaf2622InputLogOnePlusV = outerEnclosure 24
      (leaf2622Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2622RoundedFacts : LeafRoundedFacts 8
    leaf2622Certificate.logOnePlusV leaf2622InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2622InputLogOnePlusV_eq }

private noncomputable def leaf2622Inputs : Inputs :=
  inputsOfCaches globalInput sk224RoundedInputs
    chi178InputQChi innerPair50Input
    leaf2622InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2622LowerChecked :
    lowerCheck 24 leaf2622Box leaf2622Inputs = true := by
  rfl'

private theorem leaf2622CoversExact : CoversExact 8
    leaf2622Box leaf2622Certificate leaf2622InnerLog leaf2622Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk224RoundedFacts chi178RoundedFacts
    innerPair50RoundedFacts leaf2622RoundedFacts (by rfl)

private theorem leaf2622FlatSound : Sound leaf2622Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2622CertificateValid
    leaf2622InnerLogValid leaf2622CoversExact leaf2622LowerChecked

private noncomputable def component55Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (1/8), chiHi := (17/128) }

set_option maxRecDepth 1000000 in
private theorem component55Node0_sound : Sound component55Node0Box :=
  sound_of_literal_split component55Node0Box leaf2562Box leaf2563Box
    .chi (33/256) (by rfl) (by rfl)
    leaf2562FlatSound leaf2563FlatSound

private noncomputable def component55Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (33/256), chiHi := (17/128) }

set_option maxRecDepth 1000000 in
private theorem component55Node1_sound : Sound component55Node1Box :=
  sound_of_literal_split component55Node1Box leaf2565Box leaf2566Box
    .chi (67/512) (by rfl) (by rfl)
    leaf2565FlatSound leaf2566FlatSound

private noncomputable def component55Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (1/8), chiHi := (17/128) }

set_option maxRecDepth 1000000 in
private theorem component55Node2_sound : Sound component55Node2Box :=
  sound_of_literal_split component55Node2Box leaf2564Box component55Node1Box
    .chi (33/256) (by rfl) (by rfl)
    leaf2564FlatSound component55Node1_sound

private noncomputable def component55Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (1/8), chiHi := (17/128) }

set_option maxRecDepth 1000000 in
private theorem component55Node3_sound : Sound component55Node3Box :=
  sound_of_literal_split component55Node3Box component55Node0Box component55Node2Box
    .k (117/32) (by rfl) (by rfl)
    component55Node0_sound component55Node2_sound

private noncomputable def component55Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (17/128), chiHi := (35/256) }

set_option maxRecDepth 1000000 in
private theorem component55Node4_sound : Sound component55Node4Box :=
  sound_of_literal_split component55Node4Box leaf2567Box leaf2568Box
    .k (233/64) (by rfl) (by rfl)
    leaf2567FlatSound leaf2568FlatSound

private noncomputable def component55Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (35/256), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component55Node5_sound : Sound component55Node5Box :=
  sound_of_literal_split component55Node5Box leaf2569Box leaf2570Box
    .k (233/64) (by rfl) (by rfl)
    leaf2569FlatSound leaf2570FlatSound

private noncomputable def component55Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (17/128), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component55Node6_sound : Sound component55Node6Box :=
  sound_of_literal_split component55Node6Box component55Node4Box component55Node5Box
    .chi (35/256) (by rfl) (by rfl)
    component55Node4_sound component55Node5_sound

private noncomputable def component55Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (17/128), chiHi := (35/256) }

set_option maxRecDepth 1000000 in
private theorem component55Node7_sound : Sound component55Node7Box :=
  sound_of_literal_split component55Node7Box leaf2571Box leaf2572Box
    .k (235/64) (by rfl) (by rfl)
    leaf2571FlatSound leaf2572FlatSound

private noncomputable def component55Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (35/256), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component55Node8_sound : Sound component55Node8Box :=
  sound_of_literal_split component55Node8Box leaf2573Box leaf2574Box
    .k (235/64) (by rfl) (by rfl)
    leaf2573FlatSound leaf2574FlatSound

private noncomputable def component55Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (17/128), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component55Node9_sound : Sound component55Node9Box :=
  sound_of_literal_split component55Node9Box component55Node7Box component55Node8Box
    .chi (35/256) (by rfl) (by rfl)
    component55Node7_sound component55Node8_sound

private noncomputable def component55Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (17/128), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component55Node10_sound : Sound component55Node10Box :=
  sound_of_literal_split component55Node10Box component55Node6Box component55Node9Box
    .k (117/32) (by rfl) (by rfl)
    component55Node6_sound component55Node9_sound

private noncomputable def component55Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (1/8), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component55Node11_sound : Sound component55Node11Box :=
  sound_of_literal_split component55Node11Box component55Node3Box component55Node10Box
    .chi (17/128) (by rfl) (by rfl)
    component55Node3_sound component55Node10_sound

private noncomputable def component55Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (1/8), chiHi := (33/256) }

set_option maxRecDepth 1000000 in
private theorem component55Node12_sound : Sound component55Node12Box :=
  sound_of_literal_split component55Node12Box leaf2575Box leaf2576Box
    .chi (65/512) (by rfl) (by rfl)
    leaf2575FlatSound leaf2576FlatSound

private noncomputable def component55Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (33/256), chiHi := (17/128) }

set_option maxRecDepth 1000000 in
private theorem component55Node13_sound : Sound component55Node13Box :=
  sound_of_literal_split component55Node13Box leaf2577Box leaf2578Box
    .chi (67/512) (by rfl) (by rfl)
    leaf2577FlatSound leaf2578FlatSound

private noncomputable def component55Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (1/8), chiHi := (17/128) }

set_option maxRecDepth 1000000 in
private theorem component55Node14_sound : Sound component55Node14Box :=
  sound_of_literal_split component55Node14Box component55Node12Box component55Node13Box
    .chi (33/256) (by rfl) (by rfl)
    component55Node12_sound component55Node13_sound

private noncomputable def component55Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (1/8), chiHi := (33/256) }

set_option maxRecDepth 1000000 in
private theorem component55Node15_sound : Sound component55Node15Box :=
  sound_of_literal_split component55Node15Box leaf2579Box leaf2580Box
    .chi (65/512) (by rfl) (by rfl)
    leaf2579FlatSound leaf2580FlatSound

private noncomputable def component55Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (33/256), chiHi := (17/128) }

set_option maxRecDepth 1000000 in
private theorem component55Node16_sound : Sound component55Node16Box :=
  sound_of_literal_split component55Node16Box leaf2581Box leaf2582Box
    .chi (67/512) (by rfl) (by rfl)
    leaf2581FlatSound leaf2582FlatSound

private noncomputable def component55Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (1/8), chiHi := (17/128) }

set_option maxRecDepth 1000000 in
private theorem component55Node17_sound : Sound component55Node17Box :=
  sound_of_literal_split component55Node17Box component55Node15Box component55Node16Box
    .chi (33/256) (by rfl) (by rfl)
    component55Node15_sound component55Node16_sound

private noncomputable def component55Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (1/8), chiHi := (17/128) }

set_option maxRecDepth 1000000 in
private theorem component55Node18_sound : Sound component55Node18Box :=
  sound_of_literal_split component55Node18Box component55Node14Box component55Node17Box
    .k (119/32) (by rfl) (by rfl)
    component55Node14_sound component55Node17_sound

private noncomputable def component55Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (17/128), chiHi := (35/256) }

set_option maxRecDepth 1000000 in
private theorem component55Node19_sound : Sound component55Node19Box :=
  sound_of_literal_split component55Node19Box leaf2583Box leaf2584Box
    .k (237/64) (by rfl) (by rfl)
    leaf2583FlatSound leaf2584FlatSound

private noncomputable def component55Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (35/256), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component55Node20_sound : Sound component55Node20Box :=
  sound_of_literal_split component55Node20Box leaf2585Box leaf2586Box
    .k (237/64) (by rfl) (by rfl)
    leaf2585FlatSound leaf2586FlatSound

private noncomputable def component55Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (17/128), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component55Node21_sound : Sound component55Node21Box :=
  sound_of_literal_split component55Node21Box component55Node19Box component55Node20Box
    .chi (35/256) (by rfl) (by rfl)
    component55Node19_sound component55Node20_sound

private noncomputable def component55Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (17/128), chiHi := (35/256) }

set_option maxRecDepth 1000000 in
private theorem component55Node22_sound : Sound component55Node22Box :=
  sound_of_literal_split component55Node22Box leaf2587Box leaf2588Box
    .k (239/64) (by rfl) (by rfl)
    leaf2587FlatSound leaf2588FlatSound

private noncomputable def component55Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (35/256), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component55Node23_sound : Sound component55Node23Box :=
  sound_of_literal_split component55Node23Box leaf2589Box leaf2590Box
    .k (239/64) (by rfl) (by rfl)
    leaf2589FlatSound leaf2590FlatSound

private noncomputable def component55Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (17/128), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component55Node24_sound : Sound component55Node24Box :=
  sound_of_literal_split component55Node24Box component55Node22Box component55Node23Box
    .chi (35/256) (by rfl) (by rfl)
    component55Node22_sound component55Node23_sound

private noncomputable def component55Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (17/128), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component55Node25_sound : Sound component55Node25Box :=
  sound_of_literal_split component55Node25Box component55Node21Box component55Node24Box
    .k (119/32) (by rfl) (by rfl)
    component55Node21_sound component55Node24_sound

private noncomputable def component55Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (1/8), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component55Node26_sound : Sound component55Node26Box :=
  sound_of_literal_split component55Node26Box component55Node18Box component55Node25Box
    .chi (17/128) (by rfl) (by rfl)
    component55Node18_sound component55Node25_sound

private noncomputable def component55Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (1/8), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component55Node27_sound : Sound component55Node27Box :=
  sound_of_literal_split component55Node27Box component55Node11Box component55Node26Box
    .k (59/16) (by rfl) (by rfl)
    component55Node11_sound component55Node26_sound

private noncomputable def component55Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (9/64), chiHi := (37/256) }

set_option maxRecDepth 1000000 in
private theorem component55Node28_sound : Sound component55Node28Box :=
  sound_of_literal_split component55Node28Box leaf2591Box leaf2592Box
    .k (233/64) (by rfl) (by rfl)
    leaf2591FlatSound leaf2592FlatSound

private noncomputable def component55Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (37/256), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component55Node29_sound : Sound component55Node29Box :=
  sound_of_literal_split component55Node29Box leaf2593Box leaf2594Box
    .k (233/64) (by rfl) (by rfl)
    leaf2593FlatSound leaf2594FlatSound

private noncomputable def component55Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (9/64), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component55Node30_sound : Sound component55Node30Box :=
  sound_of_literal_split component55Node30Box component55Node28Box component55Node29Box
    .chi (37/256) (by rfl) (by rfl)
    component55Node28_sound component55Node29_sound

private noncomputable def component55Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (9/64), chiHi := (37/256) }

set_option maxRecDepth 1000000 in
private theorem component55Node31_sound : Sound component55Node31Box :=
  sound_of_literal_split component55Node31Box leaf2595Box leaf2596Box
    .k (235/64) (by rfl) (by rfl)
    leaf2595FlatSound leaf2596FlatSound

private noncomputable def component55Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (37/256), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component55Node32_sound : Sound component55Node32Box :=
  sound_of_literal_split component55Node32Box leaf2597Box leaf2598Box
    .k (235/64) (by rfl) (by rfl)
    leaf2597FlatSound leaf2598FlatSound

private noncomputable def component55Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (9/64), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component55Node33_sound : Sound component55Node33Box :=
  sound_of_literal_split component55Node33Box component55Node31Box component55Node32Box
    .chi (37/256) (by rfl) (by rfl)
    component55Node31_sound component55Node32_sound

private noncomputable def component55Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (9/64), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component55Node34_sound : Sound component55Node34Box :=
  sound_of_literal_split component55Node34Box component55Node30Box component55Node33Box
    .k (117/32) (by rfl) (by rfl)
    component55Node30_sound component55Node33_sound

private noncomputable def component55Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (19/128), chiHi := (39/256) }

set_option maxRecDepth 1000000 in
private theorem component55Node35_sound : Sound component55Node35Box :=
  sound_of_literal_split component55Node35Box leaf2599Box leaf2600Box
    .k (233/64) (by rfl) (by rfl)
    leaf2599FlatSound leaf2600FlatSound

private noncomputable def component55Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (39/256), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component55Node36_sound : Sound component55Node36Box :=
  sound_of_literal_split component55Node36Box leaf2601Box leaf2602Box
    .k (233/64) (by rfl) (by rfl)
    leaf2601FlatSound leaf2602FlatSound

private noncomputable def component55Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (19/128), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component55Node37_sound : Sound component55Node37Box :=
  sound_of_literal_split component55Node37Box component55Node35Box component55Node36Box
    .chi (39/256) (by rfl) (by rfl)
    component55Node35_sound component55Node36_sound

private noncomputable def component55Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (19/128), chiHi := (39/256) }

set_option maxRecDepth 1000000 in
private theorem component55Node38_sound : Sound component55Node38Box :=
  sound_of_literal_split component55Node38Box leaf2603Box leaf2604Box
    .k (235/64) (by rfl) (by rfl)
    leaf2603FlatSound leaf2604FlatSound

private noncomputable def component55Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (39/256), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component55Node39_sound : Sound component55Node39Box :=
  sound_of_literal_split component55Node39Box leaf2605Box leaf2606Box
    .k (235/64) (by rfl) (by rfl)
    leaf2605FlatSound leaf2606FlatSound

private noncomputable def component55Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (19/128), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component55Node40_sound : Sound component55Node40Box :=
  sound_of_literal_split component55Node40Box component55Node38Box component55Node39Box
    .chi (39/256) (by rfl) (by rfl)
    component55Node38_sound component55Node39_sound

private noncomputable def component55Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (19/128), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component55Node41_sound : Sound component55Node41Box :=
  sound_of_literal_split component55Node41Box component55Node37Box component55Node40Box
    .k (117/32) (by rfl) (by rfl)
    component55Node37_sound component55Node40_sound

private noncomputable def component55Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (9/64), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component55Node42_sound : Sound component55Node42Box :=
  sound_of_literal_split component55Node42Box component55Node34Box component55Node41Box
    .chi (19/128) (by rfl) (by rfl)
    component55Node34_sound component55Node41_sound

private noncomputable def component55Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (9/64), chiHi := (37/256) }

set_option maxRecDepth 1000000 in
private theorem component55Node43_sound : Sound component55Node43Box :=
  sound_of_literal_split component55Node43Box leaf2607Box leaf2608Box
    .k (237/64) (by rfl) (by rfl)
    leaf2607FlatSound leaf2608FlatSound

private noncomputable def component55Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (37/256), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component55Node44_sound : Sound component55Node44Box :=
  sound_of_literal_split component55Node44Box leaf2609Box leaf2610Box
    .k (237/64) (by rfl) (by rfl)
    leaf2609FlatSound leaf2610FlatSound

private noncomputable def component55Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (9/64), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component55Node45_sound : Sound component55Node45Box :=
  sound_of_literal_split component55Node45Box component55Node43Box component55Node44Box
    .chi (37/256) (by rfl) (by rfl)
    component55Node43_sound component55Node44_sound

private noncomputable def component55Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (9/64), chiHi := (37/256) }

set_option maxRecDepth 1000000 in
private theorem component55Node46_sound : Sound component55Node46Box :=
  sound_of_literal_split component55Node46Box leaf2611Box leaf2612Box
    .k (239/64) (by rfl) (by rfl)
    leaf2611FlatSound leaf2612FlatSound

private noncomputable def component55Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (37/256), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component55Node47_sound : Sound component55Node47Box :=
  sound_of_literal_split component55Node47Box leaf2613Box leaf2614Box
    .k (239/64) (by rfl) (by rfl)
    leaf2613FlatSound leaf2614FlatSound

private noncomputable def component55Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (9/64), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component55Node48_sound : Sound component55Node48Box :=
  sound_of_literal_split component55Node48Box component55Node46Box component55Node47Box
    .chi (37/256) (by rfl) (by rfl)
    component55Node46_sound component55Node47_sound

private noncomputable def component55Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (9/64), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component55Node49_sound : Sound component55Node49Box :=
  sound_of_literal_split component55Node49Box component55Node45Box component55Node48Box
    .k (119/32) (by rfl) (by rfl)
    component55Node45_sound component55Node48_sound

private noncomputable def component55Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (19/128), chiHi := (39/256) }

set_option maxRecDepth 1000000 in
private theorem component55Node50_sound : Sound component55Node50Box :=
  sound_of_literal_split component55Node50Box leaf2615Box leaf2616Box
    .k (237/64) (by rfl) (by rfl)
    leaf2615FlatSound leaf2616FlatSound

private noncomputable def component55Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (39/256), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component55Node51_sound : Sound component55Node51Box :=
  sound_of_literal_split component55Node51Box leaf2617Box leaf2618Box
    .k (237/64) (by rfl) (by rfl)
    leaf2617FlatSound leaf2618FlatSound

private noncomputable def component55Node52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (19/128), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component55Node52_sound : Sound component55Node52Box :=
  sound_of_literal_split component55Node52Box component55Node50Box component55Node51Box
    .chi (39/256) (by rfl) (by rfl)
    component55Node50_sound component55Node51_sound

private noncomputable def component55Node53Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (19/128), chiHi := (39/256) }

set_option maxRecDepth 1000000 in
private theorem component55Node53_sound : Sound component55Node53Box :=
  sound_of_literal_split component55Node53Box leaf2619Box leaf2620Box
    .k (239/64) (by rfl) (by rfl)
    leaf2619FlatSound leaf2620FlatSound

private noncomputable def component55Node54Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (39/256), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component55Node54_sound : Sound component55Node54Box :=
  sound_of_literal_split component55Node54Box leaf2621Box leaf2622Box
    .k (239/64) (by rfl) (by rfl)
    leaf2621FlatSound leaf2622FlatSound

private noncomputable def component55Node55Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (19/128), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component55Node55_sound : Sound component55Node55Box :=
  sound_of_literal_split component55Node55Box component55Node53Box component55Node54Box
    .chi (39/256) (by rfl) (by rfl)
    component55Node53_sound component55Node54_sound

private noncomputable def component55Node56Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (19/128), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component55Node56_sound : Sound component55Node56Box :=
  sound_of_literal_split component55Node56Box component55Node52Box component55Node55Box
    .k (119/32) (by rfl) (by rfl)
    component55Node52_sound component55Node55_sound

private noncomputable def component55Node57Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (9/64), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component55Node57_sound : Sound component55Node57Box :=
  sound_of_literal_split component55Node57Box component55Node49Box component55Node56Box
    .chi (19/128) (by rfl) (by rfl)
    component55Node49_sound component55Node56_sound

private noncomputable def component55Node58Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (9/64), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component55Node58_sound : Sound component55Node58Box :=
  sound_of_literal_split component55Node58Box component55Node42Box component55Node57Box
    .k (59/16) (by rfl) (by rfl)
    component55Node42_sound component55Node57_sound

noncomputable def component55Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (1/8), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
theorem component55_sound : Sound component55Box :=
  sound_of_literal_split component55Box component55Node27Box component55Node58Box
    .chi (9/64) (by rfl) (by rfl)
    component55Node27_sound component55Node58_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
