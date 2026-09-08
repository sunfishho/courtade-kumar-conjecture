import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch3
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

private noncomputable def leaf2316Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (3/16), chiHi := (49/256) }

private noncomputable def leaf2316Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871219/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68716842496) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (863973583/536870912) }, upper := { exponent := 0, mantissa := (13337/8192) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi187LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435336191/137433684992) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf2316InnerLog : WideLogData :=
  innerPair157Data

set_option maxRecDepth 1000000 in
private theorem leaf2316LocalValidity :
    LeafFacts leaf2316Box leaf2316Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2316Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68716842496) }) = true
      norm_num [leaf2316Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2316CertificateValid :
    WideCertificateValid leaf2316Box leaf2316Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi187ValidityFacts
    leaf2316LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2316CoverageChecked :
    coverageCheck (innerAD leaf2316Box) leaf2316InnerLog = true := by
  rfl'

private theorem leaf2316InnerLogValid :
    leaf2316InnerLog.Valid 8 (innerAD leaf2316Box) :=
  wideLogDataValid_of_cachedCheck endpoint44PositiveFacts
    endpoint45PositiveFacts.valid leaf2316CoverageChecked

private noncomputable def leaf2316InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814641/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2316InputLogOnePlusV_eq :
    leaf2316InputLogOnePlusV = outerEnclosure 24
      (leaf2316Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2316RoundedFacts : LeafRoundedFacts 8
    leaf2316Certificate.logOnePlusV leaf2316InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2316InputLogOnePlusV_eq }

private noncomputable def leaf2316Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi187InputQChi innerPair157Input
    leaf2316InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2316LowerChecked :
    lowerCheck 24 leaf2316Box leaf2316Inputs = true := by
  rfl'

private theorem leaf2316CoversExact : CoversExact 8
    leaf2316Box leaf2316Certificate leaf2316InnerLog leaf2316Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi187RoundedFacts
    innerPair157RoundedFacts leaf2316RoundedFacts (by rfl)

private theorem leaf2316FlatSound : Sound leaf2316Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2316CertificateValid
    leaf2316InnerLogValid leaf2316CoversExact leaf2316LowerChecked

private noncomputable def leaf2317Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (49/256), chiHi := (25/128) }

private noncomputable def leaf2317Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871221/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68716788736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (870788909/536870912) }, upper := { exponent := 0, mantissa := (6721/4096) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi188LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435282431/137433577472) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf2317InnerLog : WideLogData :=
  innerPair188Data

set_option maxRecDepth 1000000 in
private theorem leaf2317LocalValidity :
    LeafFacts leaf2317Box leaf2317Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2317Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68716788736) }) = true
      norm_num [leaf2317Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2317CertificateValid :
    WideCertificateValid leaf2317Box leaf2317Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi188ValidityFacts
    leaf2317LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2317CoverageChecked :
    coverageCheck (innerAD leaf2317Box) leaf2317InnerLog = true := by
  rfl'

private theorem leaf2317InnerLogValid :
    leaf2317InnerLog.Valid 8 (innerAD leaf2317Box) :=
  wideLogDataValid_of_cachedCheck endpoint55PositiveFacts
    endpoint171PositiveFacts.valid leaf2317CoverageChecked

private noncomputable def leaf2317InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629289/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2317InputLogOnePlusV_eq :
    leaf2317InputLogOnePlusV = outerEnclosure 24
      (leaf2317Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2317RoundedFacts : LeafRoundedFacts 8
    leaf2317Certificate.logOnePlusV leaf2317InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2317InputLogOnePlusV_eq }

private noncomputable def leaf2317Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi188InputQChi innerPair188Input
    leaf2317InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2317LowerChecked :
    lowerCheck 24 leaf2317Box leaf2317Inputs = true := by
  rfl'

private theorem leaf2317CoversExact : CoversExact 8
    leaf2317Box leaf2317Certificate leaf2317InnerLog leaf2317Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi188RoundedFacts
    innerPair188RoundedFacts leaf2317RoundedFacts (by rfl)

private theorem leaf2317FlatSound : Sound leaf2317Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2317CertificateValid
    leaf2317InnerLogValid leaf2317CoversExact leaf2317LowerChecked

private noncomputable def leaf2318Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (3/16), chiHi := (49/256) }

private noncomputable def leaf2318Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871221/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68716817408) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (867119117/536870912) }, upper := { exponent := 0, mantissa := (6693/4096) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi187LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435311103/137433634816) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf2318InnerLog : WideLogData :=
  innerPair166Data

set_option maxRecDepth 1000000 in
private theorem leaf2318LocalValidity :
    LeafFacts leaf2318Box leaf2318Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2318Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68716817408) }) = true
      norm_num [leaf2318Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2318CertificateValid :
    WideCertificateValid leaf2318Box leaf2318Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi187ValidityFacts
    leaf2318LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2318CoverageChecked :
    coverageCheck (innerAD leaf2318Box) leaf2318InnerLog = true := by
  rfl'

private theorem leaf2318InnerLogValid :
    leaf2318InnerLog.Valid 8 (innerAD leaf2318Box) :=
  wideLogDataValid_of_cachedCheck endpoint46PositiveFacts
    endpoint45PositiveFacts.valid leaf2318CoverageChecked

private noncomputable def leaf2318InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629285/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2318InputLogOnePlusV_eq :
    leaf2318InputLogOnePlusV = outerEnclosure 24
      (leaf2318Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2318RoundedFacts : LeafRoundedFacts 8
    leaf2318Certificate.logOnePlusV leaf2318InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2318InputLogOnePlusV_eq }

private noncomputable def leaf2318Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi187InputQChi innerPair166Input
    leaf2318InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2318LowerChecked :
    lowerCheck 24 leaf2318Box leaf2318Inputs = true := by
  rfl'

private theorem leaf2318CoversExact : CoversExact 8
    leaf2318Box leaf2318Certificate leaf2318InnerLog leaf2318Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi187RoundedFacts
    innerPair166RoundedFacts leaf2318RoundedFacts (by rfl)

private theorem leaf2318FlatSound : Sound leaf2318Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2318CertificateValid
    leaf2318InnerLogValid leaf2318CoversExact leaf2318LowerChecked

private noncomputable def leaf2319Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (49/256), chiHi := (25/128) }

private noncomputable def leaf2319Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871223/536870912) }, vSqrt := { lower := (65529/65536), upper := (22906164565/22905587712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (873999975/536870912) }, upper := { exponent := 0, mantissa := (3373/2048) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi188LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (45811752277/45811175424) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf2319InnerLog : WideLogData :=
  innerPair61Data

set_option maxRecDepth 1000000 in
private theorem leaf2319LocalValidity :
    LeafFacts leaf2319Box leaf2319Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2319Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22906164565/22905587712) }) = true
      norm_num [leaf2319Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2319CertificateValid :
    WideCertificateValid leaf2319Box leaf2319Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi188ValidityFacts
    leaf2319LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2319CoverageChecked :
    coverageCheck (innerAD leaf2319Box) leaf2319InnerLog = true := by
  rfl'

private theorem leaf2319InnerLogValid :
    leaf2319InnerLog.Valid 8 (innerAD leaf2319Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint48PositiveFacts.valid leaf2319CoverageChecked

private noncomputable def leaf2319InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907323/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2319InputLogOnePlusV_eq :
    leaf2319InputLogOnePlusV = outerEnclosure 24
      (leaf2319Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2319RoundedFacts : LeafRoundedFacts 8
    leaf2319Certificate.logOnePlusV leaf2319InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2319InputLogOnePlusV_eq }

private noncomputable def leaf2319Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi188InputQChi innerPair61Input
    leaf2319InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2319LowerChecked :
    lowerCheck 24 leaf2319Box leaf2319Inputs = true := by
  rfl'

private theorem leaf2319CoversExact : CoversExact 8
    leaf2319Box leaf2319Certificate leaf2319InnerLog leaf2319Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi188RoundedFacts
    innerPair61RoundedFacts leaf2319RoundedFacts (by rfl)

private theorem leaf2319FlatSound : Sound leaf2319Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2319CertificateValid
    leaf2319InnerLogValid leaf2319CoversExact leaf2319LowerChecked

private noncomputable def leaf2320Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (209/64), chiLo := (25/128), chiHi := (13/64) }

private noncomputable def leaf2320Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871381/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433389056) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (877604077/536870912) }, upper := { exponent := 0, mantissa := (6813/4096) } }, logOuter := sk201LogOuterCertificate, logK := sk201LogKCertificate, logChi := chi116LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870310911/274866778112) } }, logDArg := sk201LogDArgCertificate }

private noncomputable def leaf2320InnerLog : WideLogData :=
  innerPair62Data

set_option maxRecDepth 1000000 in
private theorem leaf2320LocalValidity :
    LeafFacts leaf2320Box leaf2320Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2320Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433389056) }) = true
      norm_num [leaf2320Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2320CertificateValid :
    WideCertificateValid leaf2320Box leaf2320Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk201ValidityFacts chi116ValidityFacts
    leaf2320LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2320CoverageChecked :
    coverageCheck (innerAD leaf2320Box) leaf2320InnerLog = true := by
  rfl'

private theorem leaf2320InnerLogValid :
    leaf2320InnerLog.Valid 8 (innerAD leaf2320Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint133PositiveFacts.valid leaf2320CoverageChecked

private noncomputable def leaf2320InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (726831/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf2320InputLogOnePlusV_eq :
    leaf2320InputLogOnePlusV = outerEnclosure 24
      (leaf2320Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2320RoundedFacts : LeafRoundedFacts 8
    leaf2320Certificate.logOnePlusV leaf2320InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2320InputLogOnePlusV_eq }

private noncomputable def leaf2320Inputs : Inputs :=
  inputsOfCaches globalInput sk201RoundedInputs
    chi116InputQChi innerPair62Input
    leaf2320InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2320LowerChecked :
    lowerCheck 24 leaf2320Box leaf2320Inputs = true := by
  rfl'

private theorem leaf2320CoversExact : CoversExact 8
    leaf2320Box leaf2320Certificate leaf2320InnerLog leaf2320Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk201RoundedFacts chi116RoundedFacts
    innerPair62RoundedFacts leaf2320RoundedFacts (by rfl)

private theorem leaf2320FlatSound : Sound leaf2320Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2320CertificateValid
    leaf2320InnerLogValid leaf2320CoversExact leaf2320LowerChecked

private noncomputable def leaf2321Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (209/64), kHi := (105/32), chiLo := (25/128), chiHi := (13/64) }

private noncomputable def leaf2321Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871383/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433362432) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (879242375/536870912) }, upper := { exponent := 0, mantissa := (3413/2048) } }, logOuter := sk202LogOuterCertificate, logK := sk202LogKCertificate, logChi := chi116LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870284287/274866724864) } }, logDArg := sk202LogDArgCertificate }

private noncomputable def leaf2321InnerLog : WideLogData :=
  innerPair62Data

set_option maxRecDepth 1000000 in
private theorem leaf2321LocalValidity :
    LeafFacts leaf2321Box leaf2321Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2321Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433362432) }) = true
      norm_num [leaf2321Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2321CertificateValid :
    WideCertificateValid leaf2321Box leaf2321Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk202ValidityFacts chi116ValidityFacts
    leaf2321LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2321CoverageChecked :
    coverageCheck (innerAD leaf2321Box) leaf2321InnerLog = true := by
  rfl'

private theorem leaf2321InnerLogValid :
    leaf2321InnerLog.Valid 8 (innerAD leaf2321Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint133PositiveFacts.valid leaf2321CoverageChecked

private noncomputable def leaf2321InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814649/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2321InputLogOnePlusV_eq :
    leaf2321InputLogOnePlusV = outerEnclosure 24
      (leaf2321Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2321RoundedFacts : LeafRoundedFacts 8
    leaf2321Certificate.logOnePlusV leaf2321InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2321InputLogOnePlusV_eq }

private noncomputable def leaf2321Inputs : Inputs :=
  inputsOfCaches globalInput sk202RoundedInputs
    chi116InputQChi innerPair62Input
    leaf2321InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2321LowerChecked :
    lowerCheck 24 leaf2321Box leaf2321Inputs = true := by
  rfl'

private theorem leaf2321CoversExact : CoversExact 8
    leaf2321Box leaf2321Certificate leaf2321InnerLog leaf2321Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk202RoundedFacts chi116RoundedFacts
    innerPair62RoundedFacts leaf2321RoundedFacts (by rfl)

private theorem leaf2321FlatSound : Sound leaf2321Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2321CertificateValid
    leaf2321InnerLogValid leaf2321CoversExact leaf2321LowerChecked

private noncomputable def leaf2322Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (211/64), chiLo := (25/128), chiHi := (13/64) }

private noncomputable def leaf2322Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871385/536870912) }, vSqrt := { lower := (65529/65536), upper := (45812307285/45811111936) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (880880673/536870912) }, upper := { exponent := 0, mantissa := (6839/4096) } }, logOuter := sk203LogOuterCertificate, logK := sk203LogKCertificate, logChi := chi116LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (91623419221/91622223872) } }, logDArg := sk203LogDArgCertificate }

private noncomputable def leaf2322InnerLog : WideLogData :=
  innerPair163Data

set_option maxRecDepth 1000000 in
private theorem leaf2322LocalValidity :
    LeafFacts leaf2322Box leaf2322Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2322Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (45812307285/45811111936) }) = true
      norm_num [leaf2322Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2322CertificateValid :
    WideCertificateValid leaf2322Box leaf2322Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk203ValidityFacts chi116ValidityFacts
    leaf2322LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2322CoverageChecked :
    coverageCheck (innerAD leaf2322Box) leaf2322InnerLog = true := by
  rfl'

private theorem leaf2322InnerLogValid :
    leaf2322InnerLog.Valid 8 (innerAD leaf2322Box) :=
  wideLogDataValid_of_cachedCheck endpoint45PositiveFacts
    endpoint133PositiveFacts.valid leaf2322CoverageChecked

private noncomputable def leaf2322InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907325/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2322InputLogOnePlusV_eq :
    leaf2322InputLogOnePlusV = outerEnclosure 24
      (leaf2322Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2322RoundedFacts : LeafRoundedFacts 8
    leaf2322Certificate.logOnePlusV leaf2322InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2322InputLogOnePlusV_eq }

private noncomputable def leaf2322Inputs : Inputs :=
  inputsOfCaches globalInput sk203RoundedInputs
    chi116InputQChi innerPair163Input
    leaf2322InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2322LowerChecked :
    lowerCheck 24 leaf2322Box leaf2322Inputs = true := by
  rfl'

private theorem leaf2322CoversExact : CoversExact 8
    leaf2322Box leaf2322Certificate leaf2322InnerLog leaf2322Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk203RoundedFacts chi116RoundedFacts
    innerPair163RoundedFacts leaf2322RoundedFacts (by rfl)

private theorem leaf2322FlatSound : Sound leaf2322Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2322CertificateValid
    leaf2322InnerLogValid leaf2322CoversExact leaf2322LowerChecked

private noncomputable def leaf2323Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (211/64), kHi := (53/16), chiLo := (25/128), chiHi := (13/64) }

private noncomputable def leaf2323Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871387/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433309184) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (882518971/536870912) }, upper := { exponent := 0, mantissa := (1713/1024) } }, logOuter := sk204LogOuterCertificate, logK := sk204LogKCertificate, logChi := chi116LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870231039/274866618368) } }, logDArg := sk204LogDArgCertificate }

private noncomputable def leaf2323InnerLog : WideLogData :=
  innerPair161Data

set_option maxRecDepth 1000000 in
private theorem leaf2323LocalValidity :
    LeafFacts leaf2323Box leaf2323Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2323Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433309184) }) = true
      norm_num [leaf2323Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2323CertificateValid :
    WideCertificateValid leaf2323Box leaf2323Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk204ValidityFacts chi116ValidityFacts
    leaf2323LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2323CoverageChecked :
    coverageCheck (innerAD leaf2323Box) leaf2323InnerLog = true := by
  rfl'

private theorem leaf2323InnerLogValid :
    leaf2323InnerLog.Valid 8 (innerAD leaf2323Box) :=
  wideLogDataValid_of_cachedCheck endpoint45PositiveFacts
    endpoint56PositiveFacts.valid leaf2323CoverageChecked

private noncomputable def leaf2323InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629301/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2323InputLogOnePlusV_eq :
    leaf2323InputLogOnePlusV = outerEnclosure 24
      (leaf2323Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2323RoundedFacts : LeafRoundedFacts 8
    leaf2323Certificate.logOnePlusV leaf2323InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2323InputLogOnePlusV_eq }

private noncomputable def leaf2323Inputs : Inputs :=
  inputsOfCaches globalInput sk204RoundedInputs
    chi116InputQChi innerPair161Input
    leaf2323InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2323LowerChecked :
    lowerCheck 24 leaf2323Box leaf2323Inputs = true := by
  rfl'

private theorem leaf2323CoversExact : CoversExact 8
    leaf2323Box leaf2323Certificate leaf2323InnerLog leaf2323Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk204RoundedFacts chi116RoundedFacts
    innerPair161RoundedFacts leaf2323RoundedFacts (by rfl)

private theorem leaf2323FlatSound : Sound leaf2323Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2323CertificateValid
    leaf2323InnerLogValid leaf2323CoversExact leaf2323LowerChecked

private noncomputable def leaf2324Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (3/16), chiHi := (49/256) }

private noncomputable def leaf2324Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871223/536870912) }, vSqrt := { lower := (65529/65536), upper := (4581232913/4581119488) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (870264651/536870912) }, upper := { exponent := 0, mantissa := (13435/8192) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi187LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (9162352401/9162238976) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf2324InnerLog : WideLogData :=
  innerPair166Data

set_option maxRecDepth 1000000 in
private theorem leaf2324LocalValidity :
    LeafFacts leaf2324Box leaf2324Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2324Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4581232913/4581119488) }) = true
      norm_num [leaf2324Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2324CertificateValid :
    WideCertificateValid leaf2324Box leaf2324Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi187ValidityFacts
    leaf2324LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2324CoverageChecked :
    coverageCheck (innerAD leaf2324Box) leaf2324InnerLog = true := by
  rfl'

private theorem leaf2324InnerLogValid :
    leaf2324InnerLog.Valid 8 (innerAD leaf2324Box) :=
  wideLogDataValid_of_cachedCheck endpoint46PositiveFacts
    endpoint45PositiveFacts.valid leaf2324CoverageChecked

private noncomputable def leaf2324InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453661/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf2324InputLogOnePlusV_eq :
    leaf2324InputLogOnePlusV = outerEnclosure 24
      (leaf2324Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2324RoundedFacts : LeafRoundedFacts 8
    leaf2324Certificate.logOnePlusV leaf2324InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2324InputLogOnePlusV_eq }

private noncomputable def leaf2324Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi187InputQChi innerPair166Input
    leaf2324InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2324LowerChecked :
    lowerCheck 24 leaf2324Box leaf2324Inputs = true := by
  rfl'

private theorem leaf2324CoversExact : CoversExact 8
    leaf2324Box leaf2324Certificate leaf2324InnerLog leaf2324Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi187RoundedFacts
    innerPair166RoundedFacts leaf2324RoundedFacts (by rfl)

private theorem leaf2324FlatSound : Sound leaf2324Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2324CertificateValid
    leaf2324InnerLogValid leaf2324CoversExact leaf2324LowerChecked

private noncomputable def leaf2325Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (49/256), chiHi := (25/128) }

private noncomputable def leaf2325Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871225/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68716737536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (877211041/536870912) }, upper := { exponent := 0, mantissa := (6771/4096) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi188LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435231231/137433475072) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf2325InnerLog : WideLogData :=
  innerPair61Data

set_option maxRecDepth 1000000 in
private theorem leaf2325LocalValidity :
    LeafFacts leaf2325Box leaf2325Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2325Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68716737536) }) = true
      norm_num [leaf2325Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2325CertificateValid :
    WideCertificateValid leaf2325Box leaf2325Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi188ValidityFacts
    leaf2325LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2325CoverageChecked :
    coverageCheck (innerAD leaf2325Box) leaf2325InnerLog = true := by
  rfl'

private theorem leaf2325InnerLogValid :
    leaf2325InnerLog.Valid 8 (innerAD leaf2325Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint48PositiveFacts.valid leaf2325CoverageChecked

private noncomputable def leaf2325InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629295/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2325InputLogOnePlusV_eq :
    leaf2325InputLogOnePlusV = outerEnclosure 24
      (leaf2325Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2325RoundedFacts : LeafRoundedFacts 8
    leaf2325Certificate.logOnePlusV leaf2325InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2325InputLogOnePlusV_eq }

private noncomputable def leaf2325Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi188InputQChi innerPair61Input
    leaf2325InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2325LowerChecked :
    lowerCheck 24 leaf2325Box leaf2325Inputs = true := by
  rfl'

private theorem leaf2325CoversExact : CoversExact 8
    leaf2325Box leaf2325Certificate leaf2325InnerLog leaf2325Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi188RoundedFacts
    innerPair61RoundedFacts leaf2325RoundedFacts (by rfl)

private theorem leaf2325FlatSound : Sound leaf2325Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2325CertificateValid
    leaf2325InnerLogValid leaf2325CoversExact leaf2325LowerChecked

private noncomputable def leaf2326Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (3/16), chiHi := (49/256) }

private noncomputable def leaf2326Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871225/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68716767232) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (873410185/536870912) }, upper := { exponent := 0, mantissa := (3371/2048) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi187LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435260927/137433534464) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf2326InnerLog : WideLogData :=
  innerPair454Data

set_option maxRecDepth 1000000 in
private theorem leaf2326LocalValidity :
    LeafFacts leaf2326Box leaf2326Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2326Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68716767232) }) = true
      norm_num [leaf2326Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2326CertificateValid :
    WideCertificateValid leaf2326Box leaf2326Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi187ValidityFacts
    leaf2326LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2326CoverageChecked :
    coverageCheck (innerAD leaf2326Box) leaf2326InnerLog = true := by
  rfl'

private theorem leaf2326InnerLogValid :
    leaf2326InnerLog.Valid 8 (innerAD leaf2326Box) :=
  wideLogDataValid_of_cachedCheck endpoint172PositiveFacts
    endpoint173PositiveFacts.valid leaf2326CoverageChecked

private noncomputable def leaf2326InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907323/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2326InputLogOnePlusV_eq :
    leaf2326InputLogOnePlusV = outerEnclosure 24
      (leaf2326Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2326RoundedFacts : LeafRoundedFacts 8
    leaf2326Certificate.logOnePlusV leaf2326InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2326InputLogOnePlusV_eq }

private noncomputable def leaf2326Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi187InputQChi innerPair454Input
    leaf2326InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2326LowerChecked :
    lowerCheck 24 leaf2326Box leaf2326Inputs = true := by
  rfl'

private theorem leaf2326CoversExact : CoversExact 8
    leaf2326Box leaf2326Certificate leaf2326InnerLog leaf2326Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi187RoundedFacts
    innerPair454RoundedFacts leaf2326RoundedFacts (by rfl)

private theorem leaf2326FlatSound : Sound leaf2326Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2326CertificateValid
    leaf2326InnerLogValid leaf2326CoversExact leaf2326LowerChecked

private noncomputable def leaf2327Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (215/64), chiLo := (49/256), chiHi := (25/128) }

private noncomputable def leaf2327Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742353/1073741824) }, vSqrt := { lower := (65529/65536), upper := (45812307285/45811149824) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1760877081/1073741824) }, upper := { exponent := 0, mantissa := (13567/8192) } }, logOuter := sk205LogOuterCertificate, logK := sk205LogKCertificate, logChi := chi188LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (91623457109/91622299648) } }, logDArg := sk205LogDArgCertificate }

private noncomputable def leaf2327InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2327LocalValidity :
    LeafFacts leaf2327Box leaf2327Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2327Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (45812307285/45811149824) }) = true
      norm_num [leaf2327Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2327CertificateValid :
    WideCertificateValid leaf2327Box leaf2327Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk205ValidityFacts chi188ValidityFacts
    leaf2327LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2327CoverageChecked :
    coverageCheck (innerAD leaf2327Box) leaf2327InnerLog = true := by
  rfl'

private theorem leaf2327InnerLogValid :
    leaf2327InnerLog.Valid 8 (innerAD leaf2327Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2327CoverageChecked

private noncomputable def leaf2327InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629293/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2327InputLogOnePlusV_eq :
    leaf2327InputLogOnePlusV = outerEnclosure 24
      (leaf2327Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2327RoundedFacts : LeafRoundedFacts 8
    leaf2327Certificate.logOnePlusV leaf2327InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2327InputLogOnePlusV_eq }

private noncomputable def leaf2327Inputs : Inputs :=
  inputsOfCaches globalInput sk205RoundedInputs
    chi188InputQChi innerPair56Input
    leaf2327InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2327LowerChecked :
    lowerCheck 24 leaf2327Box leaf2327Inputs = true := by
  rfl'

private theorem leaf2327CoversExact : CoversExact 8
    leaf2327Box leaf2327Certificate leaf2327InnerLog leaf2327Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk205RoundedFacts chi188RoundedFacts
    innerPair56RoundedFacts leaf2327RoundedFacts (by rfl)

private theorem leaf2327FlatSound : Sound leaf2327Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2327CertificateValid
    leaf2327InnerLogValid leaf2327CoversExact leaf2327LowerChecked

private noncomputable def leaf2328Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (215/64), kHi := (27/8), chiLo := (49/256), chiHi := (25/128) }

private noncomputable def leaf2328Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742355/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433423872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1764088147/1073741824) }, upper := { exponent := 0, mantissa := (1699/1024) } }, logOuter := sk206LogOuterCertificate, logK := sk206LogKCertificate, logChi := chi188LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870345727/274866847744) } }, logDArg := sk206LogDArgCertificate }

private noncomputable def leaf2328InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2328LocalValidity :
    LeafFacts leaf2328Box leaf2328Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2328Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433423872) }) = true
      norm_num [leaf2328Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2328CertificateValid :
    WideCertificateValid leaf2328Box leaf2328Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk206ValidityFacts chi188ValidityFacts
    leaf2328LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2328CoverageChecked :
    coverageCheck (innerAD leaf2328Box) leaf2328InnerLog = true := by
  rfl'

private theorem leaf2328InnerLogValid :
    leaf2328InnerLog.Valid 8 (innerAD leaf2328Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2328CoverageChecked

private noncomputable def leaf2328InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814647/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2328InputLogOnePlusV_eq :
    leaf2328InputLogOnePlusV = outerEnclosure 24
      (leaf2328Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2328RoundedFacts : LeafRoundedFacts 8
    leaf2328Certificate.logOnePlusV leaf2328InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2328InputLogOnePlusV_eq }

private noncomputable def leaf2328Inputs : Inputs :=
  inputsOfCaches globalInput sk206RoundedInputs
    chi188InputQChi innerPair56Input
    leaf2328InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2328LowerChecked :
    lowerCheck 24 leaf2328Box leaf2328Inputs = true := by
  rfl'

private theorem leaf2328CoversExact : CoversExact 8
    leaf2328Box leaf2328Certificate leaf2328InnerLog leaf2328Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk206RoundedFacts chi188RoundedFacts
    innerPair56RoundedFacts leaf2328RoundedFacts (by rfl)

private theorem leaf2328FlatSound : Sound leaf2328Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2328CertificateValid
    leaf2328InnerLogValid leaf2328CoversExact leaf2328LowerChecked

private noncomputable def leaf2329Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (213/64), chiLo := (25/128), chiHi := (13/64) }

private noncomputable def leaf2329Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871389/536870912) }, vSqrt := { lower := (65529/65536), upper := (27487384371/27486656512) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (884157269/536870912) }, upper := { exponent := 0, mantissa := (6865/4096) } }, logOuter := sk207LogOuterCertificate, logK := sk207LogKCertificate, logChi := chi116LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (54974040883/54973313024) } }, logDArg := sk207LogDArgCertificate }

private noncomputable def leaf2329InnerLog : WideLogData :=
  innerPair452Data

set_option maxRecDepth 1000000 in
private theorem leaf2329LocalValidity :
    LeafFacts leaf2329Box leaf2329Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2329Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (27487384371/27486656512) }) = true
      norm_num [leaf2329Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2329CertificateValid :
    WideCertificateValid leaf2329Box leaf2329Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk207ValidityFacts chi116ValidityFacts
    leaf2329LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2329CoverageChecked :
    coverageCheck (innerAD leaf2329Box) leaf2329InnerLog = true := by
  rfl'

private theorem leaf2329InnerLogValid :
    leaf2329InnerLog.Valid 8 (innerAD leaf2329Box) :=
  wideLogDataValid_of_cachedCheck endpoint171PositiveFacts
    endpoint59PositiveFacts.valid leaf2329CoverageChecked

private noncomputable def leaf2329InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629303/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2329InputLogOnePlusV_eq :
    leaf2329InputLogOnePlusV = outerEnclosure 24
      (leaf2329Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2329RoundedFacts : LeafRoundedFacts 8
    leaf2329Certificate.logOnePlusV leaf2329InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2329InputLogOnePlusV_eq }

private noncomputable def leaf2329Inputs : Inputs :=
  inputsOfCaches globalInput sk207RoundedInputs
    chi116InputQChi innerPair452Input
    leaf2329InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2329LowerChecked :
    lowerCheck 24 leaf2329Box leaf2329Inputs = true := by
  rfl'

private theorem leaf2329CoversExact : CoversExact 8
    leaf2329Box leaf2329Certificate leaf2329InnerLog leaf2329Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk207RoundedFacts chi116RoundedFacts
    innerPair452RoundedFacts leaf2329RoundedFacts (by rfl)

private theorem leaf2329FlatSound : Sound leaf2329Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2329CertificateValid
    leaf2329InnerLogValid leaf2329CoversExact leaf2329LowerChecked

private noncomputable def leaf2330Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (213/64), kHi := (107/32), chiLo := (25/128), chiHi := (13/64) }

private noncomputable def leaf2330Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871391/536870912) }, vSqrt := { lower := (65529/65536), upper := (45812307285/45811085312) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (885795567/536870912) }, upper := { exponent := 0, mantissa := (3439/2048) } }, logOuter := sk208LogOuterCertificate, logK := sk208LogKCertificate, logChi := chi116LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (91623392597/91622170624) } }, logDArg := sk208LogDArgCertificate }

private noncomputable def leaf2330InnerLog : WideLogData :=
  innerPair426Data

set_option maxRecDepth 1000000 in
private theorem leaf2330LocalValidity :
    LeafFacts leaf2330Box leaf2330Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2330Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (45812307285/45811085312) }) = true
      norm_num [leaf2330Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2330CertificateValid :
    WideCertificateValid leaf2330Box leaf2330Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk208ValidityFacts chi116ValidityFacts
    leaf2330LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2330CoverageChecked :
    coverageCheck (innerAD leaf2330Box) leaf2330InnerLog = true := by
  rfl'

private theorem leaf2330InnerLogValid :
    leaf2330InnerLog.Valid 8 (innerAD leaf2330Box) :=
  wideLogDataValid_of_cachedCheck endpoint135PositiveFacts
    endpoint59PositiveFacts.valid leaf2330CoverageChecked

private noncomputable def leaf2330InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629305/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2330InputLogOnePlusV_eq :
    leaf2330InputLogOnePlusV = outerEnclosure 24
      (leaf2330Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2330RoundedFacts : LeafRoundedFacts 8
    leaf2330Certificate.logOnePlusV leaf2330InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2330InputLogOnePlusV_eq }

private noncomputable def leaf2330Inputs : Inputs :=
  inputsOfCaches globalInput sk208RoundedInputs
    chi116InputQChi innerPair426Input
    leaf2330InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2330LowerChecked :
    lowerCheck 24 leaf2330Box leaf2330Inputs = true := by
  rfl'

private theorem leaf2330CoversExact : CoversExact 8
    leaf2330Box leaf2330Certificate leaf2330InnerLog leaf2330Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk208RoundedFacts chi116RoundedFacts
    innerPair426RoundedFacts leaf2330RoundedFacts (by rfl)

private theorem leaf2330FlatSound : Sound leaf2330Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2330CertificateValid
    leaf2330InnerLogValid leaf2330CoversExact leaf2330LowerChecked

private noncomputable def leaf2331Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (215/64), chiLo := (25/128), chiHi := (13/64) }

private noncomputable def leaf2331Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871393/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433229312) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (887433865/536870912) }, upper := { exponent := 0, mantissa := (6891/4096) } }, logOuter := sk205LogOuterCertificate, logK := sk205LogKCertificate, logChi := chi116LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870151167/274866458624) } }, logDArg := sk205LogDArgCertificate }

private noncomputable def leaf2331InnerLog : WideLogData :=
  innerPair456Data

set_option maxRecDepth 1000000 in
private theorem leaf2331LocalValidity :
    LeafFacts leaf2331Box leaf2331Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2331Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433229312) }) = true
      norm_num [leaf2331Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2331CertificateValid :
    WideCertificateValid leaf2331Box leaf2331Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk205ValidityFacts chi116ValidityFacts
    leaf2331LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2331CoverageChecked :
    coverageCheck (innerAD leaf2331Box) leaf2331InnerLog = true := by
  rfl'

private theorem leaf2331InnerLogValid :
    leaf2331InnerLog.Valid 8 (innerAD leaf2331Box) :=
  wideLogDataValid_of_cachedCheck endpoint174PositiveFacts
    endpoint58PositiveFacts.valid leaf2331CoverageChecked

private noncomputable def leaf2331InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814653/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2331InputLogOnePlusV_eq :
    leaf2331InputLogOnePlusV = outerEnclosure 24
      (leaf2331Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2331RoundedFacts : LeafRoundedFacts 8
    leaf2331Certificate.logOnePlusV leaf2331InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2331InputLogOnePlusV_eq }

private noncomputable def leaf2331Inputs : Inputs :=
  inputsOfCaches globalInput sk205RoundedInputs
    chi116InputQChi innerPair456Input
    leaf2331InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2331LowerChecked :
    lowerCheck 24 leaf2331Box leaf2331Inputs = true := by
  rfl'

private theorem leaf2331CoversExact : CoversExact 8
    leaf2331Box leaf2331Certificate leaf2331InnerLog leaf2331Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk205RoundedFacts chi116RoundedFacts
    innerPair456RoundedFacts leaf2331RoundedFacts (by rfl)

private theorem leaf2331FlatSound : Sound leaf2331Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2331CertificateValid
    leaf2331InnerLogValid leaf2331CoversExact leaf2331LowerChecked

private noncomputable def leaf2332Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (215/64), kHi := (27/8), chiLo := (25/128), chiHi := (51/256) }

private noncomputable def leaf2332Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742357/1073741824) }, vSqrt := { lower := (65529/65536), upper := (27487384371/27486662656) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1778177525/1073741824) }, upper := { exponent := 0, mantissa := (3425/2048) } }, logOuter := sk206LogOuterCertificate, logK := sk206LogKCertificate, logChi := chi193LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (54974047027/54973325312) } }, logDArg := sk206LogDArgCertificate }

private noncomputable def leaf2332InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2332LocalValidity :
    LeafFacts leaf2332Box leaf2332Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2332Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (27487384371/27486662656) }) = true
      norm_num [leaf2332Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2332CertificateValid :
    WideCertificateValid leaf2332Box leaf2332Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk206ValidityFacts chi193ValidityFacts
    leaf2332LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2332CoverageChecked :
    coverageCheck (innerAD leaf2332Box) leaf2332InnerLog = true := by
  rfl'

private theorem leaf2332InnerLogValid :
    leaf2332InnerLog.Valid 8 (innerAD leaf2332Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2332CoverageChecked

private noncomputable def leaf2332InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629301/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2332InputLogOnePlusV_eq :
    leaf2332InputLogOnePlusV = outerEnclosure 24
      (leaf2332Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2332RoundedFacts : LeafRoundedFacts 8
    leaf2332Certificate.logOnePlusV leaf2332InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2332InputLogOnePlusV_eq }

private noncomputable def leaf2332Inputs : Inputs :=
  inputsOfCaches globalInput sk206RoundedInputs
    chi193InputQChi innerPair56Input
    leaf2332InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2332LowerChecked :
    lowerCheck 24 leaf2332Box leaf2332Inputs = true := by
  rfl'

private theorem leaf2332CoversExact : CoversExact 8
    leaf2332Box leaf2332Certificate leaf2332InnerLog leaf2332Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk206RoundedFacts chi193RoundedFacts
    innerPair56RoundedFacts leaf2332RoundedFacts (by rfl)

private theorem leaf2332FlatSound : Sound leaf2332Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2332CertificateValid
    leaf2332InnerLogValid leaf2332CoversExact leaf2332LowerChecked

private noncomputable def leaf2333Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (215/64), kHi := (27/8), chiLo := (51/256), chiHi := (13/64) }

private noncomputable def leaf2333Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742359/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433202688) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1792266903/1073741824) }, upper := { exponent := 0, mantissa := (863/512) } }, logOuter := sk206LogOuterCertificate, logK := sk206LogKCertificate, logChi := chi194LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870124543/274866405376) } }, logDArg := sk206LogDArgCertificate }

private noncomputable def leaf2333InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2333LocalValidity :
    LeafFacts leaf2333Box leaf2333Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2333Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433202688) }) = true
      norm_num [leaf2333Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2333CertificateValid :
    WideCertificateValid leaf2333Box leaf2333Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk206ValidityFacts chi194ValidityFacts
    leaf2333LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2333CoverageChecked :
    coverageCheck (innerAD leaf2333Box) leaf2333InnerLog = true := by
  rfl'

private theorem leaf2333InnerLogValid :
    leaf2333InnerLog.Valid 8 (innerAD leaf2333Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2333CoverageChecked

private noncomputable def leaf2333InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907327/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2333InputLogOnePlusV_eq :
    leaf2333InputLogOnePlusV = outerEnclosure 24
      (leaf2333Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2333RoundedFacts : LeafRoundedFacts 8
    leaf2333Certificate.logOnePlusV leaf2333InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2333InputLogOnePlusV_eq }

private noncomputable def leaf2333Inputs : Inputs :=
  inputsOfCaches globalInput sk206RoundedInputs
    chi194InputQChi innerPair56Input
    leaf2333InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2333LowerChecked :
    lowerCheck 24 leaf2333Box leaf2333Inputs = true := by
  rfl'

private theorem leaf2333CoversExact : CoversExact 8
    leaf2333Box leaf2333Certificate leaf2333InnerLog leaf2333Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk206RoundedFacts chi194RoundedFacts
    innerPair56RoundedFacts leaf2333RoundedFacts (by rfl)

private theorem leaf2333FlatSound : Sound leaf2333Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2333CertificateValid
    leaf2333InnerLogValid leaf2333CoversExact leaf2333LowerChecked

private noncomputable def leaf2334Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (209/64), chiLo := (13/64), chiHi := (27/128) }

private noncomputable def leaf2334Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871383/536870912) }, vSqrt := { lower := (65529/65536), upper := (27487384371/27486635008) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (891234731/536870912) }, upper := { exponent := 0, mantissa := (13835/8192) } }, logOuter := sk201LogOuterCertificate, logK := sk201LogKCertificate, logChi := chi117LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (54974019379/54973270016) } }, logDArg := sk201LogDArgCertificate }

private noncomputable def leaf2334InnerLog : WideLogData :=
  innerPair173Data

set_option maxRecDepth 1000000 in
private theorem leaf2334LocalValidity :
    LeafFacts leaf2334Box leaf2334Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2334Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (27487384371/27486635008) }) = true
      norm_num [leaf2334Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2334CertificateValid :
    WideCertificateValid leaf2334Box leaf2334Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk201ValidityFacts chi117ValidityFacts
    leaf2334LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2334CoverageChecked :
    coverageCheck (innerAD leaf2334Box) leaf2334InnerLog = true := by
  rfl'

private theorem leaf2334InnerLogValid :
    leaf2334InnerLog.Valid 8 (innerAD leaf2334Box) :=
  wideLogDataValid_of_cachedCheck endpoint48PositiveFacts
    endpoint20PositiveFacts.valid leaf2334CoverageChecked

private noncomputable def leaf2334InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629309/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2334InputLogOnePlusV_eq :
    leaf2334InputLogOnePlusV = outerEnclosure 24
      (leaf2334Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2334RoundedFacts : LeafRoundedFacts 8
    leaf2334Certificate.logOnePlusV leaf2334InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2334InputLogOnePlusV_eq }

private noncomputable def leaf2334Inputs : Inputs :=
  inputsOfCaches globalInput sk201RoundedInputs
    chi117InputQChi innerPair173Input
    leaf2334InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2334LowerChecked :
    lowerCheck 24 leaf2334Box leaf2334Inputs = true := by
  rfl'

private theorem leaf2334CoversExact : CoversExact 8
    leaf2334Box leaf2334Certificate leaf2334InnerLog leaf2334Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk201RoundedFacts chi117RoundedFacts
    innerPair173RoundedFacts leaf2334RoundedFacts (by rfl)

private theorem leaf2334FlatSound : Sound leaf2334Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2334CertificateValid
    leaf2334InnerLogValid leaf2334CoversExact leaf2334LowerChecked

private noncomputable def leaf2335Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (209/64), kHi := (105/32), chiLo := (13/64), chiHi := (27/128) }

private noncomputable def leaf2335Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871385/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433147392) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (892938561/536870912) }, upper := { exponent := 0, mantissa := (6931/4096) } }, logOuter := sk202LogOuterCertificate, logK := sk202LogKCertificate, logChi := chi117LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870069247/274866294784) } }, logDArg := sk202LogDArgCertificate }

private noncomputable def leaf2335InnerLog : WideLogData :=
  innerPair173Data

set_option maxRecDepth 1000000 in
private theorem leaf2335LocalValidity :
    LeafFacts leaf2335Box leaf2335Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2335Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433147392) }) = true
      norm_num [leaf2335Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2335CertificateValid :
    WideCertificateValid leaf2335Box leaf2335Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk202ValidityFacts chi117ValidityFacts
    leaf2335LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2335CoverageChecked :
    coverageCheck (innerAD leaf2335Box) leaf2335InnerLog = true := by
  rfl'

private theorem leaf2335InnerLogValid :
    leaf2335InnerLog.Valid 8 (innerAD leaf2335Box) :=
  wideLogDataValid_of_cachedCheck endpoint48PositiveFacts
    endpoint20PositiveFacts.valid leaf2335CoverageChecked

private noncomputable def leaf2335InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629311/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2335InputLogOnePlusV_eq :
    leaf2335InputLogOnePlusV = outerEnclosure 24
      (leaf2335Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2335RoundedFacts : LeafRoundedFacts 8
    leaf2335Certificate.logOnePlusV leaf2335InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2335InputLogOnePlusV_eq }

private noncomputable def leaf2335Inputs : Inputs :=
  inputsOfCaches globalInput sk202RoundedInputs
    chi117InputQChi innerPair173Input
    leaf2335InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2335LowerChecked :
    lowerCheck 24 leaf2335Box leaf2335Inputs = true := by
  rfl'

private theorem leaf2335CoversExact : CoversExact 8
    leaf2335Box leaf2335Certificate leaf2335InnerLog leaf2335Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk202RoundedFacts chi117RoundedFacts
    innerPair173RoundedFacts leaf2335RoundedFacts (by rfl)

private theorem leaf2335FlatSound : Sound leaf2335Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2335CertificateValid
    leaf2335InnerLogValid leaf2335CoversExact leaf2335LowerChecked

private noncomputable def leaf2336Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (211/64), chiLo := (13/64), chiHi := (27/128) }

private noncomputable def leaf2336Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871387/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433119744) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (894642391/536870912) }, upper := { exponent := 0, mantissa := (13889/8192) } }, logOuter := sk203LogOuterCertificate, logK := sk203LogKCertificate, logChi := chi117LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870041599/274866239488) } }, logDArg := sk203LogDArgCertificate }

private noncomputable def leaf2336InnerLog : WideLogData :=
  innerPair173Data

set_option maxRecDepth 1000000 in
private theorem leaf2336LocalValidity :
    LeafFacts leaf2336Box leaf2336Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2336Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433119744) }) = true
      norm_num [leaf2336Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2336CertificateValid :
    WideCertificateValid leaf2336Box leaf2336Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk203ValidityFacts chi117ValidityFacts
    leaf2336LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2336CoverageChecked :
    coverageCheck (innerAD leaf2336Box) leaf2336InnerLog = true := by
  rfl'

private theorem leaf2336InnerLogValid :
    leaf2336InnerLog.Valid 8 (innerAD leaf2336Box) :=
  wideLogDataValid_of_cachedCheck endpoint48PositiveFacts
    endpoint20PositiveFacts.valid leaf2336CoverageChecked

private noncomputable def leaf2336InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629313/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2336InputLogOnePlusV_eq :
    leaf2336InputLogOnePlusV = outerEnclosure 24
      (leaf2336Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2336RoundedFacts : LeafRoundedFacts 8
    leaf2336Certificate.logOnePlusV leaf2336InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2336InputLogOnePlusV_eq }

private noncomputable def leaf2336Inputs : Inputs :=
  inputsOfCaches globalInput sk203RoundedInputs
    chi117InputQChi innerPair173Input
    leaf2336InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2336LowerChecked :
    lowerCheck 24 leaf2336Box leaf2336Inputs = true := by
  rfl'

private theorem leaf2336CoversExact : CoversExact 8
    leaf2336Box leaf2336Certificate leaf2336InnerLog leaf2336Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk203RoundedFacts chi117RoundedFacts
    innerPair173RoundedFacts leaf2336RoundedFacts (by rfl)

private theorem leaf2336FlatSound : Sound leaf2336Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2336CertificateValid
    leaf2336InnerLogValid leaf2336CoversExact leaf2336LowerChecked

private noncomputable def leaf2337Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (211/64), kHi := (53/16), chiLo := (13/64), chiHi := (27/128) }

private noncomputable def leaf2337Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871389/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433092096) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (896346221/536870912) }, upper := { exponent := 0, mantissa := (3479/2048) } }, logOuter := sk204LogOuterCertificate, logK := sk204LogKCertificate, logChi := chi117LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870013951/274866184192) } }, logDArg := sk204LogDArgCertificate }

private noncomputable def leaf2337InnerLog : WideLogData :=
  innerPair173Data

set_option maxRecDepth 1000000 in
private theorem leaf2337LocalValidity :
    LeafFacts leaf2337Box leaf2337Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2337Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433092096) }) = true
      norm_num [leaf2337Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2337CertificateValid :
    WideCertificateValid leaf2337Box leaf2337Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk204ValidityFacts chi117ValidityFacts
    leaf2337LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2337CoverageChecked :
    coverageCheck (innerAD leaf2337Box) leaf2337InnerLog = true := by
  rfl'

private theorem leaf2337InnerLogValid :
    leaf2337InnerLog.Valid 8 (innerAD leaf2337Box) :=
  wideLogDataValid_of_cachedCheck endpoint48PositiveFacts
    endpoint20PositiveFacts.valid leaf2337CoverageChecked

private noncomputable def leaf2337InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629315/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2337InputLogOnePlusV_eq :
    leaf2337InputLogOnePlusV = outerEnclosure 24
      (leaf2337Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2337RoundedFacts : LeafRoundedFacts 8
    leaf2337Certificate.logOnePlusV leaf2337InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2337InputLogOnePlusV_eq }

private noncomputable def leaf2337Inputs : Inputs :=
  inputsOfCaches globalInput sk204RoundedInputs
    chi117InputQChi innerPair173Input
    leaf2337InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2337LowerChecked :
    lowerCheck 24 leaf2337Box leaf2337Inputs = true := by
  rfl'

private theorem leaf2337CoversExact : CoversExact 8
    leaf2337Box leaf2337Certificate leaf2337InnerLog leaf2337Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk204RoundedFacts chi117RoundedFacts
    innerPair173RoundedFacts leaf2337RoundedFacts (by rfl)

private theorem leaf2337FlatSound : Sound leaf2337Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2337CertificateValid
    leaf2337InnerLogValid leaf2337CoversExact leaf2337LowerChecked

private noncomputable def leaf2338Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (209/64), chiLo := (27/128), chiHi := (7/32) }

private noncomputable def leaf2338Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871385/536870912) }, vSqrt := { lower := (65529/65536), upper := (45812307285/45810987008) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (904865385/536870912) }, upper := { exponent := 0, mantissa := (3511/2048) } }, logOuter := sk201LogOuterCertificate, logK := sk201LogKCertificate, logChi := chi118LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (91623294293/91621974016) } }, logDArg := sk201LogDArgCertificate }

private noncomputable def leaf2338InnerLog : WideLogData :=
  innerPair421Data

set_option maxRecDepth 1000000 in
private theorem leaf2338LocalValidity :
    LeafFacts leaf2338Box leaf2338Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2338Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (45812307285/45810987008) }) = true
      norm_num [leaf2338Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2338CertificateValid :
    WideCertificateValid leaf2338Box leaf2338Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk201ValidityFacts chi118ValidityFacts
    leaf2338LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2338CoverageChecked :
    coverageCheck (innerAD leaf2338Box) leaf2338InnerLog = true := by
  rfl'

private theorem leaf2338InnerLogValid :
    leaf2338InnerLog.Valid 8 (innerAD leaf2338Box) :=
  wideLogDataValid_of_cachedCheck endpoint133PositiveFacts
    endpoint62PositiveFacts.valid leaf2338CoverageChecked

private noncomputable def leaf2338InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629323/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2338InputLogOnePlusV_eq :
    leaf2338InputLogOnePlusV = outerEnclosure 24
      (leaf2338Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2338RoundedFacts : LeafRoundedFacts 8
    leaf2338Certificate.logOnePlusV leaf2338InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2338InputLogOnePlusV_eq }

private noncomputable def leaf2338Inputs : Inputs :=
  inputsOfCaches globalInput sk201RoundedInputs
    chi118InputQChi innerPair421Input
    leaf2338InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2338LowerChecked :
    lowerCheck 24 leaf2338Box leaf2338Inputs = true := by
  rfl'

private theorem leaf2338CoversExact : CoversExact 8
    leaf2338Box leaf2338Certificate leaf2338InnerLog leaf2338Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk201RoundedFacts chi118RoundedFacts
    innerPair421RoundedFacts leaf2338RoundedFacts (by rfl)

private theorem leaf2338FlatSound : Sound leaf2338Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2338CertificateValid
    leaf2338InnerLogValid leaf2338CoversExact leaf2338LowerChecked

private noncomputable def leaf2339Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (209/64), kHi := (105/32), chiLo := (27/128), chiHi := (7/32) }

private noncomputable def leaf2339Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871387/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432932352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (906634747/536870912) }, upper := { exponent := 0, mantissa := (1759/1024) } }, logOuter := sk202LogOuterCertificate, logK := sk202LogKCertificate, logChi := chi118LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869854207/274865864704) } }, logDArg := sk202LogDArgCertificate }

private noncomputable def leaf2339InnerLog : WideLogData :=
  innerPair68Data

set_option maxRecDepth 1000000 in
private theorem leaf2339LocalValidity :
    LeafFacts leaf2339Box leaf2339Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2339Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432932352) }) = true
      norm_num [leaf2339Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2339CertificateValid :
    WideCertificateValid leaf2339Box leaf2339Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk202ValidityFacts chi118ValidityFacts
    leaf2339LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2339CoverageChecked :
    coverageCheck (innerAD leaf2339Box) leaf2339InnerLog = true := by
  rfl'

private theorem leaf2339InnerLogValid :
    leaf2339InnerLog.Valid 8 (innerAD leaf2339Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint62PositiveFacts.valid leaf2339CoverageChecked

private noncomputable def leaf2339InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907331/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2339InputLogOnePlusV_eq :
    leaf2339InputLogOnePlusV = outerEnclosure 24
      (leaf2339Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2339RoundedFacts : LeafRoundedFacts 8
    leaf2339Certificate.logOnePlusV leaf2339InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2339InputLogOnePlusV_eq }

private noncomputable def leaf2339Inputs : Inputs :=
  inputsOfCaches globalInput sk202RoundedInputs
    chi118InputQChi innerPair68Input
    leaf2339InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2339LowerChecked :
    lowerCheck 24 leaf2339Box leaf2339Inputs = true := by
  rfl'

private theorem leaf2339CoversExact : CoversExact 8
    leaf2339Box leaf2339Certificate leaf2339InnerLog leaf2339Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk202RoundedFacts chi118RoundedFacts
    innerPair68RoundedFacts leaf2339RoundedFacts (by rfl)

private theorem leaf2339FlatSound : Sound leaf2339Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2339CertificateValid
    leaf2339InnerLogValid leaf2339CoversExact leaf2339LowerChecked

private noncomputable def leaf2340Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (211/64), chiLo := (27/128), chiHi := (7/32) }

private noncomputable def leaf2340Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871389/536870912) }, vSqrt := { lower := (65529/65536), upper := (27487384371/27486580736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (908404109/536870912) }, upper := { exponent := 0, mantissa := (3525/2048) } }, logOuter := sk203LogOuterCertificate, logK := sk203LogKCertificate, logChi := chi118LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (54973965107/54973161472) } }, logDArg := sk203LogDArgCertificate }

private noncomputable def leaf2340InnerLog : WideLogData :=
  innerPair70Data

set_option maxRecDepth 1000000 in
private theorem leaf2340LocalValidity :
    LeafFacts leaf2340Box leaf2340Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2340Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (27487384371/27486580736) }) = true
      norm_num [leaf2340Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2340CertificateValid :
    WideCertificateValid leaf2340Box leaf2340Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk203ValidityFacts chi118ValidityFacts
    leaf2340LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2340CoverageChecked :
    coverageCheck (innerAD leaf2340Box) leaf2340InnerLog = true := by
  rfl'

private theorem leaf2340InnerLogValid :
    leaf2340InnerLog.Valid 8 (innerAD leaf2340Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint139PositiveFacts.valid leaf2340CoverageChecked

private noncomputable def leaf2340InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814663/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2340InputLogOnePlusV_eq :
    leaf2340InputLogOnePlusV = outerEnclosure 24
      (leaf2340Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2340RoundedFacts : LeafRoundedFacts 8
    leaf2340Certificate.logOnePlusV leaf2340InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2340InputLogOnePlusV_eq }

private noncomputable def leaf2340Inputs : Inputs :=
  inputsOfCaches globalInput sk203RoundedInputs
    chi118InputQChi innerPair70Input
    leaf2340InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2340LowerChecked :
    lowerCheck 24 leaf2340Box leaf2340Inputs = true := by
  rfl'

private theorem leaf2340CoversExact : CoversExact 8
    leaf2340Box leaf2340Certificate leaf2340InnerLog leaf2340Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk203RoundedFacts chi118RoundedFacts
    innerPair70RoundedFacts leaf2340RoundedFacts (by rfl)

private theorem leaf2340FlatSound : Sound leaf2340Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2340CertificateValid
    leaf2340InnerLogValid leaf2340CoversExact leaf2340LowerChecked

private noncomputable def leaf2341Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (211/64), kHi := (53/16), chiLo := (27/128), chiHi := (7/32) }

private noncomputable def leaf2341Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871391/536870912) }, vSqrt := { lower := (65529/65536), upper := (45812307285/45810958336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (910173471/536870912) }, upper := { exponent := 0, mantissa := (883/512) } }, logOuter := sk204LogOuterCertificate, logK := sk204LogKCertificate, logChi := chi118LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (91623265621/91621916672) } }, logDArg := sk204LogDArgCertificate }

private noncomputable def leaf2341InnerLog : WideLogData :=
  innerPair70Data

set_option maxRecDepth 1000000 in
private theorem leaf2341LocalValidity :
    LeafFacts leaf2341Box leaf2341Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2341Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (45812307285/45810958336) }) = true
      norm_num [leaf2341Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2341CertificateValid :
    WideCertificateValid leaf2341Box leaf2341Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk204ValidityFacts chi118ValidityFacts
    leaf2341LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2341CoverageChecked :
    coverageCheck (innerAD leaf2341Box) leaf2341InnerLog = true := by
  rfl'

private theorem leaf2341InnerLogValid :
    leaf2341InnerLog.Valid 8 (innerAD leaf2341Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint139PositiveFacts.valid leaf2341CoverageChecked

private noncomputable def leaf2341InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (726833/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf2341InputLogOnePlusV_eq :
    leaf2341InputLogOnePlusV = outerEnclosure 24
      (leaf2341Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2341RoundedFacts : LeafRoundedFacts 8
    leaf2341Certificate.logOnePlusV leaf2341InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2341InputLogOnePlusV_eq }

private noncomputable def leaf2341Inputs : Inputs :=
  inputsOfCaches globalInput sk204RoundedInputs
    chi118InputQChi innerPair70Input
    leaf2341InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2341LowerChecked :
    lowerCheck 24 leaf2341Box leaf2341Inputs = true := by
  rfl'

private theorem leaf2341CoversExact : CoversExact 8
    leaf2341Box leaf2341Certificate leaf2341InnerLog leaf2341Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk204RoundedFacts chi118RoundedFacts
    innerPair70RoundedFacts leaf2341RoundedFacts (by rfl)

private theorem leaf2341FlatSound : Sound leaf2341Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2341CertificateValid
    leaf2341InnerLogValid leaf2341CoversExact leaf2341LowerChecked

private noncomputable def leaf2342Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (213/64), chiLo := (13/64), chiHi := (27/128) }

private noncomputable def leaf2342Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871391/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433064448) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (898050051/536870912) }, upper := { exponent := 0, mantissa := (13943/8192) } }, logOuter := sk207LogOuterCertificate, logK := sk207LogKCertificate, logChi := chi117LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869986303/274866128896) } }, logDArg := sk207LogDArgCertificate }

private noncomputable def leaf2342InnerLog : WideLogData :=
  innerPair420Data

set_option maxRecDepth 1000000 in
private theorem leaf2342LocalValidity :
    LeafFacts leaf2342Box leaf2342Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2342Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433064448) }) = true
      norm_num [leaf2342Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2342CertificateValid :
    WideCertificateValid leaf2342Box leaf2342Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk207ValidityFacts chi117ValidityFacts
    leaf2342LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2342CoverageChecked :
    coverageCheck (innerAD leaf2342Box) leaf2342InnerLog = true := by
  rfl'

private theorem leaf2342InnerLogValid :
    leaf2342InnerLog.Valid 8 (innerAD leaf2342Box) :=
  wideLogDataValid_of_cachedCheck endpoint133PositiveFacts
    endpoint20PositiveFacts.valid leaf2342CoverageChecked

private noncomputable def leaf2342InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907329/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2342InputLogOnePlusV_eq :
    leaf2342InputLogOnePlusV = outerEnclosure 24
      (leaf2342Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2342RoundedFacts : LeafRoundedFacts 8
    leaf2342Certificate.logOnePlusV leaf2342InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2342InputLogOnePlusV_eq }

private noncomputable def leaf2342Inputs : Inputs :=
  inputsOfCaches globalInput sk207RoundedInputs
    chi117InputQChi innerPair420Input
    leaf2342InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2342LowerChecked :
    lowerCheck 24 leaf2342Box leaf2342Inputs = true := by
  rfl'

private theorem leaf2342CoversExact : CoversExact 8
    leaf2342Box leaf2342Certificate leaf2342InnerLog leaf2342Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk207RoundedFacts chi117RoundedFacts
    innerPair420RoundedFacts leaf2342RoundedFacts (by rfl)

private theorem leaf2342FlatSound : Sound leaf2342Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2342CertificateValid
    leaf2342InnerLogValid leaf2342CoversExact leaf2342LowerChecked

private noncomputable def leaf2343Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (213/64), kHi := (107/32), chiLo := (13/64), chiHi := (27/128) }

private noncomputable def leaf2343Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871393/536870912) }, vSqrt := { lower := (65529/65536), upper := (27487384371/27486607360) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (899753881/536870912) }, upper := { exponent := 0, mantissa := (6985/4096) } }, logOuter := sk208LogOuterCertificate, logK := sk208LogKCertificate, logChi := chi117LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (54973991731/54973214720) } }, logDArg := sk208LogDArgCertificate }

private noncomputable def leaf2343InnerLog : WideLogData :=
  innerPair189Data

set_option maxRecDepth 1000000 in
private theorem leaf2343LocalValidity :
    LeafFacts leaf2343Box leaf2343Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2343Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (27487384371/27486607360) }) = true
      norm_num [leaf2343Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2343CertificateValid :
    WideCertificateValid leaf2343Box leaf2343Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk208ValidityFacts chi117ValidityFacts
    leaf2343LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2343CoverageChecked :
    coverageCheck (innerAD leaf2343Box) leaf2343InnerLog = true := by
  rfl'

private theorem leaf2343InnerLogValid :
    leaf2343InnerLog.Valid 8 (innerAD leaf2343Box) :=
  wideLogDataValid_of_cachedCheck endpoint56PositiveFacts
    endpoint136PositiveFacts.valid leaf2343CoverageChecked

private noncomputable def leaf2343InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814659/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2343InputLogOnePlusV_eq :
    leaf2343InputLogOnePlusV = outerEnclosure 24
      (leaf2343Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2343RoundedFacts : LeafRoundedFacts 8
    leaf2343Certificate.logOnePlusV leaf2343InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2343InputLogOnePlusV_eq }

private noncomputable def leaf2343Inputs : Inputs :=
  inputsOfCaches globalInput sk208RoundedInputs
    chi117InputQChi innerPair189Input
    leaf2343InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2343LowerChecked :
    lowerCheck 24 leaf2343Box leaf2343Inputs = true := by
  rfl'

private theorem leaf2343CoversExact : CoversExact 8
    leaf2343Box leaf2343Certificate leaf2343InnerLog leaf2343Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk208RoundedFacts chi117RoundedFacts
    innerPair189RoundedFacts leaf2343RoundedFacts (by rfl)

private theorem leaf2343FlatSound : Sound leaf2343Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2343CertificateValid
    leaf2343InnerLogValid leaf2343CoversExact leaf2343LowerChecked

private noncomputable def leaf2344Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (215/64), chiLo := (13/64), chiHi := (27/128) }

private noncomputable def leaf2344Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871395/536870912) }, vSqrt := { lower := (65529/65536), upper := (8084524815/8084294656) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (901457711/536870912) }, upper := { exponent := 0, mantissa := (13997/8192) } }, logOuter := sk205LogOuterCertificate, logK := sk205LogKCertificate, logChi := chi117LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (16168819471/16168589312) } }, logDArg := sk205LogDArgCertificate }

private noncomputable def leaf2344InnerLog : WideLogData :=
  innerPair192Data

set_option maxRecDepth 1000000 in
private theorem leaf2344LocalValidity :
    LeafFacts leaf2344Box leaf2344Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2344Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8084524815/8084294656) }) = true
      norm_num [leaf2344Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2344CertificateValid :
    WideCertificateValid leaf2344Box leaf2344Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk205ValidityFacts chi117ValidityFacts
    leaf2344LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2344CoverageChecked :
    coverageCheck (innerAD leaf2344Box) leaf2344InnerLog = true := by
  rfl'

private theorem leaf2344InnerLogValid :
    leaf2344InnerLog.Valid 8 (innerAD leaf2344Box) :=
  wideLogDataValid_of_cachedCheck endpoint56PositiveFacts
    endpoint175PositiveFacts.valid leaf2344CoverageChecked

private noncomputable def leaf2344InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453665/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf2344InputLogOnePlusV_eq :
    leaf2344InputLogOnePlusV = outerEnclosure 24
      (leaf2344Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2344RoundedFacts : LeafRoundedFacts 8
    leaf2344Certificate.logOnePlusV leaf2344InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2344InputLogOnePlusV_eq }

private noncomputable def leaf2344Inputs : Inputs :=
  inputsOfCaches globalInput sk205RoundedInputs
    chi117InputQChi innerPair192Input
    leaf2344InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2344LowerChecked :
    lowerCheck 24 leaf2344Box leaf2344Inputs = true := by
  rfl'

private theorem leaf2344CoversExact : CoversExact 8
    leaf2344Box leaf2344Certificate leaf2344InnerLog leaf2344Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk205RoundedFacts chi117RoundedFacts
    innerPair192RoundedFacts leaf2344RoundedFacts (by rfl)

private theorem leaf2344FlatSound : Sound leaf2344Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2344CertificateValid
    leaf2344InnerLogValid leaf2344CoversExact leaf2344LowerChecked

private noncomputable def leaf2345Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (215/64), kHi := (27/8), chiLo := (13/64), chiHi := (53/256) }

private noncomputable def leaf2345Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742361/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433092096) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1806356281/1073741824) }, upper := { exponent := 0, mantissa := (3479/2048) } }, logOuter := sk206LogOuterCertificate, logK := sk206LogKCertificate, logChi := chi195LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870013951/274866184192) } }, logDArg := sk206LogDArgCertificate }

private noncomputable def leaf2345InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf2345LocalValidity :
    LeafFacts leaf2345Box leaf2345Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2345Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433092096) }) = true
      norm_num [leaf2345Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2345CertificateValid :
    WideCertificateValid leaf2345Box leaf2345Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk206ValidityFacts chi195ValidityFacts
    leaf2345LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2345CoverageChecked :
    coverageCheck (innerAD leaf2345Box) leaf2345InnerLog = true := by
  rfl'

private theorem leaf2345InnerLogValid :
    leaf2345InnerLog.Valid 8 (innerAD leaf2345Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf2345CoverageChecked

private noncomputable def leaf2345InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629315/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2345InputLogOnePlusV_eq :
    leaf2345InputLogOnePlusV = outerEnclosure 24
      (leaf2345Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2345RoundedFacts : LeafRoundedFacts 8
    leaf2345Certificate.logOnePlusV leaf2345InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2345InputLogOnePlusV_eq }

private noncomputable def leaf2345Inputs : Inputs :=
  inputsOfCaches globalInput sk206RoundedInputs
    chi195InputQChi innerPair57Input
    leaf2345InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2345LowerChecked :
    lowerCheck 24 leaf2345Box leaf2345Inputs = true := by
  rfl'

private theorem leaf2345CoversExact : CoversExact 8
    leaf2345Box leaf2345Certificate leaf2345InnerLog leaf2345Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk206RoundedFacts chi195RoundedFacts
    innerPair57RoundedFacts leaf2345RoundedFacts (by rfl)

private theorem leaf2345FlatSound : Sound leaf2345Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2345CertificateValid
    leaf2345InnerLogValid leaf2345CoversExact leaf2345LowerChecked

private noncomputable def leaf2346Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (215/64), kHi := (27/8), chiLo := (53/256), chiHi := (27/128) }

private noncomputable def leaf2346Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742363/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432981504) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1820445659/1073741824) }, upper := { exponent := 0, mantissa := (1753/1024) } }, logOuter := sk206LogOuterCertificate, logK := sk206LogKCertificate, logChi := chi196LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869903359/274865963008) } }, logDArg := sk206LogDArgCertificate }

private noncomputable def leaf2346InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf2346LocalValidity :
    LeafFacts leaf2346Box leaf2346Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2346Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432981504) }) = true
      norm_num [leaf2346Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2346CertificateValid :
    WideCertificateValid leaf2346Box leaf2346Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk206ValidityFacts chi196ValidityFacts
    leaf2346LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2346CoverageChecked :
    coverageCheck (innerAD leaf2346Box) leaf2346InnerLog = true := by
  rfl'

private theorem leaf2346InnerLogValid :
    leaf2346InnerLog.Valid 8 (innerAD leaf2346Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf2346CoverageChecked

private noncomputable def leaf2346InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629321/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2346InputLogOnePlusV_eq :
    leaf2346InputLogOnePlusV = outerEnclosure 24
      (leaf2346Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2346RoundedFacts : LeafRoundedFacts 8
    leaf2346Certificate.logOnePlusV leaf2346InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2346InputLogOnePlusV_eq }

private noncomputable def leaf2346Inputs : Inputs :=
  inputsOfCaches globalInput sk206RoundedInputs
    chi196InputQChi innerPair64Input
    leaf2346InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2346LowerChecked :
    lowerCheck 24 leaf2346Box leaf2346Inputs = true := by
  rfl'

private theorem leaf2346CoversExact : CoversExact 8
    leaf2346Box leaf2346Certificate leaf2346InnerLog leaf2346Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk206RoundedFacts chi196RoundedFacts
    innerPair64RoundedFacts leaf2346RoundedFacts (by rfl)

private theorem leaf2346FlatSound : Sound leaf2346Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2346CertificateValid
    leaf2346InnerLogValid leaf2346CoversExact leaf2346LowerChecked

private noncomputable def leaf2347Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (213/64), chiLo := (27/128), chiHi := (7/32) }

private noncomputable def leaf2347Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871393/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432846336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (911942833/536870912) }, upper := { exponent := 0, mantissa := (3539/2048) } }, logOuter := sk207LogOuterCertificate, logK := sk207LogKCertificate, logChi := chi118LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869768191/274865692672) } }, logDArg := sk207LogDArgCertificate }

private noncomputable def leaf2347InnerLog : WideLogData :=
  innerPair70Data

set_option maxRecDepth 1000000 in
private theorem leaf2347LocalValidity :
    LeafFacts leaf2347Box leaf2347Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2347Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432846336) }) = true
      norm_num [leaf2347Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2347CertificateValid :
    WideCertificateValid leaf2347Box leaf2347Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk207ValidityFacts chi118ValidityFacts
    leaf2347LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2347CoverageChecked :
    coverageCheck (innerAD leaf2347Box) leaf2347InnerLog = true := by
  rfl'

private theorem leaf2347InnerLogValid :
    leaf2347InnerLog.Valid 8 (innerAD leaf2347Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint139PositiveFacts.valid leaf2347CoverageChecked

private noncomputable def leaf2347InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814665/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2347InputLogOnePlusV_eq :
    leaf2347InputLogOnePlusV = outerEnclosure 24
      (leaf2347Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2347RoundedFacts : LeafRoundedFacts 8
    leaf2347Certificate.logOnePlusV leaf2347InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2347InputLogOnePlusV_eq }

private noncomputable def leaf2347Inputs : Inputs :=
  inputsOfCaches globalInput sk207RoundedInputs
    chi118InputQChi innerPair70Input
    leaf2347InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2347LowerChecked :
    lowerCheck 24 leaf2347Box leaf2347Inputs = true := by
  rfl'

private theorem leaf2347CoversExact : CoversExact 8
    leaf2347Box leaf2347Certificate leaf2347InnerLog leaf2347Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk207RoundedFacts chi118RoundedFacts
    innerPair70RoundedFacts leaf2347RoundedFacts (by rfl)

private theorem leaf2347FlatSound : Sound leaf2347Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2347CertificateValid
    leaf2347InnerLogValid leaf2347CoversExact leaf2347LowerChecked

private noncomputable def leaf2348Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (213/64), kHi := (107/32), chiLo := (27/128), chiHi := (7/32) }

private noncomputable def leaf2348Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871395/536870912) }, vSqrt := { lower := (65529/65536), upper := (8084524815/8084283392) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (913712195/536870912) }, upper := { exponent := 0, mantissa := (1773/1024) } }, logOuter := sk208LogOuterCertificate, logK := sk208LogKCertificate, logChi := chi118LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (16168808207/16168566784) } }, logDArg := sk208LogDArgCertificate }

private noncomputable def leaf2348InnerLog : WideLogData :=
  innerPair70Data

set_option maxRecDepth 1000000 in
private theorem leaf2348LocalValidity :
    LeafFacts leaf2348Box leaf2348Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2348Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8084524815/8084283392) }) = true
      norm_num [leaf2348Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2348CertificateValid :
    WideCertificateValid leaf2348Box leaf2348Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk208ValidityFacts chi118ValidityFacts
    leaf2348LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2348CoverageChecked :
    coverageCheck (innerAD leaf2348Box) leaf2348InnerLog = true := by
  rfl'

private theorem leaf2348InnerLogValid :
    leaf2348InnerLog.Valid 8 (innerAD leaf2348Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint139PositiveFacts.valid leaf2348CoverageChecked

private noncomputable def leaf2348InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629331/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2348InputLogOnePlusV_eq :
    leaf2348InputLogOnePlusV = outerEnclosure 24
      (leaf2348Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2348RoundedFacts : LeafRoundedFacts 8
    leaf2348Certificate.logOnePlusV leaf2348InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2348InputLogOnePlusV_eq }

private noncomputable def leaf2348Inputs : Inputs :=
  inputsOfCaches globalInput sk208RoundedInputs
    chi118InputQChi innerPair70Input
    leaf2348InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2348LowerChecked :
    lowerCheck 24 leaf2348Box leaf2348Inputs = true := by
  rfl'

private theorem leaf2348CoversExact : CoversExact 8
    leaf2348Box leaf2348Certificate leaf2348InnerLog leaf2348Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk208RoundedFacts chi118RoundedFacts
    innerPair70RoundedFacts leaf2348RoundedFacts (by rfl)

private theorem leaf2348FlatSound : Sound leaf2348Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2348CertificateValid
    leaf2348InnerLogValid leaf2348CoversExact leaf2348LowerChecked

private noncomputable def leaf2349Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (215/64), chiLo := (27/128), chiHi := (7/32) }

private noncomputable def leaf2349Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871397/536870912) }, vSqrt := { lower := (65529/65536), upper := (5090256365/5090103296) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (915481557/536870912) }, upper := { exponent := 0, mantissa := (3553/2048) } }, logOuter := sk205LogOuterCertificate, logK := sk205LogKCertificate, logChi := chi118LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (10180359661/10180206592) } }, logDArg := sk205LogDArgCertificate }

private noncomputable def leaf2349InnerLog : WideLogData :=
  innerPair457Data

set_option maxRecDepth 1000000 in
private theorem leaf2349LocalValidity :
    LeafFacts leaf2349Box leaf2349Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2349Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (5090256365/5090103296) }) = true
      norm_num [leaf2349Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2349CertificateValid :
    WideCertificateValid leaf2349Box leaf2349Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk205ValidityFacts chi118ValidityFacts
    leaf2349LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2349CoverageChecked :
    coverageCheck (innerAD leaf2349Box) leaf2349InnerLog = true := by
  rfl'

private theorem leaf2349InnerLogValid :
    leaf2349InnerLog.Valid 8 (innerAD leaf2349Box) :=
  wideLogDataValid_of_cachedCheck endpoint176PositiveFacts
    endpoint177PositiveFacts.valid leaf2349CoverageChecked

private noncomputable def leaf2349InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629333/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2349InputLogOnePlusV_eq :
    leaf2349InputLogOnePlusV = outerEnclosure 24
      (leaf2349Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2349RoundedFacts : LeafRoundedFacts 8
    leaf2349Certificate.logOnePlusV leaf2349InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2349InputLogOnePlusV_eq }

private noncomputable def leaf2349Inputs : Inputs :=
  inputsOfCaches globalInput sk205RoundedInputs
    chi118InputQChi innerPair457Input
    leaf2349InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2349LowerChecked :
    lowerCheck 24 leaf2349Box leaf2349Inputs = true := by
  rfl'

private theorem leaf2349CoversExact : CoversExact 8
    leaf2349Box leaf2349Certificate leaf2349InnerLog leaf2349Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk205RoundedFacts chi118RoundedFacts
    innerPair457RoundedFacts leaf2349RoundedFacts (by rfl)

private theorem leaf2349FlatSound : Sound leaf2349Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2349CertificateValid
    leaf2349InnerLogValid leaf2349CoversExact leaf2349LowerChecked

private noncomputable def leaf2350Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (215/64), kHi := (27/8), chiLo := (27/128), chiHi := (55/256) }

private noncomputable def leaf2350Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742365/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432870912) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1834535037/1073741824) }, upper := { exponent := 0, mantissa := (3533/2048) } }, logOuter := sk206LogOuterCertificate, logK := sk206LogKCertificate, logChi := chi197LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869792767/274865741824) } }, logDArg := sk206LogDArgCertificate }

private noncomputable def leaf2350InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf2350LocalValidity :
    LeafFacts leaf2350Box leaf2350Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2350Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432870912) }) = true
      norm_num [leaf2350Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2350CertificateValid :
    WideCertificateValid leaf2350Box leaf2350Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk206ValidityFacts chi197ValidityFacts
    leaf2350LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2350CoverageChecked :
    coverageCheck (innerAD leaf2350Box) leaf2350InnerLog = true := by
  rfl'

private theorem leaf2350InnerLogValid :
    leaf2350InnerLog.Valid 8 (innerAD leaf2350Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf2350CoverageChecked

private noncomputable def leaf2350InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (726833/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf2350InputLogOnePlusV_eq :
    leaf2350InputLogOnePlusV = outerEnclosure 24
      (leaf2350Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2350RoundedFacts : LeafRoundedFacts 8
    leaf2350Certificate.logOnePlusV leaf2350InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2350InputLogOnePlusV_eq }

private noncomputable def leaf2350Inputs : Inputs :=
  inputsOfCaches globalInput sk206RoundedInputs
    chi197InputQChi innerPair64Input
    leaf2350InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2350LowerChecked :
    lowerCheck 24 leaf2350Box leaf2350Inputs = true := by
  rfl'

private theorem leaf2350CoversExact : CoversExact 8
    leaf2350Box leaf2350Certificate leaf2350InnerLog leaf2350Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk206RoundedFacts chi197RoundedFacts
    innerPair64RoundedFacts leaf2350RoundedFacts (by rfl)

private theorem leaf2350FlatSound : Sound leaf2350Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2350CertificateValid
    leaf2350InnerLogValid leaf2350CoversExact leaf2350LowerChecked

private noncomputable def leaf2351Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (215/64), kHi := (27/8), chiLo := (55/256), chiHi := (7/32) }

private noncomputable def leaf2351Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742367/1073741824) }, vSqrt := { lower := (65529/65536), upper := (27487384371/27486552064) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1848624415/1073741824) }, upper := { exponent := 0, mantissa := (445/256) } }, logOuter := sk206LogOuterCertificate, logK := sk206LogKCertificate, logChi := chi198LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (54973936435/54973104128) } }, logDArg := sk206LogDArgCertificate }

private noncomputable def leaf2351InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf2351LocalValidity :
    LeafFacts leaf2351Box leaf2351Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2351Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (27487384371/27486552064) }) = true
      norm_num [leaf2351Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2351CertificateValid :
    WideCertificateValid leaf2351Box leaf2351Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk206ValidityFacts chi198ValidityFacts
    leaf2351LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2351CoverageChecked :
    coverageCheck (innerAD leaf2351Box) leaf2351InnerLog = true := by
  rfl'

private theorem leaf2351InnerLogValid :
    leaf2351InnerLog.Valid 8 (innerAD leaf2351Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf2351CoverageChecked

private noncomputable def leaf2351InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629335/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2351InputLogOnePlusV_eq :
    leaf2351InputLogOnePlusV = outerEnclosure 24
      (leaf2351Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2351RoundedFacts : LeafRoundedFacts 8
    leaf2351Certificate.logOnePlusV leaf2351InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2351InputLogOnePlusV_eq }

private noncomputable def leaf2351Inputs : Inputs :=
  inputsOfCaches globalInput sk206RoundedInputs
    chi198InputQChi innerPair64Input
    leaf2351InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2351LowerChecked :
    lowerCheck 24 leaf2351Box leaf2351Inputs = true := by
  rfl'

private theorem leaf2351CoversExact : CoversExact 8
    leaf2351Box leaf2351Certificate leaf2351InnerLog leaf2351Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk206RoundedFacts chi198RoundedFacts
    innerPair64RoundedFacts leaf2351RoundedFacts (by rfl)

private theorem leaf2351FlatSound : Sound leaf2351Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2351CertificateValid
    leaf2351InnerLogValid leaf2351CoversExact leaf2351LowerChecked

private noncomputable def component50Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (3/16), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component50Node0_sound : Sound component50Node0Box :=
  sound_of_literal_split component50Node0Box leaf2316Box leaf2317Box
    .chi (49/256) (by rfl) (by rfl)
    leaf2316FlatSound leaf2317FlatSound

private noncomputable def component50Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (3/16), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component50Node1_sound : Sound component50Node1Box :=
  sound_of_literal_split component50Node1Box leaf2318Box leaf2319Box
    .chi (49/256) (by rfl) (by rfl)
    leaf2318FlatSound leaf2319FlatSound

private noncomputable def component50Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (3/16), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component50Node2_sound : Sound component50Node2Box :=
  sound_of_literal_split component50Node2Box component50Node0Box component50Node1Box
    .k (105/32) (by rfl) (by rfl)
    component50Node0_sound component50Node1_sound

private noncomputable def component50Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (25/128), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component50Node3_sound : Sound component50Node3Box :=
  sound_of_literal_split component50Node3Box leaf2320Box leaf2321Box
    .k (209/64) (by rfl) (by rfl)
    leaf2320FlatSound leaf2321FlatSound

private noncomputable def component50Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (25/128), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component50Node4_sound : Sound component50Node4Box :=
  sound_of_literal_split component50Node4Box leaf2322Box leaf2323Box
    .k (211/64) (by rfl) (by rfl)
    leaf2322FlatSound leaf2323FlatSound

private noncomputable def component50Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (25/128), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component50Node5_sound : Sound component50Node5Box :=
  sound_of_literal_split component50Node5Box component50Node3Box component50Node4Box
    .k (105/32) (by rfl) (by rfl)
    component50Node3_sound component50Node4_sound

private noncomputable def component50Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (3/16), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component50Node6_sound : Sound component50Node6Box :=
  sound_of_literal_split component50Node6Box component50Node2Box component50Node5Box
    .chi (25/128) (by rfl) (by rfl)
    component50Node2_sound component50Node5_sound

private noncomputable def component50Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (3/16), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component50Node7_sound : Sound component50Node7Box :=
  sound_of_literal_split component50Node7Box leaf2324Box leaf2325Box
    .chi (49/256) (by rfl) (by rfl)
    leaf2324FlatSound leaf2325FlatSound

private noncomputable def component50Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (49/256), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component50Node8_sound : Sound component50Node8Box :=
  sound_of_literal_split component50Node8Box leaf2327Box leaf2328Box
    .k (215/64) (by rfl) (by rfl)
    leaf2327FlatSound leaf2328FlatSound

private noncomputable def component50Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (3/16), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component50Node9_sound : Sound component50Node9Box :=
  sound_of_literal_split component50Node9Box leaf2326Box component50Node8Box
    .chi (49/256) (by rfl) (by rfl)
    leaf2326FlatSound component50Node8_sound

private noncomputable def component50Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (3/16), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component50Node10_sound : Sound component50Node10Box :=
  sound_of_literal_split component50Node10Box component50Node7Box component50Node9Box
    .k (107/32) (by rfl) (by rfl)
    component50Node7_sound component50Node9_sound

private noncomputable def component50Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (25/128), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component50Node11_sound : Sound component50Node11Box :=
  sound_of_literal_split component50Node11Box leaf2329Box leaf2330Box
    .k (213/64) (by rfl) (by rfl)
    leaf2329FlatSound leaf2330FlatSound

private noncomputable def component50Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (215/64), kHi := (27/8), chiLo := (25/128), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component50Node12_sound : Sound component50Node12Box :=
  sound_of_literal_split component50Node12Box leaf2332Box leaf2333Box
    .chi (51/256) (by rfl) (by rfl)
    leaf2332FlatSound leaf2333FlatSound

private noncomputable def component50Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (25/128), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component50Node13_sound : Sound component50Node13Box :=
  sound_of_literal_split component50Node13Box leaf2331Box component50Node12Box
    .k (215/64) (by rfl) (by rfl)
    leaf2331FlatSound component50Node12_sound

private noncomputable def component50Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (25/128), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component50Node14_sound : Sound component50Node14Box :=
  sound_of_literal_split component50Node14Box component50Node11Box component50Node13Box
    .k (107/32) (by rfl) (by rfl)
    component50Node11_sound component50Node13_sound

private noncomputable def component50Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (3/16), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component50Node15_sound : Sound component50Node15Box :=
  sound_of_literal_split component50Node15Box component50Node10Box component50Node14Box
    .chi (25/128) (by rfl) (by rfl)
    component50Node10_sound component50Node14_sound

private noncomputable def component50Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (3/16), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component50Node16_sound : Sound component50Node16Box :=
  sound_of_literal_split component50Node16Box component50Node6Box component50Node15Box
    .k (53/16) (by rfl) (by rfl)
    component50Node6_sound component50Node15_sound

private noncomputable def component50Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (13/64), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component50Node17_sound : Sound component50Node17Box :=
  sound_of_literal_split component50Node17Box leaf2334Box leaf2335Box
    .k (209/64) (by rfl) (by rfl)
    leaf2334FlatSound leaf2335FlatSound

private noncomputable def component50Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (13/64), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component50Node18_sound : Sound component50Node18Box :=
  sound_of_literal_split component50Node18Box leaf2336Box leaf2337Box
    .k (211/64) (by rfl) (by rfl)
    leaf2336FlatSound leaf2337FlatSound

private noncomputable def component50Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (13/64), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component50Node19_sound : Sound component50Node19Box :=
  sound_of_literal_split component50Node19Box component50Node17Box component50Node18Box
    .k (105/32) (by rfl) (by rfl)
    component50Node17_sound component50Node18_sound

private noncomputable def component50Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (27/128), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component50Node20_sound : Sound component50Node20Box :=
  sound_of_literal_split component50Node20Box leaf2338Box leaf2339Box
    .k (209/64) (by rfl) (by rfl)
    leaf2338FlatSound leaf2339FlatSound

private noncomputable def component50Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (27/128), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component50Node21_sound : Sound component50Node21Box :=
  sound_of_literal_split component50Node21Box leaf2340Box leaf2341Box
    .k (211/64) (by rfl) (by rfl)
    leaf2340FlatSound leaf2341FlatSound

private noncomputable def component50Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (27/128), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component50Node22_sound : Sound component50Node22Box :=
  sound_of_literal_split component50Node22Box component50Node20Box component50Node21Box
    .k (105/32) (by rfl) (by rfl)
    component50Node20_sound component50Node21_sound

private noncomputable def component50Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component50Node23_sound : Sound component50Node23Box :=
  sound_of_literal_split component50Node23Box component50Node19Box component50Node22Box
    .chi (27/128) (by rfl) (by rfl)
    component50Node19_sound component50Node22_sound

private noncomputable def component50Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (13/64), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component50Node24_sound : Sound component50Node24Box :=
  sound_of_literal_split component50Node24Box leaf2342Box leaf2343Box
    .k (213/64) (by rfl) (by rfl)
    leaf2342FlatSound leaf2343FlatSound

private noncomputable def component50Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (215/64), kHi := (27/8), chiLo := (13/64), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component50Node25_sound : Sound component50Node25Box :=
  sound_of_literal_split component50Node25Box leaf2345Box leaf2346Box
    .chi (53/256) (by rfl) (by rfl)
    leaf2345FlatSound leaf2346FlatSound

private noncomputable def component50Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (13/64), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component50Node26_sound : Sound component50Node26Box :=
  sound_of_literal_split component50Node26Box leaf2344Box component50Node25Box
    .k (215/64) (by rfl) (by rfl)
    leaf2344FlatSound component50Node25_sound

private noncomputable def component50Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (13/64), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component50Node27_sound : Sound component50Node27Box :=
  sound_of_literal_split component50Node27Box component50Node24Box component50Node26Box
    .k (107/32) (by rfl) (by rfl)
    component50Node24_sound component50Node26_sound

private noncomputable def component50Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (27/128), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component50Node28_sound : Sound component50Node28Box :=
  sound_of_literal_split component50Node28Box leaf2347Box leaf2348Box
    .k (213/64) (by rfl) (by rfl)
    leaf2347FlatSound leaf2348FlatSound

private noncomputable def component50Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (215/64), kHi := (27/8), chiLo := (27/128), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component50Node29_sound : Sound component50Node29Box :=
  sound_of_literal_split component50Node29Box leaf2350Box leaf2351Box
    .chi (55/256) (by rfl) (by rfl)
    leaf2350FlatSound leaf2351FlatSound

private noncomputable def component50Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (27/128), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component50Node30_sound : Sound component50Node30Box :=
  sound_of_literal_split component50Node30Box leaf2349Box component50Node29Box
    .k (215/64) (by rfl) (by rfl)
    leaf2349FlatSound component50Node29_sound

private noncomputable def component50Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (27/128), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component50Node31_sound : Sound component50Node31Box :=
  sound_of_literal_split component50Node31Box component50Node28Box component50Node30Box
    .k (107/32) (by rfl) (by rfl)
    component50Node28_sound component50Node30_sound

private noncomputable def component50Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component50Node32_sound : Sound component50Node32Box :=
  sound_of_literal_split component50Node32Box component50Node27Box component50Node31Box
    .chi (27/128) (by rfl) (by rfl)
    component50Node27_sound component50Node31_sound

private noncomputable def component50Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component50Node33_sound : Sound component50Node33Box :=
  sound_of_literal_split component50Node33Box component50Node23Box component50Node32Box
    .k (53/16) (by rfl) (by rfl)
    component50Node23_sound component50Node32_sound

noncomputable def component50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (3/16), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
theorem component50_sound : Sound component50Box :=
  sound_of_literal_split component50Box component50Node16Box component50Node33Box
    .chi (13/64) (by rfl) (by rfl)
    component50Node16_sound component50Node33_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
