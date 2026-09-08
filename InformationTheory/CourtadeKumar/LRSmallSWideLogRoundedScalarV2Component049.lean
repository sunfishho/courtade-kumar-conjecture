import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch6
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

private noncomputable def leaf2252Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (193/64), chiLo := (7/32), chiHi := (29/128) }

private noncomputable def leaf2252Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871355/536870912) }, vSqrt := { lower := (65529/65536), upper := (15270769095/15270358016) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (889137735/536870912) }, upper := { exponent := 0, mantissa := (13789/8192) } }, logOuter := sk185LogOuterCertificate, logK := sk185LogKCertificate, logChi := chi119LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (30541127111/30540716032) } }, logDArg := sk185LogDArgCertificate }

private noncomputable def leaf2252InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2252LocalValidity :
    LeafFacts leaf2252Box leaf2252Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2252Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (15270769095/15270358016) }) = true
      norm_num [leaf2252Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2252CertificateValid :
    WideCertificateValid leaf2252Box leaf2252Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk185ValidityFacts chi119ValidityFacts
    leaf2252LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2252CoverageChecked :
    coverageCheck (innerAD leaf2252Box) leaf2252InnerLog = true := by
  rfl'

private theorem leaf2252InnerLogValid :
    leaf2252InnerLog.Valid 8 (innerAD leaf2252Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2252CoverageChecked

private noncomputable def leaf2252InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629307/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2252InputLogOnePlusV_eq :
    leaf2252InputLogOnePlusV = outerEnclosure 24
      (leaf2252Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2252RoundedFacts : LeafRoundedFacts 8
    leaf2252Certificate.logOnePlusV leaf2252InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2252InputLogOnePlusV_eq }

private noncomputable def leaf2252Inputs : Inputs :=
  inputsOfCaches globalInput sk185RoundedInputs
    chi119InputQChi innerPair56Input
    leaf2252InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2252LowerChecked :
    lowerCheck 24 leaf2252Box leaf2252Inputs = true := by
  rfl'

private theorem leaf2252CoversExact : CoversExact 8
    leaf2252Box leaf2252Certificate leaf2252InnerLog leaf2252Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk185RoundedFacts chi119RoundedFacts
    innerPair56RoundedFacts leaf2252RoundedFacts (by rfl)

private theorem leaf2252FlatSound : Sound leaf2252Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2252CertificateValid
    leaf2252InnerLogValid leaf2252CoversExact leaf2252LowerChecked

private noncomputable def leaf2253Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (193/64), kHi := (97/32), chiLo := (7/32), chiHi := (29/128) }

private noncomputable def leaf2253Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871357/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433192448) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (890972629/536870912) }, upper := { exponent := 0, mantissa := (6909/4096) } }, logOuter := sk186LogOuterCertificate, logK := sk186LogKCertificate, logChi := chi119LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870114303/274866384896) } }, logDArg := sk186LogDArgCertificate }

private noncomputable def leaf2253InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2253LocalValidity :
    LeafFacts leaf2253Box leaf2253Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2253Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433192448) }) = true
      norm_num [leaf2253Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2253CertificateValid :
    WideCertificateValid leaf2253Box leaf2253Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk186ValidityFacts chi119ValidityFacts
    leaf2253LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2253CoverageChecked :
    coverageCheck (innerAD leaf2253Box) leaf2253InnerLog = true := by
  rfl'

private theorem leaf2253InnerLogValid :
    leaf2253InnerLog.Valid 8 (innerAD leaf2253Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2253CoverageChecked

private noncomputable def leaf2253InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907327/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2253InputLogOnePlusV_eq :
    leaf2253InputLogOnePlusV = outerEnclosure 24
      (leaf2253Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2253RoundedFacts : LeafRoundedFacts 8
    leaf2253Certificate.logOnePlusV leaf2253InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2253InputLogOnePlusV_eq }

private noncomputable def leaf2253Inputs : Inputs :=
  inputsOfCaches globalInput sk186RoundedInputs
    chi119InputQChi innerPair56Input
    leaf2253InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2253LowerChecked :
    lowerCheck 24 leaf2253Box leaf2253Inputs = true := by
  rfl'

private theorem leaf2253CoversExact : CoversExact 8
    leaf2253Box leaf2253Certificate leaf2253InnerLog leaf2253Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk186RoundedFacts chi119RoundedFacts
    innerPair56RoundedFacts leaf2253RoundedFacts (by rfl)

private theorem leaf2253FlatSound : Sound leaf2253Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2253CertificateValid
    leaf2253InnerLogValid leaf2253CoversExact leaf2253LowerChecked

private noncomputable def leaf2254Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (193/64), chiLo := (29/128), chiHi := (15/64) }

private noncomputable def leaf2254Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871357/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433024512) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (901719877/536870912) }, upper := { exponent := 0, mantissa := (6991/4096) } }, logOuter := sk185LogOuterCertificate, logK := sk185LogKCertificate, logChi := chi120LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869946367/274866049024) } }, logDArg := sk185LogDArgCertificate }

private noncomputable def leaf2254InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf2254LocalValidity :
    LeafFacts leaf2254Box leaf2254Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2254Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433024512) }) = true
      norm_num [leaf2254Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2254CertificateValid :
    WideCertificateValid leaf2254Box leaf2254Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk185ValidityFacts chi120ValidityFacts
    leaf2254LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2254CoverageChecked :
    coverageCheck (innerAD leaf2254Box) leaf2254InnerLog = true := by
  rfl'

private theorem leaf2254InnerLogValid :
    leaf2254InnerLog.Valid 8 (innerAD leaf2254Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf2254CoverageChecked

private noncomputable def leaf2254InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629319/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2254InputLogOnePlusV_eq :
    leaf2254InputLogOnePlusV = outerEnclosure 24
      (leaf2254Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2254RoundedFacts : LeafRoundedFacts 8
    leaf2254Certificate.logOnePlusV leaf2254InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2254InputLogOnePlusV_eq }

private noncomputable def leaf2254Inputs : Inputs :=
  inputsOfCaches globalInput sk185RoundedInputs
    chi120InputQChi innerPair57Input
    leaf2254InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2254LowerChecked :
    lowerCheck 24 leaf2254Box leaf2254Inputs = true := by
  rfl'

private theorem leaf2254CoversExact : CoversExact 8
    leaf2254Box leaf2254Certificate leaf2254InnerLog leaf2254Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk185RoundedFacts chi120RoundedFacts
    innerPair57RoundedFacts leaf2254RoundedFacts (by rfl)

private theorem leaf2254FlatSound : Sound leaf2254Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2254CertificateValid
    leaf2254InnerLogValid leaf2254CoversExact leaf2254LowerChecked

private noncomputable def leaf2255Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (193/64), kHi := (97/32), chiLo := (29/128), chiHi := (15/64) }

private noncomputable def leaf2255Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871359/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432993792) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (903620303/536870912) }, upper := { exponent := 0, mantissa := (3503/2048) } }, logOuter := sk186LogOuterCertificate, logK := sk186LogKCertificate, logChi := chi120LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869915647/274865987584) } }, logDArg := sk186LogDArgCertificate }

private noncomputable def leaf2255InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf2255LocalValidity :
    LeafFacts leaf2255Box leaf2255Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2255Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432993792) }) = true
      norm_num [leaf2255Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2255CertificateValid :
    WideCertificateValid leaf2255Box leaf2255Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk186ValidityFacts chi120ValidityFacts
    leaf2255LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2255CoverageChecked :
    coverageCheck (innerAD leaf2255Box) leaf2255InnerLog = true := by
  rfl'

private theorem leaf2255InnerLogValid :
    leaf2255InnerLog.Valid 8 (innerAD leaf2255Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf2255CoverageChecked

private noncomputable def leaf2255InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629321/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2255InputLogOnePlusV_eq :
    leaf2255InputLogOnePlusV = outerEnclosure 24
      (leaf2255Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2255RoundedFacts : LeafRoundedFacts 8
    leaf2255Certificate.logOnePlusV leaf2255InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2255InputLogOnePlusV_eq }

private noncomputable def leaf2255Inputs : Inputs :=
  inputsOfCaches globalInput sk186RoundedInputs
    chi120InputQChi innerPair57Input
    leaf2255InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2255LowerChecked :
    lowerCheck 24 leaf2255Box leaf2255Inputs = true := by
  rfl'

private theorem leaf2255CoversExact : CoversExact 8
    leaf2255Box leaf2255Certificate leaf2255InnerLog leaf2255Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk186RoundedFacts chi120RoundedFacts
    innerPair57RoundedFacts leaf2255RoundedFacts (by rfl)

private theorem leaf2255FlatSound : Sound leaf2255Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2255CertificateValid
    leaf2255InnerLogValid leaf2255CoversExact leaf2255LowerChecked

private noncomputable def leaf2256Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (195/64), chiLo := (7/32), chiHi := (29/128) }

private noncomputable def leaf2256Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871359/536870912) }, vSqrt := { lower := (65529/65536), upper := (3196207485/3196120064) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (892807523/536870912) }, upper := { exponent := 0, mantissa := (13847/8192) } }, logOuter := sk187LogOuterCertificate, logK := sk187LogKCertificate, logChi := chi119LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (6392327549/6392240128) } }, logDArg := sk187LogDArgCertificate }

private noncomputable def leaf2256InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf2256LocalValidity :
    LeafFacts leaf2256Box leaf2256Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2256Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (3196207485/3196120064) }) = true
      norm_num [leaf2256Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2256CertificateValid :
    WideCertificateValid leaf2256Box leaf2256Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk187ValidityFacts chi119ValidityFacts
    leaf2256LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2256CoverageChecked :
    coverageCheck (innerAD leaf2256Box) leaf2256InnerLog = true := by
  rfl'

private theorem leaf2256InnerLogValid :
    leaf2256InnerLog.Valid 8 (innerAD leaf2256Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf2256CoverageChecked

private noncomputable def leaf2256InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814655/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2256InputLogOnePlusV_eq :
    leaf2256InputLogOnePlusV = outerEnclosure 24
      (leaf2256Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2256RoundedFacts : LeafRoundedFacts 8
    leaf2256Certificate.logOnePlusV leaf2256InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2256InputLogOnePlusV_eq }

private noncomputable def leaf2256Inputs : Inputs :=
  inputsOfCaches globalInput sk187RoundedInputs
    chi119InputQChi innerPair57Input
    leaf2256InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2256LowerChecked :
    lowerCheck 24 leaf2256Box leaf2256Inputs = true := by
  rfl'

private theorem leaf2256CoversExact : CoversExact 8
    leaf2256Box leaf2256Certificate leaf2256InnerLog leaf2256Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk187RoundedFacts chi119RoundedFacts
    innerPair57RoundedFacts leaf2256RoundedFacts (by rfl)

private theorem leaf2256FlatSound : Sound leaf2256Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2256CertificateValid
    leaf2256InnerLogValid leaf2256CoversExact leaf2256LowerChecked

private noncomputable def leaf2257Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (195/64), kHi := (49/16), chiLo := (7/32), chiHi := (29/128) }

private noncomputable def leaf2257Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871361/536870912) }, vSqrt := { lower := (65529/65536), upper := (45812307285/45811044352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (894642417/536870912) }, upper := { exponent := 0, mantissa := (3469/2048) } }, logOuter := sk188LogOuterCertificate, logK := sk188LogKCertificate, logChi := chi119LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (91623351637/91622088704) } }, logDArg := sk188LogDArgCertificate }

private noncomputable def leaf2257InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf2257LocalValidity :
    LeafFacts leaf2257Box leaf2257Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2257Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (45812307285/45811044352) }) = true
      norm_num [leaf2257Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2257CertificateValid :
    WideCertificateValid leaf2257Box leaf2257Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk188ValidityFacts chi119ValidityFacts
    leaf2257LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2257CoverageChecked :
    coverageCheck (innerAD leaf2257Box) leaf2257InnerLog = true := by
  rfl'

private theorem leaf2257InnerLogValid :
    leaf2257InnerLog.Valid 8 (innerAD leaf2257Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf2257CoverageChecked

private noncomputable def leaf2257InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (45427/65536) }

set_option maxRecDepth 1000000 in
private theorem leaf2257InputLogOnePlusV_eq :
    leaf2257InputLogOnePlusV = outerEnclosure 24
      (leaf2257Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2257RoundedFacts : LeafRoundedFacts 8
    leaf2257Certificate.logOnePlusV leaf2257InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2257InputLogOnePlusV_eq }

private noncomputable def leaf2257Inputs : Inputs :=
  inputsOfCaches globalInput sk188RoundedInputs
    chi119InputQChi innerPair57Input
    leaf2257InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2257LowerChecked :
    lowerCheck 24 leaf2257Box leaf2257Inputs = true := by
  rfl'

private theorem leaf2257CoversExact : CoversExact 8
    leaf2257Box leaf2257Certificate leaf2257InnerLog leaf2257Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk188RoundedFacts chi119RoundedFacts
    innerPair57RoundedFacts leaf2257RoundedFacts (by rfl)

private theorem leaf2257FlatSound : Sound leaf2257Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2257CertificateValid
    leaf2257InnerLogValid leaf2257CoversExact leaf2257LowerChecked

private noncomputable def leaf2258Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (195/64), chiLo := (29/128), chiHi := (15/64) }

private noncomputable def leaf2258Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871361/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432963072) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (905520729/536870912) }, upper := { exponent := 0, mantissa := (7021/4096) } }, logOuter := sk187LogOuterCertificate, logK := sk187LogKCertificate, logChi := chi120LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869884927/274865926144) } }, logDArg := sk187LogDArgCertificate }

private noncomputable def leaf2258InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf2258LocalValidity :
    LeafFacts leaf2258Box leaf2258Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2258Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432963072) }) = true
      norm_num [leaf2258Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2258CertificateValid :
    WideCertificateValid leaf2258Box leaf2258Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk187ValidityFacts chi120ValidityFacts
    leaf2258LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2258CoverageChecked :
    coverageCheck (innerAD leaf2258Box) leaf2258InnerLog = true := by
  rfl'

private theorem leaf2258InnerLogValid :
    leaf2258InnerLog.Valid 8 (innerAD leaf2258Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf2258CoverageChecked

private noncomputable def leaf2258InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814661/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2258InputLogOnePlusV_eq :
    leaf2258InputLogOnePlusV = outerEnclosure 24
      (leaf2258Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2258RoundedFacts : LeafRoundedFacts 8
    leaf2258Certificate.logOnePlusV leaf2258InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2258InputLogOnePlusV_eq }

private noncomputable def leaf2258Inputs : Inputs :=
  inputsOfCaches globalInput sk187RoundedInputs
    chi120InputQChi innerPair57Input
    leaf2258InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2258LowerChecked :
    lowerCheck 24 leaf2258Box leaf2258Inputs = true := by
  rfl'

private theorem leaf2258CoversExact : CoversExact 8
    leaf2258Box leaf2258Certificate leaf2258InnerLog leaf2258Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk187RoundedFacts chi120RoundedFacts
    innerPair57RoundedFacts leaf2258RoundedFacts (by rfl)

private theorem leaf2258FlatSound : Sound leaf2258Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2258CertificateValid
    leaf2258InnerLogValid leaf2258CoversExact leaf2258LowerChecked

private noncomputable def leaf2259Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (195/64), kHi := (49/16), chiLo := (29/128), chiHi := (15/64) }

private noncomputable def leaf2259Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871363/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432932352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (907421155/536870912) }, upper := { exponent := 0, mantissa := (1759/1024) } }, logOuter := sk188LogOuterCertificate, logK := sk188LogKCertificate, logChi := chi120LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869854207/274865864704) } }, logDArg := sk188LogDArgCertificate }

private noncomputable def leaf2259InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf2259LocalValidity :
    LeafFacts leaf2259Box leaf2259Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2259Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432932352) }) = true
      norm_num [leaf2259Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2259CertificateValid :
    WideCertificateValid leaf2259Box leaf2259Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk188ValidityFacts chi120ValidityFacts
    leaf2259LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2259CoverageChecked :
    coverageCheck (innerAD leaf2259Box) leaf2259InnerLog = true := by
  rfl'

private theorem leaf2259InnerLogValid :
    leaf2259InnerLog.Valid 8 (innerAD leaf2259Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf2259CoverageChecked

private noncomputable def leaf2259InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907331/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2259InputLogOnePlusV_eq :
    leaf2259InputLogOnePlusV = outerEnclosure 24
      (leaf2259Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2259RoundedFacts : LeafRoundedFacts 8
    leaf2259Certificate.logOnePlusV leaf2259InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2259InputLogOnePlusV_eq }

private noncomputable def leaf2259Inputs : Inputs :=
  inputsOfCaches globalInput sk188RoundedInputs
    chi120InputQChi innerPair64Input
    leaf2259InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2259LowerChecked :
    lowerCheck 24 leaf2259Box leaf2259Inputs = true := by
  rfl'

private theorem leaf2259CoversExact : CoversExact 8
    leaf2259Box leaf2259Certificate leaf2259InnerLog leaf2259Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk188RoundedFacts chi120RoundedFacts
    innerPair64RoundedFacts leaf2259RoundedFacts (by rfl)

private theorem leaf2259FlatSound : Sound leaf2259Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2259CertificateValid
    leaf2259InnerLogValid leaf2259CoversExact leaf2259LowerChecked

private noncomputable def leaf2260Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (197/64), chiLo := (7/32), chiHi := (29/128) }

private noncomputable def leaf2260Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871363/536870912) }, vSqrt := { lower := (65529/65536), upper := (27487384371/27486620672) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (896477311/536870912) }, upper := { exponent := 0, mantissa := (13905/8192) } }, logOuter := sk189LogOuterCertificate, logK := sk189LogKCertificate, logChi := chi119LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (54974005043/54973241344) } }, logDArg := sk189LogDArgCertificate }

private noncomputable def leaf2260InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf2260LocalValidity :
    LeafFacts leaf2260Box leaf2260Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2260Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (27487384371/27486620672) }) = true
      norm_num [leaf2260Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2260CertificateValid :
    WideCertificateValid leaf2260Box leaf2260Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk189ValidityFacts chi119ValidityFacts
    leaf2260LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2260CoverageChecked :
    coverageCheck (innerAD leaf2260Box) leaf2260InnerLog = true := by
  rfl'

private theorem leaf2260InnerLogValid :
    leaf2260InnerLog.Valid 8 (innerAD leaf2260Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf2260CoverageChecked

private noncomputable def leaf2260InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814657/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2260InputLogOnePlusV_eq :
    leaf2260InputLogOnePlusV = outerEnclosure 24
      (leaf2260Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2260RoundedFacts : LeafRoundedFacts 8
    leaf2260Certificate.logOnePlusV leaf2260InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2260InputLogOnePlusV_eq }

private noncomputable def leaf2260Inputs : Inputs :=
  inputsOfCaches globalInput sk189RoundedInputs
    chi119InputQChi innerPair57Input
    leaf2260InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2260LowerChecked :
    lowerCheck 24 leaf2260Box leaf2260Inputs = true := by
  rfl'

private theorem leaf2260CoversExact : CoversExact 8
    leaf2260Box leaf2260Certificate leaf2260InnerLog leaf2260Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk189RoundedFacts chi119RoundedFacts
    innerPair57RoundedFacts leaf2260RoundedFacts (by rfl)

private theorem leaf2260FlatSound : Sound leaf2260Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2260CertificateValid
    leaf2260InnerLogValid leaf2260CoversExact leaf2260LowerChecked

private noncomputable def leaf2261Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (197/64), kHi := (99/32), chiLo := (7/32), chiHi := (29/128) }

private noncomputable def leaf2261Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871365/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433073664) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (898312205/536870912) }, upper := { exponent := 0, mantissa := (6967/4096) } }, logOuter := sk190LogOuterCertificate, logK := sk190LogKCertificate, logChi := chi119LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869995519/274866147328) } }, logDArg := sk190LogDArgCertificate }

private noncomputable def leaf2261InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf2261LocalValidity :
    LeafFacts leaf2261Box leaf2261Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2261Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433073664) }) = true
      norm_num [leaf2261Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2261CertificateValid :
    WideCertificateValid leaf2261Box leaf2261Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk190ValidityFacts chi119ValidityFacts
    leaf2261LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2261CoverageChecked :
    coverageCheck (innerAD leaf2261Box) leaf2261InnerLog = true := by
  rfl'

private theorem leaf2261InnerLogValid :
    leaf2261InnerLog.Valid 8 (innerAD leaf2261Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf2261CoverageChecked

private noncomputable def leaf2261InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907329/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2261InputLogOnePlusV_eq :
    leaf2261InputLogOnePlusV = outerEnclosure 24
      (leaf2261Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2261RoundedFacts : LeafRoundedFacts 8
    leaf2261Certificate.logOnePlusV leaf2261InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2261InputLogOnePlusV_eq }

private noncomputable def leaf2261Inputs : Inputs :=
  inputsOfCaches globalInput sk190RoundedInputs
    chi119InputQChi innerPair57Input
    leaf2261InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2261LowerChecked :
    lowerCheck 24 leaf2261Box leaf2261Inputs = true := by
  rfl'

private theorem leaf2261CoversExact : CoversExact 8
    leaf2261Box leaf2261Certificate leaf2261InnerLog leaf2261Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk190RoundedFacts chi119RoundedFacts
    innerPair57RoundedFacts leaf2261RoundedFacts (by rfl)

private theorem leaf2261FlatSound : Sound leaf2261Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2261CertificateValid
    leaf2261InnerLogValid leaf2261CoversExact leaf2261LowerChecked

private noncomputable def leaf2262Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (197/64), chiLo := (29/128), chiHi := (15/64) }

private noncomputable def leaf2262Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871365/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432901632) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (909321581/536870912) }, upper := { exponent := 0, mantissa := (7051/4096) } }, logOuter := sk189LogOuterCertificate, logK := sk189LogKCertificate, logChi := chi120LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869823487/274865803264) } }, logDArg := sk189LogDArgCertificate }

private noncomputable def leaf2262InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf2262LocalValidity :
    LeafFacts leaf2262Box leaf2262Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2262Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432901632) }) = true
      norm_num [leaf2262Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2262CertificateValid :
    WideCertificateValid leaf2262Box leaf2262Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk189ValidityFacts chi120ValidityFacts
    leaf2262LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2262CoverageChecked :
    coverageCheck (innerAD leaf2262Box) leaf2262InnerLog = true := by
  rfl'

private theorem leaf2262InnerLogValid :
    leaf2262InnerLog.Valid 8 (innerAD leaf2262Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf2262CoverageChecked

private noncomputable def leaf2262InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814663/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2262InputLogOnePlusV_eq :
    leaf2262InputLogOnePlusV = outerEnclosure 24
      (leaf2262Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2262RoundedFacts : LeafRoundedFacts 8
    leaf2262Certificate.logOnePlusV leaf2262InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2262InputLogOnePlusV_eq }

private noncomputable def leaf2262Inputs : Inputs :=
  inputsOfCaches globalInput sk189RoundedInputs
    chi120InputQChi innerPair64Input
    leaf2262InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2262LowerChecked :
    lowerCheck 24 leaf2262Box leaf2262Inputs = true := by
  rfl'

private theorem leaf2262CoversExact : CoversExact 8
    leaf2262Box leaf2262Certificate leaf2262InnerLog leaf2262Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk189RoundedFacts chi120RoundedFacts
    innerPair64RoundedFacts leaf2262RoundedFacts (by rfl)

private theorem leaf2262FlatSound : Sound leaf2262Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2262CertificateValid
    leaf2262InnerLogValid leaf2262CoversExact leaf2262LowerChecked

private noncomputable def leaf2263Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (197/64), kHi := (99/32), chiLo := (29/128), chiHi := (15/64) }

private noncomputable def leaf2263Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871367/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432870912) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (911222007/536870912) }, upper := { exponent := 0, mantissa := (3533/2048) } }, logOuter := sk190LogOuterCertificate, logK := sk190LogKCertificate, logChi := chi120LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869792767/274865741824) } }, logDArg := sk190LogDArgCertificate }

private noncomputable def leaf2263InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf2263LocalValidity :
    LeafFacts leaf2263Box leaf2263Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2263Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432870912) }) = true
      norm_num [leaf2263Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2263CertificateValid :
    WideCertificateValid leaf2263Box leaf2263Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk190ValidityFacts chi120ValidityFacts
    leaf2263LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2263CoverageChecked :
    coverageCheck (innerAD leaf2263Box) leaf2263InnerLog = true := by
  rfl'

private theorem leaf2263InnerLogValid :
    leaf2263InnerLog.Valid 8 (innerAD leaf2263Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf2263CoverageChecked

private noncomputable def leaf2263InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (726833/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf2263InputLogOnePlusV_eq :
    leaf2263InputLogOnePlusV = outerEnclosure 24
      (leaf2263Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2263RoundedFacts : LeafRoundedFacts 8
    leaf2263Certificate.logOnePlusV leaf2263InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2263InputLogOnePlusV_eq }

private noncomputable def leaf2263Inputs : Inputs :=
  inputsOfCaches globalInput sk190RoundedInputs
    chi120InputQChi innerPair64Input
    leaf2263InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2263LowerChecked :
    lowerCheck 24 leaf2263Box leaf2263Inputs = true := by
  rfl'

private theorem leaf2263CoversExact : CoversExact 8
    leaf2263Box leaf2263Certificate leaf2263InnerLog leaf2263Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk190RoundedFacts chi120RoundedFacts
    innerPair64RoundedFacts leaf2263RoundedFacts (by rfl)

private theorem leaf2263FlatSound : Sound leaf2263Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2263CertificateValid
    leaf2263InnerLogValid leaf2263CoversExact leaf2263LowerChecked

private noncomputable def leaf2264Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (199/64), chiLo := (7/32), chiHi := (29/128) }

private noncomputable def leaf2264Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871367/536870912) }, vSqrt := { lower := (65529/65536), upper := (2694841605/2694765568) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (900147099/536870912) }, upper := { exponent := 0, mantissa := (13963/8192) } }, logOuter := sk191LogOuterCertificate, logK := sk191LogKCertificate, logChi := chi119LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (5389607173/5389531136) } }, logDArg := sk191LogDArgCertificate }

private noncomputable def leaf2264InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf2264LocalValidity :
    LeafFacts leaf2264Box leaf2264Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2264Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (2694841605/2694765568) }) = true
      norm_num [leaf2264Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2264CertificateValid :
    WideCertificateValid leaf2264Box leaf2264Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk191ValidityFacts chi119ValidityFacts
    leaf2264LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2264CoverageChecked :
    coverageCheck (innerAD leaf2264Box) leaf2264InnerLog = true := by
  rfl'

private theorem leaf2264InnerLogValid :
    leaf2264InnerLog.Valid 8 (innerAD leaf2264Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf2264CoverageChecked

private noncomputable def leaf2264InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629317/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2264InputLogOnePlusV_eq :
    leaf2264InputLogOnePlusV = outerEnclosure 24
      (leaf2264Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2264RoundedFacts : LeafRoundedFacts 8
    leaf2264Certificate.logOnePlusV leaf2264InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2264InputLogOnePlusV_eq }

private noncomputable def leaf2264Inputs : Inputs :=
  inputsOfCaches globalInput sk191RoundedInputs
    chi119InputQChi innerPair57Input
    leaf2264InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2264LowerChecked :
    lowerCheck 24 leaf2264Box leaf2264Inputs = true := by
  rfl'

private theorem leaf2264CoversExact : CoversExact 8
    leaf2264Box leaf2264Certificate leaf2264InnerLog leaf2264Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk191RoundedFacts chi119RoundedFacts
    innerPair57RoundedFacts leaf2264RoundedFacts (by rfl)

private theorem leaf2264FlatSound : Sound leaf2264Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2264CertificateValid
    leaf2264InnerLogValid leaf2264CoversExact leaf2264LowerChecked

private noncomputable def leaf2265Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (199/64), kHi := (25/8), chiLo := (7/32), chiHi := (29/128) }

private noncomputable def leaf2265Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871369/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433014272) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (901981993/536870912) }, upper := { exponent := 0, mantissa := (1749/1024) } }, logOuter := sk192LogOuterCertificate, logK := sk192LogKCertificate, logChi := chi119LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869936127/274866028544) } }, logDArg := sk192LogDArgCertificate }

private noncomputable def leaf2265InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf2265LocalValidity :
    LeafFacts leaf2265Box leaf2265Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2265Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433014272) }) = true
      norm_num [leaf2265Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2265CertificateValid :
    WideCertificateValid leaf2265Box leaf2265Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk192ValidityFacts chi119ValidityFacts
    leaf2265LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2265CoverageChecked :
    coverageCheck (innerAD leaf2265Box) leaf2265InnerLog = true := by
  rfl'

private theorem leaf2265InnerLogValid :
    leaf2265InnerLog.Valid 8 (innerAD leaf2265Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf2265CoverageChecked

private noncomputable def leaf2265InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629319/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2265InputLogOnePlusV_eq :
    leaf2265InputLogOnePlusV = outerEnclosure 24
      (leaf2265Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2265RoundedFacts : LeafRoundedFacts 8
    leaf2265Certificate.logOnePlusV leaf2265InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2265InputLogOnePlusV_eq }

private noncomputable def leaf2265Inputs : Inputs :=
  inputsOfCaches globalInput sk192RoundedInputs
    chi119InputQChi innerPair57Input
    leaf2265InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2265LowerChecked :
    lowerCheck 24 leaf2265Box leaf2265Inputs = true := by
  rfl'

private theorem leaf2265CoversExact : CoversExact 8
    leaf2265Box leaf2265Certificate leaf2265InnerLog leaf2265Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk192RoundedFacts chi119RoundedFacts
    innerPair57RoundedFacts leaf2265RoundedFacts (by rfl)

private theorem leaf2265FlatSound : Sound leaf2265Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2265CertificateValid
    leaf2265InnerLogValid leaf2265CoversExact leaf2265LowerChecked

private noncomputable def leaf2266Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (199/64), chiLo := (29/128), chiHi := (15/64) }

private noncomputable def leaf2266Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871369/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432840192) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (913122433/536870912) }, upper := { exponent := 0, mantissa := (7081/4096) } }, logOuter := sk191LogOuterCertificate, logK := sk191LogKCertificate, logChi := chi120LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869762047/274865680384) } }, logDArg := sk191LogDArgCertificate }

private noncomputable def leaf2266InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf2266LocalValidity :
    LeafFacts leaf2266Box leaf2266Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2266Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432840192) }) = true
      norm_num [leaf2266Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2266CertificateValid :
    WideCertificateValid leaf2266Box leaf2266Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk191ValidityFacts chi120ValidityFacts
    leaf2266LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2266CoverageChecked :
    coverageCheck (innerAD leaf2266Box) leaf2266InnerLog = true := by
  rfl'

private theorem leaf2266InnerLogValid :
    leaf2266InnerLog.Valid 8 (innerAD leaf2266Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf2266CoverageChecked

private noncomputable def leaf2266InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814665/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2266InputLogOnePlusV_eq :
    leaf2266InputLogOnePlusV = outerEnclosure 24
      (leaf2266Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2266RoundedFacts : LeafRoundedFacts 8
    leaf2266Certificate.logOnePlusV leaf2266InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2266InputLogOnePlusV_eq }

private noncomputable def leaf2266Inputs : Inputs :=
  inputsOfCaches globalInput sk191RoundedInputs
    chi120InputQChi innerPair64Input
    leaf2266InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2266LowerChecked :
    lowerCheck 24 leaf2266Box leaf2266Inputs = true := by
  rfl'

private theorem leaf2266CoversExact : CoversExact 8
    leaf2266Box leaf2266Certificate leaf2266InnerLog leaf2266Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk191RoundedFacts chi120RoundedFacts
    innerPair64RoundedFacts leaf2266RoundedFacts (by rfl)

private theorem leaf2266FlatSound : Sound leaf2266Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2266CertificateValid
    leaf2266InnerLogValid leaf2266CoversExact leaf2266LowerChecked

private noncomputable def leaf2267Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (199/64), kHi := (25/8), chiLo := (29/128), chiHi := (15/64) }

private noncomputable def leaf2267Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871371/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432809472) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (915022859/536870912) }, upper := { exponent := 0, mantissa := (887/512) } }, logOuter := sk192LogOuterCertificate, logK := sk192LogKCertificate, logChi := chi120LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869731327/274865618944) } }, logDArg := sk192LogDArgCertificate }

private noncomputable def leaf2267InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf2267LocalValidity :
    LeafFacts leaf2267Box leaf2267Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2267Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432809472) }) = true
      norm_num [leaf2267Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2267CertificateValid :
    WideCertificateValid leaf2267Box leaf2267Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk192ValidityFacts chi120ValidityFacts
    leaf2267LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2267CoverageChecked :
    coverageCheck (innerAD leaf2267Box) leaf2267InnerLog = true := by
  rfl'

private theorem leaf2267InnerLogValid :
    leaf2267InnerLog.Valid 8 (innerAD leaf2267Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf2267CoverageChecked

private noncomputable def leaf2267InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907333/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2267InputLogOnePlusV_eq :
    leaf2267InputLogOnePlusV = outerEnclosure 24
      (leaf2267Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2267RoundedFacts : LeafRoundedFacts 8
    leaf2267Certificate.logOnePlusV leaf2267InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2267InputLogOnePlusV_eq }

private noncomputable def leaf2267Inputs : Inputs :=
  inputsOfCaches globalInput sk192RoundedInputs
    chi120InputQChi innerPair64Input
    leaf2267InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2267LowerChecked :
    lowerCheck 24 leaf2267Box leaf2267Inputs = true := by
  rfl'

private theorem leaf2267CoversExact : CoversExact 8
    leaf2267Box leaf2267Certificate leaf2267InnerLog leaf2267Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk192RoundedFacts chi120RoundedFacts
    innerPair64RoundedFacts leaf2267RoundedFacts (by rfl)

private theorem leaf2267FlatSound : Sound leaf2267Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2267CertificateValid
    leaf2267InnerLogValid leaf2267CoversExact leaf2267LowerChecked

private noncomputable def leaf2268Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (193/64), chiLo := (15/64), chiHi := (31/128) }

private noncomputable def leaf2268Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871359/536870912) }, vSqrt := { lower := (65529/65536), upper := (27487384371/27486565376) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (914302019/536870912) }, upper := { exponent := 0, mantissa := (14175/8192) } }, logOuter := sk185LogOuterCertificate, logK := sk185LogKCertificate, logChi := chi121LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (54973949747/54973130752) } }, logDArg := sk185LogDArgCertificate }

private noncomputable def leaf2268InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf2268LocalValidity :
    LeafFacts leaf2268Box leaf2268Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2268Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (27487384371/27486565376) }) = true
      norm_num [leaf2268Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2268CertificateValid :
    WideCertificateValid leaf2268Box leaf2268Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk185ValidityFacts chi121ValidityFacts
    leaf2268LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2268CoverageChecked :
    coverageCheck (innerAD leaf2268Box) leaf2268InnerLog = true := by
  rfl'

private theorem leaf2268InnerLogValid :
    leaf2268InnerLog.Valid 8 (innerAD leaf2268Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf2268CoverageChecked

private noncomputable def leaf2268InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629331/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2268InputLogOnePlusV_eq :
    leaf2268InputLogOnePlusV = outerEnclosure 24
      (leaf2268Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2268RoundedFacts : LeafRoundedFacts 8
    leaf2268Certificate.logOnePlusV leaf2268InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2268InputLogOnePlusV_eq }

private noncomputable def leaf2268Inputs : Inputs :=
  inputsOfCaches globalInput sk185RoundedInputs
    chi121InputQChi innerPair64Input
    leaf2268InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2268LowerChecked :
    lowerCheck 24 leaf2268Box leaf2268Inputs = true := by
  rfl'

private theorem leaf2268CoversExact : CoversExact 8
    leaf2268Box leaf2268Certificate leaf2268InnerLog leaf2268Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk185RoundedFacts chi121RoundedFacts
    innerPair64RoundedFacts leaf2268RoundedFacts (by rfl)

private theorem leaf2268FlatSound : Sound leaf2268Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2268CertificateValid
    leaf2268InnerLogValid leaf2268CoversExact leaf2268LowerChecked

private noncomputable def leaf2269Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (193/64), kHi := (97/32), chiLo := (15/64), chiHi := (31/128) }

private noncomputable def leaf2269Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871361/536870912) }, vSqrt := { lower := (65529/65536), upper := (45812307285/45810931712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (916267977/536870912) }, upper := { exponent := 0, mantissa := (7103/4096) } }, logOuter := sk186LogOuterCertificate, logK := sk186LogKCertificate, logChi := chi121LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (91623238997/91621863424) } }, logDArg := sk186LogDArgCertificate }

private noncomputable def leaf2269InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf2269LocalValidity :
    LeafFacts leaf2269Box leaf2269Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2269Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (45812307285/45810931712) }) = true
      norm_num [leaf2269Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2269CertificateValid :
    WideCertificateValid leaf2269Box leaf2269Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk186ValidityFacts chi121ValidityFacts
    leaf2269LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2269CoverageChecked :
    coverageCheck (innerAD leaf2269Box) leaf2269InnerLog = true := by
  rfl'

private theorem leaf2269InnerLogValid :
    leaf2269InnerLog.Valid 8 (innerAD leaf2269Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf2269CoverageChecked

private noncomputable def leaf2269InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629333/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2269InputLogOnePlusV_eq :
    leaf2269InputLogOnePlusV = outerEnclosure 24
      (leaf2269Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2269RoundedFacts : LeafRoundedFacts 8
    leaf2269Certificate.logOnePlusV leaf2269InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2269InputLogOnePlusV_eq }

private noncomputable def leaf2269Inputs : Inputs :=
  inputsOfCaches globalInput sk186RoundedInputs
    chi121InputQChi innerPair64Input
    leaf2269InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2269LowerChecked :
    lowerCheck 24 leaf2269Box leaf2269Inputs = true := by
  rfl'

private theorem leaf2269CoversExact : CoversExact 8
    leaf2269Box leaf2269Certificate leaf2269InnerLog leaf2269Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk186RoundedFacts chi121RoundedFacts
    innerPair64RoundedFacts leaf2269RoundedFacts (by rfl)

private theorem leaf2269FlatSound : Sound leaf2269Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2269CertificateValid
    leaf2269InnerLogValid leaf2269CoversExact leaf2269LowerChecked

private noncomputable def leaf2270Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (193/64), chiLo := (31/128), chiHi := (1/4) }

private noncomputable def leaf2270Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871361/536870912) }, vSqrt := { lower := (65529/65536), upper := (45812307285/45810876416) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (926884161/536870912) }, upper := { exponent := 0, mantissa := (449/256) } }, logOuter := sk185LogOuterCertificate, logK := sk185LogKCertificate, logChi := chi122LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (91623183701/91621752832) } }, logDArg := sk185LogDArgCertificate }

private noncomputable def leaf2270InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf2270LocalValidity :
    LeafFacts leaf2270Box leaf2270Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2270Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (45812307285/45810876416) }) = true
      norm_num [leaf2270Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2270CertificateValid :
    WideCertificateValid leaf2270Box leaf2270Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk185ValidityFacts chi122ValidityFacts
    leaf2270LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2270CoverageChecked :
    coverageCheck (innerAD leaf2270Box) leaf2270InnerLog = true := by
  rfl'

private theorem leaf2270InnerLogValid :
    leaf2270InnerLog.Valid 8 (innerAD leaf2270Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf2270CoverageChecked

private noncomputable def leaf2270InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629343/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2270InputLogOnePlusV_eq :
    leaf2270InputLogOnePlusV = outerEnclosure 24
      (leaf2270Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2270RoundedFacts : LeafRoundedFacts 8
    leaf2270Certificate.logOnePlusV leaf2270InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2270InputLogOnePlusV_eq }

private noncomputable def leaf2270Inputs : Inputs :=
  inputsOfCaches globalInput sk185RoundedInputs
    chi122InputQChi innerPair66Input
    leaf2270InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2270LowerChecked :
    lowerCheck 24 leaf2270Box leaf2270Inputs = true := by
  rfl'

private theorem leaf2270CoversExact : CoversExact 8
    leaf2270Box leaf2270Certificate leaf2270InnerLog leaf2270Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk185RoundedFacts chi122RoundedFacts
    innerPair66RoundedFacts leaf2270RoundedFacts (by rfl)

private theorem leaf2270FlatSound : Sound leaf2270Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2270CertificateValid
    leaf2270InnerLogValid leaf2270CoversExact leaf2270LowerChecked

private noncomputable def leaf2271Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (193/64), kHi := (97/32), chiLo := (31/128), chiHi := (1/4) }

private noncomputable def leaf2271Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871363/536870912) }, vSqrt := { lower := (65529/65536), upper := (27487384371/27486519296) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (928915651/536870912) }, upper := { exponent := 0, mantissa := (225/128) } }, logOuter := sk186LogOuterCertificate, logK := sk186LogKCertificate, logChi := chi122LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (54973903667/54973038592) } }, logDArg := sk186LogDArgCertificate }

private noncomputable def leaf2271InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf2271LocalValidity :
    LeafFacts leaf2271Box leaf2271Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2271Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (27487384371/27486519296) }) = true
      norm_num [leaf2271Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2271CertificateValid :
    WideCertificateValid leaf2271Box leaf2271Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk186ValidityFacts chi122ValidityFacts
    leaf2271LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2271CoverageChecked :
    coverageCheck (innerAD leaf2271Box) leaf2271InnerLog = true := by
  rfl'

private theorem leaf2271InnerLogValid :
    leaf2271InnerLog.Valid 8 (innerAD leaf2271Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf2271CoverageChecked

private noncomputable def leaf2271InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629345/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2271InputLogOnePlusV_eq :
    leaf2271InputLogOnePlusV = outerEnclosure 24
      (leaf2271Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2271RoundedFacts : LeafRoundedFacts 8
    leaf2271Certificate.logOnePlusV leaf2271InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2271InputLogOnePlusV_eq }

private noncomputable def leaf2271Inputs : Inputs :=
  inputsOfCaches globalInput sk186RoundedInputs
    chi122InputQChi innerPair66Input
    leaf2271InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2271LowerChecked :
    lowerCheck 24 leaf2271Box leaf2271Inputs = true := by
  rfl'

private theorem leaf2271CoversExact : CoversExact 8
    leaf2271Box leaf2271Certificate leaf2271InnerLog leaf2271Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk186RoundedFacts chi122RoundedFacts
    innerPair66RoundedFacts leaf2271RoundedFacts (by rfl)

private theorem leaf2271FlatSound : Sound leaf2271Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2271CertificateValid
    leaf2271InnerLogValid leaf2271CoversExact leaf2271LowerChecked

private noncomputable def leaf2272Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (195/64), chiLo := (15/64), chiHi := (31/128) }

private noncomputable def leaf2272Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871363/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432763392) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (918233935/536870912) }, upper := { exponent := 0, mantissa := (14237/8192) } }, logOuter := sk187LogOuterCertificate, logK := sk187LogKCertificate, logChi := chi121LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869685247/274865526784) } }, logDArg := sk187LogDArgCertificate }

private noncomputable def leaf2272InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf2272LocalValidity :
    LeafFacts leaf2272Box leaf2272Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2272Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432763392) }) = true
      norm_num [leaf2272Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2272CertificateValid :
    WideCertificateValid leaf2272Box leaf2272Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk187ValidityFacts chi121ValidityFacts
    leaf2272LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2272CoverageChecked :
    coverageCheck (innerAD leaf2272Box) leaf2272InnerLog = true := by
  rfl'

private theorem leaf2272InnerLogValid :
    leaf2272InnerLog.Valid 8 (innerAD leaf2272Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf2272CoverageChecked

private noncomputable def leaf2272InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629335/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2272InputLogOnePlusV_eq :
    leaf2272InputLogOnePlusV = outerEnclosure 24
      (leaf2272Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2272RoundedFacts : LeafRoundedFacts 8
    leaf2272Certificate.logOnePlusV leaf2272InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2272InputLogOnePlusV_eq }

private noncomputable def leaf2272Inputs : Inputs :=
  inputsOfCaches globalInput sk187RoundedInputs
    chi121InputQChi innerPair64Input
    leaf2272InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2272LowerChecked :
    lowerCheck 24 leaf2272Box leaf2272Inputs = true := by
  rfl'

private theorem leaf2272CoversExact : CoversExact 8
    leaf2272Box leaf2272Certificate leaf2272InnerLog leaf2272Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk187RoundedFacts chi121RoundedFacts
    innerPair64RoundedFacts leaf2272RoundedFacts (by rfl)

private theorem leaf2272FlatSound : Sound leaf2272Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2272CertificateValid
    leaf2272InnerLogValid leaf2272CoversExact leaf2272LowerChecked

private noncomputable def leaf2273Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (195/64), kHi := (49/16), chiLo := (15/64), chiHi := (31/128) }

private noncomputable def leaf2273Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871365/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432731648) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (920199893/536870912) }, upper := { exponent := 0, mantissa := (3567/2048) } }, logOuter := sk188LogOuterCertificate, logK := sk188LogKCertificate, logChi := chi121LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869653503/274865463296) } }, logDArg := sk188LogDArgCertificate }

private noncomputable def leaf2273InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf2273LocalValidity :
    LeafFacts leaf2273Box leaf2273Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2273Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432731648) }) = true
      norm_num [leaf2273Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2273CertificateValid :
    WideCertificateValid leaf2273Box leaf2273Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk188ValidityFacts chi121ValidityFacts
    leaf2273LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2273CoverageChecked :
    coverageCheck (innerAD leaf2273Box) leaf2273InnerLog = true := by
  rfl'

private theorem leaf2273InnerLogValid :
    leaf2273InnerLog.Valid 8 (innerAD leaf2273Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf2273CoverageChecked

private noncomputable def leaf2273InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629337/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2273InputLogOnePlusV_eq :
    leaf2273InputLogOnePlusV = outerEnclosure 24
      (leaf2273Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2273RoundedFacts : LeafRoundedFacts 8
    leaf2273Certificate.logOnePlusV leaf2273InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2273InputLogOnePlusV_eq }

private noncomputable def leaf2273Inputs : Inputs :=
  inputsOfCaches globalInput sk188RoundedInputs
    chi121InputQChi innerPair64Input
    leaf2273InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2273LowerChecked :
    lowerCheck 24 leaf2273Box leaf2273Inputs = true := by
  rfl'

private theorem leaf2273CoversExact : CoversExact 8
    leaf2273Box leaf2273Certificate leaf2273InnerLog leaf2273Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk188RoundedFacts chi121RoundedFacts
    innerPair64RoundedFacts leaf2273RoundedFacts (by rfl)

private theorem leaf2273FlatSound : Sound leaf2273Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2273CertificateValid
    leaf2273InnerLogValid leaf2273CoversExact leaf2273LowerChecked

private noncomputable def leaf2274Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (195/64), chiLo := (31/128), chiHi := (1/4) }

private noncomputable def leaf2274Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871365/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432563712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (930947141/536870912) }, upper := { exponent := 0, mantissa := (451/256) } }, logOuter := sk187LogOuterCertificate, logK := sk187LogKCertificate, logChi := chi122LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869485567/274865127424) } }, logDArg := sk187LogDArgCertificate }

private noncomputable def leaf2274InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf2274LocalValidity :
    LeafFacts leaf2274Box leaf2274Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2274Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432563712) }) = true
      norm_num [leaf2274Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2274CertificateValid :
    WideCertificateValid leaf2274Box leaf2274Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk187ValidityFacts chi122ValidityFacts
    leaf2274LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2274CoverageChecked :
    coverageCheck (innerAD leaf2274Box) leaf2274InnerLog = true := by
  rfl'

private theorem leaf2274InnerLogValid :
    leaf2274InnerLog.Valid 8 (innerAD leaf2274Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf2274CoverageChecked

private noncomputable def leaf2274InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629347/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2274InputLogOnePlusV_eq :
    leaf2274InputLogOnePlusV = outerEnclosure 24
      (leaf2274Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2274RoundedFacts : LeafRoundedFacts 8
    leaf2274Certificate.logOnePlusV leaf2274InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2274InputLogOnePlusV_eq }

private noncomputable def leaf2274Inputs : Inputs :=
  inputsOfCaches globalInput sk187RoundedInputs
    chi122InputQChi innerPair66Input
    leaf2274InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2274LowerChecked :
    lowerCheck 24 leaf2274Box leaf2274Inputs = true := by
  rfl'

private theorem leaf2274CoversExact : CoversExact 8
    leaf2274Box leaf2274Certificate leaf2274InnerLog leaf2274Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk187RoundedFacts chi122RoundedFacts
    innerPair66RoundedFacts leaf2274RoundedFacts (by rfl)

private theorem leaf2274FlatSound : Sound leaf2274Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2274CertificateValid
    leaf2274InnerLogValid leaf2274CoversExact leaf2274LowerChecked

private noncomputable def leaf2275Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (195/64), kHi := (49/16), chiLo := (31/128), chiHi := (1/4) }

private noncomputable def leaf2275Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871367/536870912) }, vSqrt := { lower := (65529/65536), upper := (15270769095/15270281216) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (932978631/536870912) }, upper := { exponent := 0, mantissa := (113/64) } }, logOuter := sk188LogOuterCertificate, logK := sk188LogKCertificate, logChi := chi122LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (30541050311/30540562432) } }, logDArg := sk188LogDArgCertificate }

private noncomputable def leaf2275InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf2275LocalValidity :
    LeafFacts leaf2275Box leaf2275Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2275Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (15270769095/15270281216) }) = true
      norm_num [leaf2275Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2275CertificateValid :
    WideCertificateValid leaf2275Box leaf2275Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk188ValidityFacts chi122ValidityFacts
    leaf2275LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2275CoverageChecked :
    coverageCheck (innerAD leaf2275Box) leaf2275InnerLog = true := by
  rfl'

private theorem leaf2275InnerLogValid :
    leaf2275InnerLog.Valid 8 (innerAD leaf2275Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf2275CoverageChecked

private noncomputable def leaf2275InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629349/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2275InputLogOnePlusV_eq :
    leaf2275InputLogOnePlusV = outerEnclosure 24
      (leaf2275Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2275RoundedFacts : LeafRoundedFacts 8
    leaf2275Certificate.logOnePlusV leaf2275InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2275InputLogOnePlusV_eq }

private noncomputable def leaf2275Inputs : Inputs :=
  inputsOfCaches globalInput sk188RoundedInputs
    chi122InputQChi innerPair66Input
    leaf2275InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2275LowerChecked :
    lowerCheck 24 leaf2275Box leaf2275Inputs = true := by
  rfl'

private theorem leaf2275CoversExact : CoversExact 8
    leaf2275Box leaf2275Certificate leaf2275InnerLog leaf2275Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk188RoundedFacts chi122RoundedFacts
    innerPair66RoundedFacts leaf2275RoundedFacts (by rfl)

private theorem leaf2275FlatSound : Sound leaf2275Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2275CertificateValid
    leaf2275InnerLogValid leaf2275CoversExact leaf2275LowerChecked

private noncomputable def leaf2276Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (197/64), chiLo := (15/64), chiHi := (31/128) }

private noncomputable def leaf2276Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871367/536870912) }, vSqrt := { lower := (65529/65536), upper := (45812307285/45810899968) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (922165851/536870912) }, upper := { exponent := 0, mantissa := (14299/8192) } }, logOuter := sk189LogOuterCertificate, logK := sk189LogKCertificate, logChi := chi121LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (91623207253/91621799936) } }, logDArg := sk189LogDArgCertificate }

private noncomputable def leaf2276InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf2276LocalValidity :
    LeafFacts leaf2276Box leaf2276Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2276Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (45812307285/45810899968) }) = true
      norm_num [leaf2276Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2276CertificateValid :
    WideCertificateValid leaf2276Box leaf2276Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk189ValidityFacts chi121ValidityFacts
    leaf2276LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2276CoverageChecked :
    coverageCheck (innerAD leaf2276Box) leaf2276InnerLog = true := by
  rfl'

private theorem leaf2276InnerLogValid :
    leaf2276InnerLog.Valid 8 (innerAD leaf2276Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf2276CoverageChecked

private noncomputable def leaf2276InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814669/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2276InputLogOnePlusV_eq :
    leaf2276InputLogOnePlusV = outerEnclosure 24
      (leaf2276Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2276RoundedFacts : LeafRoundedFacts 8
    leaf2276Certificate.logOnePlusV leaf2276InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2276InputLogOnePlusV_eq }

private noncomputable def leaf2276Inputs : Inputs :=
  inputsOfCaches globalInput sk189RoundedInputs
    chi121InputQChi innerPair64Input
    leaf2276InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2276LowerChecked :
    lowerCheck 24 leaf2276Box leaf2276Inputs = true := by
  rfl'

private theorem leaf2276CoversExact : CoversExact 8
    leaf2276Box leaf2276Certificate leaf2276InnerLog leaf2276Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk189RoundedFacts chi121RoundedFacts
    innerPair64RoundedFacts leaf2276RoundedFacts (by rfl)

private theorem leaf2276FlatSound : Sound leaf2276Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2276CertificateValid
    leaf2276InnerLogValid leaf2276CoversExact leaf2276LowerChecked

private noncomputable def leaf2277Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (197/64), kHi := (99/32), chiLo := (15/64), chiHi := (31/128) }

private noncomputable def leaf2277Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871369/536870912) }, vSqrt := { lower := (65529/65536), upper := (27487384371/27486533632) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (924131809/536870912) }, upper := { exponent := 0, mantissa := (7165/4096) } }, logOuter := sk190LogOuterCertificate, logK := sk190LogKCertificate, logChi := chi121LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (54973918003/54973067264) } }, logDArg := sk190LogDArgCertificate }

private noncomputable def leaf2277InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf2277LocalValidity :
    LeafFacts leaf2277Box leaf2277Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2277Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (27487384371/27486533632) }) = true
      norm_num [leaf2277Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2277CertificateValid :
    WideCertificateValid leaf2277Box leaf2277Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk190ValidityFacts chi121ValidityFacts
    leaf2277LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2277CoverageChecked :
    coverageCheck (innerAD leaf2277Box) leaf2277InnerLog = true := by
  rfl'

private theorem leaf2277InnerLogValid :
    leaf2277InnerLog.Valid 8 (innerAD leaf2277Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf2277CoverageChecked

private noncomputable def leaf2277InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907335/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2277InputLogOnePlusV_eq :
    leaf2277InputLogOnePlusV = outerEnclosure 24
      (leaf2277Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2277RoundedFacts : LeafRoundedFacts 8
    leaf2277Certificate.logOnePlusV leaf2277InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2277InputLogOnePlusV_eq }

private noncomputable def leaf2277Inputs : Inputs :=
  inputsOfCaches globalInput sk190RoundedInputs
    chi121InputQChi innerPair64Input
    leaf2277InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2277LowerChecked :
    lowerCheck 24 leaf2277Box leaf2277Inputs = true := by
  rfl'

private theorem leaf2277CoversExact : CoversExact 8
    leaf2277Box leaf2277Certificate leaf2277InnerLog leaf2277Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk190RoundedFacts chi121RoundedFacts
    innerPair64RoundedFacts leaf2277RoundedFacts (by rfl)

private theorem leaf2277FlatSound : Sound leaf2277Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2277CertificateValid
    leaf2277InnerLogValid leaf2277CoversExact leaf2277LowerChecked

private noncomputable def leaf2278Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (199/64), chiLo := (15/64), chiHi := (31/128) }

private noncomputable def leaf2278Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871371/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432636416) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (926097767/536870912) }, upper := { exponent := 0, mantissa := (14361/8192) } }, logOuter := sk191LogOuterCertificate, logK := sk191LogKCertificate, logChi := chi121LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869558271/274865272832) } }, logDArg := sk191LogDArgCertificate }

private noncomputable def leaf2278InnerLog : WideLogData :=
  innerPair204Data

set_option maxRecDepth 1000000 in
private theorem leaf2278LocalValidity :
    LeafFacts leaf2278Box leaf2278Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2278Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432636416) }) = true
      norm_num [leaf2278Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2278CertificateValid :
    WideCertificateValid leaf2278Box leaf2278Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk191ValidityFacts chi121ValidityFacts
    leaf2278LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2278CoverageChecked :
    coverageCheck (innerAD leaf2278Box) leaf2278InnerLog = true := by
  rfl'

private theorem leaf2278InnerLogValid :
    leaf2278InnerLog.Valid 8 (innerAD leaf2278Box) :=
  wideLogDataValid_of_cachedCheck endpoint62PositiveFacts
    endpoint63PositiveFacts.valid leaf2278CoverageChecked

private noncomputable def leaf2278InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814671/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2278InputLogOnePlusV_eq :
    leaf2278InputLogOnePlusV = outerEnclosure 24
      (leaf2278Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2278RoundedFacts : LeafRoundedFacts 8
    leaf2278Certificate.logOnePlusV leaf2278InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2278InputLogOnePlusV_eq }

private noncomputable def leaf2278Inputs : Inputs :=
  inputsOfCaches globalInput sk191RoundedInputs
    chi121InputQChi innerPair204Input
    leaf2278InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2278LowerChecked :
    lowerCheck 24 leaf2278Box leaf2278Inputs = true := by
  rfl'

private theorem leaf2278CoversExact : CoversExact 8
    leaf2278Box leaf2278Certificate leaf2278InnerLog leaf2278Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk191RoundedFacts chi121RoundedFacts
    innerPair204RoundedFacts leaf2278RoundedFacts (by rfl)

private theorem leaf2278FlatSound : Sound leaf2278Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2278CertificateValid
    leaf2278InnerLogValid leaf2278CoversExact leaf2278LowerChecked

private noncomputable def leaf2279Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (199/64), kHi := (25/8), chiLo := (15/64), chiHi := (31/128) }

private noncomputable def leaf2279Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871373/536870912) }, vSqrt := { lower := (65529/65536), upper := (15270769095/15270289408) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (928063725/536870912) }, upper := { exponent := 0, mantissa := (1799/1024) } }, logOuter := sk192LogOuterCertificate, logK := sk192LogKCertificate, logChi := chi121LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (30541058503/30540578816) } }, logDArg := sk192LogDArgCertificate }

private noncomputable def leaf2279InnerLog : WideLogData :=
  innerPair204Data

set_option maxRecDepth 1000000 in
private theorem leaf2279LocalValidity :
    LeafFacts leaf2279Box leaf2279Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2279Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (15270769095/15270289408) }) = true
      norm_num [leaf2279Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2279CertificateValid :
    WideCertificateValid leaf2279Box leaf2279Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk192ValidityFacts chi121ValidityFacts
    leaf2279LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2279CoverageChecked :
    coverageCheck (innerAD leaf2279Box) leaf2279InnerLog = true := by
  rfl'

private theorem leaf2279InnerLogValid :
    leaf2279InnerLog.Valid 8 (innerAD leaf2279Box) :=
  wideLogDataValid_of_cachedCheck endpoint62PositiveFacts
    endpoint63PositiveFacts.valid leaf2279CoverageChecked

private noncomputable def leaf2279InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (363417/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf2279InputLogOnePlusV_eq :
    leaf2279InputLogOnePlusV = outerEnclosure 24
      (leaf2279Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2279RoundedFacts : LeafRoundedFacts 8
    leaf2279Certificate.logOnePlusV leaf2279InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2279InputLogOnePlusV_eq }

private noncomputable def leaf2279Inputs : Inputs :=
  inputsOfCaches globalInput sk192RoundedInputs
    chi121InputQChi innerPair204Input
    leaf2279InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2279LowerChecked :
    lowerCheck 24 leaf2279Box leaf2279Inputs = true := by
  rfl'

private theorem leaf2279CoversExact : CoversExact 8
    leaf2279Box leaf2279Certificate leaf2279InnerLog leaf2279Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk192RoundedFacts chi121RoundedFacts
    innerPair204RoundedFacts leaf2279RoundedFacts (by rfl)

private theorem leaf2279FlatSound : Sound leaf2279Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2279CertificateValid
    leaf2279InnerLogValid leaf2279CoversExact leaf2279LowerChecked

private noncomputable def leaf2280Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (197/64), chiLo := (31/128), chiHi := (1/4) }

private noncomputable def leaf2280Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871369/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432498176) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (935010121/536870912) }, upper := { exponent := 0, mantissa := (453/256) } }, logOuter := sk189LogOuterCertificate, logK := sk189LogKCertificate, logChi := chi122LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869420031/274864996352) } }, logDArg := sk189LogDArgCertificate }

private noncomputable def leaf2280InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf2280LocalValidity :
    LeafFacts leaf2280Box leaf2280Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2280Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432498176) }) = true
      norm_num [leaf2280Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2280CertificateValid :
    WideCertificateValid leaf2280Box leaf2280Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk189ValidityFacts chi122ValidityFacts
    leaf2280LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2280CoverageChecked :
    coverageCheck (innerAD leaf2280Box) leaf2280InnerLog = true := by
  rfl'

private theorem leaf2280InnerLogValid :
    leaf2280InnerLog.Valid 8 (innerAD leaf2280Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf2280CoverageChecked

private noncomputable def leaf2280InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629351/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2280InputLogOnePlusV_eq :
    leaf2280InputLogOnePlusV = outerEnclosure 24
      (leaf2280Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2280RoundedFacts : LeafRoundedFacts 8
    leaf2280Certificate.logOnePlusV leaf2280InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2280InputLogOnePlusV_eq }

private noncomputable def leaf2280Inputs : Inputs :=
  inputsOfCaches globalInput sk189RoundedInputs
    chi122InputQChi innerPair66Input
    leaf2280InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2280LowerChecked :
    lowerCheck 24 leaf2280Box leaf2280Inputs = true := by
  rfl'

private theorem leaf2280CoversExact : CoversExact 8
    leaf2280Box leaf2280Certificate leaf2280InnerLog leaf2280Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk189RoundedFacts chi122RoundedFacts
    innerPair66RoundedFacts leaf2280RoundedFacts (by rfl)

private theorem leaf2280FlatSound : Sound leaf2280Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2280CertificateValid
    leaf2280InnerLogValid leaf2280CoversExact leaf2280LowerChecked

private noncomputable def leaf2281Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (197/64), kHi := (99/32), chiLo := (31/128), chiHi := (1/4) }

private noncomputable def leaf2281Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871371/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432465408) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (937041611/536870912) }, upper := { exponent := 0, mantissa := (227/128) } }, logOuter := sk190LogOuterCertificate, logK := sk190LogKCertificate, logChi := chi122LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869387263/274864930816) } }, logDArg := sk190LogDArgCertificate }

private noncomputable def leaf2281InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf2281LocalValidity :
    LeafFacts leaf2281Box leaf2281Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2281Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432465408) }) = true
      norm_num [leaf2281Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2281CertificateValid :
    WideCertificateValid leaf2281Box leaf2281Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk190ValidityFacts chi122ValidityFacts
    leaf2281LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2281CoverageChecked :
    coverageCheck (innerAD leaf2281Box) leaf2281InnerLog = true := by
  rfl'

private theorem leaf2281InnerLogValid :
    leaf2281InnerLog.Valid 8 (innerAD leaf2281Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf2281CoverageChecked

private noncomputable def leaf2281InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629353/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2281InputLogOnePlusV_eq :
    leaf2281InputLogOnePlusV = outerEnclosure 24
      (leaf2281Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2281RoundedFacts : LeafRoundedFacts 8
    leaf2281Certificate.logOnePlusV leaf2281InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2281InputLogOnePlusV_eq }

private noncomputable def leaf2281Inputs : Inputs :=
  inputsOfCaches globalInput sk190RoundedInputs
    chi122InputQChi innerPair66Input
    leaf2281InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2281LowerChecked :
    lowerCheck 24 leaf2281Box leaf2281Inputs = true := by
  rfl'

private theorem leaf2281CoversExact : CoversExact 8
    leaf2281Box leaf2281Certificate leaf2281InnerLog leaf2281Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk190RoundedFacts chi122RoundedFacts
    innerPair66RoundedFacts leaf2281RoundedFacts (by rfl)

private theorem leaf2281FlatSound : Sound leaf2281Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2281CertificateValid
    leaf2281InnerLogValid leaf2281CoversExact leaf2281LowerChecked

private noncomputable def leaf2282Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (199/64), chiLo := (31/128), chiHi := (1/4) }

private noncomputable def leaf2282Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871373/536870912) }, vSqrt := { lower := (65529/65536), upper := (9162461457/9162162176) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (939073101/536870912) }, upper := { exponent := 0, mantissa := (455/256) } }, logOuter := sk191LogOuterCertificate, logK := sk191LogKCertificate, logChi := chi122LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (18324623633/18324324352) } }, logDArg := sk191LogDArgCertificate }

private noncomputable def leaf2282InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf2282LocalValidity :
    LeafFacts leaf2282Box leaf2282Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2282Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (9162461457/9162162176) }) = true
      norm_num [leaf2282Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2282CertificateValid :
    WideCertificateValid leaf2282Box leaf2282Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk191ValidityFacts chi122ValidityFacts
    leaf2282LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2282CoverageChecked :
    coverageCheck (innerAD leaf2282Box) leaf2282InnerLog = true := by
  rfl'

private theorem leaf2282InnerLogValid :
    leaf2282InnerLog.Valid 8 (innerAD leaf2282Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf2282CoverageChecked

private noncomputable def leaf2282InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629355/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2282InputLogOnePlusV_eq :
    leaf2282InputLogOnePlusV = outerEnclosure 24
      (leaf2282Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2282RoundedFacts : LeafRoundedFacts 8
    leaf2282Certificate.logOnePlusV leaf2282InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2282InputLogOnePlusV_eq }

private noncomputable def leaf2282Inputs : Inputs :=
  inputsOfCaches globalInput sk191RoundedInputs
    chi122InputQChi innerPair66Input
    leaf2282InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2282LowerChecked :
    lowerCheck 24 leaf2282Box leaf2282Inputs = true := by
  rfl'

private theorem leaf2282CoversExact : CoversExact 8
    leaf2282Box leaf2282Certificate leaf2282InnerLog leaf2282Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk191RoundedFacts chi122RoundedFacts
    innerPair66RoundedFacts leaf2282RoundedFacts (by rfl)

private theorem leaf2282FlatSound : Sound leaf2282Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2282CertificateValid
    leaf2282InnerLogValid leaf2282CoversExact leaf2282LowerChecked

private noncomputable def leaf2283Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (199/64), kHi := (25/8), chiLo := (31/128), chiHi := (1/4) }

private noncomputable def leaf2283Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871375/536870912) }, vSqrt := { lower := (65529/65536), upper := (8084524815/8084258816) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (941104591/536870912) }, upper := { exponent := 0, mantissa := (57/32) } }, logOuter := sk192LogOuterCertificate, logK := sk192LogKCertificate, logChi := chi122LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (16168783631/16168517632) } }, logDArg := sk192LogDArgCertificate }

private noncomputable def leaf2283InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf2283LocalValidity :
    LeafFacts leaf2283Box leaf2283Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2283Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8084524815/8084258816) }) = true
      norm_num [leaf2283Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2283CertificateValid :
    WideCertificateValid leaf2283Box leaf2283Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk192ValidityFacts chi122ValidityFacts
    leaf2283LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2283CoverageChecked :
    coverageCheck (innerAD leaf2283Box) leaf2283InnerLog = true := by
  rfl'

private theorem leaf2283InnerLogValid :
    leaf2283InnerLog.Valid 8 (innerAD leaf2283Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf2283CoverageChecked

private noncomputable def leaf2283InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629357/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2283InputLogOnePlusV_eq :
    leaf2283InputLogOnePlusV = outerEnclosure 24
      (leaf2283Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2283RoundedFacts : LeafRoundedFacts 8
    leaf2283Certificate.logOnePlusV leaf2283InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2283InputLogOnePlusV_eq }

private noncomputable def leaf2283Inputs : Inputs :=
  inputsOfCaches globalInput sk192RoundedInputs
    chi122InputQChi innerPair71Input
    leaf2283InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2283LowerChecked :
    lowerCheck 24 leaf2283Box leaf2283Inputs = true := by
  rfl'

private theorem leaf2283CoversExact : CoversExact 8
    leaf2283Box leaf2283Certificate leaf2283InnerLog leaf2283Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk192RoundedFacts chi122RoundedFacts
    innerPair71RoundedFacts leaf2283RoundedFacts (by rfl)

private theorem leaf2283FlatSound : Sound leaf2283Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2283CertificateValid
    leaf2283InnerLogValid leaf2283CoversExact leaf2283LowerChecked

private noncomputable def leaf2284Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (201/64), chiLo := (7/32), chiHi := (29/128) }

private noncomputable def leaf2284Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871371/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432984576) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (903816887/536870912) }, upper := { exponent := 0, mantissa := (14021/8192) } }, logOuter := sk193LogOuterCertificate, logK := sk193LogKCertificate, logChi := chi119LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869906431/274865969152) } }, logDArg := sk193LogDArgCertificate }

private noncomputable def leaf2284InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf2284LocalValidity :
    LeafFacts leaf2284Box leaf2284Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2284Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432984576) }) = true
      norm_num [leaf2284Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2284CertificateValid :
    WideCertificateValid leaf2284Box leaf2284Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk193ValidityFacts chi119ValidityFacts
    leaf2284LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2284CoverageChecked :
    coverageCheck (innerAD leaf2284Box) leaf2284InnerLog = true := by
  rfl'

private theorem leaf2284InnerLogValid :
    leaf2284InnerLog.Valid 8 (innerAD leaf2284Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf2284CoverageChecked

private noncomputable def leaf2284InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629321/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2284InputLogOnePlusV_eq :
    leaf2284InputLogOnePlusV = outerEnclosure 24
      (leaf2284Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2284RoundedFacts : LeafRoundedFacts 8
    leaf2284Certificate.logOnePlusV leaf2284InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2284InputLogOnePlusV_eq }

private noncomputable def leaf2284Inputs : Inputs :=
  inputsOfCaches globalInput sk193RoundedInputs
    chi119InputQChi innerPair57Input
    leaf2284InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2284LowerChecked :
    lowerCheck 24 leaf2284Box leaf2284Inputs = true := by
  rfl'

private theorem leaf2284CoversExact : CoversExact 8
    leaf2284Box leaf2284Certificate leaf2284InnerLog leaf2284Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk193RoundedFacts chi119RoundedFacts
    innerPair57RoundedFacts leaf2284RoundedFacts (by rfl)

private theorem leaf2284FlatSound : Sound leaf2284Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2284CertificateValid
    leaf2284InnerLogValid leaf2284CoversExact leaf2284LowerChecked

private noncomputable def leaf2285Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (201/64), kHi := (101/32), chiLo := (7/32), chiHi := (29/128) }

private noncomputable def leaf2285Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871373/536870912) }, vSqrt := { lower := (65529/65536), upper := (1018051273/1018021888) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (905651781/536870912) }, upper := { exponent := 0, mantissa := (7025/4096) } }, logOuter := sk194LogOuterCertificate, logK := sk194LogKCertificate, logChi := chi119LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (2036073161/2036043776) } }, logDArg := sk194LogDArgCertificate }

private noncomputable def leaf2285InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf2285LocalValidity :
    LeafFacts leaf2285Box leaf2285Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2285Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (1018051273/1018021888) }) = true
      norm_num [leaf2285Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2285CertificateValid :
    WideCertificateValid leaf2285Box leaf2285Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk194ValidityFacts chi119ValidityFacts
    leaf2285LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2285CoverageChecked :
    coverageCheck (innerAD leaf2285Box) leaf2285InnerLog = true := by
  rfl'

private theorem leaf2285InnerLogValid :
    leaf2285InnerLog.Valid 8 (innerAD leaf2285Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf2285CoverageChecked

private noncomputable def leaf2285InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629323/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2285InputLogOnePlusV_eq :
    leaf2285InputLogOnePlusV = outerEnclosure 24
      (leaf2285Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2285RoundedFacts : LeafRoundedFacts 8
    leaf2285Certificate.logOnePlusV leaf2285InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2285InputLogOnePlusV_eq }

private noncomputable def leaf2285Inputs : Inputs :=
  inputsOfCaches globalInput sk194RoundedInputs
    chi119InputQChi innerPair57Input
    leaf2285InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2285LowerChecked :
    lowerCheck 24 leaf2285Box leaf2285Inputs = true := by
  rfl'

private theorem leaf2285CoversExact : CoversExact 8
    leaf2285Box leaf2285Certificate leaf2285InnerLog leaf2285Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk194RoundedFacts chi119RoundedFacts
    innerPair57RoundedFacts leaf2285RoundedFacts (by rfl)

private theorem leaf2285FlatSound : Sound leaf2285Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2285CertificateValid
    leaf2285InnerLogValid leaf2285CoversExact leaf2285LowerChecked

private noncomputable def leaf2286Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (203/64), chiLo := (7/32), chiHi := (29/128) }

private noncomputable def leaf2286Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871375/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432925184) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (907486675/536870912) }, upper := { exponent := 0, mantissa := (14079/8192) } }, logOuter := sk195LogOuterCertificate, logK := sk195LogKCertificate, logChi := chi119LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869847039/274865850368) } }, logDArg := sk195LogDArgCertificate }

private noncomputable def leaf2286InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf2286LocalValidity :
    LeafFacts leaf2286Box leaf2286Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2286Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432925184) }) = true
      norm_num [leaf2286Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2286CertificateValid :
    WideCertificateValid leaf2286Box leaf2286Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk195ValidityFacts chi119ValidityFacts
    leaf2286LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2286CoverageChecked :
    coverageCheck (innerAD leaf2286Box) leaf2286InnerLog = true := by
  rfl'

private theorem leaf2286InnerLogValid :
    leaf2286InnerLog.Valid 8 (innerAD leaf2286Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf2286CoverageChecked

private noncomputable def leaf2286InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629325/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2286InputLogOnePlusV_eq :
    leaf2286InputLogOnePlusV = outerEnclosure 24
      (leaf2286Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2286RoundedFacts : LeafRoundedFacts 8
    leaf2286Certificate.logOnePlusV leaf2286InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2286InputLogOnePlusV_eq }

private noncomputable def leaf2286Inputs : Inputs :=
  inputsOfCaches globalInput sk195RoundedInputs
    chi119InputQChi innerPair64Input
    leaf2286InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2286LowerChecked :
    lowerCheck 24 leaf2286Box leaf2286Inputs = true := by
  rfl'

private theorem leaf2286CoversExact : CoversExact 8
    leaf2286Box leaf2286Certificate leaf2286InnerLog leaf2286Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk195RoundedFacts chi119RoundedFacts
    innerPair64RoundedFacts leaf2286RoundedFacts (by rfl)

private theorem leaf2286FlatSound : Sound leaf2286Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2286CertificateValid
    leaf2286InnerLogValid leaf2286CoversExact leaf2286LowerChecked

private noncomputable def leaf2287Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (203/64), kHi := (51/16), chiLo := (7/32), chiHi := (29/128) }

private noncomputable def leaf2287Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871377/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432895488) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (909321569/536870912) }, upper := { exponent := 0, mantissa := (3527/2048) } }, logOuter := sk196LogOuterCertificate, logK := sk196LogKCertificate, logChi := chi119LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869817343/274865790976) } }, logDArg := sk196LogDArgCertificate }

private noncomputable def leaf2287InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf2287LocalValidity :
    LeafFacts leaf2287Box leaf2287Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2287Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432895488) }) = true
      norm_num [leaf2287Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2287CertificateValid :
    WideCertificateValid leaf2287Box leaf2287Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk196ValidityFacts chi119ValidityFacts
    leaf2287LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2287CoverageChecked :
    coverageCheck (innerAD leaf2287Box) leaf2287InnerLog = true := by
  rfl'

private theorem leaf2287InnerLogValid :
    leaf2287InnerLog.Valid 8 (innerAD leaf2287Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf2287CoverageChecked

private noncomputable def leaf2287InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629327/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2287InputLogOnePlusV_eq :
    leaf2287InputLogOnePlusV = outerEnclosure 24
      (leaf2287Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2287RoundedFacts : LeafRoundedFacts 8
    leaf2287Certificate.logOnePlusV leaf2287InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2287InputLogOnePlusV_eq }

private noncomputable def leaf2287Inputs : Inputs :=
  inputsOfCaches globalInput sk196RoundedInputs
    chi119InputQChi innerPair64Input
    leaf2287InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2287LowerChecked :
    lowerCheck 24 leaf2287Box leaf2287Inputs = true := by
  rfl'

private theorem leaf2287CoversExact : CoversExact 8
    leaf2287Box leaf2287Certificate leaf2287InnerLog leaf2287Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk196RoundedFacts chi119RoundedFacts
    innerPair64RoundedFacts leaf2287RoundedFacts (by rfl)

private theorem leaf2287FlatSound : Sound leaf2287Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2287CertificateValid
    leaf2287InnerLogValid leaf2287CoversExact leaf2287LowerChecked

private noncomputable def leaf2288Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (201/64), chiLo := (29/128), chiHi := (15/64) }

private noncomputable def leaf2288Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871373/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432778752) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (916923285/536870912) }, upper := { exponent := 0, mantissa := (7111/4096) } }, logOuter := sk193LogOuterCertificate, logK := sk193LogKCertificate, logChi := chi120LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869700607/274865557504) } }, logDArg := sk193LogDArgCertificate }

private noncomputable def leaf2288InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf2288LocalValidity :
    LeafFacts leaf2288Box leaf2288Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2288Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432778752) }) = true
      norm_num [leaf2288Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2288CertificateValid :
    WideCertificateValid leaf2288Box leaf2288Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk193ValidityFacts chi120ValidityFacts
    leaf2288LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2288CoverageChecked :
    coverageCheck (innerAD leaf2288Box) leaf2288InnerLog = true := by
  rfl'

private theorem leaf2288InnerLogValid :
    leaf2288InnerLog.Valid 8 (innerAD leaf2288Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf2288CoverageChecked

private noncomputable def leaf2288InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814667/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2288InputLogOnePlusV_eq :
    leaf2288InputLogOnePlusV = outerEnclosure 24
      (leaf2288Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2288RoundedFacts : LeafRoundedFacts 8
    leaf2288Certificate.logOnePlusV leaf2288InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2288InputLogOnePlusV_eq }

private noncomputable def leaf2288Inputs : Inputs :=
  inputsOfCaches globalInput sk193RoundedInputs
    chi120InputQChi innerPair64Input
    leaf2288InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2288LowerChecked :
    lowerCheck 24 leaf2288Box leaf2288Inputs = true := by
  rfl'

private theorem leaf2288CoversExact : CoversExact 8
    leaf2288Box leaf2288Certificate leaf2288InnerLog leaf2288Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk193RoundedFacts chi120RoundedFacts
    innerPair64RoundedFacts leaf2288RoundedFacts (by rfl)

private theorem leaf2288FlatSound : Sound leaf2288Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2288CertificateValid
    leaf2288InnerLogValid leaf2288CoversExact leaf2288LowerChecked

private noncomputable def leaf2289Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (201/64), kHi := (101/32), chiLo := (29/128), chiHi := (15/64) }

private noncomputable def leaf2289Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871375/536870912) }, vSqrt := { lower := (65529/65536), upper := (8084524815/8084279296) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (918823711/536870912) }, upper := { exponent := 0, mantissa := (3563/2048) } }, logOuter := sk194LogOuterCertificate, logK := sk194LogKCertificate, logChi := chi120LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (16168804111/16168558592) } }, logDArg := sk194LogDArgCertificate }

private noncomputable def leaf2289InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf2289LocalValidity :
    LeafFacts leaf2289Box leaf2289Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2289Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8084524815/8084279296) }) = true
      norm_num [leaf2289Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2289CertificateValid :
    WideCertificateValid leaf2289Box leaf2289Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk194ValidityFacts chi120ValidityFacts
    leaf2289LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2289CoverageChecked :
    coverageCheck (innerAD leaf2289Box) leaf2289InnerLog = true := by
  rfl'

private theorem leaf2289InnerLogValid :
    leaf2289InnerLog.Valid 8 (innerAD leaf2289Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf2289CoverageChecked

private noncomputable def leaf2289InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453667/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf2289InputLogOnePlusV_eq :
    leaf2289InputLogOnePlusV = outerEnclosure 24
      (leaf2289Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2289RoundedFacts : LeafRoundedFacts 8
    leaf2289Certificate.logOnePlusV leaf2289InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2289InputLogOnePlusV_eq }

private noncomputable def leaf2289Inputs : Inputs :=
  inputsOfCaches globalInput sk194RoundedInputs
    chi120InputQChi innerPair64Input
    leaf2289InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2289LowerChecked :
    lowerCheck 24 leaf2289Box leaf2289Inputs = true := by
  rfl'

private theorem leaf2289CoversExact : CoversExact 8
    leaf2289Box leaf2289Certificate leaf2289InnerLog leaf2289Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk194RoundedFacts chi120RoundedFacts
    innerPair64RoundedFacts leaf2289RoundedFacts (by rfl)

private theorem leaf2289FlatSound : Sound leaf2289Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2289CertificateValid
    leaf2289InnerLogValid leaf2289CoversExact leaf2289LowerChecked

private noncomputable def leaf2290Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (203/64), chiLo := (29/128), chiHi := (15/64) }

private noncomputable def leaf2290Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871377/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432717312) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (920724137/536870912) }, upper := { exponent := 0, mantissa := (7141/4096) } }, logOuter := sk195LogOuterCertificate, logK := sk195LogKCertificate, logChi := chi120LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869639167/274865434624) } }, logDArg := sk195LogDArgCertificate }

private noncomputable def leaf2290InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf2290LocalValidity :
    LeafFacts leaf2290Box leaf2290Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2290Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432717312) }) = true
      norm_num [leaf2290Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2290CertificateValid :
    WideCertificateValid leaf2290Box leaf2290Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk195ValidityFacts chi120ValidityFacts
    leaf2290LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2290CoverageChecked :
    coverageCheck (innerAD leaf2290Box) leaf2290InnerLog = true := by
  rfl'

private theorem leaf2290InnerLogValid :
    leaf2290InnerLog.Valid 8 (innerAD leaf2290Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf2290CoverageChecked

private noncomputable def leaf2290InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629337/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2290InputLogOnePlusV_eq :
    leaf2290InputLogOnePlusV = outerEnclosure 24
      (leaf2290Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2290RoundedFacts : LeafRoundedFacts 8
    leaf2290Certificate.logOnePlusV leaf2290InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2290InputLogOnePlusV_eq }

private noncomputable def leaf2290Inputs : Inputs :=
  inputsOfCaches globalInput sk195RoundedInputs
    chi120InputQChi innerPair64Input
    leaf2290InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2290LowerChecked :
    lowerCheck 24 leaf2290Box leaf2290Inputs = true := by
  rfl'

private theorem leaf2290CoversExact : CoversExact 8
    leaf2290Box leaf2290Certificate leaf2290InnerLog leaf2290Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk195RoundedFacts chi120RoundedFacts
    innerPair64RoundedFacts leaf2290RoundedFacts (by rfl)

private theorem leaf2290FlatSound : Sound leaf2290Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2290CertificateValid
    leaf2290InnerLogValid leaf2290CoversExact leaf2290LowerChecked

private noncomputable def leaf2291Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (203/64), kHi := (51/16), chiLo := (29/128), chiHi := (15/64) }

private noncomputable def leaf2291Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871379/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432686592) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (922624563/536870912) }, upper := { exponent := 0, mantissa := (1789/1024) } }, logOuter := sk196LogOuterCertificate, logK := sk196LogKCertificate, logChi := chi120LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869608447/274865373184) } }, logDArg := sk196LogDArgCertificate }

private noncomputable def leaf2291InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf2291LocalValidity :
    LeafFacts leaf2291Box leaf2291Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2291Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432686592) }) = true
      norm_num [leaf2291Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2291CertificateValid :
    WideCertificateValid leaf2291Box leaf2291Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk196ValidityFacts chi120ValidityFacts
    leaf2291LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2291CoverageChecked :
    coverageCheck (innerAD leaf2291Box) leaf2291InnerLog = true := by
  rfl'

private theorem leaf2291InnerLogValid :
    leaf2291InnerLog.Valid 8 (innerAD leaf2291Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf2291CoverageChecked

private noncomputable def leaf2291InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629339/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2291InputLogOnePlusV_eq :
    leaf2291InputLogOnePlusV = outerEnclosure 24
      (leaf2291Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2291RoundedFacts : LeafRoundedFacts 8
    leaf2291Certificate.logOnePlusV leaf2291InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2291InputLogOnePlusV_eq }

private noncomputable def leaf2291Inputs : Inputs :=
  inputsOfCaches globalInput sk196RoundedInputs
    chi120InputQChi innerPair64Input
    leaf2291InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2291LowerChecked :
    lowerCheck 24 leaf2291Box leaf2291Inputs = true := by
  rfl'

private theorem leaf2291CoversExact : CoversExact 8
    leaf2291Box leaf2291Certificate leaf2291InnerLog leaf2291Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk196RoundedFacts chi120RoundedFacts
    innerPair64RoundedFacts leaf2291RoundedFacts (by rfl)

private theorem leaf2291FlatSound : Sound leaf2291Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2291CertificateValid
    leaf2291InnerLogValid leaf2291CoversExact leaf2291LowerChecked

private noncomputable def leaf2292Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (205/64), chiLo := (7/32), chiHi := (29/128) }

private noncomputable def leaf2292Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871379/536870912) }, vSqrt := { lower := (65529/65536), upper := (45812307285/45810955264) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (911156463/536870912) }, upper := { exponent := 0, mantissa := (14137/8192) } }, logOuter := sk197LogOuterCertificate, logK := sk197LogKCertificate, logChi := chi119LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (91623262549/91621910528) } }, logDArg := sk197LogDArgCertificate }

private noncomputable def leaf2292InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf2292LocalValidity :
    LeafFacts leaf2292Box leaf2292Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2292Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (45812307285/45810955264) }) = true
      norm_num [leaf2292Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2292CertificateValid :
    WideCertificateValid leaf2292Box leaf2292Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk197ValidityFacts chi119ValidityFacts
    leaf2292LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2292CoverageChecked :
    coverageCheck (innerAD leaf2292Box) leaf2292InnerLog = true := by
  rfl'

private theorem leaf2292InnerLogValid :
    leaf2292InnerLog.Valid 8 (innerAD leaf2292Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf2292CoverageChecked

private noncomputable def leaf2292InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (726833/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf2292InputLogOnePlusV_eq :
    leaf2292InputLogOnePlusV = outerEnclosure 24
      (leaf2292Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2292RoundedFacts : LeafRoundedFacts 8
    leaf2292Certificate.logOnePlusV leaf2292InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2292InputLogOnePlusV_eq }

private noncomputable def leaf2292Inputs : Inputs :=
  inputsOfCaches globalInput sk197RoundedInputs
    chi119InputQChi innerPair64Input
    leaf2292InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2292LowerChecked :
    lowerCheck 24 leaf2292Box leaf2292Inputs = true := by
  rfl'

private theorem leaf2292CoversExact : CoversExact 8
    leaf2292Box leaf2292Certificate leaf2292InnerLog leaf2292Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk197RoundedFacts chi119RoundedFacts
    innerPair64RoundedFacts leaf2292RoundedFacts (by rfl)

private theorem leaf2292FlatSound : Sound leaf2292Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2292CertificateValid
    leaf2292InnerLogValid leaf2292CoversExact leaf2292LowerChecked

private noncomputable def leaf2293Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (205/64), kHi := (103/32), chiLo := (7/32), chiHi := (29/128) }

private noncomputable def leaf2293Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871381/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432836096) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (912991357/536870912) }, upper := { exponent := 0, mantissa := (7083/4096) } }, logOuter := sk198LogOuterCertificate, logK := sk198LogKCertificate, logChi := chi119LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869757951/274865672192) } }, logDArg := sk198LogDArgCertificate }

private noncomputable def leaf2293InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf2293LocalValidity :
    LeafFacts leaf2293Box leaf2293Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2293Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432836096) }) = true
      norm_num [leaf2293Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2293CertificateValid :
    WideCertificateValid leaf2293Box leaf2293Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk198ValidityFacts chi119ValidityFacts
    leaf2293LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2293CoverageChecked :
    coverageCheck (innerAD leaf2293Box) leaf2293InnerLog = true := by
  rfl'

private theorem leaf2293InnerLogValid :
    leaf2293InnerLog.Valid 8 (innerAD leaf2293Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf2293CoverageChecked

private noncomputable def leaf2293InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814665/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2293InputLogOnePlusV_eq :
    leaf2293InputLogOnePlusV = outerEnclosure 24
      (leaf2293Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2293RoundedFacts : LeafRoundedFacts 8
    leaf2293Certificate.logOnePlusV leaf2293InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2293InputLogOnePlusV_eq }

private noncomputable def leaf2293Inputs : Inputs :=
  inputsOfCaches globalInput sk198RoundedInputs
    chi119InputQChi innerPair64Input
    leaf2293InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2293LowerChecked :
    lowerCheck 24 leaf2293Box leaf2293Inputs = true := by
  rfl'

private theorem leaf2293CoversExact : CoversExact 8
    leaf2293Box leaf2293Certificate leaf2293InnerLog leaf2293Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk198RoundedFacts chi119RoundedFacts
    innerPair64RoundedFacts leaf2293RoundedFacts (by rfl)

private theorem leaf2293FlatSound : Sound leaf2293Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2293CertificateValid
    leaf2293InnerLogValid leaf2293CoversExact leaf2293LowerChecked

private noncomputable def leaf2294Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (207/64), chiLo := (7/32), chiHi := (29/128) }

private noncomputable def leaf2294Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871383/536870912) }, vSqrt := { lower := (65529/65536), upper := (27487384371/27486561280) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (914826251/536870912) }, upper := { exponent := 0, mantissa := (14195/8192) } }, logOuter := sk199LogOuterCertificate, logK := sk199LogKCertificate, logChi := chi119LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (54973945651/54973122560) } }, logDArg := sk199LogDArgCertificate }

private noncomputable def leaf2294InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf2294LocalValidity :
    LeafFacts leaf2294Box leaf2294Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2294Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (27487384371/27486561280) }) = true
      norm_num [leaf2294Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2294CertificateValid :
    WideCertificateValid leaf2294Box leaf2294Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk199ValidityFacts chi119ValidityFacts
    leaf2294LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2294CoverageChecked :
    coverageCheck (innerAD leaf2294Box) leaf2294InnerLog = true := by
  rfl'

private theorem leaf2294InnerLogValid :
    leaf2294InnerLog.Valid 8 (innerAD leaf2294Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf2294CoverageChecked

private noncomputable def leaf2294InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907333/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2294InputLogOnePlusV_eq :
    leaf2294InputLogOnePlusV = outerEnclosure 24
      (leaf2294Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2294RoundedFacts : LeafRoundedFacts 8
    leaf2294Certificate.logOnePlusV leaf2294InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2294InputLogOnePlusV_eq }

private noncomputable def leaf2294Inputs : Inputs :=
  inputsOfCaches globalInput sk199RoundedInputs
    chi119InputQChi innerPair64Input
    leaf2294InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2294LowerChecked :
    lowerCheck 24 leaf2294Box leaf2294Inputs = true := by
  rfl'

private theorem leaf2294CoversExact : CoversExact 8
    leaf2294Box leaf2294Certificate leaf2294InnerLog leaf2294Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk199RoundedFacts chi119RoundedFacts
    innerPair64RoundedFacts leaf2294RoundedFacts (by rfl)

private theorem leaf2294FlatSound : Sound leaf2294Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2294CertificateValid
    leaf2294InnerLogValid leaf2294CoversExact leaf2294LowerChecked

private noncomputable def leaf2295Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (207/64), kHi := (13/4), chiLo := (7/32), chiHi := (29/128) }

private noncomputable def leaf2295Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871385/536870912) }, vSqrt := { lower := (65529/65536), upper := (45812307285/45810925568) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (916661145/536870912) }, upper := { exponent := 0, mantissa := (889/512) } }, logOuter := sk200LogOuterCertificate, logK := sk200LogKCertificate, logChi := chi119LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (91623232853/91621851136) } }, logDArg := sk200LogDArgCertificate }

private noncomputable def leaf2295InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf2295LocalValidity :
    LeafFacts leaf2295Box leaf2295Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2295Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (45812307285/45810925568) }) = true
      norm_num [leaf2295Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2295CertificateValid :
    WideCertificateValid leaf2295Box leaf2295Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk200ValidityFacts chi119ValidityFacts
    leaf2295LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2295CoverageChecked :
    coverageCheck (innerAD leaf2295Box) leaf2295InnerLog = true := by
  rfl'

private theorem leaf2295InnerLogValid :
    leaf2295InnerLog.Valid 8 (innerAD leaf2295Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf2295CoverageChecked

private noncomputable def leaf2295InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814667/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2295InputLogOnePlusV_eq :
    leaf2295InputLogOnePlusV = outerEnclosure 24
      (leaf2295Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2295RoundedFacts : LeafRoundedFacts 8
    leaf2295Certificate.logOnePlusV leaf2295InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2295InputLogOnePlusV_eq }

private noncomputable def leaf2295Inputs : Inputs :=
  inputsOfCaches globalInput sk200RoundedInputs
    chi119InputQChi innerPair64Input
    leaf2295InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2295LowerChecked :
    lowerCheck 24 leaf2295Box leaf2295Inputs = true := by
  rfl'

private theorem leaf2295CoversExact : CoversExact 8
    leaf2295Box leaf2295Certificate leaf2295InnerLog leaf2295Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk200RoundedFacts chi119RoundedFacts
    innerPair64RoundedFacts leaf2295RoundedFacts (by rfl)

private theorem leaf2295FlatSound : Sound leaf2295Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2295CertificateValid
    leaf2295InnerLogValid leaf2295CoversExact leaf2295LowerChecked

private noncomputable def leaf2296Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (205/64), chiLo := (29/128), chiHi := (15/64) }

private noncomputable def leaf2296Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871381/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432655872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (924524989/536870912) }, upper := { exponent := 0, mantissa := (7171/4096) } }, logOuter := sk197LogOuterCertificate, logK := sk197LogKCertificate, logChi := chi120LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869577727/274865311744) } }, logDArg := sk197LogDArgCertificate }

private noncomputable def leaf2296InnerLog : WideLogData :=
  innerPair204Data

set_option maxRecDepth 1000000 in
private theorem leaf2296LocalValidity :
    LeafFacts leaf2296Box leaf2296Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2296Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432655872) }) = true
      norm_num [leaf2296Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2296CertificateValid :
    WideCertificateValid leaf2296Box leaf2296Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk197ValidityFacts chi120ValidityFacts
    leaf2296LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2296CoverageChecked :
    coverageCheck (innerAD leaf2296Box) leaf2296InnerLog = true := by
  rfl'

private theorem leaf2296InnerLogValid :
    leaf2296InnerLog.Valid 8 (innerAD leaf2296Box) :=
  wideLogDataValid_of_cachedCheck endpoint62PositiveFacts
    endpoint63PositiveFacts.valid leaf2296CoverageChecked

private noncomputable def leaf2296InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629341/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2296InputLogOnePlusV_eq :
    leaf2296InputLogOnePlusV = outerEnclosure 24
      (leaf2296Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2296RoundedFacts : LeafRoundedFacts 8
    leaf2296Certificate.logOnePlusV leaf2296InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2296InputLogOnePlusV_eq }

private noncomputable def leaf2296Inputs : Inputs :=
  inputsOfCaches globalInput sk197RoundedInputs
    chi120InputQChi innerPair204Input
    leaf2296InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2296LowerChecked :
    lowerCheck 24 leaf2296Box leaf2296Inputs = true := by
  rfl'

private theorem leaf2296CoversExact : CoversExact 8
    leaf2296Box leaf2296Certificate leaf2296InnerLog leaf2296Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk197RoundedFacts chi120RoundedFacts
    innerPair204RoundedFacts leaf2296RoundedFacts (by rfl)

private theorem leaf2296FlatSound : Sound leaf2296Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2296CertificateValid
    leaf2296InnerLogValid leaf2296CoversExact leaf2296LowerChecked

private noncomputable def leaf2297Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (205/64), kHi := (103/32), chiLo := (29/128), chiHi := (15/64) }

private noncomputable def leaf2297Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871383/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432625152) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (926425415/536870912) }, upper := { exponent := 0, mantissa := (3593/2048) } }, logOuter := sk198LogOuterCertificate, logK := sk198LogKCertificate, logChi := chi120LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869547007/274865250304) } }, logDArg := sk198LogDArgCertificate }

private noncomputable def leaf2297InnerLog : WideLogData :=
  innerPair204Data

set_option maxRecDepth 1000000 in
private theorem leaf2297LocalValidity :
    LeafFacts leaf2297Box leaf2297Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2297Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432625152) }) = true
      norm_num [leaf2297Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2297CertificateValid :
    WideCertificateValid leaf2297Box leaf2297Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk198ValidityFacts chi120ValidityFacts
    leaf2297LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2297CoverageChecked :
    coverageCheck (innerAD leaf2297Box) leaf2297InnerLog = true := by
  rfl'

private theorem leaf2297InnerLogValid :
    leaf2297InnerLog.Valid 8 (innerAD leaf2297Box) :=
  wideLogDataValid_of_cachedCheck endpoint62PositiveFacts
    endpoint63PositiveFacts.valid leaf2297CoverageChecked

private noncomputable def leaf2297InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629343/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2297InputLogOnePlusV_eq :
    leaf2297InputLogOnePlusV = outerEnclosure 24
      (leaf2297Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2297RoundedFacts : LeafRoundedFacts 8
    leaf2297Certificate.logOnePlusV leaf2297InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2297InputLogOnePlusV_eq }

private noncomputable def leaf2297Inputs : Inputs :=
  inputsOfCaches globalInput sk198RoundedInputs
    chi120InputQChi innerPair204Input
    leaf2297InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2297LowerChecked :
    lowerCheck 24 leaf2297Box leaf2297Inputs = true := by
  rfl'

private theorem leaf2297CoversExact : CoversExact 8
    leaf2297Box leaf2297Certificate leaf2297InnerLog leaf2297Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk198RoundedFacts chi120RoundedFacts
    innerPair204RoundedFacts leaf2297RoundedFacts (by rfl)

private theorem leaf2297FlatSound : Sound leaf2297Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2297CertificateValid
    leaf2297InnerLogValid leaf2297CoversExact leaf2297LowerChecked

private noncomputable def leaf2298Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (207/64), chiLo := (29/128), chiHi := (15/64) }

private noncomputable def leaf2298Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871385/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432594432) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (928325841/536870912) }, upper := { exponent := 0, mantissa := (7201/4096) } }, logOuter := sk199LogOuterCertificate, logK := sk199LogKCertificate, logChi := chi120LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869516287/274865188864) } }, logDArg := sk199LogDArgCertificate }

private noncomputable def leaf2298InnerLog : WideLogData :=
  innerPair204Data

set_option maxRecDepth 1000000 in
private theorem leaf2298LocalValidity :
    LeafFacts leaf2298Box leaf2298Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2298Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432594432) }) = true
      norm_num [leaf2298Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2298CertificateValid :
    WideCertificateValid leaf2298Box leaf2298Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk199ValidityFacts chi120ValidityFacts
    leaf2298LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2298CoverageChecked :
    coverageCheck (innerAD leaf2298Box) leaf2298InnerLog = true := by
  rfl'

private theorem leaf2298InnerLogValid :
    leaf2298InnerLog.Valid 8 (innerAD leaf2298Box) :=
  wideLogDataValid_of_cachedCheck endpoint62PositiveFacts
    endpoint63PositiveFacts.valid leaf2298CoverageChecked

private noncomputable def leaf2298InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629345/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2298InputLogOnePlusV_eq :
    leaf2298InputLogOnePlusV = outerEnclosure 24
      (leaf2298Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2298RoundedFacts : LeafRoundedFacts 8
    leaf2298Certificate.logOnePlusV leaf2298InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2298InputLogOnePlusV_eq }

private noncomputable def leaf2298Inputs : Inputs :=
  inputsOfCaches globalInput sk199RoundedInputs
    chi120InputQChi innerPair204Input
    leaf2298InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2298LowerChecked :
    lowerCheck 24 leaf2298Box leaf2298Inputs = true := by
  rfl'

private theorem leaf2298CoversExact : CoversExact 8
    leaf2298Box leaf2298Certificate leaf2298InnerLog leaf2298Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk199RoundedFacts chi120RoundedFacts
    innerPair204RoundedFacts leaf2298RoundedFacts (by rfl)

private theorem leaf2298FlatSound : Sound leaf2298Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2298CertificateValid
    leaf2298InnerLogValid leaf2298CoversExact leaf2298LowerChecked

private noncomputable def leaf2299Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (207/64), kHi := (13/4), chiLo := (29/128), chiHi := (15/64) }

private noncomputable def leaf2299Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871387/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432563712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (930226267/536870912) }, upper := { exponent := 0, mantissa := (451/256) } }, logOuter := sk200LogOuterCertificate, logK := sk200LogKCertificate, logChi := chi120LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869485567/274865127424) } }, logDArg := sk200LogDArgCertificate }

private noncomputable def leaf2299InnerLog : WideLogData :=
  innerPair204Data

set_option maxRecDepth 1000000 in
private theorem leaf2299LocalValidity :
    LeafFacts leaf2299Box leaf2299Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2299Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432563712) }) = true
      norm_num [leaf2299Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2299CertificateValid :
    WideCertificateValid leaf2299Box leaf2299Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk200ValidityFacts chi120ValidityFacts
    leaf2299LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2299CoverageChecked :
    coverageCheck (innerAD leaf2299Box) leaf2299InnerLog = true := by
  rfl'

private theorem leaf2299InnerLogValid :
    leaf2299InnerLog.Valid 8 (innerAD leaf2299Box) :=
  wideLogDataValid_of_cachedCheck endpoint62PositiveFacts
    endpoint63PositiveFacts.valid leaf2299CoverageChecked

private noncomputable def leaf2299InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629347/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2299InputLogOnePlusV_eq :
    leaf2299InputLogOnePlusV = outerEnclosure 24
      (leaf2299Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2299RoundedFacts : LeafRoundedFacts 8
    leaf2299Certificate.logOnePlusV leaf2299InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2299InputLogOnePlusV_eq }

private noncomputable def leaf2299Inputs : Inputs :=
  inputsOfCaches globalInput sk200RoundedInputs
    chi120InputQChi innerPair204Input
    leaf2299InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2299LowerChecked :
    lowerCheck 24 leaf2299Box leaf2299Inputs = true := by
  rfl'

private theorem leaf2299CoversExact : CoversExact 8
    leaf2299Box leaf2299Certificate leaf2299InnerLog leaf2299Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk200RoundedFacts chi120RoundedFacts
    innerPair204RoundedFacts leaf2299RoundedFacts (by rfl)

private theorem leaf2299FlatSound : Sound leaf2299Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2299CertificateValid
    leaf2299InnerLogValid leaf2299CoversExact leaf2299LowerChecked

private noncomputable def leaf2300Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (201/64), chiLo := (15/64), chiHi := (31/128) }

private noncomputable def leaf2300Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871375/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432572928) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (930029683/536870912) }, upper := { exponent := 0, mantissa := (14423/8192) } }, logOuter := sk193LogOuterCertificate, logK := sk193LogKCertificate, logChi := chi121LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869494783/274865145856) } }, logDArg := sk193LogDArgCertificate }

private noncomputable def leaf2300InnerLog : WideLogData :=
  innerPair204Data

set_option maxRecDepth 1000000 in
private theorem leaf2300LocalValidity :
    LeafFacts leaf2300Box leaf2300Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2300Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432572928) }) = true
      norm_num [leaf2300Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2300CertificateValid :
    WideCertificateValid leaf2300Box leaf2300Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk193ValidityFacts chi121ValidityFacts
    leaf2300LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2300CoverageChecked :
    coverageCheck (innerAD leaf2300Box) leaf2300InnerLog = true := by
  rfl'

private theorem leaf2300InnerLogValid :
    leaf2300InnerLog.Valid 8 (innerAD leaf2300Box) :=
  wideLogDataValid_of_cachedCheck endpoint62PositiveFacts
    endpoint63PositiveFacts.valid leaf2300CoverageChecked

private noncomputable def leaf2300InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814673/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2300InputLogOnePlusV_eq :
    leaf2300InputLogOnePlusV = outerEnclosure 24
      (leaf2300Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2300RoundedFacts : LeafRoundedFacts 8
    leaf2300Certificate.logOnePlusV leaf2300InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2300InputLogOnePlusV_eq }

private noncomputable def leaf2300Inputs : Inputs :=
  inputsOfCaches globalInput sk193RoundedInputs
    chi121InputQChi innerPair204Input
    leaf2300InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2300LowerChecked :
    lowerCheck 24 leaf2300Box leaf2300Inputs = true := by
  rfl'

private theorem leaf2300CoversExact : CoversExact 8
    leaf2300Box leaf2300Certificate leaf2300InnerLog leaf2300Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk193RoundedFacts chi121RoundedFacts
    innerPair204RoundedFacts leaf2300RoundedFacts (by rfl)

private theorem leaf2300FlatSound : Sound leaf2300Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2300CertificateValid
    leaf2300InnerLogValid leaf2300CoversExact leaf2300LowerChecked

private noncomputable def leaf2301Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (201/64), kHi := (101/32), chiLo := (15/64), chiHi := (31/128) }

private noncomputable def leaf2301Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871377/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432541184) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (931995641/536870912) }, upper := { exponent := 0, mantissa := (7227/4096) } }, logOuter := sk194LogOuterCertificate, logK := sk194LogKCertificate, logChi := chi121LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869463039/274865082368) } }, logDArg := sk194LogDArgCertificate }

private noncomputable def leaf2301InnerLog : WideLogData :=
  innerPair430Data

set_option maxRecDepth 1000000 in
private theorem leaf2301LocalValidity :
    LeafFacts leaf2301Box leaf2301Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2301Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432541184) }) = true
      norm_num [leaf2301Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2301CertificateValid :
    WideCertificateValid leaf2301Box leaf2301Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk194ValidityFacts chi121ValidityFacts
    leaf2301LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2301CoverageChecked :
    coverageCheck (innerAD leaf2301Box) leaf2301InnerLog = true := by
  rfl'

private theorem leaf2301InnerLogValid :
    leaf2301InnerLog.Valid 8 (innerAD leaf2301Box) :=
  wideLogDataValid_of_cachedCheck endpoint139PositiveFacts
    endpoint63PositiveFacts.valid leaf2301CoverageChecked

private noncomputable def leaf2301InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907337/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2301InputLogOnePlusV_eq :
    leaf2301InputLogOnePlusV = outerEnclosure 24
      (leaf2301Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2301RoundedFacts : LeafRoundedFacts 8
    leaf2301Certificate.logOnePlusV leaf2301InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2301InputLogOnePlusV_eq }

private noncomputable def leaf2301Inputs : Inputs :=
  inputsOfCaches globalInput sk194RoundedInputs
    chi121InputQChi innerPair430Input
    leaf2301InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2301LowerChecked :
    lowerCheck 24 leaf2301Box leaf2301Inputs = true := by
  rfl'

private theorem leaf2301CoversExact : CoversExact 8
    leaf2301Box leaf2301Certificate leaf2301InnerLog leaf2301Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk194RoundedFacts chi121RoundedFacts
    innerPair430RoundedFacts leaf2301RoundedFacts (by rfl)

private theorem leaf2301FlatSound : Sound leaf2301Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2301CertificateValid
    leaf2301InnerLogValid leaf2301CoversExact leaf2301LowerChecked

private noncomputable def leaf2302Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (203/64), chiLo := (15/64), chiHi := (31/128) }

private noncomputable def leaf2302Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871379/536870912) }, vSqrt := { lower := (65529/65536), upper := (9162461457/9162167296) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (933961599/536870912) }, upper := { exponent := 0, mantissa := (14485/8192) } }, logOuter := sk195LogOuterCertificate, logK := sk195LogKCertificate, logChi := chi121LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (18324628753/18324334592) } }, logDArg := sk195LogDArgCertificate }

private noncomputable def leaf2302InnerLog : WideLogData :=
  innerPair431Data

set_option maxRecDepth 1000000 in
private theorem leaf2302LocalValidity :
    LeafFacts leaf2302Box leaf2302Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2302Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (9162461457/9162167296) }) = true
      norm_num [leaf2302Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2302CertificateValid :
    WideCertificateValid leaf2302Box leaf2302Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk195ValidityFacts chi121ValidityFacts
    leaf2302LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2302CoverageChecked :
    coverageCheck (innerAD leaf2302Box) leaf2302InnerLog = true := by
  rfl'

private theorem leaf2302InnerLogValid :
    leaf2302InnerLog.Valid 8 (innerAD leaf2302Box) :=
  wideLogDataValid_of_cachedCheck endpoint139PositiveFacts
    endpoint68PositiveFacts.valid leaf2302CoverageChecked

private noncomputable def leaf2302InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814675/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2302InputLogOnePlusV_eq :
    leaf2302InputLogOnePlusV = outerEnclosure 24
      (leaf2302Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2302RoundedFacts : LeafRoundedFacts 8
    leaf2302Certificate.logOnePlusV leaf2302InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2302InputLogOnePlusV_eq }

private noncomputable def leaf2302Inputs : Inputs :=
  inputsOfCaches globalInput sk195RoundedInputs
    chi121InputQChi innerPair431Input
    leaf2302InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2302LowerChecked :
    lowerCheck 24 leaf2302Box leaf2302Inputs = true := by
  rfl'

private theorem leaf2302CoversExact : CoversExact 8
    leaf2302Box leaf2302Certificate leaf2302InnerLog leaf2302Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk195RoundedFacts chi121RoundedFacts
    innerPair431RoundedFacts leaf2302RoundedFacts (by rfl)

private theorem leaf2302FlatSound : Sound leaf2302Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2302CertificateValid
    leaf2302InnerLogValid leaf2302CoversExact leaf2302LowerChecked

private noncomputable def leaf2303Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (203/64), kHi := (51/16), chiLo := (15/64), chiHi := (31/128) }

private noncomputable def leaf2303Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871381/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432477696) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (935927557/536870912) }, upper := { exponent := 0, mantissa := (3629/2048) } }, logOuter := sk196LogOuterCertificate, logK := sk196LogKCertificate, logChi := chi121LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869399551/274864955392) } }, logDArg := sk196LogDArgCertificate }

private noncomputable def leaf2303InnerLog : WideLogData :=
  innerPair431Data

set_option maxRecDepth 1000000 in
private theorem leaf2303LocalValidity :
    LeafFacts leaf2303Box leaf2303Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2303Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432477696) }) = true
      norm_num [leaf2303Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2303CertificateValid :
    WideCertificateValid leaf2303Box leaf2303Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk196ValidityFacts chi121ValidityFacts
    leaf2303LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2303CoverageChecked :
    coverageCheck (innerAD leaf2303Box) leaf2303InnerLog = true := by
  rfl'

private theorem leaf2303InnerLogValid :
    leaf2303InnerLog.Valid 8 (innerAD leaf2303Box) :=
  wideLogDataValid_of_cachedCheck endpoint139PositiveFacts
    endpoint68PositiveFacts.valid leaf2303CoverageChecked

private noncomputable def leaf2303InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453669/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf2303InputLogOnePlusV_eq :
    leaf2303InputLogOnePlusV = outerEnclosure 24
      (leaf2303Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2303RoundedFacts : LeafRoundedFacts 8
    leaf2303Certificate.logOnePlusV leaf2303InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2303InputLogOnePlusV_eq }

private noncomputable def leaf2303Inputs : Inputs :=
  inputsOfCaches globalInput sk196RoundedInputs
    chi121InputQChi innerPair431Input
    leaf2303InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2303LowerChecked :
    lowerCheck 24 leaf2303Box leaf2303Inputs = true := by
  rfl'

private theorem leaf2303CoversExact : CoversExact 8
    leaf2303Box leaf2303Certificate leaf2303InnerLog leaf2303Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk196RoundedFacts chi121RoundedFacts
    innerPair431RoundedFacts leaf2303RoundedFacts (by rfl)

private theorem leaf2303FlatSound : Sound leaf2303Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2303CertificateValid
    leaf2303InnerLogValid leaf2303CoversExact leaf2303LowerChecked

private noncomputable def leaf2304Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (201/64), chiLo := (31/128), chiHi := (1/4) }

private noncomputable def leaf2304Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871377/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432367104) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (943136081/536870912) }, upper := { exponent := 0, mantissa := (457/256) } }, logOuter := sk193LogOuterCertificate, logK := sk193LogKCertificate, logChi := chi122LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869288959/274864734208) } }, logDArg := sk193LogDArgCertificate }

private noncomputable def leaf2304InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf2304LocalValidity :
    LeafFacts leaf2304Box leaf2304Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2304Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432367104) }) = true
      norm_num [leaf2304Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2304CertificateValid :
    WideCertificateValid leaf2304Box leaf2304Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk193ValidityFacts chi122ValidityFacts
    leaf2304LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2304CoverageChecked :
    coverageCheck (innerAD leaf2304Box) leaf2304InnerLog = true := by
  rfl'

private theorem leaf2304InnerLogValid :
    leaf2304InnerLog.Valid 8 (innerAD leaf2304Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf2304CoverageChecked

private noncomputable def leaf2304InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629359/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2304InputLogOnePlusV_eq :
    leaf2304InputLogOnePlusV = outerEnclosure 24
      (leaf2304Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2304RoundedFacts : LeafRoundedFacts 8
    leaf2304Certificate.logOnePlusV leaf2304InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2304InputLogOnePlusV_eq }

private noncomputable def leaf2304Inputs : Inputs :=
  inputsOfCaches globalInput sk193RoundedInputs
    chi122InputQChi innerPair71Input
    leaf2304InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2304LowerChecked :
    lowerCheck 24 leaf2304Box leaf2304Inputs = true := by
  rfl'

private theorem leaf2304CoversExact : CoversExact 8
    leaf2304Box leaf2304Certificate leaf2304InnerLog leaf2304Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk193RoundedFacts chi122RoundedFacts
    innerPair71RoundedFacts leaf2304RoundedFacts (by rfl)

private theorem leaf2304FlatSound : Sound leaf2304Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2304CertificateValid
    leaf2304InnerLogValid leaf2304CoversExact leaf2304LowerChecked

private noncomputable def leaf2305Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (201/64), kHi := (101/32), chiLo := (31/128), chiHi := (1/4) }

private noncomputable def leaf2305Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871379/536870912) }, vSqrt := { lower := (65529/65536), upper := (45812307285/45810778112) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (945167571/536870912) }, upper := { exponent := 0, mantissa := (229/128) } }, logOuter := sk194LogOuterCertificate, logK := sk194LogKCertificate, logChi := chi122LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (91623085397/91621556224) } }, logDArg := sk194LogDArgCertificate }

private noncomputable def leaf2305InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf2305LocalValidity :
    LeafFacts leaf2305Box leaf2305Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2305Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (45812307285/45810778112) }) = true
      norm_num [leaf2305Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2305CertificateValid :
    WideCertificateValid leaf2305Box leaf2305Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk194ValidityFacts chi122ValidityFacts
    leaf2305LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2305CoverageChecked :
    coverageCheck (innerAD leaf2305Box) leaf2305InnerLog = true := by
  rfl'

private theorem leaf2305InnerLogValid :
    leaf2305InnerLog.Valid 8 (innerAD leaf2305Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf2305CoverageChecked

private noncomputable def leaf2305InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629361/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2305InputLogOnePlusV_eq :
    leaf2305InputLogOnePlusV = outerEnclosure 24
      (leaf2305Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2305RoundedFacts : LeafRoundedFacts 8
    leaf2305Certificate.logOnePlusV leaf2305InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2305InputLogOnePlusV_eq }

private noncomputable def leaf2305Inputs : Inputs :=
  inputsOfCaches globalInput sk194RoundedInputs
    chi122InputQChi innerPair71Input
    leaf2305InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2305LowerChecked :
    lowerCheck 24 leaf2305Box leaf2305Inputs = true := by
  rfl'

private theorem leaf2305CoversExact : CoversExact 8
    leaf2305Box leaf2305Certificate leaf2305InnerLog leaf2305Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk194RoundedFacts chi122RoundedFacts
    innerPair71RoundedFacts leaf2305RoundedFacts (by rfl)

private theorem leaf2305FlatSound : Sound leaf2305Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2305CertificateValid
    leaf2305InnerLogValid leaf2305CoversExact leaf2305LowerChecked

private noncomputable def leaf2306Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (31/128), chiHi := (63/256) }

private noncomputable def leaf2306Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871241/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68716186624) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (947199201/536870912) }, upper := { exponent := 0, mantissa := (7309/4096) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi189LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434680319/137432373248) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf2306InnerLog : WideLogData :=
  innerPair77Data

set_option maxRecDepth 1000000 in
private theorem leaf2306LocalValidity :
    LeafFacts leaf2306Box leaf2306Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2306Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68716186624) }) = true
      norm_num [leaf2306Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2306CertificateValid :
    WideCertificateValid leaf2306Box leaf2306Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi189ValidityFacts
    leaf2306LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2306CoverageChecked :
    coverageCheck (innerAD leaf2306Box) leaf2306InnerLog = true := by
  rfl'

private theorem leaf2306InnerLogValid :
    leaf2306InnerLog.Valid 8 (innerAD leaf2306Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint67PositiveFacts.valid leaf2306CoverageChecked

private noncomputable def leaf2306InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814681/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2306InputLogOnePlusV_eq :
    leaf2306InputLogOnePlusV = outerEnclosure 24
      (leaf2306Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2306RoundedFacts : LeafRoundedFacts 8
    leaf2306Certificate.logOnePlusV leaf2306InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2306InputLogOnePlusV_eq }

private noncomputable def leaf2306Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi189InputQChi innerPair77Input
    leaf2306InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2306LowerChecked :
    lowerCheck 24 leaf2306Box leaf2306Inputs = true := by
  rfl'

private theorem leaf2306CoversExact : CoversExact 8
    leaf2306Box leaf2306Certificate leaf2306InnerLog leaf2306Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi189RoundedFacts
    innerPair77RoundedFacts leaf2306RoundedFacts (by rfl)

private theorem leaf2306FlatSound : Sound leaf2306Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2306CertificateValid
    leaf2306InnerLogValid leaf2306CoversExact leaf2306LowerChecked

private noncomputable def leaf2307Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (63/256), chiHi := (1/4) }

private noncomputable def leaf2307Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871243/536870912) }, vSqrt := { lower := (65529/65536), upper := (13743698739/13743226880) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (953817931/536870912) }, upper := { exponent := 0, mantissa := (115/64) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi190LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (27486925619/27486453760) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf2307InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf2307LocalValidity :
    LeafFacts leaf2307Box leaf2307Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2307Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (13743698739/13743226880) }) = true
      norm_num [leaf2307Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2307CertificateValid :
    WideCertificateValid leaf2307Box leaf2307Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi190ValidityFacts
    leaf2307LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2307CoverageChecked :
    coverageCheck (innerAD leaf2307Box) leaf2307InnerLog = true := by
  rfl'

private theorem leaf2307InnerLogValid :
    leaf2307InnerLog.Valid 8 (innerAD leaf2307Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf2307CoverageChecked

private noncomputable def leaf2307InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629369/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2307InputLogOnePlusV_eq :
    leaf2307InputLogOnePlusV = outerEnclosure 24
      (leaf2307Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2307RoundedFacts : LeafRoundedFacts 8
    leaf2307Certificate.logOnePlusV leaf2307InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2307InputLogOnePlusV_eq }

private noncomputable def leaf2307Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi190InputQChi innerPair71Input
    leaf2307InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2307LowerChecked :
    lowerCheck 24 leaf2307Box leaf2307Inputs = true := by
  rfl'

private theorem leaf2307CoversExact : CoversExact 8
    leaf2307Box leaf2307Certificate leaf2307InnerLog leaf2307Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi190RoundedFacts
    innerPair71RoundedFacts leaf2307RoundedFacts (by rfl)

private theorem leaf2307FlatSound : Sound leaf2307Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2307CertificateValid
    leaf2307InnerLogValid leaf2307CoversExact leaf2307LowerChecked

private noncomputable def leaf2308Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (205/64), chiLo := (15/64), chiHi := (31/128) }

private noncomputable def leaf2308Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871383/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432445952) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (937893515/536870912) }, upper := { exponent := 0, mantissa := (14547/8192) } }, logOuter := sk197LogOuterCertificate, logK := sk197LogKCertificate, logChi := chi121LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869367807/274864891904) } }, logDArg := sk197LogDArgCertificate }

private noncomputable def leaf2308InnerLog : WideLogData :=
  innerPair431Data

set_option maxRecDepth 1000000 in
private theorem leaf2308LocalValidity :
    LeafFacts leaf2308Box leaf2308Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2308Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432445952) }) = true
      norm_num [leaf2308Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2308CertificateValid :
    WideCertificateValid leaf2308Box leaf2308Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk197ValidityFacts chi121ValidityFacts
    leaf2308LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2308CoverageChecked :
    coverageCheck (innerAD leaf2308Box) leaf2308InnerLog = true := by
  rfl'

private theorem leaf2308InnerLogValid :
    leaf2308InnerLog.Valid 8 (innerAD leaf2308Box) :=
  wideLogDataValid_of_cachedCheck endpoint139PositiveFacts
    endpoint68PositiveFacts.valid leaf2308CoverageChecked

private noncomputable def leaf2308InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814677/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2308InputLogOnePlusV_eq :
    leaf2308InputLogOnePlusV = outerEnclosure 24
      (leaf2308Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2308RoundedFacts : LeafRoundedFacts 8
    leaf2308Certificate.logOnePlusV leaf2308InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2308InputLogOnePlusV_eq }

private noncomputable def leaf2308Inputs : Inputs :=
  inputsOfCaches globalInput sk197RoundedInputs
    chi121InputQChi innerPair431Input
    leaf2308InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2308LowerChecked :
    lowerCheck 24 leaf2308Box leaf2308Inputs = true := by
  rfl'

private theorem leaf2308CoversExact : CoversExact 8
    leaf2308Box leaf2308Certificate leaf2308InnerLog leaf2308Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk197RoundedFacts chi121RoundedFacts
    innerPair431RoundedFacts leaf2308RoundedFacts (by rfl)

private theorem leaf2308FlatSound : Sound leaf2308Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2308CertificateValid
    leaf2308InnerLogValid leaf2308CoversExact leaf2308LowerChecked

private noncomputable def leaf2309Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (205/64), kHi := (103/32), chiLo := (15/64), chiHi := (31/128) }

private noncomputable def leaf2309Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871385/536870912) }, vSqrt := { lower := (65529/65536), upper := (1065402495/1065367552) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (939859473/536870912) }, upper := { exponent := 0, mantissa := (7289/4096) } }, logOuter := sk198LogOuterCertificate, logK := sk198LogKCertificate, logChi := chi121LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (2130770047/2130735104) } }, logDArg := sk198LogDArgCertificate }

private noncomputable def leaf2309InnerLog : WideLogData :=
  innerPair78Data

set_option maxRecDepth 1000000 in
private theorem leaf2309LocalValidity :
    LeafFacts leaf2309Box leaf2309Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2309Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (1065402495/1065367552) }) = true
      norm_num [leaf2309Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2309CertificateValid :
    WideCertificateValid leaf2309Box leaf2309Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk198ValidityFacts chi121ValidityFacts
    leaf2309LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2309CoverageChecked :
    coverageCheck (innerAD leaf2309Box) leaf2309InnerLog = true := by
  rfl'

private theorem leaf2309InnerLogValid :
    leaf2309InnerLog.Valid 8 (innerAD leaf2309Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint68PositiveFacts.valid leaf2309CoverageChecked

private noncomputable def leaf2309InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907339/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2309InputLogOnePlusV_eq :
    leaf2309InputLogOnePlusV = outerEnclosure 24
      (leaf2309Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2309RoundedFacts : LeafRoundedFacts 8
    leaf2309Certificate.logOnePlusV leaf2309InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2309InputLogOnePlusV_eq }

private noncomputable def leaf2309Inputs : Inputs :=
  inputsOfCaches globalInput sk198RoundedInputs
    chi121InputQChi innerPair78Input
    leaf2309InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2309LowerChecked :
    lowerCheck 24 leaf2309Box leaf2309Inputs = true := by
  rfl'

private theorem leaf2309CoversExact : CoversExact 8
    leaf2309Box leaf2309Certificate leaf2309InnerLog leaf2309Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk198RoundedFacts chi121RoundedFacts
    innerPair78RoundedFacts leaf2309RoundedFacts (by rfl)

private theorem leaf2309FlatSound : Sound leaf2309Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2309CertificateValid
    leaf2309InnerLogValid leaf2309CoversExact leaf2309LowerChecked

private noncomputable def leaf2310Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (15/64), chiHi := (61/256) }

private noncomputable def leaf2310Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871241/536870912) }, vSqrt := { lower := (65529/65536), upper := (22906164565/22905409536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (941825577/536870912) }, upper := { exponent := 0, mantissa := (1817/1024) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi191LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (45811574101/45810819072) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf2310InnerLog : WideLogData :=
  innerPair78Data

set_option maxRecDepth 1000000 in
private theorem leaf2310LocalValidity :
    LeafFacts leaf2310Box leaf2310Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2310Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22906164565/22905409536) }) = true
      norm_num [leaf2310Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2310CertificateValid :
    WideCertificateValid leaf2310Box leaf2310Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi191ValidityFacts
    leaf2310LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2310CoverageChecked :
    coverageCheck (innerAD leaf2310Box) leaf2310InnerLog = true := by
  rfl'

private theorem leaf2310InnerLogValid :
    leaf2310InnerLog.Valid 8 (innerAD leaf2310Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint68PositiveFacts.valid leaf2310CoverageChecked

private noncomputable def leaf2310InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629357/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2310InputLogOnePlusV_eq :
    leaf2310InputLogOnePlusV = outerEnclosure 24
      (leaf2310Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2310RoundedFacts : LeafRoundedFacts 8
    leaf2310Certificate.logOnePlusV leaf2310InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2310InputLogOnePlusV_eq }

private noncomputable def leaf2310Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi191InputQChi innerPair78Input
    leaf2310InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2310LowerChecked :
    lowerCheck 24 leaf2310Box leaf2310Inputs = true := by
  rfl'

private theorem leaf2310CoversExact : CoversExact 8
    leaf2310Box leaf2310Certificate leaf2310InnerLog leaf2310Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi191RoundedFacts
    innerPair78RoundedFacts leaf2310RoundedFacts (by rfl)

private theorem leaf2310FlatSound : Sound leaf2310Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2310CertificateValid
    leaf2310InnerLogValid leaf2310CoversExact leaf2310LowerChecked

private noncomputable def leaf2311Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (61/256), chiHi := (31/128) }

private noncomputable def leaf2311Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871243/536870912) }, vSqrt := { lower := (65529/65536), upper := (13743698739/13743235072) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (948575371/536870912) }, upper := { exponent := 0, mantissa := (915/512) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi192LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (27486933811/27486470144) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf2311InnerLog : WideLogData :=
  innerPair209Data

set_option maxRecDepth 1000000 in
private theorem leaf2311LocalValidity :
    LeafFacts leaf2311Box leaf2311Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2311Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (13743698739/13743235072) }) = true
      norm_num [leaf2311Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2311CertificateValid :
    WideCertificateValid leaf2311Box leaf2311Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi192ValidityFacts
    leaf2311LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2311CoverageChecked :
    coverageCheck (innerAD leaf2311Box) leaf2311InnerLog = true := by
  rfl'

private theorem leaf2311InnerLogValid :
    leaf2311InnerLog.Valid 8 (innerAD leaf2311Box) :=
  wideLogDataValid_of_cachedCheck endpoint63PositiveFacts
    endpoint67PositiveFacts.valid leaf2311CoverageChecked

private noncomputable def leaf2311InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907341/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2311InputLogOnePlusV_eq :
    leaf2311InputLogOnePlusV = outerEnclosure 24
      (leaf2311Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2311RoundedFacts : LeafRoundedFacts 8
    leaf2311Certificate.logOnePlusV leaf2311InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2311InputLogOnePlusV_eq }

private noncomputable def leaf2311Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi192InputQChi innerPair209Input
    leaf2311InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2311LowerChecked :
    lowerCheck 24 leaf2311Box leaf2311Inputs = true := by
  rfl'

private theorem leaf2311CoversExact : CoversExact 8
    leaf2311Box leaf2311Certificate leaf2311InnerLog leaf2311Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi192RoundedFacts
    innerPair209RoundedFacts leaf2311RoundedFacts (by rfl)

private theorem leaf2311FlatSound : Sound leaf2311Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2311CertificateValid
    leaf2311InnerLogValid leaf2311CoversExact leaf2311LowerChecked

private noncomputable def leaf2312Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (31/128), chiHi := (63/256) }

private noncomputable def leaf2312Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871243/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68716154368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (951262183/536870912) }, upper := { exponent := 0, mantissa := (14681/8192) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi189LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434648063/137432308736) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf2312InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf2312LocalValidity :
    LeafFacts leaf2312Box leaf2312Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2312Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68716154368) }) = true
      norm_num [leaf2312Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2312CertificateValid :
    WideCertificateValid leaf2312Box leaf2312Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi189ValidityFacts
    leaf2312LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2312CoverageChecked :
    coverageCheck (innerAD leaf2312Box) leaf2312InnerLog = true := by
  rfl'

private theorem leaf2312InnerLogValid :
    leaf2312InnerLog.Valid 8 (innerAD leaf2312Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf2312CoverageChecked

private noncomputable def leaf2312InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814683/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2312InputLogOnePlusV_eq :
    leaf2312InputLogOnePlusV = outerEnclosure 24
      (leaf2312Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2312RoundedFacts : LeafRoundedFacts 8
    leaf2312Certificate.logOnePlusV leaf2312InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2312InputLogOnePlusV_eq }

private noncomputable def leaf2312Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi189InputQChi innerPair71Input
    leaf2312InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2312LowerChecked :
    lowerCheck 24 leaf2312Box leaf2312Inputs = true := by
  rfl'

private theorem leaf2312CoversExact : CoversExact 8
    leaf2312Box leaf2312Certificate leaf2312InnerLog leaf2312Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi189RoundedFacts
    innerPair71RoundedFacts leaf2312RoundedFacts (by rfl)

private theorem leaf2312FlatSound : Sound leaf2312Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2312CertificateValid
    leaf2312InnerLogValid leaf2312CoversExact leaf2312LowerChecked

private noncomputable def leaf2313Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (63/256), chiHi := (1/4) }

private noncomputable def leaf2313Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871245/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68716101632) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (957946445/536870912) }, upper := { exponent := 0, mantissa := (231/128) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi190LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434595327/137432203264) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf2313InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf2313LocalValidity :
    LeafFacts leaf2313Box leaf2313Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2313Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68716101632) }) = true
      norm_num [leaf2313Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2313CertificateValid :
    WideCertificateValid leaf2313Box leaf2313Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi190ValidityFacts
    leaf2313LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2313CoverageChecked :
    coverageCheck (innerAD leaf2313Box) leaf2313InnerLog = true := by
  rfl'

private theorem leaf2313InnerLogValid :
    leaf2313InnerLog.Valid 8 (innerAD leaf2313Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf2313CoverageChecked

private noncomputable def leaf2313InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629373/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2313InputLogOnePlusV_eq :
    leaf2313InputLogOnePlusV = outerEnclosure 24
      (leaf2313Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2313RoundedFacts : LeafRoundedFacts 8
    leaf2313Certificate.logOnePlusV leaf2313InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2313InputLogOnePlusV_eq }

private noncomputable def leaf2313Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi190InputQChi innerPair71Input
    leaf2313InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2313LowerChecked :
    lowerCheck 24 leaf2313Box leaf2313Inputs = true := by
  rfl'

private theorem leaf2313CoversExact : CoversExact 8
    leaf2313Box leaf2313Certificate leaf2313InnerLog leaf2313Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi190RoundedFacts
    innerPair71RoundedFacts leaf2313RoundedFacts (by rfl)

private theorem leaf2313FlatSound : Sound leaf2313Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2313CertificateValid
    leaf2313InnerLogValid leaf2313CoversExact leaf2313LowerChecked

private noncomputable def leaf2314Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (31/128), chiHi := (63/256) }

private noncomputable def leaf2314Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871245/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68716122112) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (955325165/536870912) }, upper := { exponent := 0, mantissa := (1843/1024) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi189LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434615807/137432244224) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf2314InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf2314LocalValidity :
    LeafFacts leaf2314Box leaf2314Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2314Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68716122112) }) = true
      norm_num [leaf2314Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2314CertificateValid :
    WideCertificateValid leaf2314Box leaf2314Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi189ValidityFacts
    leaf2314LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2314CoverageChecked :
    coverageCheck (innerAD leaf2314Box) leaf2314InnerLog = true := by
  rfl'

private theorem leaf2314InnerLogValid :
    leaf2314InnerLog.Valid 8 (innerAD leaf2314Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf2314CoverageChecked

private noncomputable def leaf2314InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814685/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2314InputLogOnePlusV_eq :
    leaf2314InputLogOnePlusV = outerEnclosure 24
      (leaf2314Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2314RoundedFacts : LeafRoundedFacts 8
    leaf2314Certificate.logOnePlusV leaf2314InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2314InputLogOnePlusV_eq }

private noncomputable def leaf2314Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi189InputQChi innerPair71Input
    leaf2314InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2314LowerChecked :
    lowerCheck 24 leaf2314Box leaf2314Inputs = true := by
  rfl'

private theorem leaf2314CoversExact : CoversExact 8
    leaf2314Box leaf2314Certificate leaf2314InnerLog leaf2314Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi189RoundedFacts
    innerPair71RoundedFacts leaf2314RoundedFacts (by rfl)

private theorem leaf2314FlatSound : Sound leaf2314Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2314CertificateValid
    leaf2314InnerLogValid leaf2314CoversExact leaf2314LowerChecked

private noncomputable def leaf2315Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (63/256), chiHi := (1/4) }

private noncomputable def leaf2315Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871247/536870912) }, vSqrt := { lower := (65529/65536), upper := (22906164565/22905356288) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (962074959/536870912) }, upper := { exponent := 0, mantissa := (29/16) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi190LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (45811520853/45810712576) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf2315InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf2315LocalValidity :
    LeafFacts leaf2315Box leaf2315Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2315Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22906164565/22905356288) }) = true
      norm_num [leaf2315Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2315CertificateValid :
    WideCertificateValid leaf2315Box leaf2315Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi190ValidityFacts
    leaf2315LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2315CoverageChecked :
    coverageCheck (innerAD leaf2315Box) leaf2315InnerLog = true := by
  rfl'

private theorem leaf2315InnerLogValid :
    leaf2315InnerLog.Valid 8 (innerAD leaf2315Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf2315CoverageChecked

private noncomputable def leaf2315InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629377/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2315InputLogOnePlusV_eq :
    leaf2315InputLogOnePlusV = outerEnclosure 24
      (leaf2315Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2315RoundedFacts : LeafRoundedFacts 8
    leaf2315Certificate.logOnePlusV leaf2315InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2315InputLogOnePlusV_eq }

private noncomputable def leaf2315Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi190InputQChi innerPair71Input
    leaf2315InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2315LowerChecked :
    lowerCheck 24 leaf2315Box leaf2315Inputs = true := by
  rfl'

private theorem leaf2315CoversExact : CoversExact 8
    leaf2315Box leaf2315Certificate leaf2315InnerLog leaf2315Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi190RoundedFacts
    innerPair71RoundedFacts leaf2315RoundedFacts (by rfl)

private theorem leaf2315FlatSound : Sound leaf2315Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2315CertificateValid
    leaf2315InnerLogValid leaf2315CoversExact leaf2315LowerChecked

private noncomputable def component49Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (7/32), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component49Node0_sound : Sound component49Node0Box :=
  sound_of_literal_split component49Node0Box leaf2252Box leaf2253Box
    .k (193/64) (by rfl) (by rfl)
    leaf2252FlatSound leaf2253FlatSound

private noncomputable def component49Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (29/128), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component49Node1_sound : Sound component49Node1Box :=
  sound_of_literal_split component49Node1Box leaf2254Box leaf2255Box
    .k (193/64) (by rfl) (by rfl)
    leaf2254FlatSound leaf2255FlatSound

private noncomputable def component49Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component49Node2_sound : Sound component49Node2Box :=
  sound_of_literal_split component49Node2Box component49Node0Box component49Node1Box
    .chi (29/128) (by rfl) (by rfl)
    component49Node0_sound component49Node1_sound

private noncomputable def component49Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (7/32), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component49Node3_sound : Sound component49Node3Box :=
  sound_of_literal_split component49Node3Box leaf2256Box leaf2257Box
    .k (195/64) (by rfl) (by rfl)
    leaf2256FlatSound leaf2257FlatSound

private noncomputable def component49Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (29/128), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component49Node4_sound : Sound component49Node4Box :=
  sound_of_literal_split component49Node4Box leaf2258Box leaf2259Box
    .k (195/64) (by rfl) (by rfl)
    leaf2258FlatSound leaf2259FlatSound

private noncomputable def component49Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component49Node5_sound : Sound component49Node5Box :=
  sound_of_literal_split component49Node5Box component49Node3Box component49Node4Box
    .chi (29/128) (by rfl) (by rfl)
    component49Node3_sound component49Node4_sound

private noncomputable def component49Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component49Node6_sound : Sound component49Node6Box :=
  sound_of_literal_split component49Node6Box component49Node2Box component49Node5Box
    .k (97/32) (by rfl) (by rfl)
    component49Node2_sound component49Node5_sound

private noncomputable def component49Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (7/32), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component49Node7_sound : Sound component49Node7Box :=
  sound_of_literal_split component49Node7Box leaf2260Box leaf2261Box
    .k (197/64) (by rfl) (by rfl)
    leaf2260FlatSound leaf2261FlatSound

private noncomputable def component49Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (29/128), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component49Node8_sound : Sound component49Node8Box :=
  sound_of_literal_split component49Node8Box leaf2262Box leaf2263Box
    .k (197/64) (by rfl) (by rfl)
    leaf2262FlatSound leaf2263FlatSound

private noncomputable def component49Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component49Node9_sound : Sound component49Node9Box :=
  sound_of_literal_split component49Node9Box component49Node7Box component49Node8Box
    .chi (29/128) (by rfl) (by rfl)
    component49Node7_sound component49Node8_sound

private noncomputable def component49Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (7/32), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component49Node10_sound : Sound component49Node10Box :=
  sound_of_literal_split component49Node10Box leaf2264Box leaf2265Box
    .k (199/64) (by rfl) (by rfl)
    leaf2264FlatSound leaf2265FlatSound

private noncomputable def component49Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (29/128), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component49Node11_sound : Sound component49Node11Box :=
  sound_of_literal_split component49Node11Box leaf2266Box leaf2267Box
    .k (199/64) (by rfl) (by rfl)
    leaf2266FlatSound leaf2267FlatSound

private noncomputable def component49Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component49Node12_sound : Sound component49Node12Box :=
  sound_of_literal_split component49Node12Box component49Node10Box component49Node11Box
    .chi (29/128) (by rfl) (by rfl)
    component49Node10_sound component49Node11_sound

private noncomputable def component49Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component49Node13_sound : Sound component49Node13Box :=
  sound_of_literal_split component49Node13Box component49Node9Box component49Node12Box
    .k (99/32) (by rfl) (by rfl)
    component49Node9_sound component49Node12_sound

private noncomputable def component49Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component49Node14_sound : Sound component49Node14Box :=
  sound_of_literal_split component49Node14Box component49Node6Box component49Node13Box
    .k (49/16) (by rfl) (by rfl)
    component49Node6_sound component49Node13_sound

private noncomputable def component49Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (15/64), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component49Node15_sound : Sound component49Node15Box :=
  sound_of_literal_split component49Node15Box leaf2268Box leaf2269Box
    .k (193/64) (by rfl) (by rfl)
    leaf2268FlatSound leaf2269FlatSound

private noncomputable def component49Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (31/128), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component49Node16_sound : Sound component49Node16Box :=
  sound_of_literal_split component49Node16Box leaf2270Box leaf2271Box
    .k (193/64) (by rfl) (by rfl)
    leaf2270FlatSound leaf2271FlatSound

private noncomputable def component49Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component49Node17_sound : Sound component49Node17Box :=
  sound_of_literal_split component49Node17Box component49Node15Box component49Node16Box
    .chi (31/128) (by rfl) (by rfl)
    component49Node15_sound component49Node16_sound

private noncomputable def component49Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (15/64), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component49Node18_sound : Sound component49Node18Box :=
  sound_of_literal_split component49Node18Box leaf2272Box leaf2273Box
    .k (195/64) (by rfl) (by rfl)
    leaf2272FlatSound leaf2273FlatSound

private noncomputable def component49Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (31/128), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component49Node19_sound : Sound component49Node19Box :=
  sound_of_literal_split component49Node19Box leaf2274Box leaf2275Box
    .k (195/64) (by rfl) (by rfl)
    leaf2274FlatSound leaf2275FlatSound

private noncomputable def component49Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component49Node20_sound : Sound component49Node20Box :=
  sound_of_literal_split component49Node20Box component49Node18Box component49Node19Box
    .chi (31/128) (by rfl) (by rfl)
    component49Node18_sound component49Node19_sound

private noncomputable def component49Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component49Node21_sound : Sound component49Node21Box :=
  sound_of_literal_split component49Node21Box component49Node17Box component49Node20Box
    .k (97/32) (by rfl) (by rfl)
    component49Node17_sound component49Node20_sound

private noncomputable def component49Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (15/64), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component49Node22_sound : Sound component49Node22Box :=
  sound_of_literal_split component49Node22Box leaf2276Box leaf2277Box
    .k (197/64) (by rfl) (by rfl)
    leaf2276FlatSound leaf2277FlatSound

private noncomputable def component49Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (15/64), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component49Node23_sound : Sound component49Node23Box :=
  sound_of_literal_split component49Node23Box leaf2278Box leaf2279Box
    .k (199/64) (by rfl) (by rfl)
    leaf2278FlatSound leaf2279FlatSound

private noncomputable def component49Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (15/64), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component49Node24_sound : Sound component49Node24Box :=
  sound_of_literal_split component49Node24Box component49Node22Box component49Node23Box
    .k (99/32) (by rfl) (by rfl)
    component49Node22_sound component49Node23_sound

private noncomputable def component49Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (31/128), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component49Node25_sound : Sound component49Node25Box :=
  sound_of_literal_split component49Node25Box leaf2280Box leaf2281Box
    .k (197/64) (by rfl) (by rfl)
    leaf2280FlatSound leaf2281FlatSound

private noncomputable def component49Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (31/128), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component49Node26_sound : Sound component49Node26Box :=
  sound_of_literal_split component49Node26Box leaf2282Box leaf2283Box
    .k (199/64) (by rfl) (by rfl)
    leaf2282FlatSound leaf2283FlatSound

private noncomputable def component49Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (31/128), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component49Node27_sound : Sound component49Node27Box :=
  sound_of_literal_split component49Node27Box component49Node25Box component49Node26Box
    .k (99/32) (by rfl) (by rfl)
    component49Node25_sound component49Node26_sound

private noncomputable def component49Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component49Node28_sound : Sound component49Node28Box :=
  sound_of_literal_split component49Node28Box component49Node24Box component49Node27Box
    .chi (31/128) (by rfl) (by rfl)
    component49Node24_sound component49Node27_sound

private noncomputable def component49Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component49Node29_sound : Sound component49Node29Box :=
  sound_of_literal_split component49Node29Box component49Node21Box component49Node28Box
    .k (49/16) (by rfl) (by rfl)
    component49Node21_sound component49Node28_sound

private noncomputable def component49Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (7/32), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component49Node30_sound : Sound component49Node30Box :=
  sound_of_literal_split component49Node30Box component49Node14Box component49Node29Box
    .chi (15/64) (by rfl) (by rfl)
    component49Node14_sound component49Node29_sound

private noncomputable def component49Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (7/32), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component49Node31_sound : Sound component49Node31Box :=
  sound_of_literal_split component49Node31Box leaf2284Box leaf2285Box
    .k (201/64) (by rfl) (by rfl)
    leaf2284FlatSound leaf2285FlatSound

private noncomputable def component49Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (7/32), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component49Node32_sound : Sound component49Node32Box :=
  sound_of_literal_split component49Node32Box leaf2286Box leaf2287Box
    .k (203/64) (by rfl) (by rfl)
    leaf2286FlatSound leaf2287FlatSound

private noncomputable def component49Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (7/32), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component49Node33_sound : Sound component49Node33Box :=
  sound_of_literal_split component49Node33Box component49Node31Box component49Node32Box
    .k (101/32) (by rfl) (by rfl)
    component49Node31_sound component49Node32_sound

private noncomputable def component49Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (29/128), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component49Node34_sound : Sound component49Node34Box :=
  sound_of_literal_split component49Node34Box leaf2288Box leaf2289Box
    .k (201/64) (by rfl) (by rfl)
    leaf2288FlatSound leaf2289FlatSound

private noncomputable def component49Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (29/128), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component49Node35_sound : Sound component49Node35Box :=
  sound_of_literal_split component49Node35Box leaf2290Box leaf2291Box
    .k (203/64) (by rfl) (by rfl)
    leaf2290FlatSound leaf2291FlatSound

private noncomputable def component49Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (29/128), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component49Node36_sound : Sound component49Node36Box :=
  sound_of_literal_split component49Node36Box component49Node34Box component49Node35Box
    .k (101/32) (by rfl) (by rfl)
    component49Node34_sound component49Node35_sound

private noncomputable def component49Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component49Node37_sound : Sound component49Node37Box :=
  sound_of_literal_split component49Node37Box component49Node33Box component49Node36Box
    .chi (29/128) (by rfl) (by rfl)
    component49Node33_sound component49Node36_sound

private noncomputable def component49Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (7/32), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component49Node38_sound : Sound component49Node38Box :=
  sound_of_literal_split component49Node38Box leaf2292Box leaf2293Box
    .k (205/64) (by rfl) (by rfl)
    leaf2292FlatSound leaf2293FlatSound

private noncomputable def component49Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (7/32), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component49Node39_sound : Sound component49Node39Box :=
  sound_of_literal_split component49Node39Box leaf2294Box leaf2295Box
    .k (207/64) (by rfl) (by rfl)
    leaf2294FlatSound leaf2295FlatSound

private noncomputable def component49Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (7/32), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component49Node40_sound : Sound component49Node40Box :=
  sound_of_literal_split component49Node40Box component49Node38Box component49Node39Box
    .k (103/32) (by rfl) (by rfl)
    component49Node38_sound component49Node39_sound

private noncomputable def component49Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (29/128), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component49Node41_sound : Sound component49Node41Box :=
  sound_of_literal_split component49Node41Box leaf2296Box leaf2297Box
    .k (205/64) (by rfl) (by rfl)
    leaf2296FlatSound leaf2297FlatSound

private noncomputable def component49Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (29/128), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component49Node42_sound : Sound component49Node42Box :=
  sound_of_literal_split component49Node42Box leaf2298Box leaf2299Box
    .k (207/64) (by rfl) (by rfl)
    leaf2298FlatSound leaf2299FlatSound

private noncomputable def component49Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (29/128), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component49Node43_sound : Sound component49Node43Box :=
  sound_of_literal_split component49Node43Box component49Node41Box component49Node42Box
    .k (103/32) (by rfl) (by rfl)
    component49Node41_sound component49Node42_sound

private noncomputable def component49Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component49Node44_sound : Sound component49Node44Box :=
  sound_of_literal_split component49Node44Box component49Node40Box component49Node43Box
    .chi (29/128) (by rfl) (by rfl)
    component49Node40_sound component49Node43_sound

private noncomputable def component49Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component49Node45_sound : Sound component49Node45Box :=
  sound_of_literal_split component49Node45Box component49Node37Box component49Node44Box
    .k (51/16) (by rfl) (by rfl)
    component49Node37_sound component49Node44_sound

private noncomputable def component49Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (15/64), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component49Node46_sound : Sound component49Node46Box :=
  sound_of_literal_split component49Node46Box leaf2300Box leaf2301Box
    .k (201/64) (by rfl) (by rfl)
    leaf2300FlatSound leaf2301FlatSound

private noncomputable def component49Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (15/64), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component49Node47_sound : Sound component49Node47Box :=
  sound_of_literal_split component49Node47Box leaf2302Box leaf2303Box
    .k (203/64) (by rfl) (by rfl)
    leaf2302FlatSound leaf2303FlatSound

private noncomputable def component49Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (15/64), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component49Node48_sound : Sound component49Node48Box :=
  sound_of_literal_split component49Node48Box component49Node46Box component49Node47Box
    .k (101/32) (by rfl) (by rfl)
    component49Node46_sound component49Node47_sound

private noncomputable def component49Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (31/128), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component49Node49_sound : Sound component49Node49Box :=
  sound_of_literal_split component49Node49Box leaf2304Box leaf2305Box
    .k (201/64) (by rfl) (by rfl)
    leaf2304FlatSound leaf2305FlatSound

private noncomputable def component49Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (31/128), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component49Node50_sound : Sound component49Node50Box :=
  sound_of_literal_split component49Node50Box leaf2306Box leaf2307Box
    .chi (63/256) (by rfl) (by rfl)
    leaf2306FlatSound leaf2307FlatSound

private noncomputable def component49Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (31/128), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component49Node51_sound : Sound component49Node51Box :=
  sound_of_literal_split component49Node51Box component49Node49Box component49Node50Box
    .k (101/32) (by rfl) (by rfl)
    component49Node49_sound component49Node50_sound

private noncomputable def component49Node52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component49Node52_sound : Sound component49Node52Box :=
  sound_of_literal_split component49Node52Box component49Node48Box component49Node51Box
    .chi (31/128) (by rfl) (by rfl)
    component49Node48_sound component49Node51_sound

private noncomputable def component49Node53Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (15/64), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component49Node53_sound : Sound component49Node53Box :=
  sound_of_literal_split component49Node53Box leaf2308Box leaf2309Box
    .k (205/64) (by rfl) (by rfl)
    leaf2308FlatSound leaf2309FlatSound

private noncomputable def component49Node54Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (15/64), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component49Node54_sound : Sound component49Node54Box :=
  sound_of_literal_split component49Node54Box leaf2310Box leaf2311Box
    .chi (61/256) (by rfl) (by rfl)
    leaf2310FlatSound leaf2311FlatSound

private noncomputable def component49Node55Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (15/64), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component49Node55_sound : Sound component49Node55Box :=
  sound_of_literal_split component49Node55Box component49Node53Box component49Node54Box
    .k (103/32) (by rfl) (by rfl)
    component49Node53_sound component49Node54_sound

private noncomputable def component49Node56Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (31/128), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component49Node56_sound : Sound component49Node56Box :=
  sound_of_literal_split component49Node56Box leaf2312Box leaf2313Box
    .chi (63/256) (by rfl) (by rfl)
    leaf2312FlatSound leaf2313FlatSound

private noncomputable def component49Node57Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (31/128), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component49Node57_sound : Sound component49Node57Box :=
  sound_of_literal_split component49Node57Box leaf2314Box leaf2315Box
    .chi (63/256) (by rfl) (by rfl)
    leaf2314FlatSound leaf2315FlatSound

private noncomputable def component49Node58Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (31/128), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component49Node58_sound : Sound component49Node58Box :=
  sound_of_literal_split component49Node58Box component49Node56Box component49Node57Box
    .k (103/32) (by rfl) (by rfl)
    component49Node56_sound component49Node57_sound

private noncomputable def component49Node59Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component49Node59_sound : Sound component49Node59Box :=
  sound_of_literal_split component49Node59Box component49Node55Box component49Node58Box
    .chi (31/128) (by rfl) (by rfl)
    component49Node55_sound component49Node58_sound

private noncomputable def component49Node60Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component49Node60_sound : Sound component49Node60Box :=
  sound_of_literal_split component49Node60Box component49Node52Box component49Node59Box
    .k (51/16) (by rfl) (by rfl)
    component49Node52_sound component49Node59_sound

private noncomputable def component49Node61Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (7/32), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component49Node61_sound : Sound component49Node61Box :=
  sound_of_literal_split component49Node61Box component49Node45Box component49Node60Box
    .chi (15/64) (by rfl) (by rfl)
    component49Node45_sound component49Node60_sound

noncomputable def component49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (13/4), chiLo := (7/32), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
theorem component49_sound : Sound component49Box :=
  sound_of_literal_split component49Box component49Node30Box component49Node61Box
    .k (25/8) (by rfl) (by rfl)
    component49Node30_sound component49Node61_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
