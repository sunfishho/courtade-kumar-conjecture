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

private noncomputable def leaf2188Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (193/64), chiLo := (3/16), chiHi := (25/128) }

private noncomputable def leaf2188Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871347/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137434012672) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (838809167/536870912) }, upper := { exponent := 0, mantissa := (13017/8192) } }, logOuter := sk185LogOuterCertificate, logK := sk185LogKCertificate, logChi := chi115LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870934527/274868025344) } }, logDArg := sk185LogDArgCertificate }

private noncomputable def leaf2188InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf2188LocalValidity :
    LeafFacts leaf2188Box leaf2188Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2188Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137434012672) }) = true
      norm_num [leaf2188Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2188CertificateValid :
    WideCertificateValid leaf2188Box leaf2188Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk185ValidityFacts chi115ValidityFacts
    leaf2188LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2188CoverageChecked :
    coverageCheck (innerAD leaf2188Box) leaf2188InnerLog = true := by
  rfl'

private theorem leaf2188InnerLogValid :
    leaf2188InnerLog.Valid 8 (innerAD leaf2188Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf2188CoverageChecked

private noncomputable def leaf2188InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814629/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2188InputLogOnePlusV_eq :
    leaf2188InputLogOnePlusV = outerEnclosure 24
      (leaf2188Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2188RoundedFacts : LeafRoundedFacts 8
    leaf2188Certificate.logOnePlusV leaf2188InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2188InputLogOnePlusV_eq }

private noncomputable def leaf2188Inputs : Inputs :=
  inputsOfCaches globalInput sk185RoundedInputs
    chi115InputQChi innerPair41Input
    leaf2188InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2188LowerChecked :
    lowerCheck 24 leaf2188Box leaf2188Inputs = true := by
  rfl'

private theorem leaf2188CoversExact : CoversExact 8
    leaf2188Box leaf2188Certificate leaf2188InnerLog leaf2188Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk185RoundedFacts chi115RoundedFacts
    innerPair41RoundedFacts leaf2188RoundedFacts (by rfl)

private theorem leaf2188FlatSound : Sound leaf2188Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2188CertificateValid
    leaf2188InnerLogValid leaf2188CoversExact leaf2188LowerChecked

private noncomputable def leaf2189Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (193/64), kHi := (97/32), chiLo := (3/16), chiHi := (25/128) }

private noncomputable def leaf2189Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871349/536870912) }, vSqrt := { lower := (65529/65536), upper := (15270769095/15270443008) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (840381933/536870912) }, upper := { exponent := 0, mantissa := (6521/4096) } }, logOuter := sk186LogOuterCertificate, logK := sk186LogKCertificate, logChi := chi115LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (30541212103/30540886016) } }, logDArg := sk186LogDArgCertificate }

private noncomputable def leaf2189InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2189LocalValidity :
    LeafFacts leaf2189Box leaf2189Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2189Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (15270769095/15270443008) }) = true
      norm_num [leaf2189Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2189CertificateValid :
    WideCertificateValid leaf2189Box leaf2189Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk186ValidityFacts chi115ValidityFacts
    leaf2189LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2189CoverageChecked :
    coverageCheck (innerAD leaf2189Box) leaf2189InnerLog = true := by
  rfl'

private theorem leaf2189InnerLogValid :
    leaf2189InnerLog.Valid 8 (innerAD leaf2189Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2189CoverageChecked

private noncomputable def leaf2189InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907315/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2189InputLogOnePlusV_eq :
    leaf2189InputLogOnePlusV = outerEnclosure 24
      (leaf2189Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2189RoundedFacts : LeafRoundedFacts 8
    leaf2189Certificate.logOnePlusV leaf2189InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2189InputLogOnePlusV_eq }

private noncomputable def leaf2189Inputs : Inputs :=
  inputsOfCaches globalInput sk186RoundedInputs
    chi115InputQChi innerPair50Input
    leaf2189InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2189LowerChecked :
    lowerCheck 24 leaf2189Box leaf2189Inputs = true := by
  rfl'

private theorem leaf2189CoversExact : CoversExact 8
    leaf2189Box leaf2189Certificate leaf2189InnerLog leaf2189Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk186RoundedFacts chi115RoundedFacts
    innerPair50RoundedFacts leaf2189RoundedFacts (by rfl)

private theorem leaf2189FlatSound : Sound leaf2189Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2189CertificateValid
    leaf2189InnerLogValid leaf2189CoversExact leaf2189LowerChecked

private noncomputable def leaf2190Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (195/64), chiLo := (3/16), chiHi := (25/128) }

private noncomputable def leaf2190Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871351/536870912) }, vSqrt := { lower := (65529/65536), upper := (534774015/534762496) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (841954699/536870912) }, upper := { exponent := 0, mantissa := (13067/8192) } }, logOuter := sk187LogOuterCertificate, logK := sk187LogKCertificate, logChi := chi115LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (1069536511/1069524992) } }, logDArg := sk187LogDArgCertificate }

private noncomputable def leaf2190InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2190LocalValidity :
    LeafFacts leaf2190Box leaf2190Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2190Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (534774015/534762496) }) = true
      norm_num [leaf2190Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2190CertificateValid :
    WideCertificateValid leaf2190Box leaf2190Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk187ValidityFacts chi115ValidityFacts
    leaf2190LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2190CoverageChecked :
    coverageCheck (innerAD leaf2190Box) leaf2190InnerLog = true := by
  rfl'

private theorem leaf2190InnerLogValid :
    leaf2190InnerLog.Valid 8 (innerAD leaf2190Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2190CoverageChecked

private noncomputable def leaf2190InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629261/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2190InputLogOnePlusV_eq :
    leaf2190InputLogOnePlusV = outerEnclosure 24
      (leaf2190Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2190RoundedFacts : LeafRoundedFacts 8
    leaf2190Certificate.logOnePlusV leaf2190InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2190InputLogOnePlusV_eq }

private noncomputable def leaf2190Inputs : Inputs :=
  inputsOfCaches globalInput sk187RoundedInputs
    chi115InputQChi innerPair50Input
    leaf2190InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2190LowerChecked :
    lowerCheck 24 leaf2190Box leaf2190Inputs = true := by
  rfl'

private theorem leaf2190CoversExact : CoversExact 8
    leaf2190Box leaf2190Certificate leaf2190InnerLog leaf2190Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk187RoundedFacts chi115RoundedFacts
    innerPair50RoundedFacts leaf2190RoundedFacts (by rfl)

private theorem leaf2190FlatSound : Sound leaf2190Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2190CertificateValid
    leaf2190InnerLogValid leaf2190CoversExact leaf2190LowerChecked

private noncomputable def leaf2191Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (195/64), kHi := (49/16), chiLo := (3/16), chiHi := (25/128) }

private noncomputable def leaf2191Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871353/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433935872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (843527465/536870912) }, upper := { exponent := 0, mantissa := (3273/2048) } }, logOuter := sk188LogOuterCertificate, logK := sk188LogKCertificate, logChi := chi115LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870857727/274867871744) } }, logDArg := sk188LogDArgCertificate }

private noncomputable def leaf2191InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2191LocalValidity :
    LeafFacts leaf2191Box leaf2191Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2191Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433935872) }) = true
      norm_num [leaf2191Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2191CertificateValid :
    WideCertificateValid leaf2191Box leaf2191Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk188ValidityFacts chi115ValidityFacts
    leaf2191LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2191CoverageChecked :
    coverageCheck (innerAD leaf2191Box) leaf2191InnerLog = true := by
  rfl'

private theorem leaf2191InnerLogValid :
    leaf2191InnerLog.Valid 8 (innerAD leaf2191Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2191CoverageChecked

private noncomputable def leaf2191InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629263/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2191InputLogOnePlusV_eq :
    leaf2191InputLogOnePlusV = outerEnclosure 24
      (leaf2191Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2191RoundedFacts : LeafRoundedFacts 8
    leaf2191Certificate.logOnePlusV leaf2191InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2191InputLogOnePlusV_eq }

private noncomputable def leaf2191Inputs : Inputs :=
  inputsOfCaches globalInput sk188RoundedInputs
    chi115InputQChi innerPair50Input
    leaf2191InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2191LowerChecked :
    lowerCheck 24 leaf2191Box leaf2191Inputs = true := by
  rfl'

private theorem leaf2191CoversExact : CoversExact 8
    leaf2191Box leaf2191Certificate leaf2191InnerLog leaf2191Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk188RoundedFacts chi115RoundedFacts
    innerPair50RoundedFacts leaf2191RoundedFacts (by rfl)

private theorem leaf2191FlatSound : Sound leaf2191Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2191CertificateValid
    leaf2191InnerLogValid leaf2191CoversExact leaf2191LowerChecked

private noncomputable def leaf2192Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (193/64), chiLo := (25/128), chiHi := (13/64) }

private noncomputable def leaf2192Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871349/536870912) }, vSqrt := { lower := (65529/65536), upper := (9162461457/9162254336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (851391309/536870912) }, upper := { exponent := 0, mantissa := (6605/4096) } }, logOuter := sk185LogOuterCertificate, logK := sk185LogKCertificate, logChi := chi116LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (18324715793/18324508672) } }, logDArg := sk185LogDArgCertificate }

private noncomputable def leaf2192InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2192LocalValidity :
    LeafFacts leaf2192Box leaf2192Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2192Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (9162461457/9162254336) }) = true
      norm_num [leaf2192Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2192CertificateValid :
    WideCertificateValid leaf2192Box leaf2192Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk185ValidityFacts chi116ValidityFacts
    leaf2192LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2192CoverageChecked :
    coverageCheck (innerAD leaf2192Box) leaf2192InnerLog = true := by
  rfl'

private theorem leaf2192InnerLogValid :
    leaf2192InnerLog.Valid 8 (innerAD leaf2192Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2192CoverageChecked

private noncomputable def leaf2192InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814635/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2192InputLogOnePlusV_eq :
    leaf2192InputLogOnePlusV = outerEnclosure 24
      (leaf2192Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2192RoundedFacts : LeafRoundedFacts 8
    leaf2192Certificate.logOnePlusV leaf2192InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2192InputLogOnePlusV_eq }

private noncomputable def leaf2192Inputs : Inputs :=
  inputsOfCaches globalInput sk185RoundedInputs
    chi116InputQChi innerPair50Input
    leaf2192InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2192LowerChecked :
    lowerCheck 24 leaf2192Box leaf2192Inputs = true := by
  rfl'

private theorem leaf2192CoversExact : CoversExact 8
    leaf2192Box leaf2192Certificate leaf2192InnerLog leaf2192Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk185RoundedFacts chi116RoundedFacts
    innerPair50RoundedFacts leaf2192RoundedFacts (by rfl)

private theorem leaf2192FlatSound : Sound leaf2192Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2192CertificateValid
    leaf2192InnerLogValid leaf2192CoversExact leaf2192LowerChecked

private noncomputable def leaf2193Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (193/64), kHi := (97/32), chiLo := (25/128), chiHi := (13/64) }

private noncomputable def leaf2193Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871351/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433788416) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (853029607/536870912) }, upper := { exponent := 0, mantissa := (3309/2048) } }, logOuter := sk186LogOuterCertificate, logK := sk186LogKCertificate, logChi := chi116LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870710271/274867576832) } }, logDArg := sk186LogDArgCertificate }

private noncomputable def leaf2193InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2193LocalValidity :
    LeafFacts leaf2193Box leaf2193Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2193Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433788416) }) = true
      norm_num [leaf2193Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2193CertificateValid :
    WideCertificateValid leaf2193Box leaf2193Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk186ValidityFacts chi116ValidityFacts
    leaf2193LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2193CoverageChecked :
    coverageCheck (innerAD leaf2193Box) leaf2193InnerLog = true := by
  rfl'

private theorem leaf2193InnerLogValid :
    leaf2193InnerLog.Valid 8 (innerAD leaf2193Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2193CoverageChecked

private noncomputable def leaf2193InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453659/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf2193InputLogOnePlusV_eq :
    leaf2193InputLogOnePlusV = outerEnclosure 24
      (leaf2193Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2193RoundedFacts : LeafRoundedFacts 8
    leaf2193Certificate.logOnePlusV leaf2193InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2193InputLogOnePlusV_eq }

private noncomputable def leaf2193Inputs : Inputs :=
  inputsOfCaches globalInput sk186RoundedInputs
    chi116InputQChi innerPair50Input
    leaf2193InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2193LowerChecked :
    lowerCheck 24 leaf2193Box leaf2193Inputs = true := by
  rfl'

private theorem leaf2193CoversExact : CoversExact 8
    leaf2193Box leaf2193Certificate leaf2193InnerLog leaf2193Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk186RoundedFacts chi116RoundedFacts
    innerPair50RoundedFacts leaf2193RoundedFacts (by rfl)

private theorem leaf2193FlatSound : Sound leaf2193Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2193CertificateValid
    leaf2193InnerLogValid leaf2193CoversExact leaf2193LowerChecked

private noncomputable def leaf2194Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (195/64), chiLo := (25/128), chiHi := (13/64) }

private noncomputable def leaf2194Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871353/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433761792) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (854667905/536870912) }, upper := { exponent := 0, mantissa := (6631/4096) } }, logOuter := sk187LogOuterCertificate, logK := sk187LogKCertificate, logChi := chi116LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870683647/274867523584) } }, logDArg := sk187LogDArgCertificate }

private noncomputable def leaf2194InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2194LocalValidity :
    LeafFacts leaf2194Box leaf2194Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2194Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433761792) }) = true
      norm_num [leaf2194Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2194CertificateValid :
    WideCertificateValid leaf2194Box leaf2194Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk187ValidityFacts chi116ValidityFacts
    leaf2194LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2194CoverageChecked :
    coverageCheck (innerAD leaf2194Box) leaf2194InnerLog = true := by
  rfl'

private theorem leaf2194InnerLogValid :
    leaf2194InnerLog.Valid 8 (innerAD leaf2194Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2194CoverageChecked

private noncomputable def leaf2194InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814637/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2194InputLogOnePlusV_eq :
    leaf2194InputLogOnePlusV = outerEnclosure 24
      (leaf2194Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2194RoundedFacts : LeafRoundedFacts 8
    leaf2194Certificate.logOnePlusV leaf2194InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2194InputLogOnePlusV_eq }

private noncomputable def leaf2194Inputs : Inputs :=
  inputsOfCaches globalInput sk187RoundedInputs
    chi116InputQChi innerPair50Input
    leaf2194InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2194LowerChecked :
    lowerCheck 24 leaf2194Box leaf2194Inputs = true := by
  rfl'

private theorem leaf2194CoversExact : CoversExact 8
    leaf2194Box leaf2194Certificate leaf2194InnerLog leaf2194Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk187RoundedFacts chi116RoundedFacts
    innerPair50RoundedFacts leaf2194RoundedFacts (by rfl)

private theorem leaf2194FlatSound : Sound leaf2194Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2194CertificateValid
    leaf2194InnerLogValid leaf2194CoversExact leaf2194LowerChecked

private noncomputable def leaf2195Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (195/64), kHi := (49/16), chiLo := (25/128), chiHi := (13/64) }

private noncomputable def leaf2195Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871355/536870912) }, vSqrt := { lower := (65529/65536), upper := (1065402495/1065377792) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (856306203/536870912) }, upper := { exponent := 0, mantissa := (1661/1024) } }, logOuter := sk188LogOuterCertificate, logK := sk188LogKCertificate, logChi := chi116LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (2130780287/2130755584) } }, logDArg := sk188LogDArgCertificate }

private noncomputable def leaf2195InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2195LocalValidity :
    LeafFacts leaf2195Box leaf2195Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2195Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (1065402495/1065377792) }) = true
      norm_num [leaf2195Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2195CertificateValid :
    WideCertificateValid leaf2195Box leaf2195Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk188ValidityFacts chi116ValidityFacts
    leaf2195LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2195CoverageChecked :
    coverageCheck (innerAD leaf2195Box) leaf2195InnerLog = true := by
  rfl'

private theorem leaf2195InnerLogValid :
    leaf2195InnerLog.Valid 8 (innerAD leaf2195Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2195CoverageChecked

private noncomputable def leaf2195InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629275/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2195InputLogOnePlusV_eq :
    leaf2195InputLogOnePlusV = outerEnclosure 24
      (leaf2195Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2195RoundedFacts : LeafRoundedFacts 8
    leaf2195Certificate.logOnePlusV leaf2195InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2195InputLogOnePlusV_eq }

private noncomputable def leaf2195Inputs : Inputs :=
  inputsOfCaches globalInput sk188RoundedInputs
    chi116InputQChi innerPair50Input
    leaf2195InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2195LowerChecked :
    lowerCheck 24 leaf2195Box leaf2195Inputs = true := by
  rfl'

private theorem leaf2195CoversExact : CoversExact 8
    leaf2195Box leaf2195Certificate leaf2195InnerLog leaf2195Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk188RoundedFacts chi116RoundedFacts
    innerPair50RoundedFacts leaf2195RoundedFacts (by rfl)

private theorem leaf2195FlatSound : Sound leaf2195Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2195CertificateValid
    leaf2195InnerLogValid leaf2195CoversExact leaf2195LowerChecked

private noncomputable def leaf2196Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (197/64), chiLo := (3/16), chiHi := (25/128) }

private noncomputable def leaf2196Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871355/536870912) }, vSqrt := { lower := (65529/65536), upper := (45812307285/45811303424) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (845100231/536870912) }, upper := { exponent := 0, mantissa := (13117/8192) } }, logOuter := sk189LogOuterCertificate, logK := sk189LogKCertificate, logChi := chi115LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (91623610709/91622606848) } }, logDArg := sk189LogDArgCertificate }

private noncomputable def leaf2196InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2196LocalValidity :
    LeafFacts leaf2196Box leaf2196Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2196Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (45812307285/45811303424) }) = true
      norm_num [leaf2196Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2196CertificateValid :
    WideCertificateValid leaf2196Box leaf2196Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk189ValidityFacts chi115ValidityFacts
    leaf2196LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2196CoverageChecked :
    coverageCheck (innerAD leaf2196Box) leaf2196InnerLog = true := by
  rfl'

private theorem leaf2196InnerLogValid :
    leaf2196InnerLog.Valid 8 (innerAD leaf2196Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2196CoverageChecked

private noncomputable def leaf2196InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629265/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2196InputLogOnePlusV_eq :
    leaf2196InputLogOnePlusV = outerEnclosure 24
      (leaf2196Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2196RoundedFacts : LeafRoundedFacts 8
    leaf2196Certificate.logOnePlusV leaf2196InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2196InputLogOnePlusV_eq }

private noncomputable def leaf2196Inputs : Inputs :=
  inputsOfCaches globalInput sk189RoundedInputs
    chi115InputQChi innerPair50Input
    leaf2196InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2196LowerChecked :
    lowerCheck 24 leaf2196Box leaf2196Inputs = true := by
  rfl'

private theorem leaf2196CoversExact : CoversExact 8
    leaf2196Box leaf2196Certificate leaf2196InnerLog leaf2196Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk189RoundedFacts chi115RoundedFacts
    innerPair50RoundedFacts leaf2196RoundedFacts (by rfl)

private theorem leaf2196FlatSound : Sound leaf2196Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2196CertificateValid
    leaf2196InnerLogValid leaf2196CoversExact leaf2196LowerChecked

private noncomputable def leaf2197Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (197/64), kHi := (99/32), chiLo := (3/16), chiHi := (25/128) }

private noncomputable def leaf2197Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871357/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433884672) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (846672997/536870912) }, upper := { exponent := 0, mantissa := (6571/4096) } }, logOuter := sk190LogOuterCertificate, logK := sk190LogKCertificate, logChi := chi115LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870806527/274867769344) } }, logDArg := sk190LogDArgCertificate }

private noncomputable def leaf2197InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2197LocalValidity :
    LeafFacts leaf2197Box leaf2197Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2197Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433884672) }) = true
      norm_num [leaf2197Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2197CertificateValid :
    WideCertificateValid leaf2197Box leaf2197Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk190ValidityFacts chi115ValidityFacts
    leaf2197LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2197CoverageChecked :
    coverageCheck (innerAD leaf2197Box) leaf2197InnerLog = true := by
  rfl'

private theorem leaf2197InnerLogValid :
    leaf2197InnerLog.Valid 8 (innerAD leaf2197Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2197CoverageChecked

private noncomputable def leaf2197InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814633/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2197InputLogOnePlusV_eq :
    leaf2197InputLogOnePlusV = outerEnclosure 24
      (leaf2197Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2197RoundedFacts : LeafRoundedFacts 8
    leaf2197Certificate.logOnePlusV leaf2197InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2197InputLogOnePlusV_eq }

private noncomputable def leaf2197Inputs : Inputs :=
  inputsOfCaches globalInput sk190RoundedInputs
    chi115InputQChi innerPair50Input
    leaf2197InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2197LowerChecked :
    lowerCheck 24 leaf2197Box leaf2197Inputs = true := by
  rfl'

private theorem leaf2197CoversExact : CoversExact 8
    leaf2197Box leaf2197Certificate leaf2197InnerLog leaf2197Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk190RoundedFacts chi115RoundedFacts
    innerPair50RoundedFacts leaf2197RoundedFacts (by rfl)

private theorem leaf2197FlatSound : Sound leaf2197Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2197CertificateValid
    leaf2197InnerLogValid leaf2197CoversExact leaf2197LowerChecked

private noncomputable def leaf2198Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (199/64), chiLo := (3/16), chiHi := (25/128) }

private noncomputable def leaf2198Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871359/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433859072) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (848245763/536870912) }, upper := { exponent := 0, mantissa := (13167/8192) } }, logOuter := sk191LogOuterCertificate, logK := sk191LogKCertificate, logChi := chi115LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870780927/274867718144) } }, logDArg := sk191LogDArgCertificate }

private noncomputable def leaf2198InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2198LocalValidity :
    LeafFacts leaf2198Box leaf2198Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2198Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433859072) }) = true
      norm_num [leaf2198Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2198CertificateValid :
    WideCertificateValid leaf2198Box leaf2198Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk191ValidityFacts chi115ValidityFacts
    leaf2198LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2198CoverageChecked :
    coverageCheck (innerAD leaf2198Box) leaf2198InnerLog = true := by
  rfl'

private theorem leaf2198InnerLogValid :
    leaf2198InnerLog.Valid 8 (innerAD leaf2198Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2198CoverageChecked

private noncomputable def leaf2198InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907317/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2198InputLogOnePlusV_eq :
    leaf2198InputLogOnePlusV = outerEnclosure 24
      (leaf2198Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2198RoundedFacts : LeafRoundedFacts 8
    leaf2198Certificate.logOnePlusV leaf2198InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2198InputLogOnePlusV_eq }

private noncomputable def leaf2198Inputs : Inputs :=
  inputsOfCaches globalInput sk191RoundedInputs
    chi115InputQChi innerPair50Input
    leaf2198InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2198LowerChecked :
    lowerCheck 24 leaf2198Box leaf2198Inputs = true := by
  rfl'

private theorem leaf2198CoversExact : CoversExact 8
    leaf2198Box leaf2198Certificate leaf2198InnerLog leaf2198Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk191RoundedFacts chi115RoundedFacts
    innerPair50RoundedFacts leaf2198RoundedFacts (by rfl)

private theorem leaf2198FlatSound : Sound leaf2198Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2198CertificateValid
    leaf2198InnerLogValid leaf2198CoversExact leaf2198LowerChecked

private noncomputable def leaf2199Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (199/64), kHi := (25/8), chiLo := (3/16), chiHi := (25/128) }

private noncomputable def leaf2199Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871361/536870912) }, vSqrt := { lower := (65529/65536), upper := (45812307285/45811277824) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (849818529/536870912) }, upper := { exponent := 0, mantissa := (1649/1024) } }, logOuter := sk192LogOuterCertificate, logK := sk192LogKCertificate, logChi := chi115LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (91623585109/91622555648) } }, logDArg := sk192LogDArgCertificate }

private noncomputable def leaf2199InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2199LocalValidity :
    LeafFacts leaf2199Box leaf2199Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2199Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (45812307285/45811277824) }) = true
      norm_num [leaf2199Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2199CertificateValid :
    WideCertificateValid leaf2199Box leaf2199Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk192ValidityFacts chi115ValidityFacts
    leaf2199LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2199CoverageChecked :
    coverageCheck (innerAD leaf2199Box) leaf2199InnerLog = true := by
  rfl'

private theorem leaf2199InnerLogValid :
    leaf2199InnerLog.Valid 8 (innerAD leaf2199Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2199CoverageChecked

private noncomputable def leaf2199InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629269/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2199InputLogOnePlusV_eq :
    leaf2199InputLogOnePlusV = outerEnclosure 24
      (leaf2199Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2199RoundedFacts : LeafRoundedFacts 8
    leaf2199Certificate.logOnePlusV leaf2199InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2199InputLogOnePlusV_eq }

private noncomputable def leaf2199Inputs : Inputs :=
  inputsOfCaches globalInput sk192RoundedInputs
    chi115InputQChi innerPair50Input
    leaf2199InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2199LowerChecked :
    lowerCheck 24 leaf2199Box leaf2199Inputs = true := by
  rfl'

private theorem leaf2199CoversExact : CoversExact 8
    leaf2199Box leaf2199Certificate leaf2199InnerLog leaf2199Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk192RoundedFacts chi115RoundedFacts
    innerPair50RoundedFacts leaf2199RoundedFacts (by rfl)

private theorem leaf2199FlatSound : Sound leaf2199Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2199CertificateValid
    leaf2199InnerLogValid leaf2199CoversExact leaf2199LowerChecked

private noncomputable def leaf2200Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (197/64), chiLo := (25/128), chiHi := (13/64) }

private noncomputable def leaf2200Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871357/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433708544) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (857944501/536870912) }, upper := { exponent := 0, mantissa := (6657/4096) } }, logOuter := sk189LogOuterCertificate, logK := sk189LogKCertificate, logChi := chi116LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870630399/274867417088) } }, logDArg := sk189LogDArgCertificate }

private noncomputable def leaf2200InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf2200LocalValidity :
    LeafFacts leaf2200Box leaf2200Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2200Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433708544) }) = true
      norm_num [leaf2200Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2200CertificateValid :
    WideCertificateValid leaf2200Box leaf2200Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk189ValidityFacts chi116ValidityFacts
    leaf2200LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2200CoverageChecked :
    coverageCheck (innerAD leaf2200Box) leaf2200InnerLog = true := by
  rfl'

private theorem leaf2200InnerLogValid :
    leaf2200InnerLog.Valid 8 (innerAD leaf2200Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf2200CoverageChecked

private noncomputable def leaf2200InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629277/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2200InputLogOnePlusV_eq :
    leaf2200InputLogOnePlusV = outerEnclosure 24
      (leaf2200Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2200RoundedFacts : LeafRoundedFacts 8
    leaf2200Certificate.logOnePlusV leaf2200InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2200InputLogOnePlusV_eq }

private noncomputable def leaf2200Inputs : Inputs :=
  inputsOfCaches globalInput sk189RoundedInputs
    chi116InputQChi innerPair51Input
    leaf2200InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2200LowerChecked :
    lowerCheck 24 leaf2200Box leaf2200Inputs = true := by
  rfl'

private theorem leaf2200CoversExact : CoversExact 8
    leaf2200Box leaf2200Certificate leaf2200InnerLog leaf2200Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk189RoundedFacts chi116RoundedFacts
    innerPair51RoundedFacts leaf2200RoundedFacts (by rfl)

private theorem leaf2200FlatSound : Sound leaf2200Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2200CertificateValid
    leaf2200InnerLogValid leaf2200CoversExact leaf2200LowerChecked

private noncomputable def leaf2201Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (197/64), kHi := (99/32), chiLo := (25/128), chiHi := (13/64) }

private noncomputable def leaf2201Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871359/536870912) }, vSqrt := { lower := (65529/65536), upper := (27487384371/27486736384) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (859582799/536870912) }, upper := { exponent := 0, mantissa := (3335/2048) } }, logOuter := sk190LogOuterCertificate, logK := sk190LogKCertificate, logChi := chi116LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (54974120755/54973472768) } }, logDArg := sk190LogDArgCertificate }

private noncomputable def leaf2201InnerLog : WideLogData :=
  innerPair157Data

set_option maxRecDepth 1000000 in
private theorem leaf2201LocalValidity :
    LeafFacts leaf2201Box leaf2201Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2201Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (27487384371/27486736384) }) = true
      norm_num [leaf2201Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2201CertificateValid :
    WideCertificateValid leaf2201Box leaf2201Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk190ValidityFacts chi116ValidityFacts
    leaf2201LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2201CoverageChecked :
    coverageCheck (innerAD leaf2201Box) leaf2201InnerLog = true := by
  rfl'

private theorem leaf2201InnerLogValid :
    leaf2201InnerLog.Valid 8 (innerAD leaf2201Box) :=
  wideLogDataValid_of_cachedCheck endpoint44PositiveFacts
    endpoint45PositiveFacts.valid leaf2201CoverageChecked

private noncomputable def leaf2201InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814639/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2201InputLogOnePlusV_eq :
    leaf2201InputLogOnePlusV = outerEnclosure 24
      (leaf2201Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2201RoundedFacts : LeafRoundedFacts 8
    leaf2201Certificate.logOnePlusV leaf2201InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2201InputLogOnePlusV_eq }

private noncomputable def leaf2201Inputs : Inputs :=
  inputsOfCaches globalInput sk190RoundedInputs
    chi116InputQChi innerPair157Input
    leaf2201InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2201LowerChecked :
    lowerCheck 24 leaf2201Box leaf2201Inputs = true := by
  rfl'

private theorem leaf2201CoversExact : CoversExact 8
    leaf2201Box leaf2201Certificate leaf2201InnerLog leaf2201Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk190RoundedFacts chi116RoundedFacts
    innerPair157RoundedFacts leaf2201RoundedFacts (by rfl)

private theorem leaf2201FlatSound : Sound leaf2201Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2201CertificateValid
    leaf2201InnerLogValid leaf2201CoversExact leaf2201LowerChecked

private noncomputable def leaf2202Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (199/64), chiLo := (25/128), chiHi := (13/64) }

private noncomputable def leaf2202Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871361/536870912) }, vSqrt := { lower := (65529/65536), upper := (15270769095/15270406144) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (861221097/536870912) }, upper := { exponent := 0, mantissa := (6683/4096) } }, logOuter := sk191LogOuterCertificate, logK := sk191LogKCertificate, logChi := chi116LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (30541175239/30540812288) } }, logDArg := sk191LogDArgCertificate }

private noncomputable def leaf2202InnerLog : WideLogData :=
  innerPair157Data

set_option maxRecDepth 1000000 in
private theorem leaf2202LocalValidity :
    LeafFacts leaf2202Box leaf2202Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2202Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (15270769095/15270406144) }) = true
      norm_num [leaf2202Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2202CertificateValid :
    WideCertificateValid leaf2202Box leaf2202Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk191ValidityFacts chi116ValidityFacts
    leaf2202LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2202CoverageChecked :
    coverageCheck (innerAD leaf2202Box) leaf2202InnerLog = true := by
  rfl'

private theorem leaf2202InnerLogValid :
    leaf2202InnerLog.Valid 8 (innerAD leaf2202Box) :=
  wideLogDataValid_of_cachedCheck endpoint44PositiveFacts
    endpoint45PositiveFacts.valid leaf2202CoverageChecked

private noncomputable def leaf2202InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (363415/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf2202InputLogOnePlusV_eq :
    leaf2202InputLogOnePlusV = outerEnclosure 24
      (leaf2202Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2202RoundedFacts : LeafRoundedFacts 8
    leaf2202Certificate.logOnePlusV leaf2202InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2202InputLogOnePlusV_eq }

private noncomputable def leaf2202Inputs : Inputs :=
  inputsOfCaches globalInput sk191RoundedInputs
    chi116InputQChi innerPair157Input
    leaf2202InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2202LowerChecked :
    lowerCheck 24 leaf2202Box leaf2202Inputs = true := by
  rfl'

private theorem leaf2202CoversExact : CoversExact 8
    leaf2202Box leaf2202Certificate leaf2202InnerLog leaf2202Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk191RoundedFacts chi116RoundedFacts
    innerPair157RoundedFacts leaf2202RoundedFacts (by rfl)

private theorem leaf2202FlatSound : Sound leaf2202Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2202CertificateValid
    leaf2202InnerLogValid leaf2202CoversExact leaf2202LowerChecked

private noncomputable def leaf2203Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (199/64), kHi := (25/8), chiLo := (25/128), chiHi := (13/64) }

private noncomputable def leaf2203Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871363/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433628672) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (862859395/536870912) }, upper := { exponent := 0, mantissa := (837/512) } }, logOuter := sk192LogOuterCertificate, logK := sk192LogKCertificate, logChi := chi116LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870550527/274867257344) } }, logDArg := sk192LogDArgCertificate }

private noncomputable def leaf2203InnerLog : WideLogData :=
  innerPair157Data

set_option maxRecDepth 1000000 in
private theorem leaf2203LocalValidity :
    LeafFacts leaf2203Box leaf2203Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2203Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433628672) }) = true
      norm_num [leaf2203Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2203CertificateValid :
    WideCertificateValid leaf2203Box leaf2203Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk192ValidityFacts chi116ValidityFacts
    leaf2203LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2203CoverageChecked :
    coverageCheck (innerAD leaf2203Box) leaf2203InnerLog = true := by
  rfl'

private theorem leaf2203InnerLogValid :
    leaf2203InnerLog.Valid 8 (innerAD leaf2203Box) :=
  wideLogDataValid_of_cachedCheck endpoint44PositiveFacts
    endpoint45PositiveFacts.valid leaf2203CoverageChecked

private noncomputable def leaf2203InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814641/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2203InputLogOnePlusV_eq :
    leaf2203InputLogOnePlusV = outerEnclosure 24
      (leaf2203Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2203RoundedFacts : LeafRoundedFacts 8
    leaf2203Certificate.logOnePlusV leaf2203InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2203InputLogOnePlusV_eq }

private noncomputable def leaf2203Inputs : Inputs :=
  inputsOfCaches globalInput sk192RoundedInputs
    chi116InputQChi innerPair157Input
    leaf2203InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2203LowerChecked :
    lowerCheck 24 leaf2203Box leaf2203Inputs = true := by
  rfl'

private theorem leaf2203CoversExact : CoversExact 8
    leaf2203Box leaf2203Certificate leaf2203InnerLog leaf2203Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk192RoundedFacts chi116RoundedFacts
    innerPair157RoundedFacts leaf2203RoundedFacts (by rfl)

private theorem leaf2203FlatSound : Sound leaf2203Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2203CertificateValid
    leaf2203InnerLogValid leaf2203CoversExact leaf2203LowerChecked

private noncomputable def leaf2204Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (193/64), chiLo := (13/64), chiHi := (27/128) }

private noncomputable def leaf2204Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871351/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433617408) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (863973451/536870912) }, upper := { exponent := 0, mantissa := (13403/8192) } }, logOuter := sk185LogOuterCertificate, logK := sk185LogKCertificate, logChi := chi117LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870539263/274867234816) } }, logDArg := sk185LogDArgCertificate }

private noncomputable def leaf2204InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf2204LocalValidity :
    LeafFacts leaf2204Box leaf2204Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2204Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433617408) }) = true
      norm_num [leaf2204Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2204CertificateValid :
    WideCertificateValid leaf2204Box leaf2204Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk185ValidityFacts chi117ValidityFacts
    leaf2204LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2204CoverageChecked :
    coverageCheck (innerAD leaf2204Box) leaf2204InnerLog = true := by
  rfl'

private theorem leaf2204InnerLogValid :
    leaf2204InnerLog.Valid 8 (innerAD leaf2204Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf2204CoverageChecked

private noncomputable def leaf2204InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814641/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2204InputLogOnePlusV_eq :
    leaf2204InputLogOnePlusV = outerEnclosure 24
      (leaf2204Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2204RoundedFacts : LeafRoundedFacts 8
    leaf2204Certificate.logOnePlusV leaf2204InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2204InputLogOnePlusV_eq }

private noncomputable def leaf2204Inputs : Inputs :=
  inputsOfCaches globalInput sk185RoundedInputs
    chi117InputQChi innerPair51Input
    leaf2204InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2204LowerChecked :
    lowerCheck 24 leaf2204Box leaf2204Inputs = true := by
  rfl'

private theorem leaf2204CoversExact : CoversExact 8
    leaf2204Box leaf2204Certificate leaf2204InnerLog leaf2204Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk185RoundedFacts chi117RoundedFacts
    innerPair51RoundedFacts leaf2204RoundedFacts (by rfl)

private theorem leaf2204FlatSound : Sound leaf2204Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2204CertificateValid
    leaf2204InnerLogValid leaf2204CoversExact leaf2204LowerChecked

private noncomputable def leaf2205Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (193/64), kHi := (97/32), chiLo := (13/64), chiHi := (27/128) }

private noncomputable def leaf2205Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871353/536870912) }, vSqrt := { lower := (65529/65536), upper := (27487384371/27486717952) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (865677281/536870912) }, upper := { exponent := 0, mantissa := (6715/4096) } }, logOuter := sk186LogOuterCertificate, logK := sk186LogKCertificate, logChi := chi117LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (54974102323/54973435904) } }, logDArg := sk186LogDArgCertificate }

private noncomputable def leaf2205InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf2205LocalValidity :
    LeafFacts leaf2205Box leaf2205Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2205Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (27487384371/27486717952) }) = true
      norm_num [leaf2205Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2205CertificateValid :
    WideCertificateValid leaf2205Box leaf2205Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk186ValidityFacts chi117ValidityFacts
    leaf2205LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2205CoverageChecked :
    coverageCheck (innerAD leaf2205Box) leaf2205InnerLog = true := by
  rfl'

private theorem leaf2205InnerLogValid :
    leaf2205InnerLog.Valid 8 (innerAD leaf2205Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf2205CoverageChecked

private noncomputable def leaf2205InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907321/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2205InputLogOnePlusV_eq :
    leaf2205InputLogOnePlusV = outerEnclosure 24
      (leaf2205Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2205RoundedFacts : LeafRoundedFacts 8
    leaf2205Certificate.logOnePlusV leaf2205InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2205InputLogOnePlusV_eq }

private noncomputable def leaf2205Inputs : Inputs :=
  inputsOfCaches globalInput sk186RoundedInputs
    chi117InputQChi innerPair51Input
    leaf2205InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2205LowerChecked :
    lowerCheck 24 leaf2205Box leaf2205Inputs = true := by
  rfl'

private theorem leaf2205CoversExact : CoversExact 8
    leaf2205Box leaf2205Certificate leaf2205InnerLog leaf2205Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk186RoundedFacts chi117RoundedFacts
    innerPair51RoundedFacts leaf2205RoundedFacts (by rfl)

private theorem leaf2205FlatSound : Sound leaf2205Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2205CertificateValid
    leaf2205InnerLogValid leaf2205CoversExact leaf2205LowerChecked

private noncomputable def leaf2206Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (193/64), chiLo := (27/128), chiHi := (7/32) }

private noncomputable def leaf2206Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871353/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433419776) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (876555593/536870912) }, upper := { exponent := 0, mantissa := (3399/2048) } }, logOuter := sk185LogOuterCertificate, logK := sk185LogKCertificate, logChi := chi118LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870341631/274866839552) } }, logDArg := sk185LogDArgCertificate }

private noncomputable def leaf2206InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2206LocalValidity :
    LeafFacts leaf2206Box leaf2206Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2206Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433419776) }) = true
      norm_num [leaf2206Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2206CertificateValid :
    WideCertificateValid leaf2206Box leaf2206Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk185ValidityFacts chi118ValidityFacts
    leaf2206LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2206CoverageChecked :
    coverageCheck (innerAD leaf2206Box) leaf2206InnerLog = true := by
  rfl'

private theorem leaf2206InnerLogValid :
    leaf2206InnerLog.Valid 8 (innerAD leaf2206Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2206CoverageChecked

private noncomputable def leaf2206InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629295/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2206InputLogOnePlusV_eq :
    leaf2206InputLogOnePlusV = outerEnclosure 24
      (leaf2206Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2206RoundedFacts : LeafRoundedFacts 8
    leaf2206Certificate.logOnePlusV leaf2206InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2206InputLogOnePlusV_eq }

private noncomputable def leaf2206Inputs : Inputs :=
  inputsOfCaches globalInput sk185RoundedInputs
    chi118InputQChi innerPair56Input
    leaf2206InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2206LowerChecked :
    lowerCheck 24 leaf2206Box leaf2206Inputs = true := by
  rfl'

private theorem leaf2206CoversExact : CoversExact 8
    leaf2206Box leaf2206Certificate leaf2206InnerLog leaf2206Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk185RoundedFacts chi118RoundedFacts
    innerPair56RoundedFacts leaf2206RoundedFacts (by rfl)

private theorem leaf2206FlatSound : Sound leaf2206Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2206CertificateValid
    leaf2206InnerLogValid leaf2206CoversExact leaf2206LowerChecked

private noncomputable def leaf2207Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (193/64), kHi := (97/32), chiLo := (27/128), chiHi := (7/32) }

private noncomputable def leaf2207Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871355/536870912) }, vSqrt := { lower := (65529/65536), upper := (45812307285/45811130368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (878324955/536870912) }, upper := { exponent := 0, mantissa := (1703/1024) } }, logOuter := sk186LogOuterCertificate, logK := sk186LogKCertificate, logChi := chi118LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (91623437653/91622260736) } }, logDArg := sk186LogDArgCertificate }

private noncomputable def leaf2207InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2207LocalValidity :
    LeafFacts leaf2207Box leaf2207Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2207Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (45812307285/45811130368) }) = true
      norm_num [leaf2207Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2207CertificateValid :
    WideCertificateValid leaf2207Box leaf2207Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk186ValidityFacts chi118ValidityFacts
    leaf2207LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2207CoverageChecked :
    coverageCheck (innerAD leaf2207Box) leaf2207InnerLog = true := by
  rfl'

private theorem leaf2207InnerLogValid :
    leaf2207InnerLog.Valid 8 (innerAD leaf2207Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2207CoverageChecked

private noncomputable def leaf2207InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (726831/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf2207InputLogOnePlusV_eq :
    leaf2207InputLogOnePlusV = outerEnclosure 24
      (leaf2207Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2207RoundedFacts : LeafRoundedFacts 8
    leaf2207Certificate.logOnePlusV leaf2207InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2207InputLogOnePlusV_eq }

private noncomputable def leaf2207Inputs : Inputs :=
  inputsOfCaches globalInput sk186RoundedInputs
    chi118InputQChi innerPair56Input
    leaf2207InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2207LowerChecked :
    lowerCheck 24 leaf2207Box leaf2207Inputs = true := by
  rfl'

private theorem leaf2207CoversExact : CoversExact 8
    leaf2207Box leaf2207Certificate leaf2207InnerLog leaf2207Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk186RoundedFacts chi118RoundedFacts
    innerPair56RoundedFacts leaf2207RoundedFacts (by rfl)

private theorem leaf2207FlatSound : Sound leaf2207Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2207CertificateValid
    leaf2207InnerLogValid leaf2207CoversExact leaf2207LowerChecked

private noncomputable def leaf2208Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (195/64), chiLo := (13/64), chiHi := (27/128) }

private noncomputable def leaf2208Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871355/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433562112) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (867381111/536870912) }, upper := { exponent := 0, mantissa := (13457/8192) } }, logOuter := sk187LogOuterCertificate, logK := sk187LogKCertificate, logChi := chi117LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870483967/274867124224) } }, logDArg := sk187LogDArgCertificate }

private noncomputable def leaf2208InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf2208LocalValidity :
    LeafFacts leaf2208Box leaf2208Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2208Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433562112) }) = true
      norm_num [leaf2208Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2208CertificateValid :
    WideCertificateValid leaf2208Box leaf2208Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk187ValidityFacts chi117ValidityFacts
    leaf2208LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2208CoverageChecked :
    coverageCheck (innerAD leaf2208Box) leaf2208InnerLog = true := by
  rfl'

private theorem leaf2208InnerLogValid :
    leaf2208InnerLog.Valid 8 (innerAD leaf2208Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf2208CoverageChecked

private noncomputable def leaf2208InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814643/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2208InputLogOnePlusV_eq :
    leaf2208InputLogOnePlusV = outerEnclosure 24
      (leaf2208Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2208RoundedFacts : LeafRoundedFacts 8
    leaf2208Certificate.logOnePlusV leaf2208InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2208InputLogOnePlusV_eq }

private noncomputable def leaf2208Inputs : Inputs :=
  inputsOfCaches globalInput sk187RoundedInputs
    chi117InputQChi innerPair51Input
    leaf2208InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2208LowerChecked :
    lowerCheck 24 leaf2208Box leaf2208Inputs = true := by
  rfl'

private theorem leaf2208CoversExact : CoversExact 8
    leaf2208Box leaf2208Certificate leaf2208InnerLog leaf2208Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk187RoundedFacts chi117RoundedFacts
    innerPair51RoundedFacts leaf2208RoundedFacts (by rfl)

private theorem leaf2208FlatSound : Sound leaf2208Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2208CertificateValid
    leaf2208InnerLogValid leaf2208CoversExact leaf2208LowerChecked

private noncomputable def leaf2209Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (195/64), kHi := (49/16), chiLo := (13/64), chiHi := (27/128) }

private noncomputable def leaf2209Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871357/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433534464) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (869084941/536870912) }, upper := { exponent := 0, mantissa := (3371/2048) } }, logOuter := sk188LogOuterCertificate, logK := sk188LogKCertificate, logChi := chi117LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870456319/274867068928) } }, logDArg := sk188LogDArgCertificate }

private noncomputable def leaf2209InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf2209LocalValidity :
    LeafFacts leaf2209Box leaf2209Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2209Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433534464) }) = true
      norm_num [leaf2209Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2209CertificateValid :
    WideCertificateValid leaf2209Box leaf2209Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk188ValidityFacts chi117ValidityFacts
    leaf2209LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2209CoverageChecked :
    coverageCheck (innerAD leaf2209Box) leaf2209InnerLog = true := by
  rfl'

private theorem leaf2209InnerLogValid :
    leaf2209InnerLog.Valid 8 (innerAD leaf2209Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf2209CoverageChecked

private noncomputable def leaf2209InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453661/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf2209InputLogOnePlusV_eq :
    leaf2209InputLogOnePlusV = outerEnclosure 24
      (leaf2209Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2209RoundedFacts : LeafRoundedFacts 8
    leaf2209Certificate.logOnePlusV leaf2209InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2209InputLogOnePlusV_eq }

private noncomputable def leaf2209Inputs : Inputs :=
  inputsOfCaches globalInput sk188RoundedInputs
    chi117InputQChi innerPair51Input
    leaf2209InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2209LowerChecked :
    lowerCheck 24 leaf2209Box leaf2209Inputs = true := by
  rfl'

private theorem leaf2209CoversExact : CoversExact 8
    leaf2209Box leaf2209Certificate leaf2209InnerLog leaf2209Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk188RoundedFacts chi117RoundedFacts
    innerPair51RoundedFacts leaf2209RoundedFacts (by rfl)

private theorem leaf2209FlatSound : Sound leaf2209Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2209CertificateValid
    leaf2209InnerLogValid leaf2209CoversExact leaf2209LowerChecked

private noncomputable def leaf2210Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (195/64), chiLo := (27/128), chiHi := (7/32) }

private noncomputable def leaf2210Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871357/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433362432) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (880094317/536870912) }, upper := { exponent := 0, mantissa := (3413/2048) } }, logOuter := sk187LogOuterCertificate, logK := sk187LogKCertificate, logChi := chi118LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870284287/274866724864) } }, logDArg := sk187LogDArgCertificate }

private noncomputable def leaf2210InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2210LocalValidity :
    LeafFacts leaf2210Box leaf2210Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2210Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433362432) }) = true
      norm_num [leaf2210Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2210CertificateValid :
    WideCertificateValid leaf2210Box leaf2210Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk187ValidityFacts chi118ValidityFacts
    leaf2210LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2210CoverageChecked :
    coverageCheck (innerAD leaf2210Box) leaf2210InnerLog = true := by
  rfl'

private theorem leaf2210InnerLogValid :
    leaf2210InnerLog.Valid 8 (innerAD leaf2210Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2210CoverageChecked

private noncomputable def leaf2210InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814649/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2210InputLogOnePlusV_eq :
    leaf2210InputLogOnePlusV = outerEnclosure 24
      (leaf2210Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2210RoundedFacts : LeafRoundedFacts 8
    leaf2210Certificate.logOnePlusV leaf2210InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2210InputLogOnePlusV_eq }

private noncomputable def leaf2210Inputs : Inputs :=
  inputsOfCaches globalInput sk187RoundedInputs
    chi118InputQChi innerPair56Input
    leaf2210InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2210LowerChecked :
    lowerCheck 24 leaf2210Box leaf2210Inputs = true := by
  rfl'

private theorem leaf2210CoversExact : CoversExact 8
    leaf2210Box leaf2210Certificate leaf2210InnerLog leaf2210Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk187RoundedFacts chi118RoundedFacts
    innerPair56RoundedFacts leaf2210RoundedFacts (by rfl)

private theorem leaf2210FlatSound : Sound leaf2210Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2210CertificateValid
    leaf2210InnerLogValid leaf2210CoversExact leaf2210LowerChecked

private noncomputable def leaf2211Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (195/64), kHi := (49/16), chiLo := (27/128), chiHi := (7/32) }

private noncomputable def leaf2211Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871359/536870912) }, vSqrt := { lower := (65529/65536), upper := (27487384371/27486666752) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (881863679/536870912) }, upper := { exponent := 0, mantissa := (855/512) } }, logOuter := sk188LogOuterCertificate, logK := sk188LogKCertificate, logChi := chi118LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (54974051123/54973333504) } }, logDArg := sk188LogDArgCertificate }

private noncomputable def leaf2211InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2211LocalValidity :
    LeafFacts leaf2211Box leaf2211Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2211Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (27487384371/27486666752) }) = true
      norm_num [leaf2211Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2211CertificateValid :
    WideCertificateValid leaf2211Box leaf2211Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk188ValidityFacts chi118ValidityFacts
    leaf2211LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2211CoverageChecked :
    coverageCheck (innerAD leaf2211Box) leaf2211InnerLog = true := by
  rfl'

private theorem leaf2211InnerLogValid :
    leaf2211InnerLog.Valid 8 (innerAD leaf2211Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2211CoverageChecked

private noncomputable def leaf2211InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907325/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2211InputLogOnePlusV_eq :
    leaf2211InputLogOnePlusV = outerEnclosure 24
      (leaf2211Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2211RoundedFacts : LeafRoundedFacts 8
    leaf2211Certificate.logOnePlusV leaf2211InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2211InputLogOnePlusV_eq }

private noncomputable def leaf2211Inputs : Inputs :=
  inputsOfCaches globalInput sk188RoundedInputs
    chi118InputQChi innerPair56Input
    leaf2211InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2211LowerChecked :
    lowerCheck 24 leaf2211Box leaf2211Inputs = true := by
  rfl'

private theorem leaf2211CoversExact : CoversExact 8
    leaf2211Box leaf2211Certificate leaf2211InnerLog leaf2211Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk188RoundedFacts chi118RoundedFacts
    innerPair56RoundedFacts leaf2211RoundedFacts (by rfl)

private theorem leaf2211FlatSound : Sound leaf2211Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2211CertificateValid
    leaf2211InnerLogValid leaf2211CoversExact leaf2211LowerChecked

private noncomputable def leaf2212Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (197/64), chiLo := (13/64), chiHi := (27/128) }

private noncomputable def leaf2212Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871359/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433506816) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (870788771/536870912) }, upper := { exponent := 0, mantissa := (13511/8192) } }, logOuter := sk189LogOuterCertificate, logK := sk189LogKCertificate, logChi := chi117LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870428671/274867013632) } }, logDArg := sk189LogDArgCertificate }

private noncomputable def leaf2212InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf2212LocalValidity :
    LeafFacts leaf2212Box leaf2212Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2212Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433506816) }) = true
      norm_num [leaf2212Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2212CertificateValid :
    WideCertificateValid leaf2212Box leaf2212Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk189ValidityFacts chi117ValidityFacts
    leaf2212LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2212CoverageChecked :
    coverageCheck (innerAD leaf2212Box) leaf2212InnerLog = true := by
  rfl'

private theorem leaf2212InnerLogValid :
    leaf2212InnerLog.Valid 8 (innerAD leaf2212Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf2212CoverageChecked

private noncomputable def leaf2212InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629289/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2212InputLogOnePlusV_eq :
    leaf2212InputLogOnePlusV = outerEnclosure 24
      (leaf2212Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2212RoundedFacts : LeafRoundedFacts 8
    leaf2212Certificate.logOnePlusV leaf2212InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2212InputLogOnePlusV_eq }

private noncomputable def leaf2212Inputs : Inputs :=
  inputsOfCaches globalInput sk189RoundedInputs
    chi117InputQChi innerPair51Input
    leaf2212InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2212LowerChecked :
    lowerCheck 24 leaf2212Box leaf2212Inputs = true := by
  rfl'

private theorem leaf2212CoversExact : CoversExact 8
    leaf2212Box leaf2212Certificate leaf2212InnerLog leaf2212Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk189RoundedFacts chi117RoundedFacts
    innerPair51RoundedFacts leaf2212RoundedFacts (by rfl)

private theorem leaf2212FlatSound : Sound leaf2212Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2212CertificateValid
    leaf2212InnerLogValid leaf2212CoversExact leaf2212LowerChecked

private noncomputable def leaf2213Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (197/64), kHi := (99/32), chiLo := (13/64), chiHi := (27/128) }

private noncomputable def leaf2213Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871361/536870912) }, vSqrt := { lower := (65529/65536), upper := (8084524815/8084322304) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (872492601/536870912) }, upper := { exponent := 0, mantissa := (6769/4096) } }, logOuter := sk190LogOuterCertificate, logK := sk190LogKCertificate, logChi := chi117LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (16168847119/16168644608) } }, logDArg := sk190LogDArgCertificate }

private noncomputable def leaf2213InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2213LocalValidity :
    LeafFacts leaf2213Box leaf2213Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2213Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8084524815/8084322304) }) = true
      norm_num [leaf2213Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2213CertificateValid :
    WideCertificateValid leaf2213Box leaf2213Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk190ValidityFacts chi117ValidityFacts
    leaf2213LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2213CoverageChecked :
    coverageCheck (innerAD leaf2213Box) leaf2213InnerLog = true := by
  rfl'

private theorem leaf2213InnerLogValid :
    leaf2213InnerLog.Valid 8 (innerAD leaf2213Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2213CoverageChecked

private noncomputable def leaf2213InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629291/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2213InputLogOnePlusV_eq :
    leaf2213InputLogOnePlusV = outerEnclosure 24
      (leaf2213Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2213RoundedFacts : LeafRoundedFacts 8
    leaf2213Certificate.logOnePlusV leaf2213InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2213InputLogOnePlusV_eq }

private noncomputable def leaf2213Inputs : Inputs :=
  inputsOfCaches globalInput sk190RoundedInputs
    chi117InputQChi innerPair56Input
    leaf2213InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2213LowerChecked :
    lowerCheck 24 leaf2213Box leaf2213Inputs = true := by
  rfl'

private theorem leaf2213CoversExact : CoversExact 8
    leaf2213Box leaf2213Certificate leaf2213InnerLog leaf2213Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk190RoundedFacts chi117RoundedFacts
    innerPair56RoundedFacts leaf2213RoundedFacts (by rfl)

private theorem leaf2213FlatSound : Sound leaf2213Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2213CertificateValid
    leaf2213InnerLogValid leaf2213CoversExact leaf2213LowerChecked

private noncomputable def leaf2214Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (197/64), chiLo := (27/128), chiHi := (7/32) }

private noncomputable def leaf2214Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871361/536870912) }, vSqrt := { lower := (65529/65536), upper := (898280535/898256896) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (883633041/536870912) }, upper := { exponent := 0, mantissa := (3427/2048) } }, logOuter := sk189LogOuterCertificate, logK := sk189LogKCertificate, logChi := chi118LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (1796537431/1796513792) } }, logDArg := sk189LogDArgCertificate }

private noncomputable def leaf2214InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2214LocalValidity :
    LeafFacts leaf2214Box leaf2214Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2214Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (898280535/898256896) }) = true
      norm_num [leaf2214Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2214CertificateValid :
    WideCertificateValid leaf2214Box leaf2214Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk189ValidityFacts chi118ValidityFacts
    leaf2214LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2214CoverageChecked :
    coverageCheck (innerAD leaf2214Box) leaf2214InnerLog = true := by
  rfl'

private theorem leaf2214InnerLogValid :
    leaf2214InnerLog.Valid 8 (innerAD leaf2214Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2214CoverageChecked

private noncomputable def leaf2214InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814651/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2214InputLogOnePlusV_eq :
    leaf2214InputLogOnePlusV = outerEnclosure 24
      (leaf2214Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2214RoundedFacts : LeafRoundedFacts 8
    leaf2214Certificate.logOnePlusV leaf2214InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2214InputLogOnePlusV_eq }

private noncomputable def leaf2214Inputs : Inputs :=
  inputsOfCaches globalInput sk189RoundedInputs
    chi118InputQChi innerPair56Input
    leaf2214InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2214LowerChecked :
    lowerCheck 24 leaf2214Box leaf2214Inputs = true := by
  rfl'

private theorem leaf2214CoversExact : CoversExact 8
    leaf2214Box leaf2214Certificate leaf2214InnerLog leaf2214Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk189RoundedFacts chi118RoundedFacts
    innerPair56RoundedFacts leaf2214RoundedFacts (by rfl)

private theorem leaf2214FlatSound : Sound leaf2214Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2214CertificateValid
    leaf2214InnerLogValid leaf2214CoversExact leaf2214LowerChecked

private noncomputable def leaf2215Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (197/64), kHi := (99/32), chiLo := (27/128), chiHi := (7/32) }

private noncomputable def leaf2215Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871363/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433276416) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (885402403/536870912) }, upper := { exponent := 0, mantissa := (1717/1024) } }, logOuter := sk190LogOuterCertificate, logK := sk190LogKCertificate, logChi := chi118LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870198271/274866552832) } }, logDArg := sk190LogDArgCertificate }

private noncomputable def leaf2215InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2215LocalValidity :
    LeafFacts leaf2215Box leaf2215Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2215Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433276416) }) = true
      norm_num [leaf2215Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2215CertificateValid :
    WideCertificateValid leaf2215Box leaf2215Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk190ValidityFacts chi118ValidityFacts
    leaf2215LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2215CoverageChecked :
    coverageCheck (innerAD leaf2215Box) leaf2215InnerLog = true := by
  rfl'

private theorem leaf2215InnerLogValid :
    leaf2215InnerLog.Valid 8 (innerAD leaf2215Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2215CoverageChecked

private noncomputable def leaf2215InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629303/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2215InputLogOnePlusV_eq :
    leaf2215InputLogOnePlusV = outerEnclosure 24
      (leaf2215Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2215RoundedFacts : LeafRoundedFacts 8
    leaf2215Certificate.logOnePlusV leaf2215InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2215InputLogOnePlusV_eq }

private noncomputable def leaf2215Inputs : Inputs :=
  inputsOfCaches globalInput sk190RoundedInputs
    chi118InputQChi innerPair56Input
    leaf2215InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2215LowerChecked :
    lowerCheck 24 leaf2215Box leaf2215Inputs = true := by
  rfl'

private theorem leaf2215CoversExact : CoversExact 8
    leaf2215Box leaf2215Certificate leaf2215InnerLog leaf2215Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk190RoundedFacts chi118RoundedFacts
    innerPair56RoundedFacts leaf2215RoundedFacts (by rfl)

private theorem leaf2215FlatSound : Sound leaf2215Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2215CertificateValid
    leaf2215InnerLogValid leaf2215CoversExact leaf2215LowerChecked

private noncomputable def leaf2216Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (199/64), chiLo := (13/64), chiHi := (27/128) }

private noncomputable def leaf2216Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871363/536870912) }, vSqrt := { lower := (65529/65536), upper := (27487384371/27486690304) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (874196431/536870912) }, upper := { exponent := 0, mantissa := (13565/8192) } }, logOuter := sk191LogOuterCertificate, logK := sk191LogKCertificate, logChi := chi117LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (54974074675/54973380608) } }, logDArg := sk191LogDArgCertificate }

private noncomputable def leaf2216InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2216LocalValidity :
    LeafFacts leaf2216Box leaf2216Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2216Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (27487384371/27486690304) }) = true
      norm_num [leaf2216Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2216CertificateValid :
    WideCertificateValid leaf2216Box leaf2216Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk191ValidityFacts chi117ValidityFacts
    leaf2216LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2216CoverageChecked :
    coverageCheck (innerAD leaf2216Box) leaf2216InnerLog = true := by
  rfl'

private theorem leaf2216InnerLogValid :
    leaf2216InnerLog.Valid 8 (innerAD leaf2216Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2216CoverageChecked

private noncomputable def leaf2216InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629293/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2216InputLogOnePlusV_eq :
    leaf2216InputLogOnePlusV = outerEnclosure 24
      (leaf2216Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2216RoundedFacts : LeafRoundedFacts 8
    leaf2216Certificate.logOnePlusV leaf2216InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2216InputLogOnePlusV_eq }

private noncomputable def leaf2216Inputs : Inputs :=
  inputsOfCaches globalInput sk191RoundedInputs
    chi117InputQChi innerPair56Input
    leaf2216InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2216LowerChecked :
    lowerCheck 24 leaf2216Box leaf2216Inputs = true := by
  rfl'

private theorem leaf2216CoversExact : CoversExact 8
    leaf2216Box leaf2216Certificate leaf2216InnerLog leaf2216Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk191RoundedFacts chi117RoundedFacts
    innerPair56RoundedFacts leaf2216RoundedFacts (by rfl)

private theorem leaf2216FlatSound : Sound leaf2216Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2216CertificateValid
    leaf2216InnerLogValid leaf2216CoversExact leaf2216LowerChecked

private noncomputable def leaf2217Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (199/64), kHi := (25/8), chiLo := (13/64), chiHi := (27/128) }

private noncomputable def leaf2217Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871365/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433423872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (875900261/536870912) }, upper := { exponent := 0, mantissa := (1699/1024) } }, logOuter := sk192LogOuterCertificate, logK := sk192LogKCertificate, logChi := chi117LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870345727/274866847744) } }, logDArg := sk192LogDArgCertificate }

private noncomputable def leaf2217InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2217LocalValidity :
    LeafFacts leaf2217Box leaf2217Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2217Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433423872) }) = true
      norm_num [leaf2217Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2217CertificateValid :
    WideCertificateValid leaf2217Box leaf2217Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk192ValidityFacts chi117ValidityFacts
    leaf2217LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2217CoverageChecked :
    coverageCheck (innerAD leaf2217Box) leaf2217InnerLog = true := by
  rfl'

private theorem leaf2217InnerLogValid :
    leaf2217InnerLog.Valid 8 (innerAD leaf2217Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2217CoverageChecked

private noncomputable def leaf2217InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814647/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2217InputLogOnePlusV_eq :
    leaf2217InputLogOnePlusV = outerEnclosure 24
      (leaf2217Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2217RoundedFacts : LeafRoundedFacts 8
    leaf2217Certificate.logOnePlusV leaf2217InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2217InputLogOnePlusV_eq }

private noncomputable def leaf2217Inputs : Inputs :=
  inputsOfCaches globalInput sk192RoundedInputs
    chi117InputQChi innerPair56Input
    leaf2217InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2217LowerChecked :
    lowerCheck 24 leaf2217Box leaf2217Inputs = true := by
  rfl'

private theorem leaf2217CoversExact : CoversExact 8
    leaf2217Box leaf2217Certificate leaf2217InnerLog leaf2217Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk192RoundedFacts chi117RoundedFacts
    innerPair56RoundedFacts leaf2217RoundedFacts (by rfl)

private theorem leaf2217FlatSound : Sound leaf2217Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2217CertificateValid
    leaf2217InnerLogValid leaf2217CoversExact leaf2217LowerChecked

private noncomputable def leaf2218Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (199/64), chiLo := (27/128), chiHi := (7/32) }

private noncomputable def leaf2218Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871365/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433247744) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (887171765/536870912) }, upper := { exponent := 0, mantissa := (3441/2048) } }, logOuter := sk191LogOuterCertificate, logK := sk191LogKCertificate, logChi := chi118LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870169599/274866495488) } }, logDArg := sk191LogDArgCertificate }

private noncomputable def leaf2218InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2218LocalValidity :
    LeafFacts leaf2218Box leaf2218Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2218Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433247744) }) = true
      norm_num [leaf2218Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2218CertificateValid :
    WideCertificateValid leaf2218Box leaf2218Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk191ValidityFacts chi118ValidityFacts
    leaf2218LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2218CoverageChecked :
    coverageCheck (innerAD leaf2218Box) leaf2218InnerLog = true := by
  rfl'

private theorem leaf2218InnerLogValid :
    leaf2218InnerLog.Valid 8 (innerAD leaf2218Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2218CoverageChecked

private noncomputable def leaf2218InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629305/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2218InputLogOnePlusV_eq :
    leaf2218InputLogOnePlusV = outerEnclosure 24
      (leaf2218Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2218RoundedFacts : LeafRoundedFacts 8
    leaf2218Certificate.logOnePlusV leaf2218InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2218InputLogOnePlusV_eq }

private noncomputable def leaf2218Inputs : Inputs :=
  inputsOfCaches globalInput sk191RoundedInputs
    chi118InputQChi innerPair56Input
    leaf2218InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2218LowerChecked :
    lowerCheck 24 leaf2218Box leaf2218Inputs = true := by
  rfl'

private theorem leaf2218CoversExact : CoversExact 8
    leaf2218Box leaf2218Certificate leaf2218InnerLog leaf2218Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk191RoundedFacts chi118RoundedFacts
    innerPair56RoundedFacts leaf2218RoundedFacts (by rfl)

private theorem leaf2218FlatSound : Sound leaf2218Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2218CertificateValid
    leaf2218InnerLogValid leaf2218CoversExact leaf2218LowerChecked

private noncomputable def leaf2219Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (199/64), kHi := (25/8), chiLo := (27/128), chiHi := (7/32) }

private noncomputable def leaf2219Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871367/536870912) }, vSqrt := { lower := (65529/65536), upper := (45812307285/45811073024) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (888941127/536870912) }, upper := { exponent := 0, mantissa := (431/256) } }, logOuter := sk192LogOuterCertificate, logK := sk192LogKCertificate, logChi := chi118LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (91623380309/91622146048) } }, logDArg := sk192LogDArgCertificate }

private noncomputable def leaf2219InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2219LocalValidity :
    LeafFacts leaf2219Box leaf2219Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2219Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (45812307285/45811073024) }) = true
      norm_num [leaf2219Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2219CertificateValid :
    WideCertificateValid leaf2219Box leaf2219Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk192ValidityFacts chi118ValidityFacts
    leaf2219LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2219CoverageChecked :
    coverageCheck (innerAD leaf2219Box) leaf2219InnerLog = true := by
  rfl'

private theorem leaf2219InnerLogValid :
    leaf2219InnerLog.Valid 8 (innerAD leaf2219Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2219CoverageChecked

private noncomputable def leaf2219InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629307/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2219InputLogOnePlusV_eq :
    leaf2219InputLogOnePlusV = outerEnclosure 24
      (leaf2219Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2219RoundedFacts : LeafRoundedFacts 8
    leaf2219Certificate.logOnePlusV leaf2219InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2219InputLogOnePlusV_eq }

private noncomputable def leaf2219Inputs : Inputs :=
  inputsOfCaches globalInput sk192RoundedInputs
    chi118InputQChi innerPair56Input
    leaf2219InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2219LowerChecked :
    lowerCheck 24 leaf2219Box leaf2219Inputs = true := by
  rfl'

private theorem leaf2219CoversExact : CoversExact 8
    leaf2219Box leaf2219Certificate leaf2219InnerLog leaf2219Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk192RoundedFacts chi118RoundedFacts
    innerPair56RoundedFacts leaf2219RoundedFacts (by rfl)

private theorem leaf2219FlatSound : Sound leaf2219Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2219CertificateValid
    leaf2219InnerLogValid leaf2219CoversExact leaf2219LowerChecked

private noncomputable def leaf2220Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (201/64), chiLo := (3/16), chiHi := (25/128) }

private noncomputable def leaf2220Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871363/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433807872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (851391295/536870912) }, upper := { exponent := 0, mantissa := (13217/8192) } }, logOuter := sk193LogOuterCertificate, logK := sk193LogKCertificate, logChi := chi115LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870729727/274867615744) } }, logDArg := sk193LogDArgCertificate }

private noncomputable def leaf2220InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2220LocalValidity :
    LeafFacts leaf2220Box leaf2220Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2220Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433807872) }) = true
      norm_num [leaf2220Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2220CertificateValid :
    WideCertificateValid leaf2220Box leaf2220Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk193ValidityFacts chi115ValidityFacts
    leaf2220LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2220CoverageChecked :
    coverageCheck (innerAD leaf2220Box) leaf2220InnerLog = true := by
  rfl'

private theorem leaf2220InnerLogValid :
    leaf2220InnerLog.Valid 8 (innerAD leaf2220Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2220CoverageChecked

private noncomputable def leaf2220InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629271/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2220InputLogOnePlusV_eq :
    leaf2220InputLogOnePlusV = outerEnclosure 24
      (leaf2220Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2220RoundedFacts : LeafRoundedFacts 8
    leaf2220Certificate.logOnePlusV leaf2220InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2220InputLogOnePlusV_eq }

private noncomputable def leaf2220Inputs : Inputs :=
  inputsOfCaches globalInput sk193RoundedInputs
    chi115InputQChi innerPair50Input
    leaf2220InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2220LowerChecked :
    lowerCheck 24 leaf2220Box leaf2220Inputs = true := by
  rfl'

private theorem leaf2220CoversExact : CoversExact 8
    leaf2220Box leaf2220Certificate leaf2220InnerLog leaf2220Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk193RoundedFacts chi115RoundedFacts
    innerPair50RoundedFacts leaf2220RoundedFacts (by rfl)

private theorem leaf2220FlatSound : Sound leaf2220Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2220CertificateValid
    leaf2220InnerLogValid leaf2220CoversExact leaf2220LowerChecked

private noncomputable def leaf2221Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (201/64), kHi := (101/32), chiLo := (3/16), chiHi := (25/128) }

private noncomputable def leaf2221Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871365/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433782272) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (852964061/536870912) }, upper := { exponent := 0, mantissa := (6621/4096) } }, logOuter := sk194LogOuterCertificate, logK := sk194LogKCertificate, logChi := chi115LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870704127/274867564544) } }, logDArg := sk194LogDArgCertificate }

private noncomputable def leaf2221InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2221LocalValidity :
    LeafFacts leaf2221Box leaf2221Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2221Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433782272) }) = true
      norm_num [leaf2221Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2221CertificateValid :
    WideCertificateValid leaf2221Box leaf2221Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk194ValidityFacts chi115ValidityFacts
    leaf2221LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2221CoverageChecked :
    coverageCheck (innerAD leaf2221Box) leaf2221InnerLog = true := by
  rfl'

private theorem leaf2221InnerLogValid :
    leaf2221InnerLog.Valid 8 (innerAD leaf2221Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2221CoverageChecked

private noncomputable def leaf2221InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453659/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf2221InputLogOnePlusV_eq :
    leaf2221InputLogOnePlusV = outerEnclosure 24
      (leaf2221Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2221RoundedFacts : LeafRoundedFacts 8
    leaf2221Certificate.logOnePlusV leaf2221InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2221InputLogOnePlusV_eq }

private noncomputable def leaf2221Inputs : Inputs :=
  inputsOfCaches globalInput sk194RoundedInputs
    chi115InputQChi innerPair50Input
    leaf2221InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2221LowerChecked :
    lowerCheck 24 leaf2221Box leaf2221Inputs = true := by
  rfl'

private theorem leaf2221CoversExact : CoversExact 8
    leaf2221Box leaf2221Certificate leaf2221InnerLog leaf2221Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk194RoundedFacts chi115RoundedFacts
    innerPair50RoundedFacts leaf2221RoundedFacts (by rfl)

private theorem leaf2221FlatSound : Sound leaf2221Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2221CertificateValid
    leaf2221InnerLogValid leaf2221CoversExact leaf2221LowerChecked

private noncomputable def leaf2222Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (203/64), chiLo := (3/16), chiHi := (25/128) }

private noncomputable def leaf2222Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871367/536870912) }, vSqrt := { lower := (65529/65536), upper := (5090256365/5090139136) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (854536827/536870912) }, upper := { exponent := 0, mantissa := (13267/8192) } }, logOuter := sk195LogOuterCertificate, logK := sk195LogKCertificate, logChi := chi115LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (10180395501/10180278272) } }, logDArg := sk195LogDArgCertificate }

private noncomputable def leaf2222InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2222LocalValidity :
    LeafFacts leaf2222Box leaf2222Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2222Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (5090256365/5090139136) }) = true
      norm_num [leaf2222Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2222CertificateValid :
    WideCertificateValid leaf2222Box leaf2222Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk195ValidityFacts chi115ValidityFacts
    leaf2222LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2222CoverageChecked :
    coverageCheck (innerAD leaf2222Box) leaf2222InnerLog = true := by
  rfl'

private theorem leaf2222InnerLogValid :
    leaf2222InnerLog.Valid 8 (innerAD leaf2222Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2222CoverageChecked

private noncomputable def leaf2222InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814637/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2222InputLogOnePlusV_eq :
    leaf2222InputLogOnePlusV = outerEnclosure 24
      (leaf2222Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2222RoundedFacts : LeafRoundedFacts 8
    leaf2222Certificate.logOnePlusV leaf2222InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2222InputLogOnePlusV_eq }

private noncomputable def leaf2222Inputs : Inputs :=
  inputsOfCaches globalInput sk195RoundedInputs
    chi115InputQChi innerPair50Input
    leaf2222InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2222LowerChecked :
    lowerCheck 24 leaf2222Box leaf2222Inputs = true := by
  rfl'

private theorem leaf2222CoversExact : CoversExact 8
    leaf2222Box leaf2222Certificate leaf2222InnerLog leaf2222Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk195RoundedFacts chi115RoundedFacts
    innerPair50RoundedFacts leaf2222RoundedFacts (by rfl)

private theorem leaf2222FlatSound : Sound leaf2222Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2222CertificateValid
    leaf2222InnerLogValid leaf2222CoversExact leaf2222LowerChecked

private noncomputable def leaf2223Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (203/64), kHi := (51/16), chiLo := (3/16), chiHi := (25/128) }

private noncomputable def leaf2223Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871369/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433731072) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (856109593/536870912) }, upper := { exponent := 0, mantissa := (3323/2048) } }, logOuter := sk196LogOuterCertificate, logK := sk196LogKCertificate, logChi := chi115LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870652927/274867462144) } }, logDArg := sk196LogDArgCertificate }

private noncomputable def leaf2223InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2223LocalValidity :
    LeafFacts leaf2223Box leaf2223Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2223Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433731072) }) = true
      norm_num [leaf2223Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2223CertificateValid :
    WideCertificateValid leaf2223Box leaf2223Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk196ValidityFacts chi115ValidityFacts
    leaf2223LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2223CoverageChecked :
    coverageCheck (innerAD leaf2223Box) leaf2223InnerLog = true := by
  rfl'

private theorem leaf2223InnerLogValid :
    leaf2223InnerLog.Valid 8 (innerAD leaf2223Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2223CoverageChecked

private noncomputable def leaf2223InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629275/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2223InputLogOnePlusV_eq :
    leaf2223InputLogOnePlusV = outerEnclosure 24
      (leaf2223Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2223RoundedFacts : LeafRoundedFacts 8
    leaf2223Certificate.logOnePlusV leaf2223InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2223InputLogOnePlusV_eq }

private noncomputable def leaf2223Inputs : Inputs :=
  inputsOfCaches globalInput sk196RoundedInputs
    chi115InputQChi innerPair50Input
    leaf2223InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2223LowerChecked :
    lowerCheck 24 leaf2223Box leaf2223Inputs = true := by
  rfl'

private theorem leaf2223CoversExact : CoversExact 8
    leaf2223Box leaf2223Certificate leaf2223InnerLog leaf2223Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk196RoundedFacts chi115RoundedFacts
    innerPair50RoundedFacts leaf2223RoundedFacts (by rfl)

private theorem leaf2223FlatSound : Sound leaf2223Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2223CertificateValid
    leaf2223InnerLogValid leaf2223CoversExact leaf2223LowerChecked

private noncomputable def leaf2224Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (201/64), chiLo := (25/128), chiHi := (13/64) }

private noncomputable def leaf2224Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871365/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433602048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (864497693/536870912) }, upper := { exponent := 0, mantissa := (6709/4096) } }, logOuter := sk193LogOuterCertificate, logK := sk193LogKCertificate, logChi := chi116LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870523903/274867204096) } }, logDArg := sk193LogDArgCertificate }

private noncomputable def leaf2224InnerLog : WideLogData :=
  innerPair166Data

set_option maxRecDepth 1000000 in
private theorem leaf2224LocalValidity :
    LeafFacts leaf2224Box leaf2224Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2224Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433602048) }) = true
      norm_num [leaf2224Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2224CertificateValid :
    WideCertificateValid leaf2224Box leaf2224Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk193ValidityFacts chi116ValidityFacts
    leaf2224LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2224CoverageChecked :
    coverageCheck (innerAD leaf2224Box) leaf2224InnerLog = true := by
  rfl'

private theorem leaf2224InnerLogValid :
    leaf2224InnerLog.Valid 8 (innerAD leaf2224Box) :=
  wideLogDataValid_of_cachedCheck endpoint46PositiveFacts
    endpoint45PositiveFacts.valid leaf2224CoverageChecked

private noncomputable def leaf2224InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629283/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2224InputLogOnePlusV_eq :
    leaf2224InputLogOnePlusV = outerEnclosure 24
      (leaf2224Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2224RoundedFacts : LeafRoundedFacts 8
    leaf2224Certificate.logOnePlusV leaf2224InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2224InputLogOnePlusV_eq }

private noncomputable def leaf2224Inputs : Inputs :=
  inputsOfCaches globalInput sk193RoundedInputs
    chi116InputQChi innerPair166Input
    leaf2224InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2224LowerChecked :
    lowerCheck 24 leaf2224Box leaf2224Inputs = true := by
  rfl'

private theorem leaf2224CoversExact : CoversExact 8
    leaf2224Box leaf2224Certificate leaf2224InnerLog leaf2224Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk193RoundedFacts chi116RoundedFacts
    innerPair166RoundedFacts leaf2224RoundedFacts (by rfl)

private theorem leaf2224FlatSound : Sound leaf2224Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2224CertificateValid
    leaf2224InnerLogValid leaf2224CoversExact leaf2224LowerChecked

private noncomputable def leaf2225Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (201/64), kHi := (101/32), chiLo := (25/128), chiHi := (13/64) }

private noncomputable def leaf2225Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871367/536870912) }, vSqrt := { lower := (65529/65536), upper := (45812307285/45811191808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (866135991/536870912) }, upper := { exponent := 0, mantissa := (3361/2048) } }, logOuter := sk194LogOuterCertificate, logK := sk194LogKCertificate, logChi := chi116LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (91623499093/91622383616) } }, logDArg := sk194LogDArgCertificate }

private noncomputable def leaf2225InnerLog : WideLogData :=
  innerPair167Data

set_option maxRecDepth 1000000 in
private theorem leaf2225LocalValidity :
    LeafFacts leaf2225Box leaf2225Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2225Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (45812307285/45811191808) }) = true
      norm_num [leaf2225Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2225CertificateValid :
    WideCertificateValid leaf2225Box leaf2225Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk194ValidityFacts chi116ValidityFacts
    leaf2225LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2225CoverageChecked :
    coverageCheck (innerAD leaf2225Box) leaf2225InnerLog = true := by
  rfl'

private theorem leaf2225InnerLogValid :
    leaf2225InnerLog.Valid 8 (innerAD leaf2225Box) :=
  wideLogDataValid_of_cachedCheck endpoint46PositiveFacts
    endpoint48PositiveFacts.valid leaf2225CoverageChecked

private noncomputable def leaf2225InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629285/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2225InputLogOnePlusV_eq :
    leaf2225InputLogOnePlusV = outerEnclosure 24
      (leaf2225Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2225RoundedFacts : LeafRoundedFacts 8
    leaf2225Certificate.logOnePlusV leaf2225InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2225InputLogOnePlusV_eq }

private noncomputable def leaf2225Inputs : Inputs :=
  inputsOfCaches globalInput sk194RoundedInputs
    chi116InputQChi innerPair167Input
    leaf2225InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2225LowerChecked :
    lowerCheck 24 leaf2225Box leaf2225Inputs = true := by
  rfl'

private theorem leaf2225CoversExact : CoversExact 8
    leaf2225Box leaf2225Certificate leaf2225InnerLog leaf2225Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk194RoundedFacts chi116RoundedFacts
    innerPair167RoundedFacts leaf2225RoundedFacts (by rfl)

private theorem leaf2225FlatSound : Sound leaf2225Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2225CertificateValid
    leaf2225InnerLogValid leaf2225CoversExact leaf2225LowerChecked

private noncomputable def leaf2226Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (203/64), chiLo := (25/128), chiHi := (13/64) }

private noncomputable def leaf2226Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871369/536870912) }, vSqrt := { lower := (65529/65536), upper := (1616904963/1616865280) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (867774289/536870912) }, upper := { exponent := 0, mantissa := (6735/4096) } }, logOuter := sk195LogOuterCertificate, logK := sk195LogKCertificate, logChi := chi116LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (3233770243/3233730560) } }, logDArg := sk195LogDArgCertificate }

private noncomputable def leaf2226InnerLog : WideLogData :=
  innerPair167Data

set_option maxRecDepth 1000000 in
private theorem leaf2226LocalValidity :
    LeafFacts leaf2226Box leaf2226Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2226Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (1616904963/1616865280) }) = true
      norm_num [leaf2226Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2226CertificateValid :
    WideCertificateValid leaf2226Box leaf2226Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk195ValidityFacts chi116ValidityFacts
    leaf2226LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2226CoverageChecked :
    coverageCheck (innerAD leaf2226Box) leaf2226InnerLog = true := by
  rfl'

private theorem leaf2226InnerLogValid :
    leaf2226InnerLog.Valid 8 (innerAD leaf2226Box) :=
  wideLogDataValid_of_cachedCheck endpoint46PositiveFacts
    endpoint48PositiveFacts.valid leaf2226CoverageChecked

private noncomputable def leaf2226InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629287/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2226InputLogOnePlusV_eq :
    leaf2226InputLogOnePlusV = outerEnclosure 24
      (leaf2226Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2226RoundedFacts : LeafRoundedFacts 8
    leaf2226Certificate.logOnePlusV leaf2226InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2226InputLogOnePlusV_eq }

private noncomputable def leaf2226Inputs : Inputs :=
  inputsOfCaches globalInput sk195RoundedInputs
    chi116InputQChi innerPair167Input
    leaf2226InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2226LowerChecked :
    lowerCheck 24 leaf2226Box leaf2226Inputs = true := by
  rfl'

private theorem leaf2226CoversExact : CoversExact 8
    leaf2226Box leaf2226Certificate leaf2226InnerLog leaf2226Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk195RoundedFacts chi116RoundedFacts
    innerPair167RoundedFacts leaf2226RoundedFacts (by rfl)

private theorem leaf2226FlatSound : Sound leaf2226Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2226CertificateValid
    leaf2226InnerLogValid leaf2226CoversExact leaf2226LowerChecked

private noncomputable def leaf2227Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (203/64), kHi := (51/16), chiLo := (25/128), chiHi := (13/64) }

private noncomputable def leaf2227Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871371/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433522176) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (869412587/536870912) }, upper := { exponent := 0, mantissa := (1687/1024) } }, logOuter := sk196LogOuterCertificate, logK := sk196LogKCertificate, logChi := chi116LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870444031/274867044352) } }, logDArg := sk196LogDArgCertificate }

private noncomputable def leaf2227InnerLog : WideLogData :=
  innerPair167Data

set_option maxRecDepth 1000000 in
private theorem leaf2227LocalValidity :
    LeafFacts leaf2227Box leaf2227Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2227Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433522176) }) = true
      norm_num [leaf2227Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2227CertificateValid :
    WideCertificateValid leaf2227Box leaf2227Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk196ValidityFacts chi116ValidityFacts
    leaf2227LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2227CoverageChecked :
    coverageCheck (innerAD leaf2227Box) leaf2227InnerLog = true := by
  rfl'

private theorem leaf2227InnerLogValid :
    leaf2227InnerLog.Valid 8 (innerAD leaf2227Box) :=
  wideLogDataValid_of_cachedCheck endpoint46PositiveFacts
    endpoint48PositiveFacts.valid leaf2227CoverageChecked

private noncomputable def leaf2227InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453661/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf2227InputLogOnePlusV_eq :
    leaf2227InputLogOnePlusV = outerEnclosure 24
      (leaf2227Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2227RoundedFacts : LeafRoundedFacts 8
    leaf2227Certificate.logOnePlusV leaf2227InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2227InputLogOnePlusV_eq }

private noncomputable def leaf2227Inputs : Inputs :=
  inputsOfCaches globalInput sk196RoundedInputs
    chi116InputQChi innerPair167Input
    leaf2227InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2227LowerChecked :
    lowerCheck 24 leaf2227Box leaf2227Inputs = true := by
  rfl'

private theorem leaf2227CoversExact : CoversExact 8
    leaf2227Box leaf2227Certificate leaf2227InnerLog leaf2227Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk196RoundedFacts chi116RoundedFacts
    innerPair167RoundedFacts leaf2227RoundedFacts (by rfl)

private theorem leaf2227FlatSound : Sound leaf2227Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2227CertificateValid
    leaf2227InnerLogValid leaf2227CoversExact leaf2227LowerChecked

private noncomputable def leaf2228Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (205/64), chiLo := (3/16), chiHi := (25/128) }

private noncomputable def leaf2228Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871371/536870912) }, vSqrt := { lower := (65529/65536), upper := (8084524815/8084335616) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (857682359/536870912) }, upper := { exponent := 0, mantissa := (13317/8192) } }, logOuter := sk197LogOuterCertificate, logK := sk197LogKCertificate, logChi := chi115LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (16168860431/16168671232) } }, logDArg := sk197LogDArgCertificate }

private noncomputable def leaf2228InnerLog : WideLogData :=
  innerPair157Data

set_option maxRecDepth 1000000 in
private theorem leaf2228LocalValidity :
    LeafFacts leaf2228Box leaf2228Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2228Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8084524815/8084335616) }) = true
      norm_num [leaf2228Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2228CertificateValid :
    WideCertificateValid leaf2228Box leaf2228Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk197ValidityFacts chi115ValidityFacts
    leaf2228LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2228CoverageChecked :
    coverageCheck (innerAD leaf2228Box) leaf2228InnerLog = true := by
  rfl'

private theorem leaf2228InnerLogValid :
    leaf2228InnerLog.Valid 8 (innerAD leaf2228Box) :=
  wideLogDataValid_of_cachedCheck endpoint44PositiveFacts
    endpoint45PositiveFacts.valid leaf2228CoverageChecked

private noncomputable def leaf2228InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629277/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2228InputLogOnePlusV_eq :
    leaf2228InputLogOnePlusV = outerEnclosure 24
      (leaf2228Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2228RoundedFacts : LeafRoundedFacts 8
    leaf2228Certificate.logOnePlusV leaf2228InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2228InputLogOnePlusV_eq }

private noncomputable def leaf2228Inputs : Inputs :=
  inputsOfCaches globalInput sk197RoundedInputs
    chi115InputQChi innerPair157Input
    leaf2228InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2228LowerChecked :
    lowerCheck 24 leaf2228Box leaf2228Inputs = true := by
  rfl'

private theorem leaf2228CoversExact : CoversExact 8
    leaf2228Box leaf2228Certificate leaf2228InnerLog leaf2228Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk197RoundedFacts chi115RoundedFacts
    innerPair157RoundedFacts leaf2228RoundedFacts (by rfl)

private theorem leaf2228FlatSound : Sound leaf2228Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2228CertificateValid
    leaf2228InnerLogValid leaf2228CoversExact leaf2228LowerChecked

private noncomputable def leaf2229Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (205/64), kHi := (103/32), chiLo := (3/16), chiHi := (25/128) }

private noncomputable def leaf2229Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871373/536870912) }, vSqrt := { lower := (65529/65536), upper := (45812307285/45811226624) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (859255125/536870912) }, upper := { exponent := 0, mantissa := (6671/4096) } }, logOuter := sk198LogOuterCertificate, logK := sk198LogKCertificate, logChi := chi115LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (91623533909/91622453248) } }, logDArg := sk198LogDArgCertificate }

private noncomputable def leaf2229InnerLog : WideLogData :=
  innerPair157Data

set_option maxRecDepth 1000000 in
private theorem leaf2229LocalValidity :
    LeafFacts leaf2229Box leaf2229Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2229Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (45812307285/45811226624) }) = true
      norm_num [leaf2229Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2229CertificateValid :
    WideCertificateValid leaf2229Box leaf2229Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk198ValidityFacts chi115ValidityFacts
    leaf2229LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2229CoverageChecked :
    coverageCheck (innerAD leaf2229Box) leaf2229InnerLog = true := by
  rfl'

private theorem leaf2229InnerLogValid :
    leaf2229InnerLog.Valid 8 (innerAD leaf2229Box) :=
  wideLogDataValid_of_cachedCheck endpoint44PositiveFacts
    endpoint45PositiveFacts.valid leaf2229CoverageChecked

private noncomputable def leaf2229InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629279/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2229InputLogOnePlusV_eq :
    leaf2229InputLogOnePlusV = outerEnclosure 24
      (leaf2229Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2229RoundedFacts : LeafRoundedFacts 8
    leaf2229Certificate.logOnePlusV leaf2229InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2229InputLogOnePlusV_eq }

private noncomputable def leaf2229Inputs : Inputs :=
  inputsOfCaches globalInput sk198RoundedInputs
    chi115InputQChi innerPair157Input
    leaf2229InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2229LowerChecked :
    lowerCheck 24 leaf2229Box leaf2229Inputs = true := by
  rfl'

private theorem leaf2229CoversExact : CoversExact 8
    leaf2229Box leaf2229Certificate leaf2229InnerLog leaf2229Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk198RoundedFacts chi115RoundedFacts
    innerPair157RoundedFacts leaf2229RoundedFacts (by rfl)

private theorem leaf2229FlatSound : Sound leaf2229Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2229CertificateValid
    leaf2229InnerLogValid leaf2229CoversExact leaf2229LowerChecked

private noncomputable def leaf2230Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (3/16), chiHi := (49/256) }

private noncomputable def leaf2230Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871217/536870912) }, vSqrt := { lower := (65529/65536), upper := (22906164565/22905622528) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (860828049/536870912) }, upper := { exponent := 0, mantissa := (1661/1024) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi187LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (45811787093/45811245056) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf2230InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2230LocalValidity :
    LeafFacts leaf2230Box leaf2230Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2230Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22906164565/22905622528) }) = true
      norm_num [leaf2230Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2230CertificateValid :
    WideCertificateValid leaf2230Box leaf2230Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi187ValidityFacts
    leaf2230LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2230CoverageChecked :
    coverageCheck (innerAD leaf2230Box) leaf2230InnerLog = true := by
  rfl'

private theorem leaf2230InnerLogValid :
    leaf2230InnerLog.Valid 8 (innerAD leaf2230Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2230CoverageChecked

private noncomputable def leaf2230InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629279/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2230InputLogOnePlusV_eq :
    leaf2230InputLogOnePlusV = outerEnclosure 24
      (leaf2230Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2230RoundedFacts : LeafRoundedFacts 8
    leaf2230Certificate.logOnePlusV leaf2230InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2230InputLogOnePlusV_eq }

private noncomputable def leaf2230Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi187InputQChi innerPair50Input
    leaf2230InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2230LowerChecked :
    lowerCheck 24 leaf2230Box leaf2230Inputs = true := by
  rfl'

private theorem leaf2230CoversExact : CoversExact 8
    leaf2230Box leaf2230Certificate leaf2230InnerLog leaf2230Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi187RoundedFacts
    innerPair50RoundedFacts leaf2230RoundedFacts (by rfl)

private theorem leaf2230FlatSound : Sound leaf2230Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2230CertificateValid
    leaf2230InnerLogValid leaf2230CoversExact leaf2230LowerChecked

private noncomputable def leaf2231Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (49/256), chiHi := (25/128) }

private noncomputable def leaf2231Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871219/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68716814336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (867577843/536870912) }, upper := { exponent := 0, mantissa := (837/512) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi188LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435308031/137433628672) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf2231InnerLog : WideLogData :=
  innerPair166Data

set_option maxRecDepth 1000000 in
private theorem leaf2231LocalValidity :
    LeafFacts leaf2231Box leaf2231Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2231Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68716814336) }) = true
      norm_num [leaf2231Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2231CertificateValid :
    WideCertificateValid leaf2231Box leaf2231Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi188ValidityFacts
    leaf2231LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2231CoverageChecked :
    coverageCheck (innerAD leaf2231Box) leaf2231InnerLog = true := by
  rfl'

private theorem leaf2231InnerLogValid :
    leaf2231InnerLog.Valid 8 (innerAD leaf2231Box) :=
  wideLogDataValid_of_cachedCheck endpoint46PositiveFacts
    endpoint45PositiveFacts.valid leaf2231CoverageChecked

private noncomputable def leaf2231InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814643/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2231InputLogOnePlusV_eq :
    leaf2231InputLogOnePlusV = outerEnclosure 24
      (leaf2231Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2231RoundedFacts : LeafRoundedFacts 8
    leaf2231Certificate.logOnePlusV leaf2231InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2231InputLogOnePlusV_eq }

private noncomputable def leaf2231Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi188InputQChi innerPair166Input
    leaf2231InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2231LowerChecked :
    lowerCheck 24 leaf2231Box leaf2231Inputs = true := by
  rfl'

private theorem leaf2231CoversExact : CoversExact 8
    leaf2231Box leaf2231Certificate leaf2231InnerLog leaf2231Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi188RoundedFacts
    innerPair166RoundedFacts leaf2231RoundedFacts (by rfl)

private theorem leaf2231FlatSound : Sound leaf2231Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2231CertificateValid
    leaf2231InnerLogValid leaf2231CoversExact leaf2231LowerChecked

private noncomputable def leaf2232Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (205/64), chiLo := (25/128), chiHi := (13/64) }

private noncomputable def leaf2232Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871373/536870912) }, vSqrt := { lower := (65529/65536), upper := (45812307285/45811165184) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (871050885/536870912) }, upper := { exponent := 0, mantissa := (6761/4096) } }, logOuter := sk197LogOuterCertificate, logK := sk197LogKCertificate, logChi := chi116LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (91623472469/91622330368) } }, logDArg := sk197LogDArgCertificate }

private noncomputable def leaf2232InnerLog : WideLogData :=
  innerPair167Data

set_option maxRecDepth 1000000 in
private theorem leaf2232LocalValidity :
    LeafFacts leaf2232Box leaf2232Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2232Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (45812307285/45811165184) }) = true
      norm_num [leaf2232Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2232CertificateValid :
    WideCertificateValid leaf2232Box leaf2232Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk197ValidityFacts chi116ValidityFacts
    leaf2232LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2232CoverageChecked :
    coverageCheck (innerAD leaf2232Box) leaf2232InnerLog = true := by
  rfl'

private theorem leaf2232InnerLogValid :
    leaf2232InnerLog.Valid 8 (innerAD leaf2232Box) :=
  wideLogDataValid_of_cachedCheck endpoint46PositiveFacts
    endpoint48PositiveFacts.valid leaf2232CoverageChecked

private noncomputable def leaf2232InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814645/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2232InputLogOnePlusV_eq :
    leaf2232InputLogOnePlusV = outerEnclosure 24
      (leaf2232Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2232RoundedFacts : LeafRoundedFacts 8
    leaf2232Certificate.logOnePlusV leaf2232InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2232InputLogOnePlusV_eq }

private noncomputable def leaf2232Inputs : Inputs :=
  inputsOfCaches globalInput sk197RoundedInputs
    chi116InputQChi innerPair167Input
    leaf2232InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2232LowerChecked :
    lowerCheck 24 leaf2232Box leaf2232Inputs = true := by
  rfl'

private theorem leaf2232CoversExact : CoversExact 8
    leaf2232Box leaf2232Certificate leaf2232InnerLog leaf2232Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk197RoundedFacts chi116RoundedFacts
    innerPair167RoundedFacts leaf2232RoundedFacts (by rfl)

private theorem leaf2232FlatSound : Sound leaf2232Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2232CertificateValid
    leaf2232InnerLogValid leaf2232CoversExact leaf2232LowerChecked

private noncomputable def leaf2233Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (205/64), kHi := (103/32), chiLo := (25/128), chiHi := (13/64) }

private noncomputable def leaf2233Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871375/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433468928) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (872689183/536870912) }, upper := { exponent := 0, mantissa := (3387/2048) } }, logOuter := sk198LogOuterCertificate, logK := sk198LogKCertificate, logChi := chi116LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870390783/274866937856) } }, logDArg := sk198LogDArgCertificate }

private noncomputable def leaf2233InnerLog : WideLogData :=
  innerPair61Data

set_option maxRecDepth 1000000 in
private theorem leaf2233LocalValidity :
    LeafFacts leaf2233Box leaf2233Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2233Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433468928) }) = true
      norm_num [leaf2233Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2233CertificateValid :
    WideCertificateValid leaf2233Box leaf2233Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk198ValidityFacts chi116ValidityFacts
    leaf2233LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2233CoverageChecked :
    coverageCheck (innerAD leaf2233Box) leaf2233InnerLog = true := by
  rfl'

private theorem leaf2233InnerLogValid :
    leaf2233InnerLog.Valid 8 (innerAD leaf2233Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint48PositiveFacts.valid leaf2233CoverageChecked

private noncomputable def leaf2233InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907323/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2233InputLogOnePlusV_eq :
    leaf2233InputLogOnePlusV = outerEnclosure 24
      (leaf2233Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2233RoundedFacts : LeafRoundedFacts 8
    leaf2233Certificate.logOnePlusV leaf2233InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2233InputLogOnePlusV_eq }

private noncomputable def leaf2233Inputs : Inputs :=
  inputsOfCaches globalInput sk198RoundedInputs
    chi116InputQChi innerPair61Input
    leaf2233InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2233LowerChecked :
    lowerCheck 24 leaf2233Box leaf2233Inputs = true := by
  rfl'

private theorem leaf2233CoversExact : CoversExact 8
    leaf2233Box leaf2233Certificate leaf2233InnerLog leaf2233Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk198RoundedFacts chi116RoundedFacts
    innerPair61RoundedFacts leaf2233RoundedFacts (by rfl)

private theorem leaf2233FlatSound : Sound leaf2233Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2233CertificateValid
    leaf2233InnerLogValid leaf2233CoversExact leaf2233LowerChecked

private noncomputable def leaf2234Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (207/64), chiLo := (25/128), chiHi := (13/64) }

private noncomputable def leaf2234Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871377/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433442304) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (874327481/536870912) }, upper := { exponent := 0, mantissa := (6787/4096) } }, logOuter := sk199LogOuterCertificate, logK := sk199LogKCertificate, logChi := chi116LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870364159/274866884608) } }, logDArg := sk199LogDArgCertificate }

private noncomputable def leaf2234InnerLog : WideLogData :=
  innerPair62Data

set_option maxRecDepth 1000000 in
private theorem leaf2234LocalValidity :
    LeafFacts leaf2234Box leaf2234Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2234Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433442304) }) = true
      norm_num [leaf2234Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2234CertificateValid :
    WideCertificateValid leaf2234Box leaf2234Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk199ValidityFacts chi116ValidityFacts
    leaf2234LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2234CoverageChecked :
    coverageCheck (innerAD leaf2234Box) leaf2234InnerLog = true := by
  rfl'

private theorem leaf2234InnerLogValid :
    leaf2234InnerLog.Valid 8 (innerAD leaf2234Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint133PositiveFacts.valid leaf2234CoverageChecked

private noncomputable def leaf2234InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629293/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2234InputLogOnePlusV_eq :
    leaf2234InputLogOnePlusV = outerEnclosure 24
      (leaf2234Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2234RoundedFacts : LeafRoundedFacts 8
    leaf2234Certificate.logOnePlusV leaf2234InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2234InputLogOnePlusV_eq }

private noncomputable def leaf2234Inputs : Inputs :=
  inputsOfCaches globalInput sk199RoundedInputs
    chi116InputQChi innerPair62Input
    leaf2234InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2234LowerChecked :
    lowerCheck 24 leaf2234Box leaf2234Inputs = true := by
  rfl'

private theorem leaf2234CoversExact : CoversExact 8
    leaf2234Box leaf2234Certificate leaf2234InnerLog leaf2234Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk199RoundedFacts chi116RoundedFacts
    innerPair62RoundedFacts leaf2234RoundedFacts (by rfl)

private theorem leaf2234FlatSound : Sound leaf2234Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2234CertificateValid
    leaf2234InnerLogValid leaf2234CoversExact leaf2234LowerChecked

private noncomputable def leaf2235Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (207/64), kHi := (13/4), chiLo := (25/128), chiHi := (13/64) }

private noncomputable def leaf2235Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871379/536870912) }, vSqrt := { lower := (65529/65536), upper := (3054153819/3054075904) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (875965779/536870912) }, upper := { exponent := 0, mantissa := (425/256) } }, logOuter := sk200LogOuterCertificate, logK := sk200LogKCertificate, logChi := chi116LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (6108229723/6108151808) } }, logDArg := sk200LogDArgCertificate }

private noncomputable def leaf2235InnerLog : WideLogData :=
  innerPair62Data

set_option maxRecDepth 1000000 in
private theorem leaf2235LocalValidity :
    LeafFacts leaf2235Box leaf2235Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2235Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (3054153819/3054075904) }) = true
      norm_num [leaf2235Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2235CertificateValid :
    WideCertificateValid leaf2235Box leaf2235Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk200ValidityFacts chi116ValidityFacts
    leaf2235LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2235CoverageChecked :
    coverageCheck (innerAD leaf2235Box) leaf2235InnerLog = true := by
  rfl'

private theorem leaf2235InnerLogValid :
    leaf2235InnerLog.Valid 8 (innerAD leaf2235Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint133PositiveFacts.valid leaf2235CoverageChecked

private noncomputable def leaf2235InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629295/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2235InputLogOnePlusV_eq :
    leaf2235InputLogOnePlusV = outerEnclosure 24
      (leaf2235Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2235RoundedFacts : LeafRoundedFacts 8
    leaf2235Certificate.logOnePlusV leaf2235InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2235InputLogOnePlusV_eq }

private noncomputable def leaf2235Inputs : Inputs :=
  inputsOfCaches globalInput sk200RoundedInputs
    chi116InputQChi innerPair62Input
    leaf2235InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2235LowerChecked :
    lowerCheck 24 leaf2235Box leaf2235Inputs = true := by
  rfl'

private theorem leaf2235CoversExact : CoversExact 8
    leaf2235Box leaf2235Certificate leaf2235InnerLog leaf2235Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk200RoundedFacts chi116RoundedFacts
    innerPair62RoundedFacts leaf2235RoundedFacts (by rfl)

private theorem leaf2235FlatSound : Sound leaf2235Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2235CertificateValid
    leaf2235InnerLogValid leaf2235CoversExact leaf2235LowerChecked

private noncomputable def leaf2236Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (201/64), chiLo := (13/64), chiHi := (27/128) }

private noncomputable def leaf2236Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871367/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433396224) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (877604091/536870912) }, upper := { exponent := 0, mantissa := (13619/8192) } }, logOuter := sk193LogOuterCertificate, logK := sk193LogKCertificate, logChi := chi117LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870318079/274866792448) } }, logDArg := sk193LogDArgCertificate }

private noncomputable def leaf2236InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2236LocalValidity :
    LeafFacts leaf2236Box leaf2236Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2236Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433396224) }) = true
      norm_num [leaf2236Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2236CertificateValid :
    WideCertificateValid leaf2236Box leaf2236Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk193ValidityFacts chi117ValidityFacts
    leaf2236LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2236CoverageChecked :
    coverageCheck (innerAD leaf2236Box) leaf2236InnerLog = true := by
  rfl'

private theorem leaf2236InnerLogValid :
    leaf2236InnerLog.Valid 8 (innerAD leaf2236Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2236CoverageChecked

private noncomputable def leaf2236InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (726831/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf2236InputLogOnePlusV_eq :
    leaf2236InputLogOnePlusV = outerEnclosure 24
      (leaf2236Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2236RoundedFacts : LeafRoundedFacts 8
    leaf2236Certificate.logOnePlusV leaf2236InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2236InputLogOnePlusV_eq }

private noncomputable def leaf2236Inputs : Inputs :=
  inputsOfCaches globalInput sk193RoundedInputs
    chi117InputQChi innerPair56Input
    leaf2236InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2236LowerChecked :
    lowerCheck 24 leaf2236Box leaf2236Inputs = true := by
  rfl'

private theorem leaf2236CoversExact : CoversExact 8
    leaf2236Box leaf2236Certificate leaf2236InnerLog leaf2236Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk193RoundedFacts chi117RoundedFacts
    innerPair56RoundedFacts leaf2236RoundedFacts (by rfl)

private theorem leaf2236FlatSound : Sound leaf2236Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2236CertificateValid
    leaf2236InnerLogValid leaf2236CoversExact leaf2236LowerChecked

private noncomputable def leaf2237Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (201/64), kHi := (101/32), chiLo := (13/64), chiHi := (27/128) }

private noncomputable def leaf2237Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871369/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433368576) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (879307921/536870912) }, upper := { exponent := 0, mantissa := (6823/4096) } }, logOuter := sk194LogOuterCertificate, logK := sk194LogKCertificate, logChi := chi117LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870290431/274866737152) } }, logDArg := sk194LogDArgCertificate }

private noncomputable def leaf2237InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2237LocalValidity :
    LeafFacts leaf2237Box leaf2237Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2237Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433368576) }) = true
      norm_num [leaf2237Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2237CertificateValid :
    WideCertificateValid leaf2237Box leaf2237Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk194ValidityFacts chi117ValidityFacts
    leaf2237LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2237CoverageChecked :
    coverageCheck (innerAD leaf2237Box) leaf2237InnerLog = true := by
  rfl'

private theorem leaf2237InnerLogValid :
    leaf2237InnerLog.Valid 8 (innerAD leaf2237Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2237CoverageChecked

private noncomputable def leaf2237InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814649/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2237InputLogOnePlusV_eq :
    leaf2237InputLogOnePlusV = outerEnclosure 24
      (leaf2237Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2237RoundedFacts : LeafRoundedFacts 8
    leaf2237Certificate.logOnePlusV leaf2237InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2237InputLogOnePlusV_eq }

private noncomputable def leaf2237Inputs : Inputs :=
  inputsOfCaches globalInput sk194RoundedInputs
    chi117InputQChi innerPair56Input
    leaf2237InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2237LowerChecked :
    lowerCheck 24 leaf2237Box leaf2237Inputs = true := by
  rfl'

private theorem leaf2237CoversExact : CoversExact 8
    leaf2237Box leaf2237Certificate leaf2237InnerLog leaf2237Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk194RoundedFacts chi117RoundedFacts
    innerPair56RoundedFacts leaf2237RoundedFacts (by rfl)

private theorem leaf2237FlatSound : Sound leaf2237Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2237CertificateValid
    leaf2237InnerLogValid leaf2237CoversExact leaf2237LowerChecked

private noncomputable def leaf2238Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (201/64), chiLo := (27/128), chiHi := (7/32) }

private noncomputable def leaf2238Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871369/536870912) }, vSqrt := { lower := (65529/65536), upper := (27487384371/27486638080) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (890710489/536870912) }, upper := { exponent := 0, mantissa := (3455/2048) } }, logOuter := sk193LogOuterCertificate, logK := sk193LogKCertificate, logChi := chi118LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (54974022451/54973276160) } }, logDArg := sk193LogDArgCertificate }

private noncomputable def leaf2238InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2238LocalValidity :
    LeafFacts leaf2238Box leaf2238Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2238Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (27487384371/27486638080) }) = true
      norm_num [leaf2238Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2238CertificateValid :
    WideCertificateValid leaf2238Box leaf2238Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk193ValidityFacts chi118ValidityFacts
    leaf2238LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2238CoverageChecked :
    coverageCheck (innerAD leaf2238Box) leaf2238InnerLog = true := by
  rfl'

private theorem leaf2238InnerLogValid :
    leaf2238InnerLog.Valid 8 (innerAD leaf2238Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2238CoverageChecked

private noncomputable def leaf2238InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629309/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2238InputLogOnePlusV_eq :
    leaf2238InputLogOnePlusV = outerEnclosure 24
      (leaf2238Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2238RoundedFacts : LeafRoundedFacts 8
    leaf2238Certificate.logOnePlusV leaf2238InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2238InputLogOnePlusV_eq }

private noncomputable def leaf2238Inputs : Inputs :=
  inputsOfCaches globalInput sk193RoundedInputs
    chi118InputQChi innerPair56Input
    leaf2238InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2238LowerChecked :
    lowerCheck 24 leaf2238Box leaf2238Inputs = true := by
  rfl'

private theorem leaf2238CoversExact : CoversExact 8
    leaf2238Box leaf2238Certificate leaf2238InnerLog leaf2238Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk193RoundedFacts chi118RoundedFacts
    innerPair56RoundedFacts leaf2238RoundedFacts (by rfl)

private theorem leaf2238FlatSound : Sound leaf2238Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2238CertificateValid
    leaf2238InnerLogValid leaf2238CoversExact leaf2238LowerChecked

private noncomputable def leaf2239Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (201/64), kHi := (101/32), chiLo := (27/128), chiHi := (7/32) }

private noncomputable def leaf2239Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871371/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433161728) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (892479851/536870912) }, upper := { exponent := 0, mantissa := (1731/1024) } }, logOuter := sk194LogOuterCertificate, logK := sk194LogKCertificate, logChi := chi118LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870083583/274866323456) } }, logDArg := sk194LogDArgCertificate }

private noncomputable def leaf2239InnerLog : WideLogData :=
  innerPair173Data

set_option maxRecDepth 1000000 in
private theorem leaf2239LocalValidity :
    LeafFacts leaf2239Box leaf2239Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2239Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433161728) }) = true
      norm_num [leaf2239Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2239CertificateValid :
    WideCertificateValid leaf2239Box leaf2239Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk194ValidityFacts chi118ValidityFacts
    leaf2239LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2239CoverageChecked :
    coverageCheck (innerAD leaf2239Box) leaf2239InnerLog = true := by
  rfl'

private theorem leaf2239InnerLogValid :
    leaf2239InnerLog.Valid 8 (innerAD leaf2239Box) :=
  wideLogDataValid_of_cachedCheck endpoint48PositiveFacts
    endpoint20PositiveFacts.valid leaf2239CoverageChecked

private noncomputable def leaf2239InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814655/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2239InputLogOnePlusV_eq :
    leaf2239InputLogOnePlusV = outerEnclosure 24
      (leaf2239Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2239RoundedFacts : LeafRoundedFacts 8
    leaf2239Certificate.logOnePlusV leaf2239InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2239InputLogOnePlusV_eq }

private noncomputable def leaf2239Inputs : Inputs :=
  inputsOfCaches globalInput sk194RoundedInputs
    chi118InputQChi innerPair173Input
    leaf2239InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2239LowerChecked :
    lowerCheck 24 leaf2239Box leaf2239Inputs = true := by
  rfl'

private theorem leaf2239CoversExact : CoversExact 8
    leaf2239Box leaf2239Certificate leaf2239InnerLog leaf2239Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk194RoundedFacts chi118RoundedFacts
    innerPair173RoundedFacts leaf2239RoundedFacts (by rfl)

private theorem leaf2239FlatSound : Sound leaf2239Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2239CertificateValid
    leaf2239InnerLogValid leaf2239CoversExact leaf2239LowerChecked

private noncomputable def leaf2240Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (203/64), chiLo := (13/64), chiHi := (27/128) }

private noncomputable def leaf2240Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871371/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433340928) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (881011751/536870912) }, upper := { exponent := 0, mantissa := (13673/8192) } }, logOuter := sk195LogOuterCertificate, logK := sk195LogKCertificate, logChi := chi117LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870262783/274866681856) } }, logDArg := sk195LogDArgCertificate }

private noncomputable def leaf2240InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2240LocalValidity :
    LeafFacts leaf2240Box leaf2240Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2240Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433340928) }) = true
      norm_num [leaf2240Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2240CertificateValid :
    WideCertificateValid leaf2240Box leaf2240Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk195ValidityFacts chi117ValidityFacts
    leaf2240LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2240CoverageChecked :
    coverageCheck (innerAD leaf2240Box) leaf2240InnerLog = true := by
  rfl'

private theorem leaf2240InnerLogValid :
    leaf2240InnerLog.Valid 8 (innerAD leaf2240Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2240CoverageChecked

private noncomputable def leaf2240InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629299/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2240InputLogOnePlusV_eq :
    leaf2240InputLogOnePlusV = outerEnclosure 24
      (leaf2240Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2240RoundedFacts : LeafRoundedFacts 8
    leaf2240Certificate.logOnePlusV leaf2240InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2240InputLogOnePlusV_eq }

private noncomputable def leaf2240Inputs : Inputs :=
  inputsOfCaches globalInput sk195RoundedInputs
    chi117InputQChi innerPair56Input
    leaf2240InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2240LowerChecked :
    lowerCheck 24 leaf2240Box leaf2240Inputs = true := by
  rfl'

private theorem leaf2240CoversExact : CoversExact 8
    leaf2240Box leaf2240Certificate leaf2240InnerLog leaf2240Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk195RoundedFacts chi117RoundedFacts
    innerPair56RoundedFacts leaf2240RoundedFacts (by rfl)

private theorem leaf2240FlatSound : Sound leaf2240Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2240CertificateValid
    leaf2240InnerLogValid leaf2240CoversExact leaf2240LowerChecked

private noncomputable def leaf2241Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (203/64), kHi := (51/16), chiLo := (13/64), chiHi := (27/128) }

private noncomputable def leaf2241Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871373/536870912) }, vSqrt := { lower := (65529/65536), upper := (27487384371/27486662656) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (882715581/536870912) }, upper := { exponent := 0, mantissa := (3425/2048) } }, logOuter := sk196LogOuterCertificate, logK := sk196LogKCertificate, logChi := chi117LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (54974047027/54973325312) } }, logDArg := sk196LogDArgCertificate }

private noncomputable def leaf2241InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2241LocalValidity :
    LeafFacts leaf2241Box leaf2241Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2241Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (27487384371/27486662656) }) = true
      norm_num [leaf2241Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2241CertificateValid :
    WideCertificateValid leaf2241Box leaf2241Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk196ValidityFacts chi117ValidityFacts
    leaf2241LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2241CoverageChecked :
    coverageCheck (innerAD leaf2241Box) leaf2241InnerLog = true := by
  rfl'

private theorem leaf2241InnerLogValid :
    leaf2241InnerLog.Valid 8 (innerAD leaf2241Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2241CoverageChecked

private noncomputable def leaf2241InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629301/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2241InputLogOnePlusV_eq :
    leaf2241InputLogOnePlusV = outerEnclosure 24
      (leaf2241Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2241RoundedFacts : LeafRoundedFacts 8
    leaf2241Certificate.logOnePlusV leaf2241InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2241InputLogOnePlusV_eq }

private noncomputable def leaf2241Inputs : Inputs :=
  inputsOfCaches globalInput sk196RoundedInputs
    chi117InputQChi innerPair56Input
    leaf2241InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2241LowerChecked :
    lowerCheck 24 leaf2241Box leaf2241Inputs = true := by
  rfl'

private theorem leaf2241CoversExact : CoversExact 8
    leaf2241Box leaf2241Certificate leaf2241InnerLog leaf2241Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk196RoundedFacts chi117RoundedFacts
    innerPair56RoundedFacts leaf2241RoundedFacts (by rfl)

private theorem leaf2241FlatSound : Sound leaf2241Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2241CertificateValid
    leaf2241InnerLogValid leaf2241CoversExact leaf2241LowerChecked

private noncomputable def leaf2242Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (203/64), chiLo := (27/128), chiHi := (7/32) }

private noncomputable def leaf2242Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871373/536870912) }, vSqrt := { lower := (65529/65536), upper := (45812307285/45811044352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (894249213/536870912) }, upper := { exponent := 0, mantissa := (3469/2048) } }, logOuter := sk195LogOuterCertificate, logK := sk195LogKCertificate, logChi := chi118LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (91623351637/91622088704) } }, logDArg := sk195LogDArgCertificate }

private noncomputable def leaf2242InnerLog : WideLogData :=
  innerPair173Data

set_option maxRecDepth 1000000 in
private theorem leaf2242LocalValidity :
    LeafFacts leaf2242Box leaf2242Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2242Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (45812307285/45811044352) }) = true
      norm_num [leaf2242Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2242CertificateValid :
    WideCertificateValid leaf2242Box leaf2242Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk195ValidityFacts chi118ValidityFacts
    leaf2242LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2242CoverageChecked :
    coverageCheck (innerAD leaf2242Box) leaf2242InnerLog = true := by
  rfl'

private theorem leaf2242InnerLogValid :
    leaf2242InnerLog.Valid 8 (innerAD leaf2242Box) :=
  wideLogDataValid_of_cachedCheck endpoint48PositiveFacts
    endpoint20PositiveFacts.valid leaf2242CoverageChecked

private noncomputable def leaf2242InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (45427/65536) }

set_option maxRecDepth 1000000 in
private theorem leaf2242InputLogOnePlusV_eq :
    leaf2242InputLogOnePlusV = outerEnclosure 24
      (leaf2242Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2242RoundedFacts : LeafRoundedFacts 8
    leaf2242Certificate.logOnePlusV leaf2242InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2242InputLogOnePlusV_eq }

private noncomputable def leaf2242Inputs : Inputs :=
  inputsOfCaches globalInput sk195RoundedInputs
    chi118InputQChi innerPair173Input
    leaf2242InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2242LowerChecked :
    lowerCheck 24 leaf2242Box leaf2242Inputs = true := by
  rfl'

private theorem leaf2242CoversExact : CoversExact 8
    leaf2242Box leaf2242Certificate leaf2242InnerLog leaf2242Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk195RoundedFacts chi118RoundedFacts
    innerPair173RoundedFacts leaf2242RoundedFacts (by rfl)

private theorem leaf2242FlatSound : Sound leaf2242Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2242CertificateValid
    leaf2242InnerLogValid leaf2242CoversExact leaf2242LowerChecked

private noncomputable def leaf2243Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (203/64), kHi := (51/16), chiLo := (27/128), chiHi := (7/32) }

private noncomputable def leaf2243Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871375/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433104384) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (896018575/536870912) }, upper := { exponent := 0, mantissa := (869/512) } }, logOuter := sk196LogOuterCertificate, logK := sk196LogKCertificate, logChi := chi118LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870026239/274866208768) } }, logDArg := sk196LogDArgCertificate }

private noncomputable def leaf2243InnerLog : WideLogData :=
  innerPair173Data

set_option maxRecDepth 1000000 in
private theorem leaf2243LocalValidity :
    LeafFacts leaf2243Box leaf2243Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2243Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433104384) }) = true
      norm_num [leaf2243Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2243CertificateValid :
    WideCertificateValid leaf2243Box leaf2243Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk196ValidityFacts chi118ValidityFacts
    leaf2243LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2243CoverageChecked :
    coverageCheck (innerAD leaf2243Box) leaf2243InnerLog = true := by
  rfl'

private theorem leaf2243InnerLogValid :
    leaf2243InnerLog.Valid 8 (innerAD leaf2243Box) :=
  wideLogDataValid_of_cachedCheck endpoint48PositiveFacts
    endpoint20PositiveFacts.valid leaf2243CoverageChecked

private noncomputable def leaf2243InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814657/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2243InputLogOnePlusV_eq :
    leaf2243InputLogOnePlusV = outerEnclosure 24
      (leaf2243Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2243RoundedFacts : LeafRoundedFacts 8
    leaf2243Certificate.logOnePlusV leaf2243InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2243InputLogOnePlusV_eq }

private noncomputable def leaf2243Inputs : Inputs :=
  inputsOfCaches globalInput sk196RoundedInputs
    chi118InputQChi innerPair173Input
    leaf2243InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2243LowerChecked :
    lowerCheck 24 leaf2243Box leaf2243Inputs = true := by
  rfl'

private theorem leaf2243CoversExact : CoversExact 8
    leaf2243Box leaf2243Certificate leaf2243InnerLog leaf2243Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk196RoundedFacts chi118RoundedFacts
    innerPair173RoundedFacts leaf2243RoundedFacts (by rfl)

private theorem leaf2243FlatSound : Sound leaf2243Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2243CertificateValid
    leaf2243InnerLogValid leaf2243CoversExact leaf2243LowerChecked

private noncomputable def leaf2244Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (205/64), chiLo := (13/64), chiHi := (27/128) }

private noncomputable def leaf2244Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871375/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433285632) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (884419411/536870912) }, upper := { exponent := 0, mantissa := (13727/8192) } }, logOuter := sk197LogOuterCertificate, logK := sk197LogKCertificate, logChi := chi117LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870207487/274866571264) } }, logDArg := sk197LogDArgCertificate }

private noncomputable def leaf2244InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2244LocalValidity :
    LeafFacts leaf2244Box leaf2244Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2244Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433285632) }) = true
      norm_num [leaf2244Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2244CertificateValid :
    WideCertificateValid leaf2244Box leaf2244Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk197ValidityFacts chi117ValidityFacts
    leaf2244LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2244CoverageChecked :
    coverageCheck (innerAD leaf2244Box) leaf2244InnerLog = true := by
  rfl'

private theorem leaf2244InnerLogValid :
    leaf2244InnerLog.Valid 8 (innerAD leaf2244Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2244CoverageChecked

private noncomputable def leaf2244InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629303/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2244InputLogOnePlusV_eq :
    leaf2244InputLogOnePlusV = outerEnclosure 24
      (leaf2244Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2244RoundedFacts : LeafRoundedFacts 8
    leaf2244Certificate.logOnePlusV leaf2244InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2244InputLogOnePlusV_eq }

private noncomputable def leaf2244Inputs : Inputs :=
  inputsOfCaches globalInput sk197RoundedInputs
    chi117InputQChi innerPair56Input
    leaf2244InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2244LowerChecked :
    lowerCheck 24 leaf2244Box leaf2244Inputs = true := by
  rfl'

private theorem leaf2244CoversExact : CoversExact 8
    leaf2244Box leaf2244Certificate leaf2244InnerLog leaf2244Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk197RoundedFacts chi117RoundedFacts
    innerPair56RoundedFacts leaf2244RoundedFacts (by rfl)

private theorem leaf2244FlatSound : Sound leaf2244Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2244CertificateValid
    leaf2244InnerLogValid leaf2244CoversExact leaf2244LowerChecked

private noncomputable def leaf2245Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (205/64), kHi := (103/32), chiLo := (13/64), chiHi := (27/128) }

private noncomputable def leaf2245Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871377/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433257984) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (886123241/536870912) }, upper := { exponent := 0, mantissa := (6877/4096) } }, logOuter := sk198LogOuterCertificate, logK := sk198LogKCertificate, logChi := chi117LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870179839/274866515968) } }, logDArg := sk198LogDArgCertificate }

private noncomputable def leaf2245InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2245LocalValidity :
    LeafFacts leaf2245Box leaf2245Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2245Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433257984) }) = true
      norm_num [leaf2245Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2245CertificateValid :
    WideCertificateValid leaf2245Box leaf2245Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk198ValidityFacts chi117ValidityFacts
    leaf2245LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2245CoverageChecked :
    coverageCheck (innerAD leaf2245Box) leaf2245InnerLog = true := by
  rfl'

private theorem leaf2245InnerLogValid :
    leaf2245InnerLog.Valid 8 (innerAD leaf2245Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2245CoverageChecked

private noncomputable def leaf2245InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453663/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf2245InputLogOnePlusV_eq :
    leaf2245InputLogOnePlusV = outerEnclosure 24
      (leaf2245Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2245RoundedFacts : LeafRoundedFacts 8
    leaf2245Certificate.logOnePlusV leaf2245InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2245InputLogOnePlusV_eq }

private noncomputable def leaf2245Inputs : Inputs :=
  inputsOfCaches globalInput sk198RoundedInputs
    chi117InputQChi innerPair56Input
    leaf2245InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2245LowerChecked :
    lowerCheck 24 leaf2245Box leaf2245Inputs = true := by
  rfl'

private theorem leaf2245CoversExact : CoversExact 8
    leaf2245Box leaf2245Certificate leaf2245InnerLog leaf2245Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk198RoundedFacts chi117RoundedFacts
    innerPair56RoundedFacts leaf2245RoundedFacts (by rfl)

private theorem leaf2245FlatSound : Sound leaf2245Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2245CertificateValid
    leaf2245InnerLogValid leaf2245CoversExact leaf2245LowerChecked

private noncomputable def leaf2246Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (207/64), chiLo := (13/64), chiHi := (27/128) }

private noncomputable def leaf2246Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871379/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433230336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (887827071/536870912) }, upper := { exponent := 0, mantissa := (13781/8192) } }, logOuter := sk199LogOuterCertificate, logK := sk199LogKCertificate, logChi := chi117LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870152191/274866460672) } }, logDArg := sk199LogDArgCertificate }

private noncomputable def leaf2246InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2246LocalValidity :
    LeafFacts leaf2246Box leaf2246Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2246Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433230336) }) = true
      norm_num [leaf2246Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2246CertificateValid :
    WideCertificateValid leaf2246Box leaf2246Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk199ValidityFacts chi117ValidityFacts
    leaf2246LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2246CoverageChecked :
    coverageCheck (innerAD leaf2246Box) leaf2246InnerLog = true := by
  rfl'

private theorem leaf2246InnerLogValid :
    leaf2246InnerLog.Valid 8 (innerAD leaf2246Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2246CoverageChecked

private noncomputable def leaf2246InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814653/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2246InputLogOnePlusV_eq :
    leaf2246InputLogOnePlusV = outerEnclosure 24
      (leaf2246Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2246RoundedFacts : LeafRoundedFacts 8
    leaf2246Certificate.logOnePlusV leaf2246InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2246InputLogOnePlusV_eq }

private noncomputable def leaf2246Inputs : Inputs :=
  inputsOfCaches globalInput sk199RoundedInputs
    chi117InputQChi innerPair56Input
    leaf2246InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2246LowerChecked :
    lowerCheck 24 leaf2246Box leaf2246Inputs = true := by
  rfl'

private theorem leaf2246CoversExact : CoversExact 8
    leaf2246Box leaf2246Certificate leaf2246InnerLog leaf2246Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk199RoundedFacts chi117RoundedFacts
    innerPair56RoundedFacts leaf2246RoundedFacts (by rfl)

private theorem leaf2246FlatSound : Sound leaf2246Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2246CertificateValid
    leaf2246InnerLogValid leaf2246CoversExact leaf2246LowerChecked

private noncomputable def leaf2247Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (207/64), kHi := (13/4), chiLo := (13/64), chiHi := (27/128) }

private noncomputable def leaf2247Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871381/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433202688) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (889530901/536870912) }, upper := { exponent := 0, mantissa := (863/512) } }, logOuter := sk200LogOuterCertificate, logK := sk200LogKCertificate, logChi := chi117LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870124543/274866405376) } }, logDArg := sk200LogDArgCertificate }

private noncomputable def leaf2247InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2247LocalValidity :
    LeafFacts leaf2247Box leaf2247Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2247Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433202688) }) = true
      norm_num [leaf2247Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2247CertificateValid :
    WideCertificateValid leaf2247Box leaf2247Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk200ValidityFacts chi117ValidityFacts
    leaf2247LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2247CoverageChecked :
    coverageCheck (innerAD leaf2247Box) leaf2247InnerLog = true := by
  rfl'

private theorem leaf2247InnerLogValid :
    leaf2247InnerLog.Valid 8 (innerAD leaf2247Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2247CoverageChecked

private noncomputable def leaf2247InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907327/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2247InputLogOnePlusV_eq :
    leaf2247InputLogOnePlusV = outerEnclosure 24
      (leaf2247Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2247RoundedFacts : LeafRoundedFacts 8
    leaf2247Certificate.logOnePlusV leaf2247InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2247InputLogOnePlusV_eq }

private noncomputable def leaf2247Inputs : Inputs :=
  inputsOfCaches globalInput sk200RoundedInputs
    chi117InputQChi innerPair56Input
    leaf2247InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2247LowerChecked :
    lowerCheck 24 leaf2247Box leaf2247Inputs = true := by
  rfl'

private theorem leaf2247CoversExact : CoversExact 8
    leaf2247Box leaf2247Certificate leaf2247InnerLog leaf2247Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk200RoundedFacts chi117RoundedFacts
    innerPair56RoundedFacts leaf2247RoundedFacts (by rfl)

private theorem leaf2247FlatSound : Sound leaf2247Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2247CertificateValid
    leaf2247InnerLogValid leaf2247CoversExact leaf2247LowerChecked

private noncomputable def leaf2248Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (205/64), chiLo := (27/128), chiHi := (7/32) }

private noncomputable def leaf2248Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871377/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433075712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (897787937/536870912) }, upper := { exponent := 0, mantissa := (3483/2048) } }, logOuter := sk197LogOuterCertificate, logK := sk197LogKCertificate, logChi := chi118LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869997567/274866151424) } }, logDArg := sk197LogDArgCertificate }

private noncomputable def leaf2248InnerLog : WideLogData :=
  innerPair420Data

set_option maxRecDepth 1000000 in
private theorem leaf2248LocalValidity :
    LeafFacts leaf2248Box leaf2248Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2248Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433075712) }) = true
      norm_num [leaf2248Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2248CertificateValid :
    WideCertificateValid leaf2248Box leaf2248Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk197ValidityFacts chi118ValidityFacts
    leaf2248LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2248CoverageChecked :
    coverageCheck (innerAD leaf2248Box) leaf2248InnerLog = true := by
  rfl'

private theorem leaf2248InnerLogValid :
    leaf2248InnerLog.Valid 8 (innerAD leaf2248Box) :=
  wideLogDataValid_of_cachedCheck endpoint133PositiveFacts
    endpoint20PositiveFacts.valid leaf2248CoverageChecked

private noncomputable def leaf2248InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907329/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2248InputLogOnePlusV_eq :
    leaf2248InputLogOnePlusV = outerEnclosure 24
      (leaf2248Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2248RoundedFacts : LeafRoundedFacts 8
    leaf2248Certificate.logOnePlusV leaf2248InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2248InputLogOnePlusV_eq }

private noncomputable def leaf2248Inputs : Inputs :=
  inputsOfCaches globalInput sk197RoundedInputs
    chi118InputQChi innerPair420Input
    leaf2248InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2248LowerChecked :
    lowerCheck 24 leaf2248Box leaf2248Inputs = true := by
  rfl'

private theorem leaf2248CoversExact : CoversExact 8
    leaf2248Box leaf2248Certificate leaf2248InnerLog leaf2248Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk197RoundedFacts chi118RoundedFacts
    innerPair420RoundedFacts leaf2248RoundedFacts (by rfl)

private theorem leaf2248FlatSound : Sound leaf2248Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2248CertificateValid
    leaf2248InnerLogValid leaf2248CoversExact leaf2248LowerChecked

private noncomputable def leaf2249Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (205/64), kHi := (103/32), chiLo := (27/128), chiHi := (7/32) }

private noncomputable def leaf2249Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871379/536870912) }, vSqrt := { lower := (65529/65536), upper := (3054153819/3054067712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (899557299/536870912) }, upper := { exponent := 0, mantissa := (1745/1024) } }, logOuter := sk198LogOuterCertificate, logK := sk198LogKCertificate, logChi := chi118LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (6108221531/6108135424) } }, logDArg := sk198LogDArgCertificate }

private noncomputable def leaf2249InnerLog : WideLogData :=
  innerPair421Data

set_option maxRecDepth 1000000 in
private theorem leaf2249LocalValidity :
    LeafFacts leaf2249Box leaf2249Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2249Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (3054153819/3054067712) }) = true
      norm_num [leaf2249Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2249CertificateValid :
    WideCertificateValid leaf2249Box leaf2249Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk198ValidityFacts chi118ValidityFacts
    leaf2249LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2249CoverageChecked :
    coverageCheck (innerAD leaf2249Box) leaf2249InnerLog = true := by
  rfl'

private theorem leaf2249InnerLogValid :
    leaf2249InnerLog.Valid 8 (innerAD leaf2249Box) :=
  wideLogDataValid_of_cachedCheck endpoint133PositiveFacts
    endpoint62PositiveFacts.valid leaf2249CoverageChecked

private noncomputable def leaf2249InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629317/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2249InputLogOnePlusV_eq :
    leaf2249InputLogOnePlusV = outerEnclosure 24
      (leaf2249Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2249RoundedFacts : LeafRoundedFacts 8
    leaf2249Certificate.logOnePlusV leaf2249InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2249InputLogOnePlusV_eq }

private noncomputable def leaf2249Inputs : Inputs :=
  inputsOfCaches globalInput sk198RoundedInputs
    chi118InputQChi innerPair421Input
    leaf2249InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2249LowerChecked :
    lowerCheck 24 leaf2249Box leaf2249Inputs = true := by
  rfl'

private theorem leaf2249CoversExact : CoversExact 8
    leaf2249Box leaf2249Certificate leaf2249InnerLog leaf2249Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk198RoundedFacts chi118RoundedFacts
    innerPair421RoundedFacts leaf2249RoundedFacts (by rfl)

private theorem leaf2249FlatSound : Sound leaf2249Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2249CertificateValid
    leaf2249InnerLogValid leaf2249CoversExact leaf2249LowerChecked

private noncomputable def leaf2250Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (207/64), chiLo := (27/128), chiHi := (7/32) }

private noncomputable def leaf2250Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871381/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433018368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (901326661/536870912) }, upper := { exponent := 0, mantissa := (3497/2048) } }, logOuter := sk199LogOuterCertificate, logK := sk199LogKCertificate, logChi := chi118LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869940223/274866036736) } }, logDArg := sk199LogDArgCertificate }

private noncomputable def leaf2250InnerLog : WideLogData :=
  innerPair421Data

set_option maxRecDepth 1000000 in
private theorem leaf2250LocalValidity :
    LeafFacts leaf2250Box leaf2250Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2250Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433018368) }) = true
      norm_num [leaf2250Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2250CertificateValid :
    WideCertificateValid leaf2250Box leaf2250Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk199ValidityFacts chi118ValidityFacts
    leaf2250LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2250CoverageChecked :
    coverageCheck (innerAD leaf2250Box) leaf2250InnerLog = true := by
  rfl'

private theorem leaf2250InnerLogValid :
    leaf2250InnerLog.Valid 8 (innerAD leaf2250Box) :=
  wideLogDataValid_of_cachedCheck endpoint133PositiveFacts
    endpoint62PositiveFacts.valid leaf2250CoverageChecked

private noncomputable def leaf2250InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629319/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2250InputLogOnePlusV_eq :
    leaf2250InputLogOnePlusV = outerEnclosure 24
      (leaf2250Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2250RoundedFacts : LeafRoundedFacts 8
    leaf2250Certificate.logOnePlusV leaf2250InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2250InputLogOnePlusV_eq }

private noncomputable def leaf2250Inputs : Inputs :=
  inputsOfCaches globalInput sk199RoundedInputs
    chi118InputQChi innerPair421Input
    leaf2250InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2250LowerChecked :
    lowerCheck 24 leaf2250Box leaf2250Inputs = true := by
  rfl'

private theorem leaf2250CoversExact : CoversExact 8
    leaf2250Box leaf2250Certificate leaf2250InnerLog leaf2250Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk199RoundedFacts chi118RoundedFacts
    innerPair421RoundedFacts leaf2250RoundedFacts (by rfl)

private theorem leaf2250FlatSound : Sound leaf2250Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2250CertificateValid
    leaf2250InnerLogValid leaf2250CoversExact leaf2250LowerChecked

private noncomputable def leaf2251Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (207/64), kHi := (13/4), chiLo := (27/128), chiHi := (7/32) }

private noncomputable def leaf2251Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871383/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432989696) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (903096023/536870912) }, upper := { exponent := 0, mantissa := (219/128) } }, logOuter := sk200LogOuterCertificate, logK := sk200LogKCertificate, logChi := chi118LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869911551/274865979392) } }, logDArg := sk200LogDArgCertificate }

private noncomputable def leaf2251InnerLog : WideLogData :=
  innerPair421Data

set_option maxRecDepth 1000000 in
private theorem leaf2251LocalValidity :
    LeafFacts leaf2251Box leaf2251Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2251Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432989696) }) = true
      norm_num [leaf2251Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2251CertificateValid :
    WideCertificateValid leaf2251Box leaf2251Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk200ValidityFacts chi118ValidityFacts
    leaf2251LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2251CoverageChecked :
    coverageCheck (innerAD leaf2251Box) leaf2251InnerLog = true := by
  rfl'

private theorem leaf2251InnerLogValid :
    leaf2251InnerLog.Valid 8 (innerAD leaf2251Box) :=
  wideLogDataValid_of_cachedCheck endpoint133PositiveFacts
    endpoint62PositiveFacts.valid leaf2251CoverageChecked

private noncomputable def leaf2251InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629321/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2251InputLogOnePlusV_eq :
    leaf2251InputLogOnePlusV = outerEnclosure 24
      (leaf2251Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2251RoundedFacts : LeafRoundedFacts 8
    leaf2251Certificate.logOnePlusV leaf2251InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2251InputLogOnePlusV_eq }

private noncomputable def leaf2251Inputs : Inputs :=
  inputsOfCaches globalInput sk200RoundedInputs
    chi118InputQChi innerPair421Input
    leaf2251InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2251LowerChecked :
    lowerCheck 24 leaf2251Box leaf2251Inputs = true := by
  rfl'

private theorem leaf2251CoversExact : CoversExact 8
    leaf2251Box leaf2251Certificate leaf2251InnerLog leaf2251Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk200RoundedFacts chi118RoundedFacts
    innerPair421RoundedFacts leaf2251RoundedFacts (by rfl)

private theorem leaf2251FlatSound : Sound leaf2251Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2251CertificateValid
    leaf2251InnerLogValid leaf2251CoversExact leaf2251LowerChecked

private noncomputable def component48Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (3/16), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component48Node0_sound : Sound component48Node0Box :=
  sound_of_literal_split component48Node0Box leaf2188Box leaf2189Box
    .k (193/64) (by rfl) (by rfl)
    leaf2188FlatSound leaf2189FlatSound

private noncomputable def component48Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (3/16), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component48Node1_sound : Sound component48Node1Box :=
  sound_of_literal_split component48Node1Box leaf2190Box leaf2191Box
    .k (195/64) (by rfl) (by rfl)
    leaf2190FlatSound leaf2191FlatSound

private noncomputable def component48Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (3/16), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component48Node2_sound : Sound component48Node2Box :=
  sound_of_literal_split component48Node2Box component48Node0Box component48Node1Box
    .k (97/32) (by rfl) (by rfl)
    component48Node0_sound component48Node1_sound

private noncomputable def component48Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (25/128), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component48Node3_sound : Sound component48Node3Box :=
  sound_of_literal_split component48Node3Box leaf2192Box leaf2193Box
    .k (193/64) (by rfl) (by rfl)
    leaf2192FlatSound leaf2193FlatSound

private noncomputable def component48Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (25/128), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component48Node4_sound : Sound component48Node4Box :=
  sound_of_literal_split component48Node4Box leaf2194Box leaf2195Box
    .k (195/64) (by rfl) (by rfl)
    leaf2194FlatSound leaf2195FlatSound

private noncomputable def component48Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (25/128), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component48Node5_sound : Sound component48Node5Box :=
  sound_of_literal_split component48Node5Box component48Node3Box component48Node4Box
    .k (97/32) (by rfl) (by rfl)
    component48Node3_sound component48Node4_sound

private noncomputable def component48Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (3/16), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component48Node6_sound : Sound component48Node6Box :=
  sound_of_literal_split component48Node6Box component48Node2Box component48Node5Box
    .chi (25/128) (by rfl) (by rfl)
    component48Node2_sound component48Node5_sound

private noncomputable def component48Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (3/16), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component48Node7_sound : Sound component48Node7Box :=
  sound_of_literal_split component48Node7Box leaf2196Box leaf2197Box
    .k (197/64) (by rfl) (by rfl)
    leaf2196FlatSound leaf2197FlatSound

private noncomputable def component48Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (3/16), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component48Node8_sound : Sound component48Node8Box :=
  sound_of_literal_split component48Node8Box leaf2198Box leaf2199Box
    .k (199/64) (by rfl) (by rfl)
    leaf2198FlatSound leaf2199FlatSound

private noncomputable def component48Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (3/16), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component48Node9_sound : Sound component48Node9Box :=
  sound_of_literal_split component48Node9Box component48Node7Box component48Node8Box
    .k (99/32) (by rfl) (by rfl)
    component48Node7_sound component48Node8_sound

private noncomputable def component48Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (25/128), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component48Node10_sound : Sound component48Node10Box :=
  sound_of_literal_split component48Node10Box leaf2200Box leaf2201Box
    .k (197/64) (by rfl) (by rfl)
    leaf2200FlatSound leaf2201FlatSound

private noncomputable def component48Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (25/128), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component48Node11_sound : Sound component48Node11Box :=
  sound_of_literal_split component48Node11Box leaf2202Box leaf2203Box
    .k (199/64) (by rfl) (by rfl)
    leaf2202FlatSound leaf2203FlatSound

private noncomputable def component48Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (25/128), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component48Node12_sound : Sound component48Node12Box :=
  sound_of_literal_split component48Node12Box component48Node10Box component48Node11Box
    .k (99/32) (by rfl) (by rfl)
    component48Node10_sound component48Node11_sound

private noncomputable def component48Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (3/16), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component48Node13_sound : Sound component48Node13Box :=
  sound_of_literal_split component48Node13Box component48Node9Box component48Node12Box
    .chi (25/128) (by rfl) (by rfl)
    component48Node9_sound component48Node12_sound

private noncomputable def component48Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (3/16), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component48Node14_sound : Sound component48Node14Box :=
  sound_of_literal_split component48Node14Box component48Node6Box component48Node13Box
    .k (49/16) (by rfl) (by rfl)
    component48Node6_sound component48Node13_sound

private noncomputable def component48Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (13/64), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component48Node15_sound : Sound component48Node15Box :=
  sound_of_literal_split component48Node15Box leaf2204Box leaf2205Box
    .k (193/64) (by rfl) (by rfl)
    leaf2204FlatSound leaf2205FlatSound

private noncomputable def component48Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (27/128), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component48Node16_sound : Sound component48Node16Box :=
  sound_of_literal_split component48Node16Box leaf2206Box leaf2207Box
    .k (193/64) (by rfl) (by rfl)
    leaf2206FlatSound leaf2207FlatSound

private noncomputable def component48Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component48Node17_sound : Sound component48Node17Box :=
  sound_of_literal_split component48Node17Box component48Node15Box component48Node16Box
    .chi (27/128) (by rfl) (by rfl)
    component48Node15_sound component48Node16_sound

private noncomputable def component48Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (13/64), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component48Node18_sound : Sound component48Node18Box :=
  sound_of_literal_split component48Node18Box leaf2208Box leaf2209Box
    .k (195/64) (by rfl) (by rfl)
    leaf2208FlatSound leaf2209FlatSound

private noncomputable def component48Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (27/128), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component48Node19_sound : Sound component48Node19Box :=
  sound_of_literal_split component48Node19Box leaf2210Box leaf2211Box
    .k (195/64) (by rfl) (by rfl)
    leaf2210FlatSound leaf2211FlatSound

private noncomputable def component48Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component48Node20_sound : Sound component48Node20Box :=
  sound_of_literal_split component48Node20Box component48Node18Box component48Node19Box
    .chi (27/128) (by rfl) (by rfl)
    component48Node18_sound component48Node19_sound

private noncomputable def component48Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component48Node21_sound : Sound component48Node21Box :=
  sound_of_literal_split component48Node21Box component48Node17Box component48Node20Box
    .k (97/32) (by rfl) (by rfl)
    component48Node17_sound component48Node20_sound

private noncomputable def component48Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (13/64), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component48Node22_sound : Sound component48Node22Box :=
  sound_of_literal_split component48Node22Box leaf2212Box leaf2213Box
    .k (197/64) (by rfl) (by rfl)
    leaf2212FlatSound leaf2213FlatSound

private noncomputable def component48Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (27/128), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component48Node23_sound : Sound component48Node23Box :=
  sound_of_literal_split component48Node23Box leaf2214Box leaf2215Box
    .k (197/64) (by rfl) (by rfl)
    leaf2214FlatSound leaf2215FlatSound

private noncomputable def component48Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component48Node24_sound : Sound component48Node24Box :=
  sound_of_literal_split component48Node24Box component48Node22Box component48Node23Box
    .chi (27/128) (by rfl) (by rfl)
    component48Node22_sound component48Node23_sound

private noncomputable def component48Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (13/64), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component48Node25_sound : Sound component48Node25Box :=
  sound_of_literal_split component48Node25Box leaf2216Box leaf2217Box
    .k (199/64) (by rfl) (by rfl)
    leaf2216FlatSound leaf2217FlatSound

private noncomputable def component48Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (27/128), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component48Node26_sound : Sound component48Node26Box :=
  sound_of_literal_split component48Node26Box leaf2218Box leaf2219Box
    .k (199/64) (by rfl) (by rfl)
    leaf2218FlatSound leaf2219FlatSound

private noncomputable def component48Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component48Node27_sound : Sound component48Node27Box :=
  sound_of_literal_split component48Node27Box component48Node25Box component48Node26Box
    .chi (27/128) (by rfl) (by rfl)
    component48Node25_sound component48Node26_sound

private noncomputable def component48Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component48Node28_sound : Sound component48Node28Box :=
  sound_of_literal_split component48Node28Box component48Node24Box component48Node27Box
    .k (99/32) (by rfl) (by rfl)
    component48Node24_sound component48Node27_sound

private noncomputable def component48Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component48Node29_sound : Sound component48Node29Box :=
  sound_of_literal_split component48Node29Box component48Node21Box component48Node28Box
    .k (49/16) (by rfl) (by rfl)
    component48Node21_sound component48Node28_sound

private noncomputable def component48Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (3/16), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component48Node30_sound : Sound component48Node30Box :=
  sound_of_literal_split component48Node30Box component48Node14Box component48Node29Box
    .chi (13/64) (by rfl) (by rfl)
    component48Node14_sound component48Node29_sound

private noncomputable def component48Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (3/16), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component48Node31_sound : Sound component48Node31Box :=
  sound_of_literal_split component48Node31Box leaf2220Box leaf2221Box
    .k (201/64) (by rfl) (by rfl)
    leaf2220FlatSound leaf2221FlatSound

private noncomputable def component48Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (3/16), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component48Node32_sound : Sound component48Node32Box :=
  sound_of_literal_split component48Node32Box leaf2222Box leaf2223Box
    .k (203/64) (by rfl) (by rfl)
    leaf2222FlatSound leaf2223FlatSound

private noncomputable def component48Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (3/16), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component48Node33_sound : Sound component48Node33Box :=
  sound_of_literal_split component48Node33Box component48Node31Box component48Node32Box
    .k (101/32) (by rfl) (by rfl)
    component48Node31_sound component48Node32_sound

private noncomputable def component48Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (25/128), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component48Node34_sound : Sound component48Node34Box :=
  sound_of_literal_split component48Node34Box leaf2224Box leaf2225Box
    .k (201/64) (by rfl) (by rfl)
    leaf2224FlatSound leaf2225FlatSound

private noncomputable def component48Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (25/128), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component48Node35_sound : Sound component48Node35Box :=
  sound_of_literal_split component48Node35Box leaf2226Box leaf2227Box
    .k (203/64) (by rfl) (by rfl)
    leaf2226FlatSound leaf2227FlatSound

private noncomputable def component48Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (25/128), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component48Node36_sound : Sound component48Node36Box :=
  sound_of_literal_split component48Node36Box component48Node34Box component48Node35Box
    .k (101/32) (by rfl) (by rfl)
    component48Node34_sound component48Node35_sound

private noncomputable def component48Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (3/16), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component48Node37_sound : Sound component48Node37Box :=
  sound_of_literal_split component48Node37Box component48Node33Box component48Node36Box
    .chi (25/128) (by rfl) (by rfl)
    component48Node33_sound component48Node36_sound

private noncomputable def component48Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (3/16), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component48Node38_sound : Sound component48Node38Box :=
  sound_of_literal_split component48Node38Box leaf2228Box leaf2229Box
    .k (205/64) (by rfl) (by rfl)
    leaf2228FlatSound leaf2229FlatSound

private noncomputable def component48Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (3/16), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component48Node39_sound : Sound component48Node39Box :=
  sound_of_literal_split component48Node39Box leaf2230Box leaf2231Box
    .chi (49/256) (by rfl) (by rfl)
    leaf2230FlatSound leaf2231FlatSound

private noncomputable def component48Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (3/16), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component48Node40_sound : Sound component48Node40Box :=
  sound_of_literal_split component48Node40Box component48Node38Box component48Node39Box
    .k (103/32) (by rfl) (by rfl)
    component48Node38_sound component48Node39_sound

private noncomputable def component48Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (25/128), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component48Node41_sound : Sound component48Node41Box :=
  sound_of_literal_split component48Node41Box leaf2232Box leaf2233Box
    .k (205/64) (by rfl) (by rfl)
    leaf2232FlatSound leaf2233FlatSound

private noncomputable def component48Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (25/128), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component48Node42_sound : Sound component48Node42Box :=
  sound_of_literal_split component48Node42Box leaf2234Box leaf2235Box
    .k (207/64) (by rfl) (by rfl)
    leaf2234FlatSound leaf2235FlatSound

private noncomputable def component48Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (25/128), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component48Node43_sound : Sound component48Node43Box :=
  sound_of_literal_split component48Node43Box component48Node41Box component48Node42Box
    .k (103/32) (by rfl) (by rfl)
    component48Node41_sound component48Node42_sound

private noncomputable def component48Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (3/16), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component48Node44_sound : Sound component48Node44Box :=
  sound_of_literal_split component48Node44Box component48Node40Box component48Node43Box
    .chi (25/128) (by rfl) (by rfl)
    component48Node40_sound component48Node43_sound

private noncomputable def component48Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (3/16), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component48Node45_sound : Sound component48Node45Box :=
  sound_of_literal_split component48Node45Box component48Node37Box component48Node44Box
    .k (51/16) (by rfl) (by rfl)
    component48Node37_sound component48Node44_sound

private noncomputable def component48Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (13/64), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component48Node46_sound : Sound component48Node46Box :=
  sound_of_literal_split component48Node46Box leaf2236Box leaf2237Box
    .k (201/64) (by rfl) (by rfl)
    leaf2236FlatSound leaf2237FlatSound

private noncomputable def component48Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (27/128), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component48Node47_sound : Sound component48Node47Box :=
  sound_of_literal_split component48Node47Box leaf2238Box leaf2239Box
    .k (201/64) (by rfl) (by rfl)
    leaf2238FlatSound leaf2239FlatSound

private noncomputable def component48Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component48Node48_sound : Sound component48Node48Box :=
  sound_of_literal_split component48Node48Box component48Node46Box component48Node47Box
    .chi (27/128) (by rfl) (by rfl)
    component48Node46_sound component48Node47_sound

private noncomputable def component48Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (13/64), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component48Node49_sound : Sound component48Node49Box :=
  sound_of_literal_split component48Node49Box leaf2240Box leaf2241Box
    .k (203/64) (by rfl) (by rfl)
    leaf2240FlatSound leaf2241FlatSound

private noncomputable def component48Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (27/128), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component48Node50_sound : Sound component48Node50Box :=
  sound_of_literal_split component48Node50Box leaf2242Box leaf2243Box
    .k (203/64) (by rfl) (by rfl)
    leaf2242FlatSound leaf2243FlatSound

private noncomputable def component48Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component48Node51_sound : Sound component48Node51Box :=
  sound_of_literal_split component48Node51Box component48Node49Box component48Node50Box
    .chi (27/128) (by rfl) (by rfl)
    component48Node49_sound component48Node50_sound

private noncomputable def component48Node52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component48Node52_sound : Sound component48Node52Box :=
  sound_of_literal_split component48Node52Box component48Node48Box component48Node51Box
    .k (101/32) (by rfl) (by rfl)
    component48Node48_sound component48Node51_sound

private noncomputable def component48Node53Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (13/64), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component48Node53_sound : Sound component48Node53Box :=
  sound_of_literal_split component48Node53Box leaf2244Box leaf2245Box
    .k (205/64) (by rfl) (by rfl)
    leaf2244FlatSound leaf2245FlatSound

private noncomputable def component48Node54Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (13/64), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component48Node54_sound : Sound component48Node54Box :=
  sound_of_literal_split component48Node54Box leaf2246Box leaf2247Box
    .k (207/64) (by rfl) (by rfl)
    leaf2246FlatSound leaf2247FlatSound

private noncomputable def component48Node55Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (13/64), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component48Node55_sound : Sound component48Node55Box :=
  sound_of_literal_split component48Node55Box component48Node53Box component48Node54Box
    .k (103/32) (by rfl) (by rfl)
    component48Node53_sound component48Node54_sound

private noncomputable def component48Node56Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (27/128), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component48Node56_sound : Sound component48Node56Box :=
  sound_of_literal_split component48Node56Box leaf2248Box leaf2249Box
    .k (205/64) (by rfl) (by rfl)
    leaf2248FlatSound leaf2249FlatSound

private noncomputable def component48Node57Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (27/128), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component48Node57_sound : Sound component48Node57Box :=
  sound_of_literal_split component48Node57Box leaf2250Box leaf2251Box
    .k (207/64) (by rfl) (by rfl)
    leaf2250FlatSound leaf2251FlatSound

private noncomputable def component48Node58Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (27/128), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component48Node58_sound : Sound component48Node58Box :=
  sound_of_literal_split component48Node58Box component48Node56Box component48Node57Box
    .k (103/32) (by rfl) (by rfl)
    component48Node56_sound component48Node57_sound

private noncomputable def component48Node59Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component48Node59_sound : Sound component48Node59Box :=
  sound_of_literal_split component48Node59Box component48Node55Box component48Node58Box
    .chi (27/128) (by rfl) (by rfl)
    component48Node55_sound component48Node58_sound

private noncomputable def component48Node60Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component48Node60_sound : Sound component48Node60Box :=
  sound_of_literal_split component48Node60Box component48Node52Box component48Node59Box
    .k (51/16) (by rfl) (by rfl)
    component48Node52_sound component48Node59_sound

private noncomputable def component48Node61Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (3/16), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component48Node61_sound : Sound component48Node61Box :=
  sound_of_literal_split component48Node61Box component48Node45Box component48Node60Box
    .chi (13/64) (by rfl) (by rfl)
    component48Node45_sound component48Node60_sound

noncomputable def component48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (13/4), chiLo := (3/16), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
theorem component48_sound : Sound component48Box :=
  sound_of_literal_split component48Box component48Node30Box component48Node61Box
    .k (25/8) (by rfl) (by rfl)
    component48Node30_sound component48Node61_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
