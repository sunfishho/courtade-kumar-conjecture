import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch1
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

private noncomputable def leaf2416Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (209/64), chiLo := (7/32), chiHi := (29/128) }

private noncomputable def leaf2416Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871387/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432747008) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (918496039/536870912) }, upper := { exponent := 0, mantissa := (14253/8192) } }, logOuter := sk201LogOuterCertificate, logK := sk201LogKCertificate, logChi := chi119LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869668863/274865494016) } }, logDArg := sk201LogDArgCertificate }

private noncomputable def leaf2416InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf2416LocalValidity :
    LeafFacts leaf2416Box leaf2416Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2416Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432747008) }) = true
      norm_num [leaf2416Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2416CertificateValid :
    WideCertificateValid leaf2416Box leaf2416Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk201ValidityFacts chi119ValidityFacts
    leaf2416LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2416CoverageChecked :
    coverageCheck (innerAD leaf2416Box) leaf2416InnerLog = true := by
  rfl'

private theorem leaf2416InnerLogValid :
    leaf2416InnerLog.Valid 8 (innerAD leaf2416Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf2416CoverageChecked

private noncomputable def leaf2416InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453667/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf2416InputLogOnePlusV_eq :
    leaf2416InputLogOnePlusV = outerEnclosure 24
      (leaf2416Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2416RoundedFacts : LeafRoundedFacts 8
    leaf2416Certificate.logOnePlusV leaf2416InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2416InputLogOnePlusV_eq }

private noncomputable def leaf2416Inputs : Inputs :=
  inputsOfCaches globalInput sk201RoundedInputs
    chi119InputQChi innerPair64Input
    leaf2416InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2416LowerChecked :
    lowerCheck 24 leaf2416Box leaf2416Inputs = true := by
  rfl'

private theorem leaf2416CoversExact : CoversExact 8
    leaf2416Box leaf2416Certificate leaf2416InnerLog leaf2416Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk201RoundedFacts chi119RoundedFacts
    innerPair64RoundedFacts leaf2416RoundedFacts (by rfl)

private theorem leaf2416FlatSound : Sound leaf2416Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2416CertificateValid
    leaf2416InnerLogValid leaf2416CoversExact leaf2416LowerChecked

private noncomputable def leaf2417Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (209/64), kHi := (105/32), chiLo := (7/32), chiHi := (29/128) }

private noncomputable def leaf2417Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871389/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432717312) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (920330933/536870912) }, upper := { exponent := 0, mantissa := (7141/4096) } }, logOuter := sk202LogOuterCertificate, logK := sk202LogKCertificate, logChi := chi119LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869639167/274865434624) } }, logDArg := sk202LogDArgCertificate }

private noncomputable def leaf2417InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf2417LocalValidity :
    LeafFacts leaf2417Box leaf2417Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2417Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432717312) }) = true
      norm_num [leaf2417Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2417CertificateValid :
    WideCertificateValid leaf2417Box leaf2417Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk202ValidityFacts chi119ValidityFacts
    leaf2417LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2417CoverageChecked :
    coverageCheck (innerAD leaf2417Box) leaf2417InnerLog = true := by
  rfl'

private theorem leaf2417InnerLogValid :
    leaf2417InnerLog.Valid 8 (innerAD leaf2417Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf2417CoverageChecked

private noncomputable def leaf2417InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629337/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2417InputLogOnePlusV_eq :
    leaf2417InputLogOnePlusV = outerEnclosure 24
      (leaf2417Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2417RoundedFacts : LeafRoundedFacts 8
    leaf2417Certificate.logOnePlusV leaf2417InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2417InputLogOnePlusV_eq }

private noncomputable def leaf2417Inputs : Inputs :=
  inputsOfCaches globalInput sk202RoundedInputs
    chi119InputQChi innerPair64Input
    leaf2417InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2417LowerChecked :
    lowerCheck 24 leaf2417Box leaf2417Inputs = true := by
  rfl'

private theorem leaf2417CoversExact : CoversExact 8
    leaf2417Box leaf2417Certificate leaf2417InnerLog leaf2417Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk202RoundedFacts chi119RoundedFacts
    innerPair64RoundedFacts leaf2417RoundedFacts (by rfl)

private theorem leaf2417FlatSound : Sound leaf2417Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2417CertificateValid
    leaf2417InnerLogValid leaf2417CoversExact leaf2417LowerChecked

private noncomputable def leaf2418Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (211/64), chiLo := (7/32), chiHi := (29/128) }

private noncomputable def leaf2418Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871391/536870912) }, vSqrt := { lower := (65529/65536), upper := (15270769095/15270298624) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (922165827/536870912) }, upper := { exponent := 0, mantissa := (14311/8192) } }, logOuter := sk203LogOuterCertificate, logK := sk203LogKCertificate, logChi := chi119LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (30541067719/30540597248) } }, logDArg := sk203LogDArgCertificate }

private noncomputable def leaf2418InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf2418LocalValidity :
    LeafFacts leaf2418Box leaf2418Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2418Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (15270769095/15270298624) }) = true
      norm_num [leaf2418Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2418CertificateValid :
    WideCertificateValid leaf2418Box leaf2418Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk203ValidityFacts chi119ValidityFacts
    leaf2418LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2418CoverageChecked :
    coverageCheck (innerAD leaf2418Box) leaf2418InnerLog = true := by
  rfl'

private theorem leaf2418InnerLogValid :
    leaf2418InnerLog.Valid 8 (innerAD leaf2418Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf2418CoverageChecked

private noncomputable def leaf2418InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629339/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2418InputLogOnePlusV_eq :
    leaf2418InputLogOnePlusV = outerEnclosure 24
      (leaf2418Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2418RoundedFacts : LeafRoundedFacts 8
    leaf2418Certificate.logOnePlusV leaf2418InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2418InputLogOnePlusV_eq }

private noncomputable def leaf2418Inputs : Inputs :=
  inputsOfCaches globalInput sk203RoundedInputs
    chi119InputQChi innerPair64Input
    leaf2418InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2418LowerChecked :
    lowerCheck 24 leaf2418Box leaf2418Inputs = true := by
  rfl'

private theorem leaf2418CoversExact : CoversExact 8
    leaf2418Box leaf2418Certificate leaf2418InnerLog leaf2418Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk203RoundedFacts chi119RoundedFacts
    innerPair64RoundedFacts leaf2418RoundedFacts (by rfl)

private theorem leaf2418FlatSound : Sound leaf2418Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2418CertificateValid
    leaf2418InnerLogValid leaf2418CoversExact leaf2418LowerChecked

private noncomputable def leaf2419Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (211/64), kHi := (53/16), chiLo := (7/32), chiHi := (29/128) }

private noncomputable def leaf2419Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871393/536870912) }, vSqrt := { lower := (65529/65536), upper := (27487384371/27486531584) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (924000721/536870912) }, upper := { exponent := 0, mantissa := (3585/2048) } }, logOuter := sk204LogOuterCertificate, logK := sk204LogKCertificate, logChi := chi119LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (54973915955/54973063168) } }, logDArg := sk204LogDArgCertificate }

private noncomputable def leaf2419InnerLog : WideLogData :=
  innerPair206Data

set_option maxRecDepth 1000000 in
private theorem leaf2419LocalValidity :
    LeafFacts leaf2419Box leaf2419Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2419Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (27487384371/27486531584) }) = true
      norm_num [leaf2419Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2419CertificateValid :
    WideCertificateValid leaf2419Box leaf2419Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk204ValidityFacts chi119ValidityFacts
    leaf2419LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2419CoverageChecked :
    coverageCheck (innerAD leaf2419Box) leaf2419InnerLog = true := by
  rfl'

private theorem leaf2419InnerLogValid :
    leaf2419InnerLog.Valid 8 (innerAD leaf2419Box) :=
  wideLogDataValid_of_cachedCheck endpoint62PositiveFacts
    endpoint178PositiveFacts.valid leaf2419CoverageChecked

private noncomputable def leaf2419InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629341/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2419InputLogOnePlusV_eq :
    leaf2419InputLogOnePlusV = outerEnclosure 24
      (leaf2419Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2419RoundedFacts : LeafRoundedFacts 8
    leaf2419Certificate.logOnePlusV leaf2419InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2419InputLogOnePlusV_eq }

private noncomputable def leaf2419Inputs : Inputs :=
  inputsOfCaches globalInput sk204RoundedInputs
    chi119InputQChi innerPair206Input
    leaf2419InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2419LowerChecked :
    lowerCheck 24 leaf2419Box leaf2419Inputs = true := by
  rfl'

private theorem leaf2419CoversExact : CoversExact 8
    leaf2419Box leaf2419Certificate leaf2419InnerLog leaf2419Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk204RoundedFacts chi119RoundedFacts
    innerPair206RoundedFacts leaf2419RoundedFacts (by rfl)

private theorem leaf2419FlatSound : Sound leaf2419Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2419CertificateValid
    leaf2419InnerLogValid leaf2419CoversExact leaf2419LowerChecked

private noncomputable def leaf2420Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (209/64), chiLo := (29/128), chiHi := (15/64) }

private noncomputable def leaf2420Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871389/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432532992) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (932126693/536870912) }, upper := { exponent := 0, mantissa := (7231/4096) } }, logOuter := sk201LogOuterCertificate, logK := sk201LogKCertificate, logChi := chi120LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869454847/274865065984) } }, logDArg := sk201LogDArgCertificate }

private noncomputable def leaf2420InnerLog : WideLogData :=
  innerPair430Data

set_option maxRecDepth 1000000 in
private theorem leaf2420LocalValidity :
    LeafFacts leaf2420Box leaf2420Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2420Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432532992) }) = true
      norm_num [leaf2420Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2420CertificateValid :
    WideCertificateValid leaf2420Box leaf2420Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk201ValidityFacts chi120ValidityFacts
    leaf2420LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2420CoverageChecked :
    coverageCheck (innerAD leaf2420Box) leaf2420InnerLog = true := by
  rfl'

private theorem leaf2420InnerLogValid :
    leaf2420InnerLog.Valid 8 (innerAD leaf2420Box) :=
  wideLogDataValid_of_cachedCheck endpoint139PositiveFacts
    endpoint63PositiveFacts.valid leaf2420CoverageChecked

private noncomputable def leaf2420InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629349/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2420InputLogOnePlusV_eq :
    leaf2420InputLogOnePlusV = outerEnclosure 24
      (leaf2420Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2420RoundedFacts : LeafRoundedFacts 8
    leaf2420Certificate.logOnePlusV leaf2420InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2420InputLogOnePlusV_eq }

private noncomputable def leaf2420Inputs : Inputs :=
  inputsOfCaches globalInput sk201RoundedInputs
    chi120InputQChi innerPair430Input
    leaf2420InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2420LowerChecked :
    lowerCheck 24 leaf2420Box leaf2420Inputs = true := by
  rfl'

private theorem leaf2420CoversExact : CoversExact 8
    leaf2420Box leaf2420Certificate leaf2420InnerLog leaf2420Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk201RoundedFacts chi120RoundedFacts
    innerPair430RoundedFacts leaf2420RoundedFacts (by rfl)

private theorem leaf2420FlatSound : Sound leaf2420Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2420CertificateValid
    leaf2420InnerLogValid leaf2420CoversExact leaf2420LowerChecked

private noncomputable def leaf2421Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (209/64), kHi := (105/32), chiLo := (29/128), chiHi := (15/64) }

private noncomputable def leaf2421Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871391/536870912) }, vSqrt := { lower := (65529/65536), upper := (3196207485/3196104704) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (934027119/536870912) }, upper := { exponent := 0, mantissa := (3623/2048) } }, logOuter := sk202LogOuterCertificate, logK := sk202LogKCertificate, logChi := chi120LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (6392312189/6392209408) } }, logDArg := sk202LogDArgCertificate }

private noncomputable def leaf2421InnerLog : WideLogData :=
  innerPair431Data

set_option maxRecDepth 1000000 in
private theorem leaf2421LocalValidity :
    LeafFacts leaf2421Box leaf2421Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2421Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (3196207485/3196104704) }) = true
      norm_num [leaf2421Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2421CertificateValid :
    WideCertificateValid leaf2421Box leaf2421Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk202ValidityFacts chi120ValidityFacts
    leaf2421LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2421CoverageChecked :
    coverageCheck (innerAD leaf2421Box) leaf2421InnerLog = true := by
  rfl'

private theorem leaf2421InnerLogValid :
    leaf2421InnerLog.Valid 8 (innerAD leaf2421Box) :=
  wideLogDataValid_of_cachedCheck endpoint139PositiveFacts
    endpoint68PositiveFacts.valid leaf2421CoverageChecked

private noncomputable def leaf2421InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629351/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2421InputLogOnePlusV_eq :
    leaf2421InputLogOnePlusV = outerEnclosure 24
      (leaf2421Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2421RoundedFacts : LeafRoundedFacts 8
    leaf2421Certificate.logOnePlusV leaf2421InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2421InputLogOnePlusV_eq }

private noncomputable def leaf2421Inputs : Inputs :=
  inputsOfCaches globalInput sk202RoundedInputs
    chi120InputQChi innerPair431Input
    leaf2421InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2421LowerChecked :
    lowerCheck 24 leaf2421Box leaf2421Inputs = true := by
  rfl'

private theorem leaf2421CoversExact : CoversExact 8
    leaf2421Box leaf2421Certificate leaf2421InnerLog leaf2421Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk202RoundedFacts chi120RoundedFacts
    innerPair431RoundedFacts leaf2421RoundedFacts (by rfl)

private theorem leaf2421FlatSound : Sound leaf2421Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2421CertificateValid
    leaf2421InnerLogValid leaf2421CoversExact leaf2421LowerChecked

private noncomputable def leaf2422Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (211/64), chiLo := (29/128), chiHi := (15/64) }

private noncomputable def leaf2422Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871393/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432471552) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (935927545/536870912) }, upper := { exponent := 0, mantissa := (7261/4096) } }, logOuter := sk203LogOuterCertificate, logK := sk203LogKCertificate, logChi := chi120LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869393407/274864943104) } }, logDArg := sk203LogDArgCertificate }

private noncomputable def leaf2422InnerLog : WideLogData :=
  innerPair431Data

set_option maxRecDepth 1000000 in
private theorem leaf2422LocalValidity :
    LeafFacts leaf2422Box leaf2422Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2422Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432471552) }) = true
      norm_num [leaf2422Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2422CertificateValid :
    WideCertificateValid leaf2422Box leaf2422Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk203ValidityFacts chi120ValidityFacts
    leaf2422LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2422CoverageChecked :
    coverageCheck (innerAD leaf2422Box) leaf2422InnerLog = true := by
  rfl'

private theorem leaf2422InnerLogValid :
    leaf2422InnerLog.Valid 8 (innerAD leaf2422Box) :=
  wideLogDataValid_of_cachedCheck endpoint139PositiveFacts
    endpoint68PositiveFacts.valid leaf2422CoverageChecked

private noncomputable def leaf2422InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453669/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf2422InputLogOnePlusV_eq :
    leaf2422InputLogOnePlusV = outerEnclosure 24
      (leaf2422Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2422RoundedFacts : LeafRoundedFacts 8
    leaf2422Certificate.logOnePlusV leaf2422InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2422InputLogOnePlusV_eq }

private noncomputable def leaf2422Inputs : Inputs :=
  inputsOfCaches globalInput sk203RoundedInputs
    chi120InputQChi innerPair431Input
    leaf2422InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2422LowerChecked :
    lowerCheck 24 leaf2422Box leaf2422Inputs = true := by
  rfl'

private theorem leaf2422CoversExact : CoversExact 8
    leaf2422Box leaf2422Certificate leaf2422InnerLog leaf2422Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk203RoundedFacts chi120RoundedFacts
    innerPair431RoundedFacts leaf2422RoundedFacts (by rfl)

private theorem leaf2422FlatSound : Sound leaf2422Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2422CertificateValid
    leaf2422InnerLogValid leaf2422CoversExact leaf2422LowerChecked

private noncomputable def leaf2423Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (211/64), kHi := (53/16), chiLo := (29/128), chiHi := (15/64) }

private noncomputable def leaf2423Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871395/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432440832) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (937827971/536870912) }, upper := { exponent := 0, mantissa := (1819/1024) } }, logOuter := sk204LogOuterCertificate, logK := sk204LogKCertificate, logChi := chi120LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869362687/274864881664) } }, logDArg := sk204LogDArgCertificate }

private noncomputable def leaf2423InnerLog : WideLogData :=
  innerPair431Data

set_option maxRecDepth 1000000 in
private theorem leaf2423LocalValidity :
    LeafFacts leaf2423Box leaf2423Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2423Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432440832) }) = true
      norm_num [leaf2423Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2423CertificateValid :
    WideCertificateValid leaf2423Box leaf2423Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk204ValidityFacts chi120ValidityFacts
    leaf2423LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2423CoverageChecked :
    coverageCheck (innerAD leaf2423Box) leaf2423InnerLog = true := by
  rfl'

private theorem leaf2423InnerLogValid :
    leaf2423InnerLog.Valid 8 (innerAD leaf2423Box) :=
  wideLogDataValid_of_cachedCheck endpoint139PositiveFacts
    endpoint68PositiveFacts.valid leaf2423CoverageChecked

private noncomputable def leaf2423InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814677/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2423InputLogOnePlusV_eq :
    leaf2423InputLogOnePlusV = outerEnclosure 24
      (leaf2423Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2423RoundedFacts : LeafRoundedFacts 8
    leaf2423Certificate.logOnePlusV leaf2423InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2423InputLogOnePlusV_eq }

private noncomputable def leaf2423Inputs : Inputs :=
  inputsOfCaches globalInput sk204RoundedInputs
    chi120InputQChi innerPair431Input
    leaf2423InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2423LowerChecked :
    lowerCheck 24 leaf2423Box leaf2423Inputs = true := by
  rfl'

private theorem leaf2423CoversExact : CoversExact 8
    leaf2423Box leaf2423Certificate leaf2423InnerLog leaf2423Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk204RoundedFacts chi120RoundedFacts
    innerPair431RoundedFacts leaf2423RoundedFacts (by rfl)

private theorem leaf2423FlatSound : Sound leaf2423Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2423CertificateValid
    leaf2423InnerLogValid leaf2423CoversExact leaf2423LowerChecked

private noncomputable def leaf2424Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (213/64), chiLo := (7/32), chiHi := (29/128) }

private noncomputable def leaf2424Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871395/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432628224) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (925835615/536870912) }, upper := { exponent := 0, mantissa := (14369/8192) } }, logOuter := sk207LogOuterCertificate, logK := sk207LogKCertificate, logChi := chi119LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869550079/274865256448) } }, logDArg := sk207LogDArgCertificate }

private noncomputable def leaf2424InnerLog : WideLogData :=
  innerPair459Data

set_option maxRecDepth 1000000 in
private theorem leaf2424LocalValidity :
    LeafFacts leaf2424Box leaf2424Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2424Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432628224) }) = true
      norm_num [leaf2424Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2424CertificateValid :
    WideCertificateValid leaf2424Box leaf2424Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk207ValidityFacts chi119ValidityFacts
    leaf2424LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2424CoverageChecked :
    coverageCheck (innerAD leaf2424Box) leaf2424InnerLog = true := by
  rfl'

private theorem leaf2424InnerLogValid :
    leaf2424InnerLog.Valid 8 (innerAD leaf2424Box) :=
  wideLogDataValid_of_cachedCheck endpoint179PositiveFacts
    endpoint66PositiveFacts.valid leaf2424CoverageChecked

private noncomputable def leaf2424InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629343/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2424InputLogOnePlusV_eq :
    leaf2424InputLogOnePlusV = outerEnclosure 24
      (leaf2424Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2424RoundedFacts : LeafRoundedFacts 8
    leaf2424Certificate.logOnePlusV leaf2424InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2424InputLogOnePlusV_eq }

private noncomputable def leaf2424Inputs : Inputs :=
  inputsOfCaches globalInput sk207RoundedInputs
    chi119InputQChi innerPair459Input
    leaf2424InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2424LowerChecked :
    lowerCheck 24 leaf2424Box leaf2424Inputs = true := by
  rfl'

private theorem leaf2424CoversExact : CoversExact 8
    leaf2424Box leaf2424Certificate leaf2424InnerLog leaf2424Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk207RoundedFacts chi119RoundedFacts
    innerPair459RoundedFacts leaf2424RoundedFacts (by rfl)

private theorem leaf2424FlatSound : Sound leaf2424Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2424CertificateValid
    leaf2424InnerLogValid leaf2424CoversExact leaf2424LowerChecked

private noncomputable def leaf2425Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (213/64), kHi := (107/32), chiLo := (7/32), chiHi := (29/128) }

private noncomputable def leaf2425Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871397/536870912) }, vSqrt := { lower := (65529/65536), upper := (45812307285/45810866176) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (927670509/536870912) }, upper := { exponent := 0, mantissa := (7199/4096) } }, logOuter := sk208LogOuterCertificate, logK := sk208LogKCertificate, logChi := chi119LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (91623173461/91621732352) } }, logDArg := sk208LogDArgCertificate }

private noncomputable def leaf2425InnerLog : WideLogData :=
  innerPair429Data

set_option maxRecDepth 1000000 in
private theorem leaf2425LocalValidity :
    LeafFacts leaf2425Box leaf2425Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2425Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (45812307285/45810866176) }) = true
      norm_num [leaf2425Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2425CertificateValid :
    WideCertificateValid leaf2425Box leaf2425Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk208ValidityFacts chi119ValidityFacts
    leaf2425LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2425CoverageChecked :
    coverageCheck (innerAD leaf2425Box) leaf2425InnerLog = true := by
  rfl'

private theorem leaf2425InnerLogValid :
    leaf2425InnerLog.Valid 8 (innerAD leaf2425Box) :=
  wideLogDataValid_of_cachedCheck endpoint138PositiveFacts
    endpoint66PositiveFacts.valid leaf2425CoverageChecked

private noncomputable def leaf2425InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629345/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2425InputLogOnePlusV_eq :
    leaf2425InputLogOnePlusV = outerEnclosure 24
      (leaf2425Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2425RoundedFacts : LeafRoundedFacts 8
    leaf2425Certificate.logOnePlusV leaf2425InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2425InputLogOnePlusV_eq }

private noncomputable def leaf2425Inputs : Inputs :=
  inputsOfCaches globalInput sk208RoundedInputs
    chi119InputQChi innerPair429Input
    leaf2425InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2425LowerChecked :
    lowerCheck 24 leaf2425Box leaf2425Inputs = true := by
  rfl'

private theorem leaf2425CoversExact : CoversExact 8
    leaf2425Box leaf2425Certificate leaf2425InnerLog leaf2425Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk208RoundedFacts chi119RoundedFacts
    innerPair429RoundedFacts leaf2425RoundedFacts (by rfl)

private theorem leaf2425FlatSound : Sound leaf2425Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2425CertificateValid
    leaf2425InnerLogValid leaf2425CoversExact leaf2425LowerChecked

private noncomputable def leaf2426Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (215/64), chiLo := (7/32), chiHi := (29/128) }

private noncomputable def leaf2426Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871399/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432568832) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (929505403/536870912) }, upper := { exponent := 0, mantissa := (14427/8192) } }, logOuter := sk205LogOuterCertificate, logK := sk205LogKCertificate, logChi := chi119LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869490687/274865137664) } }, logDArg := sk205LogDArgCertificate }

private noncomputable def leaf2426InnerLog : WideLogData :=
  innerPair462Data

set_option maxRecDepth 1000000 in
private theorem leaf2426LocalValidity :
    LeafFacts leaf2426Box leaf2426Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2426Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432568832) }) = true
      norm_num [leaf2426Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2426CertificateValid :
    WideCertificateValid leaf2426Box leaf2426Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk205ValidityFacts chi119ValidityFacts
    leaf2426LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2426CoverageChecked :
    coverageCheck (innerAD leaf2426Box) leaf2426InnerLog = true := by
  rfl'

private theorem leaf2426InnerLogValid :
    leaf2426InnerLog.Valid 8 (innerAD leaf2426Box) :=
  wideLogDataValid_of_cachedCheck endpoint180PositiveFacts
    endpoint60PositiveFacts.valid leaf2426CoverageChecked

private noncomputable def leaf2426InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814673/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2426InputLogOnePlusV_eq :
    leaf2426InputLogOnePlusV = outerEnclosure 24
      (leaf2426Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2426RoundedFacts : LeafRoundedFacts 8
    leaf2426Certificate.logOnePlusV leaf2426InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2426InputLogOnePlusV_eq }

private noncomputable def leaf2426Inputs : Inputs :=
  inputsOfCaches globalInput sk205RoundedInputs
    chi119InputQChi innerPair462Input
    leaf2426InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2426LowerChecked :
    lowerCheck 24 leaf2426Box leaf2426Inputs = true := by
  rfl'

private theorem leaf2426CoversExact : CoversExact 8
    leaf2426Box leaf2426Certificate leaf2426InnerLog leaf2426Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk205RoundedFacts chi119RoundedFacts
    innerPair462RoundedFacts leaf2426RoundedFacts (by rfl)

private theorem leaf2426FlatSound : Sound leaf2426Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2426CertificateValid
    leaf2426InnerLogValid leaf2426CoversExact leaf2426LowerChecked

private noncomputable def leaf2427Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (215/64), kHi := (27/8), chiLo := (7/32), chiHi := (29/128) }

private noncomputable def leaf2427Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871401/536870912) }, vSqrt := { lower := (65529/65536), upper := (8084524815/8084267008) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (931340297/536870912) }, upper := { exponent := 0, mantissa := (1807/1024) } }, logOuter := sk206LogOuterCertificate, logK := sk206LogKCertificate, logChi := chi119LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (16168791823/16168534016) } }, logDArg := sk206LogDArgCertificate }

private noncomputable def leaf2427InnerLog : WideLogData :=
  innerPair433Data

set_option maxRecDepth 1000000 in
private theorem leaf2427LocalValidity :
    LeafFacts leaf2427Box leaf2427Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2427Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8084524815/8084267008) }) = true
      norm_num [leaf2427Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2427CertificateValid :
    WideCertificateValid leaf2427Box leaf2427Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk206ValidityFacts chi119ValidityFacts
    leaf2427LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2427CoverageChecked :
    coverageCheck (innerAD leaf2427Box) leaf2427InnerLog = true := by
  rfl'

private theorem leaf2427InnerLogValid :
    leaf2427InnerLog.Valid 8 (innerAD leaf2427Box) :=
  wideLogDataValid_of_cachedCheck endpoint139PositiveFacts
    endpoint181PositiveFacts.valid leaf2427CoverageChecked

private noncomputable def leaf2427InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907337/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2427InputLogOnePlusV_eq :
    leaf2427InputLogOnePlusV = outerEnclosure 24
      (leaf2427Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2427RoundedFacts : LeafRoundedFacts 8
    leaf2427Certificate.logOnePlusV leaf2427InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2427InputLogOnePlusV_eq }

private noncomputable def leaf2427Inputs : Inputs :=
  inputsOfCaches globalInput sk206RoundedInputs
    chi119InputQChi innerPair433Input
    leaf2427InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2427LowerChecked :
    lowerCheck 24 leaf2427Box leaf2427Inputs = true := by
  rfl'

private theorem leaf2427CoversExact : CoversExact 8
    leaf2427Box leaf2427Certificate leaf2427InnerLog leaf2427Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk206RoundedFacts chi119RoundedFacts
    innerPair433RoundedFacts leaf2427RoundedFacts (by rfl)

private theorem leaf2427FlatSound : Sound leaf2427Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2427CertificateValid
    leaf2427InnerLogValid leaf2427CoversExact leaf2427LowerChecked

private noncomputable def leaf2428Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (29/128), chiHi := (59/256) }

private noncomputable def leaf2428Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871243/536870912) }, vSqrt := { lower := (65529/65536), upper := (13743698739/13743248896) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (939728551/536870912) }, upper := { exponent := 0, mantissa := (14505/8192) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi199LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (27486947635/27486497792) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf2428InnerLog : WideLogData :=
  innerPair79Data

set_option maxRecDepth 1000000 in
private theorem leaf2428LocalValidity :
    LeafFacts leaf2428Box leaf2428Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2428Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (13743698739/13743248896) }) = true
      norm_num [leaf2428Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2428CertificateValid :
    WideCertificateValid leaf2428Box leaf2428Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi199ValidityFacts
    leaf2428LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2428CoverageChecked :
    coverageCheck (innerAD leaf2428Box) leaf2428InnerLog = true := by
  rfl'

private theorem leaf2428InnerLogValid :
    leaf2428InnerLog.Valid 8 (innerAD leaf2428Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint182PositiveFacts.valid leaf2428CoverageChecked

private noncomputable def leaf2428InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629355/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2428InputLogOnePlusV_eq :
    leaf2428InputLogOnePlusV = outerEnclosure 24
      (leaf2428Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2428RoundedFacts : LeafRoundedFacts 8
    leaf2428Certificate.logOnePlusV leaf2428InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2428InputLogOnePlusV_eq }

private noncomputable def leaf2428Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi199InputQChi innerPair79Input
    leaf2428InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2428LowerChecked :
    lowerCheck 24 leaf2428Box leaf2428Inputs = true := by
  rfl'

private theorem leaf2428CoversExact : CoversExact 8
    leaf2428Box leaf2428Certificate leaf2428InnerLog leaf2428Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi199RoundedFacts
    innerPair79RoundedFacts leaf2428RoundedFacts (by rfl)

private theorem leaf2428FlatSound : Sound leaf2428Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2428CertificateValid
    leaf2428InnerLogValid leaf2428CoversExact leaf2428LowerChecked

private noncomputable def leaf2429Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (59/256), chiHi := (15/64) }

private noncomputable def leaf2429Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871245/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68716189696) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (946674941/536870912) }, upper := { exponent := 0, mantissa := (3653/2048) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi200LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434683391/137432379392) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf2429InnerLog : WideLogData :=
  innerPair198Data

set_option maxRecDepth 1000000 in
private theorem leaf2429LocalValidity :
    LeafFacts leaf2429Box leaf2429Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2429Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68716189696) }) = true
      norm_num [leaf2429Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2429CertificateValid :
    WideCertificateValid leaf2429Box leaf2429Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi200ValidityFacts
    leaf2429LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2429CoverageChecked :
    coverageCheck (innerAD leaf2429Box) leaf2429InnerLog = true := by
  rfl'

private theorem leaf2429InnerLogValid :
    leaf2429InnerLog.Valid 8 (innerAD leaf2429Box) :=
  wideLogDataValid_of_cachedCheck endpoint60PositiveFacts
    endpoint183PositiveFacts.valid leaf2429CoverageChecked

private noncomputable def leaf2429InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814681/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2429InputLogOnePlusV_eq :
    leaf2429InputLogOnePlusV = outerEnclosure 24
      (leaf2429Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2429RoundedFacts : LeafRoundedFacts 8
    leaf2429Certificate.logOnePlusV leaf2429InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2429InputLogOnePlusV_eq }

private noncomputable def leaf2429Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi200InputQChi innerPair198Input
    leaf2429InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2429LowerChecked :
    lowerCheck 24 leaf2429Box leaf2429Inputs = true := by
  rfl'

private theorem leaf2429CoversExact : CoversExact 8
    leaf2429Box leaf2429Certificate leaf2429InnerLog leaf2429Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi200RoundedFacts
    innerPair198RoundedFacts leaf2429RoundedFacts (by rfl)

private theorem leaf2429FlatSound : Sound leaf2429Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2429CertificateValid
    leaf2429InnerLogValid leaf2429CoversExact leaf2429LowerChecked

private noncomputable def leaf2430Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (215/64), chiLo := (29/128), chiHi := (59/256) }

private noncomputable def leaf2430Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742371/1073741824) }, vSqrt := { lower := (65529/65536), upper := (45812307285/45810819584) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1887091695/1073741824) }, upper := { exponent := 0, mantissa := (29069/16384) } }, logOuter := sk205LogOuterCertificate, logK := sk205LogKCertificate, logChi := chi199LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (91623126869/91621639168) } }, logDArg := sk205LogDArgCertificate }

private noncomputable def leaf2430InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf2430LocalValidity :
    LeafFacts leaf2430Box leaf2430Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2430Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (45812307285/45810819584) }) = true
      norm_num [leaf2430Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2430CertificateValid :
    WideCertificateValid leaf2430Box leaf2430Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk205ValidityFacts chi199ValidityFacts
    leaf2430LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2430CoverageChecked :
    coverageCheck (innerAD leaf2430Box) leaf2430InnerLog = true := by
  rfl'

private theorem leaf2430InnerLogValid :
    leaf2430InnerLog.Valid 8 (innerAD leaf2430Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf2430CoverageChecked

private noncomputable def leaf2430InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629353/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2430InputLogOnePlusV_eq :
    leaf2430InputLogOnePlusV = outerEnclosure 24
      (leaf2430Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2430RoundedFacts : LeafRoundedFacts 8
    leaf2430Certificate.logOnePlusV leaf2430InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2430InputLogOnePlusV_eq }

private noncomputable def leaf2430Inputs : Inputs :=
  inputsOfCaches globalInput sk205RoundedInputs
    chi199InputQChi innerPair71Input
    leaf2430InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2430LowerChecked :
    lowerCheck 24 leaf2430Box leaf2430Inputs = true := by
  rfl'

private theorem leaf2430CoversExact : CoversExact 8
    leaf2430Box leaf2430Certificate leaf2430InnerLog leaf2430Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk205RoundedFacts chi199RoundedFacts
    innerPair71RoundedFacts leaf2430RoundedFacts (by rfl)

private theorem leaf2430FlatSound : Sound leaf2430Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2430CertificateValid
    leaf2430InnerLogValid leaf2430CoversExact leaf2430LowerChecked

private noncomputable def leaf2431Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (215/64), kHi := (27/8), chiLo := (29/128), chiHi := (59/256) }

private noncomputable def leaf2431Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742373/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432428544) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1890892549/1073741824) }, upper := { exponent := 0, mantissa := (3641/2048) } }, logOuter := sk206LogOuterCertificate, logK := sk206LogKCertificate, logChi := chi199LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869350399/274864857088) } }, logDArg := sk206LogDArgCertificate }

private noncomputable def leaf2431InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf2431LocalValidity :
    LeafFacts leaf2431Box leaf2431Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2431Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432428544) }) = true
      norm_num [leaf2431Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2431CertificateValid :
    WideCertificateValid leaf2431Box leaf2431Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk206ValidityFacts chi199ValidityFacts
    leaf2431LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2431CoverageChecked :
    coverageCheck (innerAD leaf2431Box) leaf2431InnerLog = true := by
  rfl'

private theorem leaf2431InnerLogValid :
    leaf2431InnerLog.Valid 8 (innerAD leaf2431Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf2431CoverageChecked

private noncomputable def leaf2431InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629355/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2431InputLogOnePlusV_eq :
    leaf2431InputLogOnePlusV = outerEnclosure 24
      (leaf2431Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2431RoundedFacts : LeafRoundedFacts 8
    leaf2431Certificate.logOnePlusV leaf2431InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2431InputLogOnePlusV_eq }

private noncomputable def leaf2431Inputs : Inputs :=
  inputsOfCaches globalInput sk206RoundedInputs
    chi199InputQChi innerPair71Input
    leaf2431InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2431LowerChecked :
    lowerCheck 24 leaf2431Box leaf2431Inputs = true := by
  rfl'

private theorem leaf2431CoversExact : CoversExact 8
    leaf2431Box leaf2431Certificate leaf2431InnerLog leaf2431Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk206RoundedFacts chi199RoundedFacts
    innerPair71RoundedFacts leaf2431RoundedFacts (by rfl)

private theorem leaf2431FlatSound : Sound leaf2431Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2431CertificateValid
    leaf2431InnerLogValid leaf2431CoversExact leaf2431LowerChecked

private noncomputable def leaf2432Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (215/64), chiLo := (59/256), chiHi := (15/64) }

private noncomputable def leaf2432Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742373/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432348672) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1901115541/1073741824) }, upper := { exponent := 0, mantissa := (7321/4096) } }, logOuter := sk205LogOuterCertificate, logK := sk205LogKCertificate, logChi := chi200LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869270527/274864697344) } }, logDArg := sk205LogDArgCertificate }

private noncomputable def leaf2432InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf2432LocalValidity :
    LeafFacts leaf2432Box leaf2432Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2432Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432348672) }) = true
      norm_num [leaf2432Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2432CertificateValid :
    WideCertificateValid leaf2432Box leaf2432Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk205ValidityFacts chi200ValidityFacts
    leaf2432LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2432CoverageChecked :
    coverageCheck (innerAD leaf2432Box) leaf2432InnerLog = true := by
  rfl'

private theorem leaf2432InnerLogValid :
    leaf2432InnerLog.Valid 8 (innerAD leaf2432Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf2432CoverageChecked

private noncomputable def leaf2432InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (726835/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf2432InputLogOnePlusV_eq :
    leaf2432InputLogOnePlusV = outerEnclosure 24
      (leaf2432Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2432RoundedFacts : LeafRoundedFacts 8
    leaf2432Certificate.logOnePlusV leaf2432InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2432InputLogOnePlusV_eq }

private noncomputable def leaf2432Inputs : Inputs :=
  inputsOfCaches globalInput sk205RoundedInputs
    chi200InputQChi innerPair71Input
    leaf2432InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2432LowerChecked :
    lowerCheck 24 leaf2432Box leaf2432Inputs = true := by
  rfl'

private theorem leaf2432CoversExact : CoversExact 8
    leaf2432Box leaf2432Certificate leaf2432InnerLog leaf2432Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk205RoundedFacts chi200RoundedFacts
    innerPair71RoundedFacts leaf2432RoundedFacts (by rfl)

private theorem leaf2432FlatSound : Sound leaf2432Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2432CertificateValid
    leaf2432InnerLogValid leaf2432CoversExact leaf2432LowerChecked

private noncomputable def leaf2433Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (215/64), kHi := (27/8), chiLo := (59/256), chiHi := (15/64) }

private noncomputable def leaf2433Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742375/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432317952) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1904981927/1073741824) }, upper := { exponent := 0, mantissa := (917/512) } }, logOuter := sk206LogOuterCertificate, logK := sk206LogKCertificate, logChi := chi200LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869239807/274864635904) } }, logDArg := sk206LogDArgCertificate }

private noncomputable def leaf2433InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf2433LocalValidity :
    LeafFacts leaf2433Box leaf2433Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2433Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432317952) }) = true
      norm_num [leaf2433Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2433CertificateValid :
    WideCertificateValid leaf2433Box leaf2433Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk206ValidityFacts chi200ValidityFacts
    leaf2433LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2433CoverageChecked :
    coverageCheck (innerAD leaf2433Box) leaf2433InnerLog = true := by
  rfl'

private theorem leaf2433InnerLogValid :
    leaf2433InnerLog.Valid 8 (innerAD leaf2433Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf2433CoverageChecked

private noncomputable def leaf2433InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814681/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2433InputLogOnePlusV_eq :
    leaf2433InputLogOnePlusV = outerEnclosure 24
      (leaf2433Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2433RoundedFacts : LeafRoundedFacts 8
    leaf2433Certificate.logOnePlusV leaf2433InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2433InputLogOnePlusV_eq }

private noncomputable def leaf2433Inputs : Inputs :=
  inputsOfCaches globalInput sk206RoundedInputs
    chi200InputQChi innerPair71Input
    leaf2433InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2433LowerChecked :
    lowerCheck 24 leaf2433Box leaf2433Inputs = true := by
  rfl'

private theorem leaf2433CoversExact : CoversExact 8
    leaf2433Box leaf2433Certificate leaf2433InnerLog leaf2433Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk206RoundedFacts chi200RoundedFacts
    innerPair71RoundedFacts leaf2433RoundedFacts (by rfl)

private theorem leaf2433FlatSound : Sound leaf2433Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2433CertificateValid
    leaf2433InnerLogValid leaf2433CoversExact leaf2433LowerChecked

private noncomputable def leaf2434Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (15/64), chiHi := (61/256) }

private noncomputable def leaf2434Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871243/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68716197376) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (945757495/536870912) }, upper := { exponent := 0, mantissa := (14597/8192) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi191LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434691071/137432394752) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf2434InnerLog : WideLogData :=
  innerPair219Data

set_option maxRecDepth 1000000 in
private theorem leaf2434LocalValidity :
    LeafFacts leaf2434Box leaf2434Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2434Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68716197376) }) = true
      norm_num [leaf2434Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2434CertificateValid :
    WideCertificateValid leaf2434Box leaf2434Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi191ValidityFacts
    leaf2434LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2434CoverageChecked :
    coverageCheck (innerAD leaf2434Box) leaf2434InnerLog = true := by
  rfl'

private theorem leaf2434InnerLogValid :
    leaf2434InnerLog.Valid 8 (innerAD leaf2434Box) :=
  wideLogDataValid_of_cachedCheck endpoint66PositiveFacts
    endpoint183PositiveFacts.valid leaf2434CoverageChecked

private noncomputable def leaf2434InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629361/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2434InputLogOnePlusV_eq :
    leaf2434InputLogOnePlusV = outerEnclosure 24
      (leaf2434Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2434RoundedFacts : LeafRoundedFacts 8
    leaf2434Certificate.logOnePlusV leaf2434InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2434InputLogOnePlusV_eq }

private noncomputable def leaf2434Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi191InputQChi innerPair219Input
    leaf2434InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2434LowerChecked :
    lowerCheck 24 leaf2434Box leaf2434Inputs = true := by
  rfl'

private theorem leaf2434CoversExact : CoversExact 8
    leaf2434Box leaf2434Certificate leaf2434InnerLog leaf2434Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi191RoundedFacts
    innerPair219RoundedFacts leaf2434RoundedFacts (by rfl)

private theorem leaf2434FlatSound : Sound leaf2434Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2434CertificateValid
    leaf2434InnerLogValid leaf2434CoversExact leaf2434LowerChecked

private noncomputable def leaf2435Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (61/256), chiHi := (31/128) }

private noncomputable def leaf2435Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871245/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68716143616) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (952572821/536870912) }, upper := { exponent := 0, mantissa := (7351/4096) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi192LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434637311/137432287232) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf2435InnerLog : WideLogData :=
  innerPair209Data

set_option maxRecDepth 1000000 in
private theorem leaf2435LocalValidity :
    LeafFacts leaf2435Box leaf2435Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2435Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68716143616) }) = true
      norm_num [leaf2435Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2435CertificateValid :
    WideCertificateValid leaf2435Box leaf2435Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi192ValidityFacts
    leaf2435LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2435CoverageChecked :
    coverageCheck (innerAD leaf2435Box) leaf2435InnerLog = true := by
  rfl'

private theorem leaf2435InnerLogValid :
    leaf2435InnerLog.Valid 8 (innerAD leaf2435Box) :=
  wideLogDataValid_of_cachedCheck endpoint63PositiveFacts
    endpoint67PositiveFacts.valid leaf2435CoverageChecked

private noncomputable def leaf2435InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453671/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf2435InputLogOnePlusV_eq :
    leaf2435InputLogOnePlusV = outerEnclosure 24
      (leaf2435Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2435RoundedFacts : LeafRoundedFacts 8
    leaf2435Certificate.logOnePlusV leaf2435InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2435InputLogOnePlusV_eq }

private noncomputable def leaf2435Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi192InputQChi innerPair209Input
    leaf2435InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2435LowerChecked :
    lowerCheck 24 leaf2435Box leaf2435Inputs = true := by
  rfl'

private theorem leaf2435CoversExact : CoversExact 8
    leaf2435Box leaf2435Certificate leaf2435InnerLog leaf2435Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi192RoundedFacts
    innerPair209RoundedFacts leaf2435RoundedFacts (by rfl)

private theorem leaf2435FlatSound : Sound leaf2435Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2435CertificateValid
    leaf2435InnerLogValid leaf2435CoversExact leaf2435LowerChecked

private noncomputable def leaf2436Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (15/64), chiHi := (61/256) }

private noncomputable def leaf2436Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871245/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68716166144) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (949689413/536870912) }, upper := { exponent := 0, mantissa := (7329/4096) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi191LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434659839/137432332288) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf2436InnerLog : WideLogData :=
  innerPair211Data

set_option maxRecDepth 1000000 in
private theorem leaf2436LocalValidity :
    LeafFacts leaf2436Box leaf2436Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2436Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68716166144) }) = true
      norm_num [leaf2436Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2436CertificateValid :
    WideCertificateValid leaf2436Box leaf2436Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi191ValidityFacts
    leaf2436LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2436CoverageChecked :
    coverageCheck (innerAD leaf2436Box) leaf2436InnerLog = true := by
  rfl'

private theorem leaf2436InnerLogValid :
    leaf2436InnerLog.Valid 8 (innerAD leaf2436Box) :=
  wideLogDataValid_of_cachedCheck endpoint63PositiveFacts
    endpoint184PositiveFacts.valid leaf2436CoverageChecked

private noncomputable def leaf2436InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629365/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2436InputLogOnePlusV_eq :
    leaf2436InputLogOnePlusV = outerEnclosure 24
      (leaf2436Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2436RoundedFacts : LeafRoundedFacts 8
    leaf2436Certificate.logOnePlusV leaf2436InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2436InputLogOnePlusV_eq }

private noncomputable def leaf2436Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi191InputQChi innerPair211Input
    leaf2436InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2436LowerChecked :
    lowerCheck 24 leaf2436Box leaf2436Inputs = true := by
  rfl'

private theorem leaf2436CoversExact : CoversExact 8
    leaf2436Box leaf2436Certificate leaf2436InnerLog leaf2436Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi191RoundedFacts
    innerPair211RoundedFacts leaf2436RoundedFacts (by rfl)

private theorem leaf2436FlatSound : Sound leaf2436Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2436CertificateValid
    leaf2436InnerLogValid leaf2436CoversExact leaf2436LowerChecked

private noncomputable def leaf2437Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (61/256), chiHi := (31/128) }

private noncomputable def leaf2437Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871247/536870912) }, vSqrt := { lower := (65529/65536), upper := (22906164565/22905370624) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (956570271/536870912) }, upper := { exponent := 0, mantissa := (3691/2048) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi192LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (45811535189/45810741248) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf2437InnerLog : WideLogData :=
  innerPair227Data

set_option maxRecDepth 1000000 in
private theorem leaf2437LocalValidity :
    LeafFacts leaf2437Box leaf2437Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2437Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22906164565/22905370624) }) = true
      norm_num [leaf2437Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2437CertificateValid :
    WideCertificateValid leaf2437Box leaf2437Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi192ValidityFacts
    leaf2437LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2437CoverageChecked :
    coverageCheck (innerAD leaf2437Box) leaf2437InnerLog = true := by
  rfl'

private theorem leaf2437InnerLogValid :
    leaf2437InnerLog.Valid 8 (innerAD leaf2437Box) :=
  wideLogDataValid_of_cachedCheck endpoint68PositiveFacts
    endpoint185PositiveFacts.valid leaf2437CoverageChecked

private noncomputable def leaf2437InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907343/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2437InputLogOnePlusV_eq :
    leaf2437InputLogOnePlusV = outerEnclosure 24
      (leaf2437Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2437RoundedFacts : LeafRoundedFacts 8
    leaf2437Certificate.logOnePlusV leaf2437InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2437InputLogOnePlusV_eq }

private noncomputable def leaf2437Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi192InputQChi innerPair227Input
    leaf2437InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2437LowerChecked :
    lowerCheck 24 leaf2437Box leaf2437Inputs = true := by
  rfl'

private theorem leaf2437CoversExact : CoversExact 8
    leaf2437Box leaf2437Certificate leaf2437InnerLog leaf2437Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi192RoundedFacts
    innerPair227RoundedFacts leaf2437RoundedFacts (by rfl)

private theorem leaf2437FlatSound : Sound leaf2437Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2437CertificateValid
    leaf2437InnerLogValid leaf2437CoversExact leaf2437LowerChecked

private noncomputable def leaf2438Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (31/128), chiHi := (63/256) }

private noncomputable def leaf2438Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871247/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68716089856) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (959388147/536870912) }, upper := { exponent := 0, mantissa := (14807/8192) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi189LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434583551/137432179712) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf2438InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf2438LocalValidity :
    LeafFacts leaf2438Box leaf2438Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2438Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68716089856) }) = true
      norm_num [leaf2438Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2438CertificateValid :
    WideCertificateValid leaf2438Box leaf2438Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi189ValidityFacts
    leaf2438LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2438CoverageChecked :
    coverageCheck (innerAD leaf2438Box) leaf2438InnerLog = true := by
  rfl'

private theorem leaf2438InnerLogValid :
    leaf2438InnerLog.Valid 8 (innerAD leaf2438Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf2438CoverageChecked

private noncomputable def leaf2438InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814687/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2438InputLogOnePlusV_eq :
    leaf2438InputLogOnePlusV = outerEnclosure 24
      (leaf2438Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2438RoundedFacts : LeafRoundedFacts 8
    leaf2438Certificate.logOnePlusV leaf2438InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2438InputLogOnePlusV_eq }

private noncomputable def leaf2438Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi189InputQChi innerPair71Input
    leaf2438InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2438LowerChecked :
    lowerCheck 24 leaf2438Box leaf2438Inputs = true := by
  rfl'

private theorem leaf2438CoversExact : CoversExact 8
    leaf2438Box leaf2438Certificate leaf2438InnerLog leaf2438Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi189RoundedFacts
    innerPair71RoundedFacts leaf2438RoundedFacts (by rfl)

private theorem leaf2438FlatSound : Sound leaf2438Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2438CertificateValid
    leaf2438InnerLogValid leaf2438CoversExact leaf2438LowerChecked

private noncomputable def leaf2439Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (63/256), chiHi := (1/4) }

private noncomputable def leaf2439Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871249/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68716036096) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (966203473/536870912) }, upper := { exponent := 0, mantissa := (233/128) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi190LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434529791/137432072192) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf2439InnerLog : WideLogData :=
  innerPair221Data

set_option maxRecDepth 1000000 in
private theorem leaf2439LocalValidity :
    LeafFacts leaf2439Box leaf2439Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2439Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68716036096) }) = true
      norm_num [leaf2439Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2439CertificateValid :
    WideCertificateValid leaf2439Box leaf2439Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi190ValidityFacts
    leaf2439LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2439CoverageChecked :
    coverageCheck (innerAD leaf2439Box) leaf2439InnerLog = true := by
  rfl'

private theorem leaf2439InnerLogValid :
    leaf2439InnerLog.Valid 8 (innerAD leaf2439Box) :=
  wideLogDataValid_of_cachedCheck endpoint67PositiveFacts
    endpoint64PositiveFacts.valid leaf2439CoverageChecked

private noncomputable def leaf2439InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629381/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2439InputLogOnePlusV_eq :
    leaf2439InputLogOnePlusV = outerEnclosure 24
      (leaf2439Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2439RoundedFacts : LeafRoundedFacts 8
    leaf2439Certificate.logOnePlusV leaf2439InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2439InputLogOnePlusV_eq }

private noncomputable def leaf2439Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi190InputQChi innerPair221Input
    leaf2439InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2439LowerChecked :
    lowerCheck 24 leaf2439Box leaf2439Inputs = true := by
  rfl'

private theorem leaf2439CoversExact : CoversExact 8
    leaf2439Box leaf2439Certificate leaf2439InnerLog leaf2439Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi190RoundedFacts
    innerPair221RoundedFacts leaf2439RoundedFacts (by rfl)

private theorem leaf2439FlatSound : Sound leaf2439Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2439CertificateValid
    leaf2439InnerLogValid leaf2439CoversExact leaf2439LowerChecked

private noncomputable def leaf2440Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (31/128), chiHi := (63/256) }

private noncomputable def leaf2440Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871249/536870912) }, vSqrt := { lower := (65529/65536), upper := (13743698739/13743211520) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (963451129/536870912) }, upper := { exponent := 0, mantissa := (7435/4096) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi189LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (27486910259/27486423040) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf2440InnerLog : WideLogData :=
  innerPair465Data

set_option maxRecDepth 1000000 in
private theorem leaf2440LocalValidity :
    LeafFacts leaf2440Box leaf2440Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2440Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (13743698739/13743211520) }) = true
      norm_num [leaf2440Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2440CertificateValid :
    WideCertificateValid leaf2440Box leaf2440Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi189ValidityFacts
    leaf2440LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2440CoverageChecked :
    coverageCheck (innerAD leaf2440Box) leaf2440InnerLog = true := by
  rfl'

private theorem leaf2440InnerLogValid :
    leaf2440InnerLog.Valid 8 (innerAD leaf2440Box) :=
  wideLogDataValid_of_cachedCheck endpoint184PositiveFacts
    endpoint186PositiveFacts.valid leaf2440CoverageChecked

private noncomputable def leaf2440InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814689/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2440InputLogOnePlusV_eq :
    leaf2440InputLogOnePlusV = outerEnclosure 24
      (leaf2440Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2440RoundedFacts : LeafRoundedFacts 8
    leaf2440Certificate.logOnePlusV leaf2440InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2440InputLogOnePlusV_eq }

private noncomputable def leaf2440Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi189InputQChi innerPair465Input
    leaf2440InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2440LowerChecked :
    lowerCheck 24 leaf2440Box leaf2440Inputs = true := by
  rfl'

private theorem leaf2440CoversExact : CoversExact 8
    leaf2440Box leaf2440Certificate leaf2440InnerLog leaf2440Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi189RoundedFacts
    innerPair465RoundedFacts leaf2440RoundedFacts (by rfl)

private theorem leaf2440FlatSound : Sound leaf2440Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2440CertificateValid
    leaf2440InnerLogValid leaf2440CoversExact leaf2440LowerChecked

private noncomputable def leaf2441Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (63/256), chiHi := (1/4) }

private noncomputable def leaf2441Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871251/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68716003328) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (970331987/536870912) }, upper := { exponent := 0, mantissa := (117/64) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi190LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434497023/137432006656) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf2441InnerLog : WideLogData :=
  innerPair221Data

set_option maxRecDepth 1000000 in
private theorem leaf2441LocalValidity :
    LeafFacts leaf2441Box leaf2441Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2441Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68716003328) }) = true
      norm_num [leaf2441Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2441CertificateValid :
    WideCertificateValid leaf2441Box leaf2441Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi190ValidityFacts
    leaf2441LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2441CoverageChecked :
    coverageCheck (innerAD leaf2441Box) leaf2441InnerLog = true := by
  rfl'

private theorem leaf2441InnerLogValid :
    leaf2441InnerLog.Valid 8 (innerAD leaf2441Box) :=
  wideLogDataValid_of_cachedCheck endpoint67PositiveFacts
    endpoint64PositiveFacts.valid leaf2441CoverageChecked

private noncomputable def leaf2441InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629385/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2441InputLogOnePlusV_eq :
    leaf2441InputLogOnePlusV = outerEnclosure 24
      (leaf2441Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2441RoundedFacts : LeafRoundedFacts 8
    leaf2441Certificate.logOnePlusV leaf2441InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2441InputLogOnePlusV_eq }

private noncomputable def leaf2441Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi190InputQChi innerPair221Input
    leaf2441InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2441LowerChecked :
    lowerCheck 24 leaf2441Box leaf2441Inputs = true := by
  rfl'

private theorem leaf2441CoversExact : CoversExact 8
    leaf2441Box leaf2441Certificate leaf2441InnerLog leaf2441Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi190RoundedFacts
    innerPair221RoundedFacts leaf2441RoundedFacts (by rfl)

private theorem leaf2441FlatSound : Sound leaf2441Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2441CertificateValid
    leaf2441InnerLogValid leaf2441CoversExact leaf2441LowerChecked

private noncomputable def leaf2442Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (15/64), chiHi := (61/256) }

private noncomputable def leaf2442Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871247/536870912) }, vSqrt := { lower := (65529/65536), upper := (22906164565/22905378304) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (953621331/536870912) }, upper := { exponent := 0, mantissa := (14719/8192) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi191LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (45811542869/45810756608) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf2442InnerLog : WideLogData :=
  innerPair209Data

set_option maxRecDepth 1000000 in
private theorem leaf2442LocalValidity :
    LeafFacts leaf2442Box leaf2442Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2442Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22906164565/22905378304) }) = true
      norm_num [leaf2442Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2442CertificateValid :
    WideCertificateValid leaf2442Box leaf2442Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi191ValidityFacts
    leaf2442LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2442CoverageChecked :
    coverageCheck (innerAD leaf2442Box) leaf2442InnerLog = true := by
  rfl'

private theorem leaf2442InnerLogValid :
    leaf2442InnerLog.Valid 8 (innerAD leaf2442Box) :=
  wideLogDataValid_of_cachedCheck endpoint63PositiveFacts
    endpoint67PositiveFacts.valid leaf2442CoverageChecked

private noncomputable def leaf2442InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629369/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2442InputLogOnePlusV_eq :
    leaf2442InputLogOnePlusV = outerEnclosure 24
      (leaf2442Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2442RoundedFacts : LeafRoundedFacts 8
    leaf2442Certificate.logOnePlusV leaf2442InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2442InputLogOnePlusV_eq }

private noncomputable def leaf2442Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi191InputQChi innerPair209Input
    leaf2442InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2442LowerChecked :
    lowerCheck 24 leaf2442Box leaf2442Inputs = true := by
  rfl'

private theorem leaf2442CoversExact : CoversExact 8
    leaf2442Box leaf2442Certificate leaf2442InnerLog leaf2442Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi191RoundedFacts
    innerPair209RoundedFacts leaf2442RoundedFacts (by rfl)

private theorem leaf2442FlatSound : Sound leaf2442Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2442CertificateValid
    leaf2442InnerLogValid leaf2442CoversExact leaf2442LowerChecked

private noncomputable def leaf2443Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (61/256), chiHi := (31/128) }

private noncomputable def leaf2443Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871249/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68716080128) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (960567721/536870912) }, upper := { exponent := 0, mantissa := (7413/4096) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi192LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434573823/137432160256) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf2443InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf2443LocalValidity :
    LeafFacts leaf2443Box leaf2443Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2443Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68716080128) }) = true
      norm_num [leaf2443Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2443CertificateValid :
    WideCertificateValid leaf2443Box leaf2443Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi192ValidityFacts
    leaf2443LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2443CoverageChecked :
    coverageCheck (innerAD leaf2443Box) leaf2443InnerLog = true := by
  rfl'

private theorem leaf2443InnerLogValid :
    leaf2443InnerLog.Valid 8 (innerAD leaf2443Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf2443CoverageChecked

private noncomputable def leaf2443InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629375/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2443InputLogOnePlusV_eq :
    leaf2443InputLogOnePlusV = outerEnclosure 24
      (leaf2443Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2443RoundedFacts : LeafRoundedFacts 8
    leaf2443Certificate.logOnePlusV leaf2443InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2443InputLogOnePlusV_eq }

private noncomputable def leaf2443Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi192InputQChi innerPair71Input
    leaf2443InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2443LowerChecked :
    lowerCheck 24 leaf2443Box leaf2443Inputs = true := by
  rfl'

private theorem leaf2443CoversExact : CoversExact 8
    leaf2443Box leaf2443Certificate leaf2443InnerLog leaf2443Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi192RoundedFacts
    innerPair71RoundedFacts leaf2443RoundedFacts (by rfl)

private theorem leaf2443FlatSound : Sound leaf2443Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2443CertificateValid
    leaf2443InnerLogValid leaf2443CoversExact leaf2443LowerChecked

private noncomputable def leaf2444Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (215/64), chiLo := (15/64), chiHi := (61/256) }

private noncomputable def leaf2444Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742375/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432238592) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1915139387/1073741824) }, upper := { exponent := 0, mantissa := (29499/16384) } }, logOuter := sk205LogOuterCertificate, logK := sk205LogKCertificate, logChi := chi191LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869160447/274864477184) } }, logDArg := sk205LogDArgCertificate }

private noncomputable def leaf2444InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf2444LocalValidity :
    LeafFacts leaf2444Box leaf2444Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2444Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432238592) }) = true
      norm_num [leaf2444Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2444CertificateValid :
    WideCertificateValid leaf2444Box leaf2444Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk205ValidityFacts chi191ValidityFacts
    leaf2444LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2444CoverageChecked :
    coverageCheck (innerAD leaf2444Box) leaf2444InnerLog = true := by
  rfl'

private theorem leaf2444InnerLogValid :
    leaf2444InnerLog.Valid 8 (innerAD leaf2444Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf2444CoverageChecked

private noncomputable def leaf2444InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629367/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2444InputLogOnePlusV_eq :
    leaf2444InputLogOnePlusV = outerEnclosure 24
      (leaf2444Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2444RoundedFacts : LeafRoundedFacts 8
    leaf2444Certificate.logOnePlusV leaf2444InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2444InputLogOnePlusV_eq }

private noncomputable def leaf2444Inputs : Inputs :=
  inputsOfCaches globalInput sk205RoundedInputs
    chi191InputQChi innerPair71Input
    leaf2444InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2444LowerChecked :
    lowerCheck 24 leaf2444Box leaf2444Inputs = true := by
  rfl'

private theorem leaf2444CoversExact : CoversExact 8
    leaf2444Box leaf2444Certificate leaf2444InnerLog leaf2444Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk205RoundedFacts chi191RoundedFacts
    innerPair71RoundedFacts leaf2444RoundedFacts (by rfl)

private theorem leaf2444FlatSound : Sound leaf2444Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2444CertificateValid
    leaf2444InnerLogValid leaf2444CoversExact leaf2444LowerChecked

private noncomputable def leaf2445Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (215/64), kHi := (27/8), chiLo := (15/64), chiHi := (61/256) }

private noncomputable def leaf2445Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742377/1073741824) }, vSqrt := { lower := (65529/65536), upper := (27487384371/27486441472) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1919071305/1073741824) }, upper := { exponent := 0, mantissa := (3695/2048) } }, logOuter := sk206LogOuterCertificate, logK := sk206LogKCertificate, logChi := chi191LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (54973825843/54972882944) } }, logDArg := sk206LogDArgCertificate }

private noncomputable def leaf2445InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf2445LocalValidity :
    LeafFacts leaf2445Box leaf2445Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2445Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (27487384371/27486441472) }) = true
      norm_num [leaf2445Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2445CertificateValid :
    WideCertificateValid leaf2445Box leaf2445Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk206ValidityFacts chi191ValidityFacts
    leaf2445LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2445CoverageChecked :
    coverageCheck (innerAD leaf2445Box) leaf2445InnerLog = true := by
  rfl'

private theorem leaf2445InnerLogValid :
    leaf2445InnerLog.Valid 8 (innerAD leaf2445Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf2445CoverageChecked

private noncomputable def leaf2445InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629369/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2445InputLogOnePlusV_eq :
    leaf2445InputLogOnePlusV = outerEnclosure 24
      (leaf2445Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2445RoundedFacts : LeafRoundedFacts 8
    leaf2445Certificate.logOnePlusV leaf2445InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2445InputLogOnePlusV_eq }

private noncomputable def leaf2445Inputs : Inputs :=
  inputsOfCaches globalInput sk206RoundedInputs
    chi191InputQChi innerPair71Input
    leaf2445InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2445LowerChecked :
    lowerCheck 24 leaf2445Box leaf2445Inputs = true := by
  rfl'

private theorem leaf2445CoversExact : CoversExact 8
    leaf2445Box leaf2445Certificate leaf2445InnerLog leaf2445Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk206RoundedFacts chi191RoundedFacts
    innerPair71RoundedFacts leaf2445RoundedFacts (by rfl)

private theorem leaf2445FlatSound : Sound leaf2445Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2445CertificateValid
    leaf2445InnerLogValid leaf2445CoversExact leaf2445LowerChecked

private noncomputable def leaf2446Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (215/64), chiLo := (61/256), chiHi := (31/128) }

private noncomputable def leaf2446Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742377/1073741824) }, vSqrt := { lower := (65529/65536), upper := (45812307285/45810709504) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1929163233/1073741824) }, upper := { exponent := 0, mantissa := (14857/8192) } }, logOuter := sk205LogOuterCertificate, logK := sk205LogKCertificate, logChi := chi192LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (91623016789/91621419008) } }, logDArg := sk205LogDArgCertificate }

private noncomputable def leaf2446InnerLog : WideLogData :=
  innerPair72Data

set_option maxRecDepth 1000000 in
private theorem leaf2446LocalValidity :
    LeafFacts leaf2446Box leaf2446Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2446Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (45812307285/45810709504) }) = true
      norm_num [leaf2446Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2446CertificateValid :
    WideCertificateValid leaf2446Box leaf2446Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk205ValidityFacts chi192ValidityFacts
    leaf2446LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2446CoverageChecked :
    coverageCheck (innerAD leaf2446Box) leaf2446InnerLog = true := by
  rfl'

private theorem leaf2446InnerLogValid :
    leaf2446InnerLog.Valid 8 (innerAD leaf2446Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint22PositiveFacts.valid leaf2446CoverageChecked

private noncomputable def leaf2446InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629373/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2446InputLogOnePlusV_eq :
    leaf2446InputLogOnePlusV = outerEnclosure 24
      (leaf2446Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2446RoundedFacts : LeafRoundedFacts 8
    leaf2446Certificate.logOnePlusV leaf2446InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2446InputLogOnePlusV_eq }

private noncomputable def leaf2446Inputs : Inputs :=
  inputsOfCaches globalInput sk205RoundedInputs
    chi192InputQChi innerPair72Input
    leaf2446InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2446LowerChecked :
    lowerCheck 24 leaf2446Box leaf2446Inputs = true := by
  rfl'

private theorem leaf2446CoversExact : CoversExact 8
    leaf2446Box leaf2446Certificate leaf2446InnerLog leaf2446Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk205RoundedFacts chi192RoundedFacts
    innerPair72RoundedFacts leaf2446RoundedFacts (by rfl)

private theorem leaf2446FlatSound : Sound leaf2446Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2446CertificateValid
    leaf2446InnerLogValid leaf2446CoversExact leaf2446LowerChecked

private noncomputable def leaf2447Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (215/64), kHi := (27/8), chiLo := (61/256), chiHi := (31/128) }

private noncomputable def leaf2447Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742379/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432096768) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1933160683/1073741824) }, upper := { exponent := 0, mantissa := (1861/1024) } }, logOuter := sk206LogOuterCertificate, logK := sk206LogKCertificate, logChi := chi192LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869018623/274864193536) } }, logDArg := sk206LogDArgCertificate }

private noncomputable def leaf2447InnerLog : WideLogData :=
  innerPair72Data

set_option maxRecDepth 1000000 in
private theorem leaf2447LocalValidity :
    LeafFacts leaf2447Box leaf2447Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2447Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432096768) }) = true
      norm_num [leaf2447Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2447CertificateValid :
    WideCertificateValid leaf2447Box leaf2447Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk206ValidityFacts chi192ValidityFacts
    leaf2447LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2447CoverageChecked :
    coverageCheck (innerAD leaf2447Box) leaf2447InnerLog = true := by
  rfl'

private theorem leaf2447InnerLogValid :
    leaf2447InnerLog.Valid 8 (innerAD leaf2447Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint22PositiveFacts.valid leaf2447CoverageChecked

private noncomputable def leaf2447InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629375/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2447InputLogOnePlusV_eq :
    leaf2447InputLogOnePlusV = outerEnclosure 24
      (leaf2447Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2447RoundedFacts : LeafRoundedFacts 8
    leaf2447Certificate.logOnePlusV leaf2447InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2447InputLogOnePlusV_eq }

private noncomputable def leaf2447Inputs : Inputs :=
  inputsOfCaches globalInput sk206RoundedInputs
    chi192InputQChi innerPair72Input
    leaf2447InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2447LowerChecked :
    lowerCheck 24 leaf2447Box leaf2447Inputs = true := by
  rfl'

private theorem leaf2447CoversExact : CoversExact 8
    leaf2447Box leaf2447Certificate leaf2447InnerLog leaf2447Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk206RoundedFacts chi192RoundedFacts
    innerPair72RoundedFacts leaf2447RoundedFacts (by rfl)

private theorem leaf2447FlatSound : Sound leaf2447Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2447CertificateValid
    leaf2447InnerLogValid leaf2447CoversExact leaf2447LowerChecked

private noncomputable def leaf2448Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (31/128), chiHi := (63/256) }

private noncomputable def leaf2448Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871251/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68716025344) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (967514111/536870912) }, upper := { exponent := 0, mantissa := (14933/8192) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi189LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434519039/137432050688) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf2448InnerLog : WideLogData :=
  innerPair468Data

set_option maxRecDepth 1000000 in
private theorem leaf2448LocalValidity :
    LeafFacts leaf2448Box leaf2448Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2448Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68716025344) }) = true
      norm_num [leaf2448Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2448CertificateValid :
    WideCertificateValid leaf2448Box leaf2448Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi189ValidityFacts
    leaf2448LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2448CoverageChecked :
    coverageCheck (innerAD leaf2448Box) leaf2448InnerLog = true := by
  rfl'

private theorem leaf2448InnerLogValid :
    leaf2448InnerLog.Valid 8 (innerAD leaf2448Box) :=
  wideLogDataValid_of_cachedCheck endpoint187PositiveFacts
    endpoint188PositiveFacts.valid leaf2448CoverageChecked

private noncomputable def leaf2448InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814691/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2448InputLogOnePlusV_eq :
    leaf2448InputLogOnePlusV = outerEnclosure 24
      (leaf2448Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2448RoundedFacts : LeafRoundedFacts 8
    leaf2448Certificate.logOnePlusV leaf2448InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2448InputLogOnePlusV_eq }

private noncomputable def leaf2448Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi189InputQChi innerPair468Input
    leaf2448InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2448LowerChecked :
    lowerCheck 24 leaf2448Box leaf2448Inputs = true := by
  rfl'

private theorem leaf2448CoversExact : CoversExact 8
    leaf2448Box leaf2448Certificate leaf2448InnerLog leaf2448Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi189RoundedFacts
    innerPair468RoundedFacts leaf2448RoundedFacts (by rfl)

private theorem leaf2448FlatSound : Sound leaf2448Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2448CertificateValid
    leaf2448InnerLogValid leaf2448CoversExact leaf2448LowerChecked

private noncomputable def leaf2449Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (63/256), chiHi := (1/4) }

private noncomputable def leaf2449Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871253/536870912) }, vSqrt := { lower := (65529/65536), upper := (4581232913/4581064704) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (974460501/536870912) }, upper := { exponent := 0, mantissa := (235/128) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi190LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (9162297617/9162129408) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf2449InnerLog : WideLogData :=
  innerPair98Data

set_option maxRecDepth 1000000 in
private theorem leaf2449LocalValidity :
    LeafFacts leaf2449Box leaf2449Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2449Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4581232913/4581064704) }) = true
      norm_num [leaf2449Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2449CertificateValid :
    WideCertificateValid leaf2449Box leaf2449Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi190ValidityFacts
    leaf2449LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2449CoverageChecked :
    coverageCheck (innerAD leaf2449Box) leaf2449InnerLog = true := by
  rfl'

private theorem leaf2449InnerLogValid :
    leaf2449InnerLog.Valid 8 (innerAD leaf2449Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint189PositiveFacts.valid leaf2449CoverageChecked

private noncomputable def leaf2449InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629389/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2449InputLogOnePlusV_eq :
    leaf2449InputLogOnePlusV = outerEnclosure 24
      (leaf2449Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2449RoundedFacts : LeafRoundedFacts 8
    leaf2449Certificate.logOnePlusV leaf2449InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2449InputLogOnePlusV_eq }

private noncomputable def leaf2449Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi190InputQChi innerPair98Input
    leaf2449InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2449LowerChecked :
    lowerCheck 24 leaf2449Box leaf2449Inputs = true := by
  rfl'

private theorem leaf2449CoversExact : CoversExact 8
    leaf2449Box leaf2449Certificate leaf2449InnerLog leaf2449Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi190RoundedFacts
    innerPair98RoundedFacts leaf2449RoundedFacts (by rfl)

private theorem leaf2449FlatSound : Sound leaf2449Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2449CertificateValid
    leaf2449InnerLogValid leaf2449CoversExact leaf2449LowerChecked

private noncomputable def leaf2450Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (215/64), chiLo := (31/128), chiHi := (63/256) }

private noncomputable def leaf2450Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742379/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432018432) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1943187079/1073741824) }, upper := { exponent := 0, mantissa := (29929/16384) } }, logOuter := sk205LogOuterCertificate, logK := sk205LogKCertificate, logChi := chi189LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274868940287/274864036864) } }, logDArg := sk205LogDArgCertificate }

private noncomputable def leaf2450InnerLog : WideLogData :=
  innerPair72Data

set_option maxRecDepth 1000000 in
private theorem leaf2450LocalValidity :
    LeafFacts leaf2450Box leaf2450Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2450Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432018432) }) = true
      norm_num [leaf2450Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2450CertificateValid :
    WideCertificateValid leaf2450Box leaf2450Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk205ValidityFacts chi189ValidityFacts
    leaf2450LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2450CoverageChecked :
    coverageCheck (innerAD leaf2450Box) leaf2450InnerLog = true := by
  rfl'

private theorem leaf2450InnerLogValid :
    leaf2450InnerLog.Valid 8 (innerAD leaf2450Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint22PositiveFacts.valid leaf2450CoverageChecked

private noncomputable def leaf2450InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907345/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2450InputLogOnePlusV_eq :
    leaf2450InputLogOnePlusV = outerEnclosure 24
      (leaf2450Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2450RoundedFacts : LeafRoundedFacts 8
    leaf2450Certificate.logOnePlusV leaf2450InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2450InputLogOnePlusV_eq }

private noncomputable def leaf2450Inputs : Inputs :=
  inputsOfCaches globalInput sk205RoundedInputs
    chi189InputQChi innerPair72Input
    leaf2450InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2450LowerChecked :
    lowerCheck 24 leaf2450Box leaf2450Inputs = true := by
  rfl'

private theorem leaf2450CoversExact : CoversExact 8
    leaf2450Box leaf2450Certificate leaf2450InnerLog leaf2450Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk205RoundedFacts chi189RoundedFacts
    innerPair72RoundedFacts leaf2450RoundedFacts (by rfl)

private theorem leaf2450FlatSound : Sound leaf2450Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2450CertificateValid
    leaf2450InnerLogValid leaf2450CoversExact leaf2450LowerChecked

private noncomputable def leaf2451Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (215/64), kHi := (27/8), chiLo := (31/128), chiHi := (63/256) }

private noncomputable def leaf2451Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742381/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137431986176) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1947250061/1073741824) }, upper := { exponent := 0, mantissa := (3749/2048) } }, logOuter := sk206LogOuterCertificate, logK := sk206LogKCertificate, logChi := chi189LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274868908031/274863972352) } }, logDArg := sk206LogDArgCertificate }

private noncomputable def leaf2451InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf2451LocalValidity :
    LeafFacts leaf2451Box leaf2451Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2451Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137431986176) }) = true
      norm_num [leaf2451Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2451CertificateValid :
    WideCertificateValid leaf2451Box leaf2451Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk206ValidityFacts chi189ValidityFacts
    leaf2451LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2451CoverageChecked :
    coverageCheck (innerAD leaf2451Box) leaf2451InnerLog = true := by
  rfl'

private theorem leaf2451InnerLogValid :
    leaf2451InnerLog.Valid 8 (innerAD leaf2451Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf2451CoverageChecked

private noncomputable def leaf2451InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814691/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2451InputLogOnePlusV_eq :
    leaf2451InputLogOnePlusV = outerEnclosure 24
      (leaf2451Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2451RoundedFacts : LeafRoundedFacts 8
    leaf2451Certificate.logOnePlusV leaf2451InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2451InputLogOnePlusV_eq }

private noncomputable def leaf2451Inputs : Inputs :=
  inputsOfCaches globalInput sk206RoundedInputs
    chi189InputQChi innerPair91Input
    leaf2451InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2451LowerChecked :
    lowerCheck 24 leaf2451Box leaf2451Inputs = true := by
  rfl'

private theorem leaf2451CoversExact : CoversExact 8
    leaf2451Box leaf2451Certificate leaf2451InnerLog leaf2451Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk206RoundedFacts chi189RoundedFacts
    innerPair91RoundedFacts leaf2451RoundedFacts (by rfl)

private theorem leaf2451FlatSound : Sound leaf2451Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2451CertificateValid
    leaf2451InnerLogValid leaf2451CoversExact leaf2451LowerChecked

private noncomputable def leaf2452Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (63/256), chiHi := (1/4) }

private noncomputable def leaf2452Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871255/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715937792) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (978589015/536870912) }, upper := { exponent := 0, mantissa := (59/32) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi190LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434431487/137431875584) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf2452InnerLog : WideLogData :=
  innerPair94Data

set_option maxRecDepth 1000000 in
private theorem leaf2452LocalValidity :
    LeafFacts leaf2452Box leaf2452Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2452Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715937792) }) = true
      norm_num [leaf2452Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2452CertificateValid :
    WideCertificateValid leaf2452Box leaf2452Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi190ValidityFacts
    leaf2452LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2452CoverageChecked :
    coverageCheck (innerAD leaf2452Box) leaf2452InnerLog = true := by
  rfl'

private theorem leaf2452InnerLogValid :
    leaf2452InnerLog.Valid 8 (innerAD leaf2452Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint61PositiveFacts.valid leaf2452CoverageChecked

private noncomputable def leaf2452InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629393/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2452InputLogOnePlusV_eq :
    leaf2452InputLogOnePlusV = outerEnclosure 24
      (leaf2452Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2452RoundedFacts : LeafRoundedFacts 8
    leaf2452Certificate.logOnePlusV leaf2452InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2452InputLogOnePlusV_eq }

private noncomputable def leaf2452Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi190InputQChi innerPair94Input
    leaf2452InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2452LowerChecked :
    lowerCheck 24 leaf2452Box leaf2452Inputs = true := by
  rfl'

private theorem leaf2452CoversExact : CoversExact 8
    leaf2452Box leaf2452Certificate leaf2452InnerLog leaf2452Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi190RoundedFacts
    innerPair94RoundedFacts leaf2452RoundedFacts (by rfl)

private theorem leaf2452FlatSound : Sound leaf2452Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2452CertificateValid
    leaf2452InnerLogValid leaf2452CoversExact leaf2452LowerChecked

private noncomputable def component52Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (7/32), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component52Node0_sound : Sound component52Node0Box :=
  sound_of_literal_split component52Node0Box leaf2416Box leaf2417Box
    .k (209/64) (by rfl) (by rfl)
    leaf2416FlatSound leaf2417FlatSound

private noncomputable def component52Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (7/32), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component52Node1_sound : Sound component52Node1Box :=
  sound_of_literal_split component52Node1Box leaf2418Box leaf2419Box
    .k (211/64) (by rfl) (by rfl)
    leaf2418FlatSound leaf2419FlatSound

private noncomputable def component52Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (7/32), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component52Node2_sound : Sound component52Node2Box :=
  sound_of_literal_split component52Node2Box component52Node0Box component52Node1Box
    .k (105/32) (by rfl) (by rfl)
    component52Node0_sound component52Node1_sound

private noncomputable def component52Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (29/128), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component52Node3_sound : Sound component52Node3Box :=
  sound_of_literal_split component52Node3Box leaf2420Box leaf2421Box
    .k (209/64) (by rfl) (by rfl)
    leaf2420FlatSound leaf2421FlatSound

private noncomputable def component52Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (29/128), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component52Node4_sound : Sound component52Node4Box :=
  sound_of_literal_split component52Node4Box leaf2422Box leaf2423Box
    .k (211/64) (by rfl) (by rfl)
    leaf2422FlatSound leaf2423FlatSound

private noncomputable def component52Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (29/128), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component52Node5_sound : Sound component52Node5Box :=
  sound_of_literal_split component52Node5Box component52Node3Box component52Node4Box
    .k (105/32) (by rfl) (by rfl)
    component52Node3_sound component52Node4_sound

private noncomputable def component52Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component52Node6_sound : Sound component52Node6Box :=
  sound_of_literal_split component52Node6Box component52Node2Box component52Node5Box
    .chi (29/128) (by rfl) (by rfl)
    component52Node2_sound component52Node5_sound

private noncomputable def component52Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (7/32), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component52Node7_sound : Sound component52Node7Box :=
  sound_of_literal_split component52Node7Box leaf2424Box leaf2425Box
    .k (213/64) (by rfl) (by rfl)
    leaf2424FlatSound leaf2425FlatSound

private noncomputable def component52Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (7/32), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component52Node8_sound : Sound component52Node8Box :=
  sound_of_literal_split component52Node8Box leaf2426Box leaf2427Box
    .k (215/64) (by rfl) (by rfl)
    leaf2426FlatSound leaf2427FlatSound

private noncomputable def component52Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (7/32), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component52Node9_sound : Sound component52Node9Box :=
  sound_of_literal_split component52Node9Box component52Node7Box component52Node8Box
    .k (107/32) (by rfl) (by rfl)
    component52Node7_sound component52Node8_sound

private noncomputable def component52Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (29/128), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component52Node10_sound : Sound component52Node10Box :=
  sound_of_literal_split component52Node10Box leaf2428Box leaf2429Box
    .chi (59/256) (by rfl) (by rfl)
    leaf2428FlatSound leaf2429FlatSound

private noncomputable def component52Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (29/128), chiHi := (59/256) }

set_option maxRecDepth 1000000 in
private theorem component52Node11_sound : Sound component52Node11Box :=
  sound_of_literal_split component52Node11Box leaf2430Box leaf2431Box
    .k (215/64) (by rfl) (by rfl)
    leaf2430FlatSound leaf2431FlatSound

private noncomputable def component52Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (59/256), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component52Node12_sound : Sound component52Node12Box :=
  sound_of_literal_split component52Node12Box leaf2432Box leaf2433Box
    .k (215/64) (by rfl) (by rfl)
    leaf2432FlatSound leaf2433FlatSound

private noncomputable def component52Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (29/128), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component52Node13_sound : Sound component52Node13Box :=
  sound_of_literal_split component52Node13Box component52Node11Box component52Node12Box
    .chi (59/256) (by rfl) (by rfl)
    component52Node11_sound component52Node12_sound

private noncomputable def component52Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (29/128), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component52Node14_sound : Sound component52Node14Box :=
  sound_of_literal_split component52Node14Box component52Node10Box component52Node13Box
    .k (107/32) (by rfl) (by rfl)
    component52Node10_sound component52Node13_sound

private noncomputable def component52Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component52Node15_sound : Sound component52Node15Box :=
  sound_of_literal_split component52Node15Box component52Node9Box component52Node14Box
    .chi (29/128) (by rfl) (by rfl)
    component52Node9_sound component52Node14_sound

private noncomputable def component52Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component52Node16_sound : Sound component52Node16Box :=
  sound_of_literal_split component52Node16Box component52Node6Box component52Node15Box
    .k (53/16) (by rfl) (by rfl)
    component52Node6_sound component52Node15_sound

private noncomputable def component52Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (15/64), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component52Node17_sound : Sound component52Node17Box :=
  sound_of_literal_split component52Node17Box leaf2434Box leaf2435Box
    .chi (61/256) (by rfl) (by rfl)
    leaf2434FlatSound leaf2435FlatSound

private noncomputable def component52Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (15/64), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component52Node18_sound : Sound component52Node18Box :=
  sound_of_literal_split component52Node18Box leaf2436Box leaf2437Box
    .chi (61/256) (by rfl) (by rfl)
    leaf2436FlatSound leaf2437FlatSound

private noncomputable def component52Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (15/64), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component52Node19_sound : Sound component52Node19Box :=
  sound_of_literal_split component52Node19Box component52Node17Box component52Node18Box
    .k (105/32) (by rfl) (by rfl)
    component52Node17_sound component52Node18_sound

private noncomputable def component52Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (31/128), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component52Node20_sound : Sound component52Node20Box :=
  sound_of_literal_split component52Node20Box leaf2438Box leaf2439Box
    .chi (63/256) (by rfl) (by rfl)
    leaf2438FlatSound leaf2439FlatSound

private noncomputable def component52Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (31/128), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component52Node21_sound : Sound component52Node21Box :=
  sound_of_literal_split component52Node21Box leaf2440Box leaf2441Box
    .chi (63/256) (by rfl) (by rfl)
    leaf2440FlatSound leaf2441FlatSound

private noncomputable def component52Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (31/128), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component52Node22_sound : Sound component52Node22Box :=
  sound_of_literal_split component52Node22Box component52Node20Box component52Node21Box
    .k (105/32) (by rfl) (by rfl)
    component52Node20_sound component52Node21_sound

private noncomputable def component52Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component52Node23_sound : Sound component52Node23Box :=
  sound_of_literal_split component52Node23Box component52Node19Box component52Node22Box
    .chi (31/128) (by rfl) (by rfl)
    component52Node19_sound component52Node22_sound

private noncomputable def component52Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (15/64), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component52Node24_sound : Sound component52Node24Box :=
  sound_of_literal_split component52Node24Box leaf2442Box leaf2443Box
    .chi (61/256) (by rfl) (by rfl)
    leaf2442FlatSound leaf2443FlatSound

private noncomputable def component52Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (15/64), chiHi := (61/256) }

set_option maxRecDepth 1000000 in
private theorem component52Node25_sound : Sound component52Node25Box :=
  sound_of_literal_split component52Node25Box leaf2444Box leaf2445Box
    .k (215/64) (by rfl) (by rfl)
    leaf2444FlatSound leaf2445FlatSound

private noncomputable def component52Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (61/256), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component52Node26_sound : Sound component52Node26Box :=
  sound_of_literal_split component52Node26Box leaf2446Box leaf2447Box
    .k (215/64) (by rfl) (by rfl)
    leaf2446FlatSound leaf2447FlatSound

private noncomputable def component52Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (15/64), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component52Node27_sound : Sound component52Node27Box :=
  sound_of_literal_split component52Node27Box component52Node25Box component52Node26Box
    .chi (61/256) (by rfl) (by rfl)
    component52Node25_sound component52Node26_sound

private noncomputable def component52Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (15/64), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component52Node28_sound : Sound component52Node28Box :=
  sound_of_literal_split component52Node28Box component52Node24Box component52Node27Box
    .k (107/32) (by rfl) (by rfl)
    component52Node24_sound component52Node27_sound

private noncomputable def component52Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (31/128), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component52Node29_sound : Sound component52Node29Box :=
  sound_of_literal_split component52Node29Box leaf2448Box leaf2449Box
    .chi (63/256) (by rfl) (by rfl)
    leaf2448FlatSound leaf2449FlatSound

private noncomputable def component52Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (31/128), chiHi := (63/256) }

set_option maxRecDepth 1000000 in
private theorem component52Node30_sound : Sound component52Node30Box :=
  sound_of_literal_split component52Node30Box leaf2450Box leaf2451Box
    .k (215/64) (by rfl) (by rfl)
    leaf2450FlatSound leaf2451FlatSound

private noncomputable def component52Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (31/128), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component52Node31_sound : Sound component52Node31Box :=
  sound_of_literal_split component52Node31Box component52Node30Box leaf2452Box
    .chi (63/256) (by rfl) (by rfl)
    component52Node30_sound leaf2452FlatSound

private noncomputable def component52Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (31/128), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component52Node32_sound : Sound component52Node32Box :=
  sound_of_literal_split component52Node32Box component52Node29Box component52Node31Box
    .k (107/32) (by rfl) (by rfl)
    component52Node29_sound component52Node31_sound

private noncomputable def component52Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component52Node33_sound : Sound component52Node33Box :=
  sound_of_literal_split component52Node33Box component52Node28Box component52Node32Box
    .chi (31/128) (by rfl) (by rfl)
    component52Node28_sound component52Node32_sound

private noncomputable def component52Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component52Node34_sound : Sound component52Node34Box :=
  sound_of_literal_split component52Node34Box component52Node23Box component52Node33Box
    .k (53/16) (by rfl) (by rfl)
    component52Node23_sound component52Node33_sound

noncomputable def component52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (7/32), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
theorem component52_sound : Sound component52Box :=
  sound_of_literal_split component52Box component52Node16Box component52Node34Box
    .chi (15/64) (by rfl) (by rfl)
    component52Node16_sound component52Node34_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
