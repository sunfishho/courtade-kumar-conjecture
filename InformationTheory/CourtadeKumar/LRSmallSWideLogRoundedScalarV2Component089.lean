import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch5
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch7
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch8
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch9
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

private noncomputable def leaf4354Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (9/32), chiHi := (73/256) }

private noncomputable def leaf4354Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871251/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715851264) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (989794991/536870912) }, upper := { exponent := 0, mantissa := (15273/8192) } }, logOuter := sk133LogOuterCertificate, logK := sk133LogKCertificate, logChi := chi281LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434344959/137431702528) } }, logDArg := sk133LogDArgCertificate }

private noncomputable def leaf4354InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf4354LocalValidity :
    LeafFacts leaf4354Box leaf4354Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4354Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715851264) }) = true
      norm_num [leaf4354Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4354CertificateValid :
    WideCertificateValid leaf4354Box leaf4354Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk133ValidityFacts chi281ValidityFacts
    leaf4354LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4354CoverageChecked :
    coverageCheck (innerAD leaf4354Box) leaf4354InnerLog = true := by
  rfl'

private theorem leaf4354InnerLogValid :
    leaf4354InnerLog.Valid 8 (innerAD leaf4354Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf4354CoverageChecked

private noncomputable def leaf4354InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629403/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4354InputLogOnePlusV_eq :
    leaf4354InputLogOnePlusV = outerEnclosure 24
      (leaf4354Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4354RoundedFacts : LeafRoundedFacts 8
    leaf4354Certificate.logOnePlusV leaf4354InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4354InputLogOnePlusV_eq }

private noncomputable def leaf4354Inputs : Inputs :=
  inputsOfCaches globalInput sk133RoundedInputs
    chi281InputQChi innerPair91Input
    leaf4354InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4354LowerChecked :
    lowerCheck 24 leaf4354Box leaf4354Inputs = true := by
  rfl'

private theorem leaf4354CoversExact : CoversExact 8
    leaf4354Box leaf4354Certificate leaf4354InnerLog leaf4354Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk133RoundedFacts chi281RoundedFacts
    innerPair91RoundedFacts leaf4354RoundedFacts (by rfl)

private theorem leaf4354FlatSound : Sound leaf4354Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4354CertificateValid
    leaf4354InnerLogValid leaf4354CoversExact leaf4354LowerChecked

private noncomputable def leaf4355Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (73/256), chiHi := (37/128) }

private noncomputable def leaf4355Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871253/536870912) }, vSqrt := { lower := (65529/65536), upper := (4581232913/4581053440) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (996086061/536870912) }, upper := { exponent := 0, mantissa := (7685/4096) } }, logOuter := sk133LogOuterCertificate, logK := sk133LogKCertificate, logChi := chi282LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (9162286353/9162106880) } }, logDArg := sk133LogDArgCertificate }

private noncomputable def leaf4355InnerLog : WideLogData :=
  innerPair92Data

set_option maxRecDepth 1000000 in
private theorem leaf4355LocalValidity :
    LeafFacts leaf4355Box leaf4355Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4355Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4581232913/4581053440) }) = true
      norm_num [leaf4355Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4355CertificateValid :
    WideCertificateValid leaf4355Box leaf4355Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk133ValidityFacts chi282ValidityFacts
    leaf4355LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4355CoverageChecked :
    coverageCheck (innerAD leaf4355Box) leaf4355InnerLog = true := by
  rfl'

private theorem leaf4355InnerLogValid :
    leaf4355InnerLog.Valid 8 (innerAD leaf4355Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint23PositiveFacts.valid leaf4355CoverageChecked

private noncomputable def leaf4355InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629409/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4355InputLogOnePlusV_eq :
    leaf4355InputLogOnePlusV = outerEnclosure 24
      (leaf4355Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4355RoundedFacts : LeafRoundedFacts 8
    leaf4355Certificate.logOnePlusV leaf4355InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4355InputLogOnePlusV_eq }

private noncomputable def leaf4355Inputs : Inputs :=
  inputsOfCaches globalInput sk133RoundedInputs
    chi282InputQChi innerPair92Input
    leaf4355InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4355LowerChecked :
    lowerCheck 24 leaf4355Box leaf4355Inputs = true := by
  rfl'

private theorem leaf4355CoversExact : CoversExact 8
    leaf4355Box leaf4355Certificate leaf4355InnerLog leaf4355Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk133RoundedFacts chi282RoundedFacts
    innerPair92RoundedFacts leaf4355RoundedFacts (by rfl)

private theorem leaf4355FlatSound : Sound leaf4355Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4355CertificateValid
    leaf4355InnerLogValid leaf4355CoversExact leaf4355LowerChecked

private noncomputable def leaf4356Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (9/32), chiHi := (73/256) }

private noncomputable def leaf4356Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871253/536870912) }, vSqrt := { lower := (65529/65536), upper := (22906164565/22905271296) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (994513293/536870912) }, upper := { exponent := 0, mantissa := (7673/4096) } }, logOuter := sk134LogOuterCertificate, logK := sk134LogKCertificate, logChi := chi281LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (45811435861/45810542592) } }, logDArg := sk134LogDArgCertificate }

private noncomputable def leaf4356InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf4356LocalValidity :
    LeafFacts leaf4356Box leaf4356Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4356Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22906164565/22905271296) }) = true
      norm_num [leaf4356Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4356CertificateValid :
    WideCertificateValid leaf4356Box leaf4356Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk134ValidityFacts chi281ValidityFacts
    leaf4356LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4356CoverageChecked :
    coverageCheck (innerAD leaf4356Box) leaf4356InnerLog = true := by
  rfl'

private theorem leaf4356InnerLogValid :
    leaf4356InnerLog.Valid 8 (innerAD leaf4356Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf4356CoverageChecked

private noncomputable def leaf4356InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (363419/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf4356InputLogOnePlusV_eq :
    leaf4356InputLogOnePlusV = outerEnclosure 24
      (leaf4356Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4356RoundedFacts : LeafRoundedFacts 8
    leaf4356Certificate.logOnePlusV leaf4356InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4356InputLogOnePlusV_eq }

private noncomputable def leaf4356Inputs : Inputs :=
  inputsOfCaches globalInput sk134RoundedInputs
    chi281InputQChi innerPair91Input
    leaf4356InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4356LowerChecked :
    lowerCheck 24 leaf4356Box leaf4356Inputs = true := by
  rfl'

private theorem leaf4356CoversExact : CoversExact 8
    leaf4356Box leaf4356Certificate leaf4356InnerLog leaf4356Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk134RoundedFacts chi281RoundedFacts
    innerPair91RoundedFacts leaf4356RoundedFacts (by rfl)

private theorem leaf4356FlatSound : Sound leaf4356Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4356CertificateValid
    leaf4356InnerLogValid leaf4356CoversExact leaf4356LowerChecked

private noncomputable def leaf4357Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (73/256), chiHi := (37/128) }

private noncomputable def leaf4357Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871255/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715763712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1000869895/536870912) }, upper := { exponent := 0, mantissa := (3861/2048) } }, logOuter := sk134LogOuterCertificate, logK := sk134LogKCertificate, logChi := chi282LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434257407/137431527424) } }, logDArg := sk134LogDArgCertificate }

private noncomputable def leaf4357InnerLog : WideLogData :=
  innerPair92Data

set_option maxRecDepth 1000000 in
private theorem leaf4357LocalValidity :
    LeafFacts leaf4357Box leaf4357Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4357Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715763712) }) = true
      norm_num [leaf4357Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4357CertificateValid :
    WideCertificateValid leaf4357Box leaf4357Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk134ValidityFacts chi282ValidityFacts
    leaf4357LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4357CoverageChecked :
    coverageCheck (innerAD leaf4357Box) leaf4357InnerLog = true := by
  rfl'

private theorem leaf4357InnerLogValid :
    leaf4357InnerLog.Valid 8 (innerAD leaf4357Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint23PositiveFacts.valid leaf4357CoverageChecked

private noncomputable def leaf4357InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814707/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4357InputLogOnePlusV_eq :
    leaf4357InputLogOnePlusV = outerEnclosure 24
      (leaf4357Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4357RoundedFacts : LeafRoundedFacts 8
    leaf4357Certificate.logOnePlusV leaf4357InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4357InputLogOnePlusV_eq }

private noncomputable def leaf4357Inputs : Inputs :=
  inputsOfCaches globalInput sk134RoundedInputs
    chi282InputQChi innerPair92Input
    leaf4357InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4357LowerChecked :
    lowerCheck 24 leaf4357Box leaf4357Inputs = true := by
  rfl'

private theorem leaf4357CoversExact : CoversExact 8
    leaf4357Box leaf4357Certificate leaf4357InnerLog leaf4357Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk134RoundedFacts chi282RoundedFacts
    innerPair92RoundedFacts leaf4357RoundedFacts (by rfl)

private theorem leaf4357FlatSound : Sound leaf4357Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4357CertificateValid
    leaf4357InnerLogValid leaf4357CoversExact leaf4357LowerChecked

private noncomputable def leaf4358Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (37/128), chiHi := (19/64) }

private noncomputable def leaf4358Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435725/268435456) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715702272) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (501172085/268435456) }, upper := { exponent := 0, mantissa := (3891/2048) } }, logOuter := sk133LogOuterCertificate, logK := sk133LogKCertificate, logChi := chi246LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434195967/137431404544) } }, logDArg := sk133LogDArgCertificate }

private noncomputable def leaf4358InnerLog : WideLogData :=
  innerPair513Data

set_option maxRecDepth 1000000 in
private theorem leaf4358LocalValidity :
    LeafFacts leaf4358Box leaf4358Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4358Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715702272) }) = true
      norm_num [leaf4358Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4358CertificateValid :
    WideCertificateValid leaf4358Box leaf4358Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk133ValidityFacts chi246ValidityFacts
    leaf4358LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4358CoverageChecked :
    coverageCheck (innerAD leaf4358Box) leaf4358InnerLog = true := by
  rfl'

private theorem leaf4358InnerLogValid :
    leaf4358InnerLog.Valid 8 (innerAD leaf4358Box) :=
  wideLogDataValid_of_cachedCheck endpoint241PositiveFacts
    endpoint247PositiveFacts.valid leaf4358CoverageChecked

private noncomputable def leaf4358InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814711/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4358InputLogOnePlusV_eq :
    leaf4358InputLogOnePlusV = outerEnclosure 24
      (leaf4358Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4358RoundedFacts : LeafRoundedFacts 8
    leaf4358Certificate.logOnePlusV leaf4358InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4358InputLogOnePlusV_eq }

private noncomputable def leaf4358Inputs : Inputs :=
  inputsOfCaches globalInput sk133RoundedInputs
    chi246InputQChi innerPair513Input
    leaf4358InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4358LowerChecked :
    lowerCheck 24 leaf4358Box leaf4358Inputs = true := by
  rfl'

private theorem leaf4358CoversExact : CoversExact 8
    leaf4358Box leaf4358Certificate leaf4358InnerLog leaf4358Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk133RoundedFacts chi246RoundedFacts
    innerPair513RoundedFacts leaf4358RoundedFacts (by rfl)

private theorem leaf4358FlatSound : Sound leaf4358Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4358CertificateValid
    leaf4358InnerLogValid leaf4358CoversExact leaf4358LowerChecked

private noncomputable def leaf4359Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (37/128), chiHi := (75/256) }

private noncomputable def leaf4359Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871257/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715713536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1007226497/536870912) }, upper := { exponent := 0, mantissa := (7771/4096) } }, logOuter := sk134LogOuterCertificate, logK := sk134LogKCertificate, logChi := chi283LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434207231/137431427072) } }, logDArg := sk134LogDArgCertificate }

private noncomputable def leaf4359InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4359LocalValidity :
    LeafFacts leaf4359Box leaf4359Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4359Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715713536) }) = true
      norm_num [leaf4359Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4359CertificateValid :
    WideCertificateValid leaf4359Box leaf4359Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk134ValidityFacts chi283ValidityFacts
    leaf4359LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4359CoverageChecked :
    coverageCheck (innerAD leaf4359Box) leaf4359InnerLog = true := by
  rfl'

private theorem leaf4359InnerLogValid :
    leaf4359InnerLog.Valid 8 (innerAD leaf4359Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4359CoverageChecked

private noncomputable def leaf4359InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907355/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4359InputLogOnePlusV_eq :
    leaf4359InputLogOnePlusV = outerEnclosure 24
      (leaf4359Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4359RoundedFacts : LeafRoundedFacts 8
    leaf4359Certificate.logOnePlusV leaf4359InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4359InputLogOnePlusV_eq }

private noncomputable def leaf4359Inputs : Inputs :=
  inputsOfCaches globalInput sk134RoundedInputs
    chi283InputQChi innerPair100Input
    leaf4359InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4359LowerChecked :
    lowerCheck 24 leaf4359Box leaf4359Inputs = true := by
  rfl'

private theorem leaf4359CoversExact : CoversExact 8
    leaf4359Box leaf4359Certificate leaf4359InnerLog leaf4359Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk134RoundedFacts chi283RoundedFacts
    innerPair100RoundedFacts leaf4359RoundedFacts (by rfl)

private theorem leaf4359FlatSound : Sound leaf4359Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4359CertificateValid
    leaf4359InnerLogValid leaf4359CoversExact leaf4359LowerChecked

private noncomputable def leaf4360Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (75/256), chiHi := (19/64) }

private noncomputable def leaf4360Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871259/536870912) }, vSqrt := { lower := (65529/65536), upper := (4581232913/4581044224) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1013583099/536870912) }, upper := { exponent := 0, mantissa := (1955/1024) } }, logOuter := sk134LogOuterCertificate, logK := sk134LogKCertificate, logChi := chi284LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (9162277137/9162088448) } }, logDArg := sk134LogDArgCertificate }

private noncomputable def leaf4360InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4360LocalValidity :
    LeafFacts leaf4360Box leaf4360Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4360Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4581232913/4581044224) }) = true
      norm_num [leaf4360Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4360CertificateValid :
    WideCertificateValid leaf4360Box leaf4360Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk134ValidityFacts chi284ValidityFacts
    leaf4360LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4360CoverageChecked :
    coverageCheck (innerAD leaf4360Box) leaf4360InnerLog = true := by
  rfl'

private theorem leaf4360InnerLogValid :
    leaf4360InnerLog.Valid 8 (innerAD leaf4360Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4360CoverageChecked

private noncomputable def leaf4360InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814713/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4360InputLogOnePlusV_eq :
    leaf4360InputLogOnePlusV = outerEnclosure 24
      (leaf4360Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4360RoundedFacts : LeafRoundedFacts 8
    leaf4360Certificate.logOnePlusV leaf4360InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4360InputLogOnePlusV_eq }

private noncomputable def leaf4360Inputs : Inputs :=
  inputsOfCaches globalInput sk134RoundedInputs
    chi284InputQChi innerPair100Input
    leaf4360InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4360LowerChecked :
    lowerCheck 24 leaf4360Box leaf4360Inputs = true := by
  rfl'

private theorem leaf4360CoversExact : CoversExact 8
    leaf4360Box leaf4360Certificate leaf4360InnerLog leaf4360Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk134RoundedFacts chi284RoundedFacts
    innerPair100RoundedFacts leaf4360RoundedFacts (by rfl)

private theorem leaf4360FlatSound : Sound leaf4360Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4360CertificateValid
    leaf4360InnerLogValid leaf4360CoversExact leaf4360LowerChecked

private noncomputable def leaf4361Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (9/32), chiHi := (73/256) }

private noncomputable def leaf4361Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871255/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715776512) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (999231595/536870912) }, upper := { exponent := 0, mantissa := (15419/8192) } }, logOuter := sk135LogOuterCertificate, logK := sk135LogKCertificate, logChi := chi281LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434270207/137431553024) } }, logDArg := sk135LogDArgCertificate }

private noncomputable def leaf4361InnerLog : WideLogData :=
  innerPair482Data

set_option maxRecDepth 1000000 in
private theorem leaf4361LocalValidity :
    LeafFacts leaf4361Box leaf4361Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4361Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715776512) }) = true
      norm_num [leaf4361Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4361CertificateValid :
    WideCertificateValid leaf4361Box leaf4361Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk135ValidityFacts chi281ValidityFacts
    leaf4361LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4361CoverageChecked :
    coverageCheck (innerAD leaf4361Box) leaf4361InnerLog = true := by
  rfl'

private theorem leaf4361InnerLogValid :
    leaf4361InnerLog.Valid 8 (innerAD leaf4361Box) :=
  wideLogDataValid_of_cachedCheck endpoint211PositiveFacts
    endpoint69PositiveFacts.valid leaf4361CoverageChecked

private noncomputable def leaf4361InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907353/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4361InputLogOnePlusV_eq :
    leaf4361InputLogOnePlusV = outerEnclosure 24
      (leaf4361Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4361RoundedFacts : LeafRoundedFacts 8
    leaf4361Certificate.logOnePlusV leaf4361InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4361InputLogOnePlusV_eq }

private noncomputable def leaf4361Inputs : Inputs :=
  inputsOfCaches globalInput sk135RoundedInputs
    chi281InputQChi innerPair482Input
    leaf4361InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4361LowerChecked :
    lowerCheck 24 leaf4361Box leaf4361Inputs = true := by
  rfl'

private theorem leaf4361CoversExact : CoversExact 8
    leaf4361Box leaf4361Certificate leaf4361InnerLog leaf4361Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk135RoundedFacts chi281RoundedFacts
    innerPair482RoundedFacts leaf4361RoundedFacts (by rfl)

private theorem leaf4361FlatSound : Sound leaf4361Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4361CertificateValid
    leaf4361InnerLogValid leaf4361CoversExact leaf4361LowerChecked

private noncomputable def leaf4362Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (73/256), chiHi := (37/128) }

private noncomputable def leaf4362Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871257/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715725824) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1005653729/536870912) }, upper := { exponent := 0, mantissa := (7759/4096) } }, logOuter := sk135LogOuterCertificate, logK := sk135LogKCertificate, logChi := chi282LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434219519/137431451648) } }, logDArg := sk135LogDArgCertificate }

private noncomputable def leaf4362InnerLog : WideLogData :=
  innerPair92Data

set_option maxRecDepth 1000000 in
private theorem leaf4362LocalValidity :
    LeafFacts leaf4362Box leaf4362Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4362Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715725824) }) = true
      norm_num [leaf4362Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4362CertificateValid :
    WideCertificateValid leaf4362Box leaf4362Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk135ValidityFacts chi282ValidityFacts
    leaf4362LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4362CoverageChecked :
    coverageCheck (innerAD leaf4362Box) leaf4362InnerLog = true := by
  rfl'

private theorem leaf4362InnerLogValid :
    leaf4362InnerLog.Valid 8 (innerAD leaf4362Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint23PositiveFacts.valid leaf4362CoverageChecked

private noncomputable def leaf4362InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629419/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4362InputLogOnePlusV_eq :
    leaf4362InputLogOnePlusV = outerEnclosure 24
      (leaf4362Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4362RoundedFacts : LeafRoundedFacts 8
    leaf4362Certificate.logOnePlusV leaf4362InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4362InputLogOnePlusV_eq }

private noncomputable def leaf4362Inputs : Inputs :=
  inputsOfCaches globalInput sk135RoundedInputs
    chi282InputQChi innerPair92Input
    leaf4362InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4362LowerChecked :
    lowerCheck 24 leaf4362Box leaf4362Inputs = true := by
  rfl'

private theorem leaf4362CoversExact : CoversExact 8
    leaf4362Box leaf4362Certificate leaf4362InnerLog leaf4362Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk135RoundedFacts chi282RoundedFacts
    innerPair92RoundedFacts leaf4362RoundedFacts (by rfl)

private theorem leaf4362FlatSound : Sound leaf4362Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4362CertificateValid
    leaf4362InnerLogValid leaf4362CoversExact leaf4362LowerChecked

private noncomputable def leaf4363Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (9/32), chiHi := (73/256) }

private noncomputable def leaf4363Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871257/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715739136) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1003949897/536870912) }, upper := { exponent := 0, mantissa := (3873/2048) } }, logOuter := sk136LogOuterCertificate, logK := sk136LogKCertificate, logChi := chi281LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434232831/137431478272) } }, logDArg := sk136LogDArgCertificate }

private noncomputable def leaf4363InnerLog : WideLogData :=
  innerPair92Data

set_option maxRecDepth 1000000 in
private theorem leaf4363LocalValidity :
    LeafFacts leaf4363Box leaf4363Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4363Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715739136) }) = true
      norm_num [leaf4363Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4363CertificateValid :
    WideCertificateValid leaf4363Box leaf4363Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk136ValidityFacts chi281ValidityFacts
    leaf4363LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4363CoverageChecked :
    coverageCheck (innerAD leaf4363Box) leaf4363InnerLog = true := by
  rfl'

private theorem leaf4363InnerLogValid :
    leaf4363InnerLog.Valid 8 (innerAD leaf4363Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint23PositiveFacts.valid leaf4363CoverageChecked

private noncomputable def leaf4363InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629417/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4363InputLogOnePlusV_eq :
    leaf4363InputLogOnePlusV = outerEnclosure 24
      (leaf4363Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4363RoundedFacts : LeafRoundedFacts 8
    leaf4363Certificate.logOnePlusV leaf4363InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4363InputLogOnePlusV_eq }

private noncomputable def leaf4363Inputs : Inputs :=
  inputsOfCaches globalInput sk136RoundedInputs
    chi281InputQChi innerPair92Input
    leaf4363InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4363LowerChecked :
    lowerCheck 24 leaf4363Box leaf4363Inputs = true := by
  rfl'

private theorem leaf4363CoversExact : CoversExact 8
    leaf4363Box leaf4363Certificate leaf4363InnerLog leaf4363Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk136RoundedFacts chi281RoundedFacts
    innerPair92RoundedFacts leaf4363RoundedFacts (by rfl)

private theorem leaf4363FlatSound : Sound leaf4363Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4363CertificateValid
    leaf4363InnerLogValid leaf4363CoversExact leaf4363LowerChecked

private noncomputable def leaf4364Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (73/256), chiHi := (37/128) }

private noncomputable def leaf4364Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871259/536870912) }, vSqrt := { lower := (65529/65536), upper := (22906164565/22905229312) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1010437563/536870912) }, upper := { exponent := 0, mantissa := (1949/1024) } }, logOuter := sk136LogOuterCertificate, logK := sk136LogKCertificate, logChi := chi282LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (45811393877/45810458624) } }, logDArg := sk136LogDArgCertificate }

private noncomputable def leaf4364InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4364LocalValidity :
    LeafFacts leaf4364Box leaf4364Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4364Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22906164565/22905229312) }) = true
      norm_num [leaf4364Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4364CertificateValid :
    WideCertificateValid leaf4364Box leaf4364Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk136ValidityFacts chi282ValidityFacts
    leaf4364LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4364CoverageChecked :
    coverageCheck (innerAD leaf4364Box) leaf4364InnerLog = true := by
  rfl'

private theorem leaf4364InnerLogValid :
    leaf4364InnerLog.Valid 8 (innerAD leaf4364Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4364CoverageChecked

private noncomputable def leaf4364InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629423/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4364InputLogOnePlusV_eq :
    leaf4364InputLogOnePlusV = outerEnclosure 24
      (leaf4364Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4364RoundedFacts : LeafRoundedFacts 8
    leaf4364Certificate.logOnePlusV leaf4364InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4364InputLogOnePlusV_eq }

private noncomputable def leaf4364Inputs : Inputs :=
  inputsOfCaches globalInput sk136RoundedInputs
    chi282InputQChi innerPair100Input
    leaf4364InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4364LowerChecked :
    lowerCheck 24 leaf4364Box leaf4364Inputs = true := by
  rfl'

private theorem leaf4364CoversExact : CoversExact 8
    leaf4364Box leaf4364Certificate leaf4364InnerLog leaf4364Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk136RoundedFacts chi282RoundedFacts
    innerPair100RoundedFacts leaf4364RoundedFacts (by rfl)

private theorem leaf4364FlatSound : Sound leaf4364Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4364CertificateValid
    leaf4364InnerLogValid leaf4364CoversExact leaf4364LowerChecked

private noncomputable def leaf4365Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (37/128), chiHi := (75/256) }

private noncomputable def leaf4365Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871259/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715675136) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1012075863/536870912) }, upper := { exponent := 0, mantissa := (15617/8192) } }, logOuter := sk135LogOuterCertificate, logK := sk135LogKCertificate, logChi := chi283LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434168831/137431350272) } }, logDArg := sk135LogDArgCertificate }

private noncomputable def leaf4365InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4365LocalValidity :
    LeafFacts leaf4365Box leaf4365Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4365Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715675136) }) = true
      norm_num [leaf4365Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4365CertificateValid :
    WideCertificateValid leaf4365Box leaf4365Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk135ValidityFacts chi283ValidityFacts
    leaf4365LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4365CoverageChecked :
    coverageCheck (innerAD leaf4365Box) leaf4365InnerLog = true := by
  rfl'

private theorem leaf4365InnerLogValid :
    leaf4365InnerLog.Valid 8 (innerAD leaf4365Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4365CoverageChecked

private noncomputable def leaf4365InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629425/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4365InputLogOnePlusV_eq :
    leaf4365InputLogOnePlusV = outerEnclosure 24
      (leaf4365Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4365RoundedFacts : LeafRoundedFacts 8
    leaf4365Certificate.logOnePlusV leaf4365InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4365InputLogOnePlusV_eq }

private noncomputable def leaf4365Inputs : Inputs :=
  inputsOfCaches globalInput sk135RoundedInputs
    chi283InputQChi innerPair100Input
    leaf4365InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4365LowerChecked :
    lowerCheck 24 leaf4365Box leaf4365Inputs = true := by
  rfl'

private theorem leaf4365CoversExact : CoversExact 8
    leaf4365Box leaf4365Certificate leaf4365InnerLog leaf4365Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk135RoundedFacts chi283RoundedFacts
    innerPair100RoundedFacts leaf4365RoundedFacts (by rfl)

private theorem leaf4365FlatSound : Sound leaf4365Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4365CertificateValid
    leaf4365InnerLogValid leaf4365CoversExact leaf4365LowerChecked

private noncomputable def leaf4366Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (75/256), chiHi := (19/64) }

private noncomputable def leaf4366Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871261/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715624448) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1018497997/536870912) }, upper := { exponent := 0, mantissa := (3929/2048) } }, logOuter := sk135LogOuterCertificate, logK := sk135LogKCertificate, logChi := chi284LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434118143/137431248896) } }, logDArg := sk135LogDArgCertificate }

private noncomputable def leaf4366InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4366LocalValidity :
    LeafFacts leaf4366Box leaf4366Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4366Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715624448) }) = true
      norm_num [leaf4366Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4366CertificateValid :
    WideCertificateValid leaf4366Box leaf4366Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk135ValidityFacts chi284ValidityFacts
    leaf4366LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4366CoverageChecked :
    coverageCheck (innerAD leaf4366Box) leaf4366InnerLog = true := by
  rfl'

private theorem leaf4366InnerLogValid :
    leaf4366InnerLog.Valid 8 (innerAD leaf4366Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4366CoverageChecked

private noncomputable def leaf4366InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629431/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4366InputLogOnePlusV_eq :
    leaf4366InputLogOnePlusV = outerEnclosure 24
      (leaf4366Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4366RoundedFacts : LeafRoundedFacts 8
    leaf4366Certificate.logOnePlusV leaf4366InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4366InputLogOnePlusV_eq }

private noncomputable def leaf4366Inputs : Inputs :=
  inputsOfCaches globalInput sk135RoundedInputs
    chi284InputQChi innerPair100Input
    leaf4366InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4366LowerChecked :
    lowerCheck 24 leaf4366Box leaf4366Inputs = true := by
  rfl'

private theorem leaf4366CoversExact : CoversExact 8
    leaf4366Box leaf4366Certificate leaf4366InnerLog leaf4366Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk135RoundedFacts chi284RoundedFacts
    innerPair100RoundedFacts leaf4366RoundedFacts (by rfl)

private theorem leaf4366FlatSound : Sound leaf4366Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4366CertificateValid
    leaf4366InnerLogValid leaf4366CoversExact leaf4366LowerChecked

private noncomputable def leaf4367Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (37/128), chiHi := (75/256) }

private noncomputable def leaf4367Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871261/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715636736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1016925229/536870912) }, upper := { exponent := 0, mantissa := (3923/2048) } }, logOuter := sk136LogOuterCertificate, logK := sk136LogKCertificate, logChi := chi283LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434130431/137431273472) } }, logDArg := sk136LogDArgCertificate }

private noncomputable def leaf4367InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4367LocalValidity :
    LeafFacts leaf4367Box leaf4367Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4367Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715636736) }) = true
      norm_num [leaf4367Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4367CertificateValid :
    WideCertificateValid leaf4367Box leaf4367Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk136ValidityFacts chi283ValidityFacts
    leaf4367LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4367CoverageChecked :
    coverageCheck (innerAD leaf4367Box) leaf4367InnerLog = true := by
  rfl'

private theorem leaf4367InnerLogValid :
    leaf4367InnerLog.Valid 8 (innerAD leaf4367Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4367CoverageChecked

private noncomputable def leaf4367InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814715/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4367InputLogOnePlusV_eq :
    leaf4367InputLogOnePlusV = outerEnclosure 24
      (leaf4367Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4367RoundedFacts : LeafRoundedFacts 8
    leaf4367Certificate.logOnePlusV leaf4367InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4367InputLogOnePlusV_eq }

private noncomputable def leaf4367Inputs : Inputs :=
  inputsOfCaches globalInput sk136RoundedInputs
    chi283InputQChi innerPair100Input
    leaf4367InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4367LowerChecked :
    lowerCheck 24 leaf4367Box leaf4367Inputs = true := by
  rfl'

private theorem leaf4367CoversExact : CoversExact 8
    leaf4367Box leaf4367Certificate leaf4367InnerLog leaf4367Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk136RoundedFacts chi283RoundedFacts
    innerPair100RoundedFacts leaf4367RoundedFacts (by rfl)

private theorem leaf4367FlatSound : Sound leaf4367Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4367CertificateValid
    leaf4367InnerLogValid leaf4367CoversExact leaf4367LowerChecked

private noncomputable def leaf4368Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (75/256), chiHi := (19/64) }

private noncomputable def leaf4368Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871263/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715585536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1023412895/536870912) }, upper := { exponent := 0, mantissa := (987/512) } }, logOuter := sk136LogOuterCertificate, logK := sk136LogKCertificate, logChi := chi284LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434079231/137431171072) } }, logDArg := sk136LogDArgCertificate }

private noncomputable def leaf4368InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4368LocalValidity :
    LeafFacts leaf4368Box leaf4368Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4368Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715585536) }) = true
      norm_num [leaf4368Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4368CertificateValid :
    WideCertificateValid leaf4368Box leaf4368Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk136ValidityFacts chi284ValidityFacts
    leaf4368LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4368CoverageChecked :
    coverageCheck (innerAD leaf4368Box) leaf4368InnerLog = true := by
  rfl'

private theorem leaf4368InnerLogValid :
    leaf4368InnerLog.Valid 8 (innerAD leaf4368Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4368CoverageChecked

private noncomputable def leaf4368InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907359/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4368InputLogOnePlusV_eq :
    leaf4368InputLogOnePlusV = outerEnclosure 24
      (leaf4368Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4368RoundedFacts : LeafRoundedFacts 8
    leaf4368Certificate.logOnePlusV leaf4368InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4368InputLogOnePlusV_eq }

private noncomputable def leaf4368Inputs : Inputs :=
  inputsOfCaches globalInput sk136RoundedInputs
    chi284InputQChi innerPair100Input
    leaf4368InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4368LowerChecked :
    lowerCheck 24 leaf4368Box leaf4368Inputs = true := by
  rfl'

private theorem leaf4368CoversExact : CoversExact 8
    leaf4368Box leaf4368Certificate leaf4368InnerLog leaf4368Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk136RoundedFacts chi284RoundedFacts
    innerPair100RoundedFacts leaf4368RoundedFacts (by rfl)

private theorem leaf4368FlatSound : Sound leaf4368Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4368CertificateValid
    leaf4368InnerLogValid leaf4368CoversExact leaf4368LowerChecked

private noncomputable def leaf4369Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (19/64), chiHi := (39/128) }

private noncomputable def leaf4369Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435727/268435456) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715602944) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (507463155/268435456) }, upper := { exponent := 0, mantissa := (7879/4096) } }, logOuter := sk133LogOuterCertificate, logK := sk133LogKCertificate, logChi := chi247LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434096639/137431205888) } }, logDArg := sk133LogDArgCertificate }

private noncomputable def leaf4369InnerLog : WideLogData :=
  innerPair516Data

set_option maxRecDepth 1000000 in
private theorem leaf4369LocalValidity :
    LeafFacts leaf4369Box leaf4369Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4369Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715602944) }) = true
      norm_num [leaf4369Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4369CertificateValid :
    WideCertificateValid leaf4369Box leaf4369Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk133ValidityFacts chi247ValidityFacts
    leaf4369LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4369CoverageChecked :
    coverageCheck (innerAD leaf4369Box) leaf4369InnerLog = true := by
  rfl'

private theorem leaf4369InnerLogValid :
    leaf4369InnerLog.Valid 8 (innerAD leaf4369Box) :=
  wideLogDataValid_of_cachedCheck endpoint245PositiveFacts
    endpoint248PositiveFacts.valid leaf4369CoverageChecked

private noncomputable def leaf4369InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814717/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4369InputLogOnePlusV_eq :
    leaf4369InputLogOnePlusV = outerEnclosure 24
      (leaf4369Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4369RoundedFacts : LeafRoundedFacts 8
    leaf4369Certificate.logOnePlusV leaf4369InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4369InputLogOnePlusV_eq }

private noncomputable def leaf4369Inputs : Inputs :=
  inputsOfCaches globalInput sk133RoundedInputs
    chi247InputQChi innerPair516Input
    leaf4369InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4369LowerChecked :
    lowerCheck 24 leaf4369Box leaf4369Inputs = true := by
  rfl'

private theorem leaf4369CoversExact : CoversExact 8
    leaf4369Box leaf4369Certificate leaf4369InnerLog leaf4369Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk133RoundedFacts chi247RoundedFacts
    innerPair516RoundedFacts leaf4369RoundedFacts (by rfl)

private theorem leaf4369FlatSound : Sound leaf4369Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4369CertificateValid
    leaf4369InnerLogValid leaf4369CoversExact leaf4369LowerChecked

private noncomputable def leaf4370Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (19/64), chiHi := (39/128) }

private noncomputable def leaf4370Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435729/268435456) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715563008) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (509953369/268435456) }, upper := { exponent := 0, mantissa := (3959/2048) } }, logOuter := sk134LogOuterCertificate, logK := sk134LogKCertificate, logChi := chi247LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434056703/137431126016) } }, logDArg := sk134LogDArgCertificate }

private noncomputable def leaf4370InnerLog : WideLogData :=
  innerPair524Data

set_option maxRecDepth 1000000 in
private theorem leaf4370LocalValidity :
    LeafFacts leaf4370Box leaf4370Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4370Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715563008) }) = true
      norm_num [leaf4370Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4370CertificateValid :
    WideCertificateValid leaf4370Box leaf4370Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk134ValidityFacts chi247ValidityFacts
    leaf4370LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4370CoverageChecked :
    coverageCheck (innerAD leaf4370Box) leaf4370InnerLog = true := by
  rfl'

private theorem leaf4370InnerLogValid :
    leaf4370InnerLog.Valid 8 (innerAD leaf4370Box) :=
  wideLogDataValid_of_cachedCheck endpoint257PositiveFacts
    endpoint265PositiveFacts.valid leaf4370CoverageChecked

private noncomputable def leaf4370InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629439/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4370InputLogOnePlusV_eq :
    leaf4370InputLogOnePlusV = outerEnclosure 24
      (leaf4370Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4370RoundedFacts : LeafRoundedFacts 8
    leaf4370Certificate.logOnePlusV leaf4370InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4370InputLogOnePlusV_eq }

private noncomputable def leaf4370Inputs : Inputs :=
  inputsOfCaches globalInput sk134RoundedInputs
    chi247InputQChi innerPair524Input
    leaf4370InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4370LowerChecked :
    lowerCheck 24 leaf4370Box leaf4370Inputs = true := by
  rfl'

private theorem leaf4370CoversExact : CoversExact 8
    leaf4370Box leaf4370Certificate leaf4370InnerLog leaf4370Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk134RoundedFacts chi247RoundedFacts
    innerPair524RoundedFacts leaf4370RoundedFacts (by rfl)

private theorem leaf4370FlatSound : Sound leaf4370Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4370CertificateValid
    leaf4370InnerLogValid leaf4370CoversExact leaf4370LowerChecked

private noncomputable def leaf4371Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (39/128), chiHi := (5/16) }

private noncomputable def leaf4371Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435729/268435456) }, vSqrt := { lower := (65529/65536), upper := (1347421445/1347362816) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (513754225/268435456) }, upper := { exponent := 0, mantissa := (997/512) } }, logOuter := sk133LogOuterCertificate, logK := sk133LogKCertificate, logChi := chi248LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (2694784261/2694725632) } }, logDArg := sk133LogDArgCertificate }

private noncomputable def leaf4371InnerLog : WideLogData :=
  innerPair233Data

set_option maxRecDepth 1000000 in
private theorem leaf4371LocalValidity :
    LeafFacts leaf4371Box leaf4371Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4371Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (1347421445/1347362816) }) = true
      norm_num [leaf4371Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4371CertificateValid :
    WideCertificateValid leaf4371Box leaf4371Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk133ValidityFacts chi248ValidityFacts
    leaf4371LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4371CoverageChecked :
    coverageCheck (innerAD leaf4371Box) leaf4371InnerLog = true := by
  rfl'

private theorem leaf4371InnerLogValid :
    leaf4371InnerLog.Valid 8 (innerAD leaf4371Box) :=
  wideLogDataValid_of_cachedCheck endpoint70PositiveFacts
    endpoint71PositiveFacts.valid leaf4371CoverageChecked

private noncomputable def leaf4371InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814723/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4371InputLogOnePlusV_eq :
    leaf4371InputLogOnePlusV = outerEnclosure 24
      (leaf4371Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4371RoundedFacts : LeafRoundedFacts 8
    leaf4371Certificate.logOnePlusV leaf4371InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4371InputLogOnePlusV_eq }

private noncomputable def leaf4371Inputs : Inputs :=
  inputsOfCaches globalInput sk133RoundedInputs
    chi248InputQChi innerPair233Input
    leaf4371InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4371LowerChecked :
    lowerCheck 24 leaf4371Box leaf4371Inputs = true := by
  rfl'

private theorem leaf4371CoversExact : CoversExact 8
    leaf4371Box leaf4371Certificate leaf4371InnerLog leaf4371Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk133RoundedFacts chi248RoundedFacts
    innerPair233RoundedFacts leaf4371RoundedFacts (by rfl)

private theorem leaf4371FlatSound : Sound leaf4371Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4371CertificateValid
    leaf4371InnerLogValid leaf4371CoversExact leaf4371LowerChecked

private noncomputable def leaf4372Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (39/128), chiHi := (5/16) }

private noncomputable def leaf4372Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435731/268435456) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715462656) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (516309971/268435456) }, upper := { exponent := 0, mantissa := (501/256) } }, logOuter := sk134LogOuterCertificate, logK := sk134LogKCertificate, logChi := chi248LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137433956351/137430925312) } }, logDArg := sk134LogDArgCertificate }

private noncomputable def leaf4372InnerLog : WideLogData :=
  innerPair307Data

set_option maxRecDepth 1000000 in
private theorem leaf4372LocalValidity :
    LeafFacts leaf4372Box leaf4372Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4372Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715462656) }) = true
      norm_num [leaf4372Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4372CertificateValid :
    WideCertificateValid leaf4372Box leaf4372Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk134ValidityFacts chi248ValidityFacts
    leaf4372LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4372CoverageChecked :
    coverageCheck (innerAD leaf4372Box) leaf4372InnerLog = true := by
  rfl'

private theorem leaf4372InnerLogValid :
    leaf4372InnerLog.Valid 8 (innerAD leaf4372Box) :=
  wideLogDataValid_of_cachedCheck endpoint81PositiveFacts
    endpoint266PositiveFacts.valid leaf4372CoverageChecked

private noncomputable def leaf4372InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629451/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4372InputLogOnePlusV_eq :
    leaf4372InputLogOnePlusV = outerEnclosure 24
      (leaf4372Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4372RoundedFacts : LeafRoundedFacts 8
    leaf4372Certificate.logOnePlusV leaf4372InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4372InputLogOnePlusV_eq }

private noncomputable def leaf4372Inputs : Inputs :=
  inputsOfCaches globalInput sk134RoundedInputs
    chi248InputQChi innerPair307Input
    leaf4372InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4372LowerChecked :
    lowerCheck 24 leaf4372Box leaf4372Inputs = true := by
  rfl'

private theorem leaf4372CoversExact : CoversExact 8
    leaf4372Box leaf4372Certificate leaf4372InnerLog leaf4372Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk134RoundedFacts chi248RoundedFacts
    innerPair307RoundedFacts leaf4372RoundedFacts (by rfl)

private theorem leaf4372FlatSound : Sound leaf4372Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4372CertificateValid
    leaf4372InnerLogValid leaf4372CoversExact leaf4372LowerChecked

private noncomputable def leaf4373Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (19/64), chiHi := (77/256) }

private noncomputable def leaf4373Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871263/536870912) }, vSqrt := { lower := (65529/65536), upper := (13743698739/13743114752) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1024920131/536870912) }, upper := { exponent := 0, mantissa := (15815/8192) } }, logOuter := sk135LogOuterCertificate, logK := sk135LogKCertificate, logChi := chi285LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (27486813491/27486229504) } }, logDArg := sk135LogDArgCertificate }

private noncomputable def leaf4373InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4373LocalValidity :
    LeafFacts leaf4373Box leaf4373Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4373Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (13743698739/13743114752) }) = true
      norm_num [leaf4373Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4373CertificateValid :
    WideCertificateValid leaf4373Box leaf4373Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk135ValidityFacts chi285ValidityFacts
    leaf4373LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4373CoverageChecked :
    coverageCheck (innerAD leaf4373Box) leaf4373InnerLog = true := by
  rfl'

private theorem leaf4373InnerLogValid :
    leaf4373InnerLog.Valid 8 (innerAD leaf4373Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4373CoverageChecked

private noncomputable def leaf4373InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629437/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4373InputLogOnePlusV_eq :
    leaf4373InputLogOnePlusV = outerEnclosure 24
      (leaf4373Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4373RoundedFacts : LeafRoundedFacts 8
    leaf4373Certificate.logOnePlusV leaf4373InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4373InputLogOnePlusV_eq }

private noncomputable def leaf4373Inputs : Inputs :=
  inputsOfCaches globalInput sk135RoundedInputs
    chi285InputQChi innerPair100Input
    leaf4373InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4373LowerChecked :
    lowerCheck 24 leaf4373Box leaf4373Inputs = true := by
  rfl'

private theorem leaf4373CoversExact : CoversExact 8
    leaf4373Box leaf4373Certificate leaf4373InnerLog leaf4373Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk135RoundedFacts chi285RoundedFacts
    innerPair100RoundedFacts leaf4373RoundedFacts (by rfl)

private theorem leaf4373FlatSound : Sound leaf4373Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4373CertificateValid
    leaf4373InnerLogValid leaf4373CoversExact leaf4373LowerChecked

private noncomputable def leaf4374Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (77/256), chiHi := (39/128) }

private noncomputable def leaf4374Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871265/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715523072) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1031342265/536870912) }, upper := { exponent := 0, mantissa := (7957/4096) } }, logOuter := sk135LogOuterCertificate, logK := sk135LogKCertificate, logChi := chi286LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434016767/137431046144) } }, logDArg := sk135LogDArgCertificate }

private noncomputable def leaf4374InnerLog : WideLogData :=
  innerPair101Data

set_option maxRecDepth 1000000 in
private theorem leaf4374LocalValidity :
    LeafFacts leaf4374Box leaf4374Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4374Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715523072) }) = true
      norm_num [leaf4374Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4374CertificateValid :
    WideCertificateValid leaf4374Box leaf4374Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk135ValidityFacts chi286ValidityFacts
    leaf4374LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4374CoverageChecked :
    coverageCheck (innerAD leaf4374Box) leaf4374InnerLog = true := by
  rfl'

private theorem leaf4374InnerLogValid :
    leaf4374InnerLog.Valid 8 (innerAD leaf4374Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint24PositiveFacts.valid leaf4374CoverageChecked

private noncomputable def leaf4374InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629443/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4374InputLogOnePlusV_eq :
    leaf4374InputLogOnePlusV = outerEnclosure 24
      (leaf4374Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4374RoundedFacts : LeafRoundedFacts 8
    leaf4374Certificate.logOnePlusV leaf4374InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4374InputLogOnePlusV_eq }

private noncomputable def leaf4374Inputs : Inputs :=
  inputsOfCaches globalInput sk135RoundedInputs
    chi286InputQChi innerPair101Input
    leaf4374InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4374LowerChecked :
    lowerCheck 24 leaf4374Box leaf4374Inputs = true := by
  rfl'

private theorem leaf4374CoversExact : CoversExact 8
    leaf4374Box leaf4374Certificate leaf4374InnerLog leaf4374Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk135RoundedFacts chi286RoundedFacts
    innerPair101RoundedFacts leaf4374RoundedFacts (by rfl)

private theorem leaf4374FlatSound : Sound leaf4374Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4374CertificateValid
    leaf4374InnerLogValid leaf4374CoversExact leaf4374LowerChecked

private noncomputable def leaf4375Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (19/64), chiHi := (77/256) }

private noncomputable def leaf4375Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871265/536870912) }, vSqrt := { lower := (65529/65536), upper := (22906164565/22905178112) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1029900561/536870912) }, upper := { exponent := 0, mantissa := (3973/2048) } }, logOuter := sk136LogOuterCertificate, logK := sk136LogKCertificate, logChi := chi285LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (45811342677/45810356224) } }, logDArg := sk136LogDArgCertificate }

private noncomputable def leaf4375InnerLog : WideLogData :=
  innerPair233Data

set_option maxRecDepth 1000000 in
private theorem leaf4375LocalValidity :
    LeafFacts leaf4375Box leaf4375Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4375Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22906164565/22905178112) }) = true
      norm_num [leaf4375Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4375CertificateValid :
    WideCertificateValid leaf4375Box leaf4375Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk136ValidityFacts chi285ValidityFacts
    leaf4375LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4375CoverageChecked :
    coverageCheck (innerAD leaf4375Box) leaf4375InnerLog = true := by
  rfl'

private theorem leaf4375InnerLogValid :
    leaf4375InnerLog.Valid 8 (innerAD leaf4375Box) :=
  wideLogDataValid_of_cachedCheck endpoint70PositiveFacts
    endpoint71PositiveFacts.valid leaf4375CoverageChecked

private noncomputable def leaf4375InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814721/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4375InputLogOnePlusV_eq :
    leaf4375InputLogOnePlusV = outerEnclosure 24
      (leaf4375Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4375RoundedFacts : LeafRoundedFacts 8
    leaf4375Certificate.logOnePlusV leaf4375InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4375InputLogOnePlusV_eq }

private noncomputable def leaf4375Inputs : Inputs :=
  inputsOfCaches globalInput sk136RoundedInputs
    chi285InputQChi innerPair233Input
    leaf4375InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4375LowerChecked :
    lowerCheck 24 leaf4375Box leaf4375Inputs = true := by
  rfl'

private theorem leaf4375CoversExact : CoversExact 8
    leaf4375Box leaf4375Certificate leaf4375InnerLog leaf4375Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk136RoundedFacts chi285RoundedFacts
    innerPair233RoundedFacts leaf4375RoundedFacts (by rfl)

private theorem leaf4375FlatSound : Sound leaf4375Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4375CertificateValid
    leaf4375InnerLogValid leaf4375CoversExact leaf4375LowerChecked

private noncomputable def leaf4376Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (77/256), chiHi := (39/128) }

private noncomputable def leaf4376Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871267/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715483136) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1036388227/536870912) }, upper := { exponent := 0, mantissa := (1999/1024) } }, logOuter := sk136LogOuterCertificate, logK := sk136LogKCertificate, logChi := chi286LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137433976831/137430966272) } }, logDArg := sk136LogDArgCertificate }

private noncomputable def leaf4376InnerLog : WideLogData :=
  innerPair101Data

set_option maxRecDepth 1000000 in
private theorem leaf4376LocalValidity :
    LeafFacts leaf4376Box leaf4376Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4376Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715483136) }) = true
      norm_num [leaf4376Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4376CertificateValid :
    WideCertificateValid leaf4376Box leaf4376Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk136ValidityFacts chi286ValidityFacts
    leaf4376LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4376CoverageChecked :
    coverageCheck (innerAD leaf4376Box) leaf4376InnerLog = true := by
  rfl'

private theorem leaf4376InnerLogValid :
    leaf4376InnerLog.Valid 8 (innerAD leaf4376Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint24PositiveFacts.valid leaf4376CoverageChecked

private noncomputable def leaf4376InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453681/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf4376InputLogOnePlusV_eq :
    leaf4376InputLogOnePlusV = outerEnclosure 24
      (leaf4376Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4376RoundedFacts : LeafRoundedFacts 8
    leaf4376Certificate.logOnePlusV leaf4376InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4376InputLogOnePlusV_eq }

private noncomputable def leaf4376Inputs : Inputs :=
  inputsOfCaches globalInput sk136RoundedInputs
    chi286InputQChi innerPair101Input
    leaf4376InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4376LowerChecked :
    lowerCheck 24 leaf4376Box leaf4376Inputs = true := by
  rfl'

private theorem leaf4376CoversExact : CoversExact 8
    leaf4376Box leaf4376Certificate leaf4376InnerLog leaf4376Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk136RoundedFacts chi286RoundedFacts
    innerPair101RoundedFacts leaf4376RoundedFacts (by rfl)

private theorem leaf4376FlatSound : Sound leaf4376Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4376CertificateValid
    leaf4376InnerLogValid leaf4376CoversExact leaf4376LowerChecked

private noncomputable def leaf4377Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (39/128), chiHi := (5/16) }

private noncomputable def leaf4377Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435733/268435456) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715421696) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (518865717/268435456) }, upper := { exponent := 0, mantissa := (1007/512) } }, logOuter := sk135LogOuterCertificate, logK := sk135LogKCertificate, logChi := chi248LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137433915391/137430843392) } }, logDArg := sk135LogDArgCertificate }

private noncomputable def leaf4377InnerLog : WideLogData :=
  innerPair596Data

set_option maxRecDepth 1000000 in
private theorem leaf4377LocalValidity :
    LeafFacts leaf4377Box leaf4377Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4377Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715421696) }) = true
      norm_num [leaf4377Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4377CertificateValid :
    WideCertificateValid leaf4377Box leaf4377Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk135ValidityFacts chi248ValidityFacts
    leaf4377LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4377CoverageChecked :
    coverageCheck (innerAD leaf4377Box) leaf4377InnerLog = true := by
  rfl'

private theorem leaf4377InnerLogValid :
    leaf4377InnerLog.Valid 8 (innerAD leaf4377Box) :=
  wideLogDataValid_of_cachedCheck endpoint311PositiveFacts
    endpoint312PositiveFacts.valid leaf4377CoverageChecked

private noncomputable def leaf4377InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (726841/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf4377InputLogOnePlusV_eq :
    leaf4377InputLogOnePlusV = outerEnclosure 24
      (leaf4377Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4377RoundedFacts : LeafRoundedFacts 8
    leaf4377Certificate.logOnePlusV leaf4377InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4377InputLogOnePlusV_eq }

private noncomputable def leaf4377Inputs : Inputs :=
  inputsOfCaches globalInput sk135RoundedInputs
    chi248InputQChi innerPair596Input
    leaf4377InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4377LowerChecked :
    lowerCheck 24 leaf4377Box leaf4377Inputs = true := by
  rfl'

private theorem leaf4377CoversExact : CoversExact 8
    leaf4377Box leaf4377Certificate leaf4377InnerLog leaf4377Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk135RoundedFacts chi248RoundedFacts
    innerPair596RoundedFacts leaf4377RoundedFacts (by rfl)

private theorem leaf4377FlatSound : Sound leaf4377Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4377CertificateValid
    leaf4377InnerLogValid leaf4377CoversExact leaf4377LowerChecked

private noncomputable def leaf4378Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (39/128), chiHi := (79/256) }

private noncomputable def leaf4378Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871269/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715431936) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1042875893/536870912) }, upper := { exponent := 0, mantissa := (4023/2048) } }, logOuter := sk136LogOuterCertificate, logK := sk136LogKCertificate, logChi := chi287LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137433925631/137430863872) } }, logDArg := sk136LogDArgCertificate }

private noncomputable def leaf4378InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4378LocalValidity :
    LeafFacts leaf4378Box leaf4378Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4378Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715431936) }) = true
      norm_num [leaf4378Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4378CertificateValid :
    WideCertificateValid leaf4378Box leaf4378Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk136ValidityFacts chi287ValidityFacts
    leaf4378LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4378CoverageChecked :
    coverageCheck (innerAD leaf4378Box) leaf4378InnerLog = true := by
  rfl'

private theorem leaf4378InnerLogValid :
    leaf4378InnerLog.Valid 8 (innerAD leaf4378Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4378CoverageChecked

private noncomputable def leaf4378InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629455/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4378InputLogOnePlusV_eq :
    leaf4378InputLogOnePlusV = outerEnclosure 24
      (leaf4378Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4378RoundedFacts : LeafRoundedFacts 8
    leaf4378Certificate.logOnePlusV leaf4378InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4378InputLogOnePlusV_eq }

private noncomputable def leaf4378Inputs : Inputs :=
  inputsOfCaches globalInput sk136RoundedInputs
    chi287InputQChi innerPair108Input
    leaf4378InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4378LowerChecked :
    lowerCheck 24 leaf4378Box leaf4378Inputs = true := by
  rfl'

private theorem leaf4378CoversExact : CoversExact 8
    leaf4378Box leaf4378Certificate leaf4378InnerLog leaf4378Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk136RoundedFacts chi287RoundedFacts
    innerPair108RoundedFacts leaf4378RoundedFacts (by rfl)

private theorem leaf4378FlatSound : Sound leaf4378Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4378CertificateValid
    leaf4378InnerLogValid leaf4378CoversExact leaf4378LowerChecked

private noncomputable def leaf4379Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (79/256), chiHi := (5/16) }

private noncomputable def leaf4379Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871271/536870912) }, vSqrt := { lower := (65529/65536), upper := (22906164565/22905126912) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1049363559/536870912) }, upper := { exponent := 0, mantissa := (253/128) } }, logOuter := sk136LogOuterCertificate, logK := sk136LogKCertificate, logChi := chi288LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (45811291477/45810253824) } }, logDArg := sk136LogDArgCertificate }

private noncomputable def leaf4379InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4379LocalValidity :
    LeafFacts leaf4379Box leaf4379Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4379Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22906164565/22905126912) }) = true
      norm_num [leaf4379Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4379CertificateValid :
    WideCertificateValid leaf4379Box leaf4379Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk136ValidityFacts chi288ValidityFacts
    leaf4379LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4379CoverageChecked :
    coverageCheck (innerAD leaf4379Box) leaf4379InnerLog = true := by
  rfl'

private theorem leaf4379InnerLogValid :
    leaf4379InnerLog.Valid 8 (innerAD leaf4379Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4379CoverageChecked

private noncomputable def leaf4379InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629461/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4379InputLogOnePlusV_eq :
    leaf4379InputLogOnePlusV = outerEnclosure 24
      (leaf4379Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4379RoundedFacts : LeafRoundedFacts 8
    leaf4379Certificate.logOnePlusV leaf4379InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4379InputLogOnePlusV_eq }

private noncomputable def leaf4379Inputs : Inputs :=
  inputsOfCaches globalInput sk136RoundedInputs
    chi288InputQChi innerPair108Input
    leaf4379InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4379LowerChecked :
    lowerCheck 24 leaf4379Box leaf4379Inputs = true := by
  rfl'

private theorem leaf4379CoversExact : CoversExact 8
    leaf4379Box leaf4379Certificate leaf4379InnerLog leaf4379Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk136RoundedFacts chi288RoundedFacts
    innerPair108RoundedFacts leaf4379RoundedFacts (by rfl)

private theorem leaf4379FlatSound : Sound leaf4379Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4379CertificateValid
    leaf4379InnerLogValid leaf4379CoversExact leaf4379LowerChecked

private noncomputable def leaf4380Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (9/32), chiHi := (73/256) }

private noncomputable def leaf4380Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871259/536870912) }, vSqrt := { lower := (65529/65536), upper := (4581232913/4581046784) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1008668199/536870912) }, upper := { exponent := 0, mantissa := (15565/8192) } }, logOuter := sk137LogOuterCertificate, logK := sk137LogKCertificate, logChi := chi281LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (9162279697/9162093568) } }, logDArg := sk137LogDArgCertificate }

private noncomputable def leaf4380InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4380LocalValidity :
    LeafFacts leaf4380Box leaf4380Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4380Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4581232913/4581046784) }) = true
      norm_num [leaf4380Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4380CertificateValid :
    WideCertificateValid leaf4380Box leaf4380Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk137ValidityFacts chi281ValidityFacts
    leaf4380LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4380CoverageChecked :
    coverageCheck (innerAD leaf4380Box) leaf4380InnerLog = true := by
  rfl'

private theorem leaf4380InnerLogValid :
    leaf4380InnerLog.Valid 8 (innerAD leaf4380Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4380CoverageChecked

private noncomputable def leaf4380InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814711/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4380InputLogOnePlusV_eq :
    leaf4380InputLogOnePlusV = outerEnclosure 24
      (leaf4380Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4380RoundedFacts : LeafRoundedFacts 8
    leaf4380Certificate.logOnePlusV leaf4380InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4380InputLogOnePlusV_eq }

private noncomputable def leaf4380Inputs : Inputs :=
  inputsOfCaches globalInput sk137RoundedInputs
    chi281InputQChi innerPair100Input
    leaf4380InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4380LowerChecked :
    lowerCheck 24 leaf4380Box leaf4380Inputs = true := by
  rfl'

private theorem leaf4380CoversExact : CoversExact 8
    leaf4380Box leaf4380Certificate leaf4380InnerLog leaf4380Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk137RoundedFacts chi281RoundedFacts
    innerPair100RoundedFacts leaf4380RoundedFacts (by rfl)

private theorem leaf4380FlatSound : Sound leaf4380Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4380CertificateValid
    leaf4380InnerLogValid leaf4380CoversExact leaf4380LowerChecked

private noncomputable def leaf4381Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (73/256), chiHi := (37/128) }

private noncomputable def leaf4381Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871261/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715650048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1015221397/536870912) }, upper := { exponent := 0, mantissa := (7833/4096) } }, logOuter := sk137LogOuterCertificate, logK := sk137LogKCertificate, logChi := chi282LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434143743/137431300096) } }, logDArg := sk137LogDArgCertificate }

private noncomputable def leaf4381InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4381LocalValidity :
    LeafFacts leaf4381Box leaf4381Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4381Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715650048) }) = true
      norm_num [leaf4381Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4381CertificateValid :
    WideCertificateValid leaf4381Box leaf4381Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk137ValidityFacts chi282ValidityFacts
    leaf4381LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4381CoverageChecked :
    coverageCheck (innerAD leaf4381Box) leaf4381InnerLog = true := by
  rfl'

private theorem leaf4381InnerLogValid :
    leaf4381InnerLog.Valid 8 (innerAD leaf4381Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4381CoverageChecked

private noncomputable def leaf4381InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907357/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4381InputLogOnePlusV_eq :
    leaf4381InputLogOnePlusV = outerEnclosure 24
      (leaf4381Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4381RoundedFacts : LeafRoundedFacts 8
    leaf4381Certificate.logOnePlusV leaf4381InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4381InputLogOnePlusV_eq }

private noncomputable def leaf4381Inputs : Inputs :=
  inputsOfCaches globalInput sk137RoundedInputs
    chi282InputQChi innerPair100Input
    leaf4381InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4381LowerChecked :
    lowerCheck 24 leaf4381Box leaf4381Inputs = true := by
  rfl'

private theorem leaf4381CoversExact : CoversExact 8
    leaf4381Box leaf4381Certificate leaf4381InnerLog leaf4381Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk137RoundedFacts chi282RoundedFacts
    innerPair100RoundedFacts leaf4381RoundedFacts (by rfl)

private theorem leaf4381FlatSound : Sound leaf4381Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4381CertificateValid
    leaf4381InnerLogValid leaf4381CoversExact leaf4381LowerChecked

private noncomputable def leaf4382Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (9/32), chiHi := (73/256) }

private noncomputable def leaf4382Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871261/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715664384) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1013386501/536870912) }, upper := { exponent := 0, mantissa := (7819/4096) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi281LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434158079/137431328768) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf4382InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4382LocalValidity :
    LeafFacts leaf4382Box leaf4382Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4382Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715664384) }) = true
      norm_num [leaf4382Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4382CertificateValid :
    WideCertificateValid leaf4382Box leaf4382Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi281ValidityFacts
    leaf4382LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4382CoverageChecked :
    coverageCheck (innerAD leaf4382Box) leaf4382InnerLog = true := by
  rfl'

private theorem leaf4382InnerLogValid :
    leaf4382InnerLog.Valid 8 (innerAD leaf4382Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4382CoverageChecked

private noncomputable def leaf4382InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814713/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4382InputLogOnePlusV_eq :
    leaf4382InputLogOnePlusV = outerEnclosure 24
      (leaf4382Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4382RoundedFacts : LeafRoundedFacts 8
    leaf4382Certificate.logOnePlusV leaf4382InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4382InputLogOnePlusV_eq }

private noncomputable def leaf4382Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi281InputQChi innerPair100Input
    leaf4382InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4382LowerChecked :
    lowerCheck 24 leaf4382Box leaf4382Inputs = true := by
  rfl'

private theorem leaf4382CoversExact : CoversExact 8
    leaf4382Box leaf4382Certificate leaf4382InnerLog leaf4382Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi281RoundedFacts
    innerPair100RoundedFacts leaf4382RoundedFacts (by rfl)

private theorem leaf4382FlatSound : Sound leaf4382Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4382CertificateValid
    leaf4382InnerLogValid leaf4382CoversExact leaf4382LowerChecked

private noncomputable def leaf4383Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (73/256), chiHi := (37/128) }

private noncomputable def leaf4383Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871263/536870912) }, vSqrt := { lower := (65529/65536), upper := (13743698739/13743122432) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1020005231/536870912) }, upper := { exponent := 0, mantissa := (3935/2048) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi282LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (27486821171/27486244864) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf4383InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4383LocalValidity :
    LeafFacts leaf4383Box leaf4383Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4383Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (13743698739/13743122432) }) = true
      norm_num [leaf4383Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4383CertificateValid :
    WideCertificateValid leaf4383Box leaf4383Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi282ValidityFacts
    leaf4383LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4383CoverageChecked :
    coverageCheck (innerAD leaf4383Box) leaf4383InnerLog = true := by
  rfl'

private theorem leaf4383InnerLogValid :
    leaf4383InnerLog.Valid 8 (innerAD leaf4383Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4383CoverageChecked

private noncomputable def leaf4383InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629433/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4383InputLogOnePlusV_eq :
    leaf4383InputLogOnePlusV = outerEnclosure 24
      (leaf4383Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4383RoundedFacts : LeafRoundedFacts 8
    leaf4383Certificate.logOnePlusV leaf4383InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4383InputLogOnePlusV_eq }

private noncomputable def leaf4383Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi282InputQChi innerPair100Input
    leaf4383InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4383LowerChecked :
    lowerCheck 24 leaf4383Box leaf4383Inputs = true := by
  rfl'

private theorem leaf4383CoversExact : CoversExact 8
    leaf4383Box leaf4383Certificate leaf4383InnerLog leaf4383Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi282RoundedFacts
    innerPair100RoundedFacts leaf4383RoundedFacts (by rfl)

private theorem leaf4383FlatSound : Sound leaf4383Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4383CertificateValid
    leaf4383InnerLogValid leaf4383CoversExact leaf4383LowerChecked

private noncomputable def leaf4384Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (37/128), chiHi := (75/256) }

private noncomputable def leaf4384Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871263/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715598336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1021774595/536870912) }, upper := { exponent := 0, mantissa := (15767/8192) } }, logOuter := sk137LogOuterCertificate, logK := sk137LogKCertificate, logChi := chi283LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434092031/137431196672) } }, logDArg := sk137LogDArgCertificate }

private noncomputable def leaf4384InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4384LocalValidity :
    LeafFacts leaf4384Box leaf4384Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4384Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715598336) }) = true
      norm_num [leaf4384Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4384CertificateValid :
    WideCertificateValid leaf4384Box leaf4384Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk137ValidityFacts chi283ValidityFacts
    leaf4384LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4384CoverageChecked :
    coverageCheck (innerAD leaf4384Box) leaf4384InnerLog = true := by
  rfl'

private theorem leaf4384InnerLogValid :
    leaf4384InnerLog.Valid 8 (innerAD leaf4384Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4384CoverageChecked

private noncomputable def leaf4384InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814717/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4384InputLogOnePlusV_eq :
    leaf4384InputLogOnePlusV = outerEnclosure 24
      (leaf4384Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4384RoundedFacts : LeafRoundedFacts 8
    leaf4384Certificate.logOnePlusV leaf4384InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4384InputLogOnePlusV_eq }

private noncomputable def leaf4384Inputs : Inputs :=
  inputsOfCaches globalInput sk137RoundedInputs
    chi283InputQChi innerPair100Input
    leaf4384InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4384LowerChecked :
    lowerCheck 24 leaf4384Box leaf4384Inputs = true := by
  rfl'

private theorem leaf4384CoversExact : CoversExact 8
    leaf4384Box leaf4384Certificate leaf4384InnerLog leaf4384Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk137RoundedFacts chi283RoundedFacts
    innerPair100RoundedFacts leaf4384RoundedFacts (by rfl)

private theorem leaf4384FlatSound : Sound leaf4384Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4384CertificateValid
    leaf4384InnerLogValid leaf4384CoversExact leaf4384LowerChecked

private noncomputable def leaf4385Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (75/256), chiHi := (19/64) }

private noncomputable def leaf4385Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871265/536870912) }, vSqrt := { lower := (65529/65536), upper := (22906164565/22905182208) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1028327793/536870912) }, upper := { exponent := 0, mantissa := (3967/2048) } }, logOuter := sk137LogOuterCertificate, logK := sk137LogKCertificate, logChi := chi284LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (45811346773/45810364416) } }, logDArg := sk137LogDArgCertificate }

private noncomputable def leaf4385InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4385LocalValidity :
    LeafFacts leaf4385Box leaf4385Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4385Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22906164565/22905182208) }) = true
      norm_num [leaf4385Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4385CertificateValid :
    WideCertificateValid leaf4385Box leaf4385Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk137ValidityFacts chi284ValidityFacts
    leaf4385LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4385CoverageChecked :
    coverageCheck (innerAD leaf4385Box) leaf4385InnerLog = true := by
  rfl'

private theorem leaf4385InnerLogValid :
    leaf4385InnerLog.Valid 8 (innerAD leaf4385Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4385CoverageChecked

private noncomputable def leaf4385InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629441/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4385InputLogOnePlusV_eq :
    leaf4385InputLogOnePlusV = outerEnclosure 24
      (leaf4385Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4385RoundedFacts : LeafRoundedFacts 8
    leaf4385Certificate.logOnePlusV leaf4385InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4385InputLogOnePlusV_eq }

private noncomputable def leaf4385Inputs : Inputs :=
  inputsOfCaches globalInput sk137RoundedInputs
    chi284InputQChi innerPair100Input
    leaf4385InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4385LowerChecked :
    lowerCheck 24 leaf4385Box leaf4385Inputs = true := by
  rfl'

private theorem leaf4385CoversExact : CoversExact 8
    leaf4385Box leaf4385Certificate leaf4385InnerLog leaf4385Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk137RoundedFacts chi284RoundedFacts
    innerPair100RoundedFacts leaf4385RoundedFacts (by rfl)

private theorem leaf4385FlatSound : Sound leaf4385Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4385CertificateValid
    leaf4385InnerLogValid leaf4385CoversExact leaf4385LowerChecked

private noncomputable def leaf4386Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (37/128), chiHi := (75/256) }

private noncomputable def leaf4386Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871265/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715559936) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1026623961/536870912) }, upper := { exponent := 0, mantissa := (7921/4096) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi283LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434053631/137431119872) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf4386InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4386LocalValidity :
    LeafFacts leaf4386Box leaf4386Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4386Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715559936) }) = true
      norm_num [leaf4386Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4386CertificateValid :
    WideCertificateValid leaf4386Box leaf4386Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi283ValidityFacts
    leaf4386LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4386CoverageChecked :
    coverageCheck (innerAD leaf4386Box) leaf4386InnerLog = true := by
  rfl'

private theorem leaf4386InnerLogValid :
    leaf4386InnerLog.Valid 8 (innerAD leaf4386Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4386CoverageChecked

private noncomputable def leaf4386InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629439/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4386InputLogOnePlusV_eq :
    leaf4386InputLogOnePlusV = outerEnclosure 24
      (leaf4386Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4386RoundedFacts : LeafRoundedFacts 8
    leaf4386Certificate.logOnePlusV leaf4386InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4386InputLogOnePlusV_eq }

private noncomputable def leaf4386Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi283InputQChi innerPair100Input
    leaf4386InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4386LowerChecked :
    lowerCheck 24 leaf4386Box leaf4386Inputs = true := by
  rfl'

private theorem leaf4386CoversExact : CoversExact 8
    leaf4386Box leaf4386Certificate leaf4386InnerLog leaf4386Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi283RoundedFacts
    innerPair100RoundedFacts leaf4386RoundedFacts (by rfl)

private theorem leaf4386FlatSound : Sound leaf4386Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4386CertificateValid
    leaf4386InnerLogValid leaf4386CoversExact leaf4386LowerChecked

private noncomputable def leaf4387Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (75/256), chiHi := (19/64) }

private noncomputable def leaf4387Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871267/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715507712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1033242691/536870912) }, upper := { exponent := 0, mantissa := (1993/1024) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi284LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434001407/137431015424) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf4387InnerLog : WideLogData :=
  innerPair304Data

set_option maxRecDepth 1000000 in
private theorem leaf4387LocalValidity :
    LeafFacts leaf4387Box leaf4387Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4387Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715507712) }) = true
      norm_num [leaf4387Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4387CertificateValid :
    WideCertificateValid leaf4387Box leaf4387Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi284ValidityFacts
    leaf4387LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4387CoverageChecked :
    coverageCheck (innerAD leaf4387Box) leaf4387InnerLog = true := by
  rfl'

private theorem leaf4387InnerLogValid :
    leaf4387InnerLog.Valid 8 (innerAD leaf4387Box) :=
  wideLogDataValid_of_cachedCheck endpoint81PositiveFacts
    endpoint71PositiveFacts.valid leaf4387CoverageChecked

private noncomputable def leaf4387InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629445/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4387InputLogOnePlusV_eq :
    leaf4387InputLogOnePlusV = outerEnclosure 24
      (leaf4387Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4387RoundedFacts : LeafRoundedFacts 8
    leaf4387Certificate.logOnePlusV leaf4387InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4387InputLogOnePlusV_eq }

private noncomputable def leaf4387Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi284InputQChi innerPair304Input
    leaf4387InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4387LowerChecked :
    lowerCheck 24 leaf4387Box leaf4387Inputs = true := by
  rfl'

private theorem leaf4387CoversExact : CoversExact 8
    leaf4387Box leaf4387Certificate leaf4387InnerLog leaf4387Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi284RoundedFacts
    innerPair304RoundedFacts leaf4387RoundedFacts (by rfl)

private theorem leaf4387FlatSound : Sound leaf4387Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4387CertificateValid
    leaf4387InnerLogValid leaf4387CoversExact leaf4387LowerChecked

private noncomputable def leaf4388Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (9/32), chiHi := (73/256) }

private noncomputable def leaf4388Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871263/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715627008) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1018104803/536870912) }, upper := { exponent := 0, mantissa := (15711/8192) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi281LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434120703/137431254016) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf4388InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4388LocalValidity :
    LeafFacts leaf4388Box leaf4388Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4388Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715627008) }) = true
      norm_num [leaf4388Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4388CertificateValid :
    WideCertificateValid leaf4388Box leaf4388Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi281ValidityFacts
    leaf4388LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4388CoverageChecked :
    coverageCheck (innerAD leaf4388Box) leaf4388InnerLog = true := by
  rfl'

private theorem leaf4388InnerLogValid :
    leaf4388InnerLog.Valid 8 (innerAD leaf4388Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4388CoverageChecked

private noncomputable def leaf4388InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629431/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4388InputLogOnePlusV_eq :
    leaf4388InputLogOnePlusV = outerEnclosure 24
      (leaf4388Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4388RoundedFacts : LeafRoundedFacts 8
    leaf4388Certificate.logOnePlusV leaf4388InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4388InputLogOnePlusV_eq }

private noncomputable def leaf4388Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi281InputQChi innerPair100Input
    leaf4388InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4388LowerChecked :
    lowerCheck 24 leaf4388Box leaf4388Inputs = true := by
  rfl'

private theorem leaf4388CoversExact : CoversExact 8
    leaf4388Box leaf4388Certificate leaf4388InnerLog leaf4388Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi281RoundedFacts
    innerPair100RoundedFacts leaf4388RoundedFacts (by rfl)

private theorem leaf4388FlatSound : Sound leaf4388Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4388CertificateValid
    leaf4388InnerLogValid leaf4388CoversExact leaf4388LowerChecked

private noncomputable def leaf4389Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (73/256), chiHi := (37/128) }

private noncomputable def leaf4389Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871265/536870912) }, vSqrt := { lower := (65529/65536), upper := (22906164565/22905191424) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1024789065/536870912) }, upper := { exponent := 0, mantissa := (7907/4096) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi282LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (45811355989/45810382848) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf4389InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4389LocalValidity :
    LeafFacts leaf4389Box leaf4389Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4389Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22906164565/22905191424) }) = true
      norm_num [leaf4389Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4389CertificateValid :
    WideCertificateValid leaf4389Box leaf4389Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi282ValidityFacts
    leaf4389LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4389CoverageChecked :
    coverageCheck (innerAD leaf4389Box) leaf4389InnerLog = true := by
  rfl'

private theorem leaf4389InnerLogValid :
    leaf4389InnerLog.Valid 8 (innerAD leaf4389Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4389CoverageChecked

private noncomputable def leaf4389InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629437/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4389InputLogOnePlusV_eq :
    leaf4389InputLogOnePlusV = outerEnclosure 24
      (leaf4389Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4389RoundedFacts : LeafRoundedFacts 8
    leaf4389Certificate.logOnePlusV leaf4389InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4389InputLogOnePlusV_eq }

private noncomputable def leaf4389Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi282InputQChi innerPair100Input
    leaf4389InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4389LowerChecked :
    lowerCheck 24 leaf4389Box leaf4389Inputs = true := by
  rfl'

private theorem leaf4389CoversExact : CoversExact 8
    leaf4389Box leaf4389Certificate leaf4389InnerLog leaf4389Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi282RoundedFacts
    innerPair100RoundedFacts leaf4389RoundedFacts (by rfl)

private theorem leaf4389FlatSound : Sound leaf4389Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4389CertificateValid
    leaf4389InnerLogValid leaf4389CoversExact leaf4389LowerChecked

private noncomputable def leaf4390Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (9/32), chiHi := (73/256) }

private noncomputable def leaf4390Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871265/536870912) }, vSqrt := { lower := (65529/65536), upper := (22906164565/22905196544) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1022823105/536870912) }, upper := { exponent := 0, mantissa := (1973/1024) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi281LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (45811361109/45810393088) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf4390InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4390LocalValidity :
    LeafFacts leaf4390Box leaf4390Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4390Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22906164565/22905196544) }) = true
      norm_num [leaf4390Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4390CertificateValid :
    WideCertificateValid leaf4390Box leaf4390Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi281ValidityFacts
    leaf4390LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4390CoverageChecked :
    coverageCheck (innerAD leaf4390Box) leaf4390InnerLog = true := by
  rfl'

private theorem leaf4390InnerLogValid :
    leaf4390InnerLog.Valid 8 (innerAD leaf4390Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4390CoverageChecked

private noncomputable def leaf4390InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629435/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4390InputLogOnePlusV_eq :
    leaf4390InputLogOnePlusV = outerEnclosure 24
      (leaf4390Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4390RoundedFacts : LeafRoundedFacts 8
    leaf4390Certificate.logOnePlusV leaf4390InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4390InputLogOnePlusV_eq }

private noncomputable def leaf4390Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi281InputQChi innerPair100Input
    leaf4390InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4390LowerChecked :
    lowerCheck 24 leaf4390Box leaf4390Inputs = true := by
  rfl'

private theorem leaf4390CoversExact : CoversExact 8
    leaf4390Box leaf4390Certificate leaf4390InnerLog leaf4390Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi281RoundedFacts
    innerPair100RoundedFacts leaf4390RoundedFacts (by rfl)

private theorem leaf4390FlatSound : Sound leaf4390Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4390CertificateValid
    leaf4390InnerLogValid leaf4390CoversExact leaf4390LowerChecked

private noncomputable def leaf4391Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (73/256), chiHi := (37/128) }

private noncomputable def leaf4391Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871267/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715536384) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1029572899/536870912) }, upper := { exponent := 0, mantissa := (993/512) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi282LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434030079/137431072768) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf4391InnerLog : WideLogData :=
  innerPair233Data

set_option maxRecDepth 1000000 in
private theorem leaf4391LocalValidity :
    LeafFacts leaf4391Box leaf4391Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4391Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715536384) }) = true
      norm_num [leaf4391Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4391CertificateValid :
    WideCertificateValid leaf4391Box leaf4391Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi282ValidityFacts
    leaf4391LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4391CoverageChecked :
    coverageCheck (innerAD leaf4391Box) leaf4391InnerLog = true := by
  rfl'

private theorem leaf4391InnerLogValid :
    leaf4391InnerLog.Valid 8 (innerAD leaf4391Box) :=
  wideLogDataValid_of_cachedCheck endpoint70PositiveFacts
    endpoint71PositiveFacts.valid leaf4391CoverageChecked

private noncomputable def leaf4391InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814721/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4391InputLogOnePlusV_eq :
    leaf4391InputLogOnePlusV = outerEnclosure 24
      (leaf4391Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4391RoundedFacts : LeafRoundedFacts 8
    leaf4391Certificate.logOnePlusV leaf4391InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4391InputLogOnePlusV_eq }

private noncomputable def leaf4391Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi282InputQChi innerPair233Input
    leaf4391InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4391LowerChecked :
    lowerCheck 24 leaf4391Box leaf4391Inputs = true := by
  rfl'

private theorem leaf4391CoversExact : CoversExact 8
    leaf4391Box leaf4391Certificate leaf4391InnerLog leaf4391Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi282RoundedFacts
    innerPair233RoundedFacts leaf4391RoundedFacts (by rfl)

private theorem leaf4391FlatSound : Sound leaf4391Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4391CertificateValid
    leaf4391InnerLogValid leaf4391CoversExact leaf4391LowerChecked

private noncomputable def leaf4392Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (37/128), chiHi := (75/256) }

private noncomputable def leaf4392Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871267/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715521536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1031473327/536870912) }, upper := { exponent := 0, mantissa := (15917/8192) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi283LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434015231/137431043072) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf4392InnerLog : WideLogData :=
  innerPair233Data

set_option maxRecDepth 1000000 in
private theorem leaf4392LocalValidity :
    LeafFacts leaf4392Box leaf4392Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4392Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715521536) }) = true
      norm_num [leaf4392Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4392CertificateValid :
    WideCertificateValid leaf4392Box leaf4392Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi283ValidityFacts
    leaf4392LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4392CoverageChecked :
    coverageCheck (innerAD leaf4392Box) leaf4392InnerLog = true := by
  rfl'

private theorem leaf4392InnerLogValid :
    leaf4392InnerLog.Valid 8 (innerAD leaf4392Box) :=
  wideLogDataValid_of_cachedCheck endpoint70PositiveFacts
    endpoint71PositiveFacts.valid leaf4392CoverageChecked

private noncomputable def leaf4392InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907361/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4392InputLogOnePlusV_eq :
    leaf4392InputLogOnePlusV = outerEnclosure 24
      (leaf4392Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4392RoundedFacts : LeafRoundedFacts 8
    leaf4392Certificate.logOnePlusV leaf4392InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4392InputLogOnePlusV_eq }

private noncomputable def leaf4392Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi283InputQChi innerPair233Input
    leaf4392InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4392LowerChecked :
    lowerCheck 24 leaf4392Box leaf4392Inputs = true := by
  rfl'

private theorem leaf4392CoversExact : CoversExact 8
    leaf4392Box leaf4392Certificate leaf4392InnerLog leaf4392Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi283RoundedFacts
    innerPair233RoundedFacts leaf4392RoundedFacts (by rfl)

private theorem leaf4392FlatSound : Sound leaf4392Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4392CertificateValid
    leaf4392InnerLogValid leaf4392CoversExact leaf4392LowerChecked

private noncomputable def leaf4393Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (75/256), chiHi := (19/64) }

private noncomputable def leaf4393Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871269/536870912) }, vSqrt := { lower := (65529/65536), upper := (808452867/808417280) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1038157589/536870912) }, upper := { exponent := 0, mantissa := (4005/2048) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi284LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (1616870147/1616834560) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf4393InnerLog : WideLogData :=
  innerPair306Data

set_option maxRecDepth 1000000 in
private theorem leaf4393LocalValidity :
    LeafFacts leaf4393Box leaf4393Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4393Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (808452867/808417280) }) = true
      norm_num [leaf4393Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4393CertificateValid :
    WideCertificateValid leaf4393Box leaf4393Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi284ValidityFacts
    leaf4393LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4393CoverageChecked :
    coverageCheck (innerAD leaf4393Box) leaf4393InnerLog = true := by
  rfl'

private theorem leaf4393InnerLogValid :
    leaf4393InnerLog.Valid 8 (innerAD leaf4393Box) :=
  wideLogDataValid_of_cachedCheck endpoint81PositiveFacts
    endpoint85PositiveFacts.valid leaf4393CoverageChecked

private noncomputable def leaf4393InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814725/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4393InputLogOnePlusV_eq :
    leaf4393InputLogOnePlusV = outerEnclosure 24
      (leaf4393Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4393RoundedFacts : LeafRoundedFacts 8
    leaf4393Certificate.logOnePlusV leaf4393InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4393InputLogOnePlusV_eq }

private noncomputable def leaf4393Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi284InputQChi innerPair306Input
    leaf4393InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4393LowerChecked :
    lowerCheck 24 leaf4393Box leaf4393Inputs = true := by
  rfl'

private theorem leaf4393CoversExact : CoversExact 8
    leaf4393Box leaf4393Certificate leaf4393InnerLog leaf4393Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi284RoundedFacts
    innerPair306RoundedFacts leaf4393RoundedFacts (by rfl)

private theorem leaf4393FlatSound : Sound leaf4393Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4393CertificateValid
    leaf4393InnerLogValid leaf4393CoversExact leaf4393LowerChecked

private noncomputable def leaf4394Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (37/128), chiHi := (75/256) }

private noncomputable def leaf4394Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871269/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715483136) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1036322693/536870912) }, upper := { exponent := 0, mantissa := (1999/1024) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi283LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137433976831/137430966272) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf4394InnerLog : WideLogData :=
  innerPair304Data

set_option maxRecDepth 1000000 in
private theorem leaf4394LocalValidity :
    LeafFacts leaf4394Box leaf4394Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4394Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715483136) }) = true
      norm_num [leaf4394Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4394CertificateValid :
    WideCertificateValid leaf4394Box leaf4394Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi283ValidityFacts
    leaf4394LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4394CoverageChecked :
    coverageCheck (innerAD leaf4394Box) leaf4394InnerLog = true := by
  rfl'

private theorem leaf4394InnerLogValid :
    leaf4394InnerLog.Valid 8 (innerAD leaf4394Box) :=
  wideLogDataValid_of_cachedCheck endpoint81PositiveFacts
    endpoint71PositiveFacts.valid leaf4394CoverageChecked

private noncomputable def leaf4394InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453681/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf4394InputLogOnePlusV_eq :
    leaf4394InputLogOnePlusV = outerEnclosure 24
      (leaf4394Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4394RoundedFacts : LeafRoundedFacts 8
    leaf4394Certificate.logOnePlusV leaf4394InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4394InputLogOnePlusV_eq }

private noncomputable def leaf4394Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi283InputQChi innerPair304Input
    leaf4394InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4394LowerChecked :
    lowerCheck 24 leaf4394Box leaf4394Inputs = true := by
  rfl'

private theorem leaf4394CoversExact : CoversExact 8
    leaf4394Box leaf4394Certificate leaf4394InnerLog leaf4394Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi283RoundedFacts
    innerPair304RoundedFacts leaf4394RoundedFacts (by rfl)

private theorem leaf4394FlatSound : Sound leaf4394Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4394CertificateValid
    leaf4394InnerLogValid leaf4394CoversExact leaf4394LowerChecked

private noncomputable def leaf4395Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (75/256), chiHi := (19/64) }

private noncomputable def leaf4395Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871271/536870912) }, vSqrt := { lower := (65529/65536), upper := (22906164565/22905143296) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1043072487/536870912) }, upper := { exponent := 0, mantissa := (503/256) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi284LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (45811307861/45810286592) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf4395InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4395LocalValidity :
    LeafFacts leaf4395Box leaf4395Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4395Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22906164565/22905143296) }) = true
      norm_num [leaf4395Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4395CertificateValid :
    WideCertificateValid leaf4395Box leaf4395Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi284ValidityFacts
    leaf4395LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4395CoverageChecked :
    coverageCheck (innerAD leaf4395Box) leaf4395InnerLog = true := by
  rfl'

private theorem leaf4395InnerLogValid :
    leaf4395InnerLog.Valid 8 (innerAD leaf4395Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4395CoverageChecked

private noncomputable def leaf4395InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629455/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4395InputLogOnePlusV_eq :
    leaf4395InputLogOnePlusV = outerEnclosure 24
      (leaf4395Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4395RoundedFacts : LeafRoundedFacts 8
    leaf4395Certificate.logOnePlusV leaf4395InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4395InputLogOnePlusV_eq }

private noncomputable def leaf4395Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi284InputQChi innerPair108Input
    leaf4395InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4395LowerChecked :
    lowerCheck 24 leaf4395Box leaf4395Inputs = true := by
  rfl'

private theorem leaf4395CoversExact : CoversExact 8
    leaf4395Box leaf4395Certificate leaf4395InnerLog leaf4395Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi284RoundedFacts
    innerPair108RoundedFacts leaf4395RoundedFacts (by rfl)

private theorem leaf4395FlatSound : Sound leaf4395Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4395CertificateValid
    leaf4395InnerLogValid leaf4395CoversExact leaf4395LowerChecked

private noncomputable def leaf4396Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (19/64), chiHi := (77/256) }

private noncomputable def leaf4396Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871267/536870912) }, vSqrt := { lower := (65529/65536), upper := (4042264335/4042087936) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1034880991/536870912) }, upper := { exponent := 0, mantissa := (15969/8192) } }, logOuter := sk137LogOuterCertificate, logK := sk137LogKCertificate, logChi := chi285LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (8084352271/8084175872) } }, logDArg := sk137LogDArgCertificate }

private noncomputable def leaf4396InnerLog : WideLogData :=
  innerPair304Data

set_option maxRecDepth 1000000 in
private theorem leaf4396LocalValidity :
    LeafFacts leaf4396Box leaf4396Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4396Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4042264335/4042087936) }) = true
      norm_num [leaf4396Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4396CertificateValid :
    WideCertificateValid leaf4396Box leaf4396Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk137ValidityFacts chi285ValidityFacts
    leaf4396LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4396CoverageChecked :
    coverageCheck (innerAD leaf4396Box) leaf4396InnerLog = true := by
  rfl'

private theorem leaf4396InnerLogValid :
    leaf4396InnerLog.Valid 8 (innerAD leaf4396Box) :=
  wideLogDataValid_of_cachedCheck endpoint81PositiveFacts
    endpoint71PositiveFacts.valid leaf4396CoverageChecked

private noncomputable def leaf4396InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629447/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4396InputLogOnePlusV_eq :
    leaf4396InputLogOnePlusV = outerEnclosure 24
      (leaf4396Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4396RoundedFacts : LeafRoundedFacts 8
    leaf4396Certificate.logOnePlusV leaf4396InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4396InputLogOnePlusV_eq }

private noncomputable def leaf4396Inputs : Inputs :=
  inputsOfCaches globalInput sk137RoundedInputs
    chi285InputQChi innerPair304Input
    leaf4396InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4396LowerChecked :
    lowerCheck 24 leaf4396Box leaf4396Inputs = true := by
  rfl'

private theorem leaf4396CoversExact : CoversExact 8
    leaf4396Box leaf4396Certificate leaf4396InnerLog leaf4396Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk137RoundedFacts chi285RoundedFacts
    innerPair304RoundedFacts leaf4396RoundedFacts (by rfl)

private theorem leaf4396FlatSound : Sound leaf4396Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4396CertificateValid
    leaf4396InnerLogValid leaf4396CoversExact leaf4396LowerChecked

private noncomputable def leaf4397Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (77/256), chiHi := (39/128) }

private noncomputable def leaf4397Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871269/536870912) }, vSqrt := { lower := (65529/65536), upper := (13743698739/13743088640) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1041434189/536870912) }, upper := { exponent := 0, mantissa := (8035/4096) } }, logOuter := sk137LogOuterCertificate, logK := sk137LogKCertificate, logChi := chi286LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (27486787379/27486177280) } }, logDArg := sk137LogDArgCertificate }

private noncomputable def leaf4397InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4397LocalValidity :
    LeafFacts leaf4397Box leaf4397Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4397Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (13743698739/13743088640) }) = true
      norm_num [leaf4397Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4397CertificateValid :
    WideCertificateValid leaf4397Box leaf4397Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk137ValidityFacts chi286ValidityFacts
    leaf4397LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4397CoverageChecked :
    coverageCheck (innerAD leaf4397Box) leaf4397InnerLog = true := by
  rfl'

private theorem leaf4397InnerLogValid :
    leaf4397InnerLog.Valid 8 (innerAD leaf4397Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4397CoverageChecked

private noncomputable def leaf4397InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629453/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4397InputLogOnePlusV_eq :
    leaf4397InputLogOnePlusV = outerEnclosure 24
      (leaf4397Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4397RoundedFacts : LeafRoundedFacts 8
    leaf4397Certificate.logOnePlusV leaf4397InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4397InputLogOnePlusV_eq }

private noncomputable def leaf4397Inputs : Inputs :=
  inputsOfCaches globalInput sk137RoundedInputs
    chi286InputQChi innerPair108Input
    leaf4397InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4397LowerChecked :
    lowerCheck 24 leaf4397Box leaf4397Inputs = true := by
  rfl'

private theorem leaf4397CoversExact : CoversExact 8
    leaf4397Box leaf4397Certificate leaf4397InnerLog leaf4397Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk137RoundedFacts chi286RoundedFacts
    innerPair108RoundedFacts leaf4397RoundedFacts (by rfl)

private theorem leaf4397FlatSound : Sound leaf4397Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4397CertificateValid
    leaf4397InnerLogValid leaf4397CoversExact leaf4397LowerChecked

private noncomputable def leaf4398Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (19/64), chiHi := (77/256) }

private noncomputable def leaf4398Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871269/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715455488) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1039861421/536870912) }, upper := { exponent := 0, mantissa := (8023/4096) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi285LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137433949183/137430910976) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf4398InnerLog : WideLogData :=
  innerPair101Data

set_option maxRecDepth 1000000 in
private theorem leaf4398LocalValidity :
    LeafFacts leaf4398Box leaf4398Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4398Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715455488) }) = true
      norm_num [leaf4398Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4398CertificateValid :
    WideCertificateValid leaf4398Box leaf4398Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi285ValidityFacts
    leaf4398LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4398CoverageChecked :
    coverageCheck (innerAD leaf4398Box) leaf4398InnerLog = true := by
  rfl'

private theorem leaf4398InnerLogValid :
    leaf4398InnerLog.Valid 8 (innerAD leaf4398Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint24PositiveFacts.valid leaf4398CoverageChecked

private noncomputable def leaf4398InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907363/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4398InputLogOnePlusV_eq :
    leaf4398InputLogOnePlusV = outerEnclosure 24
      (leaf4398Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4398RoundedFacts : LeafRoundedFacts 8
    leaf4398Certificate.logOnePlusV leaf4398InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4398InputLogOnePlusV_eq }

private noncomputable def leaf4398Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi285InputQChi innerPair101Input
    leaf4398InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4398LowerChecked :
    lowerCheck 24 leaf4398Box leaf4398Inputs = true := by
  rfl'

private theorem leaf4398CoversExact : CoversExact 8
    leaf4398Box leaf4398Certificate leaf4398InnerLog leaf4398Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi285RoundedFacts
    innerPair101RoundedFacts leaf4398RoundedFacts (by rfl)

private theorem leaf4398FlatSound : Sound leaf4398Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4398CertificateValid
    leaf4398InnerLogValid leaf4398CoversExact leaf4398LowerChecked

private noncomputable def leaf4399Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (77/256), chiHi := (39/128) }

private noncomputable def leaf4399Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871271/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715403264) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1046480151/536870912) }, upper := { exponent := 0, mantissa := (4037/2048) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi286LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137433896959/137430806528) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf4399InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4399LocalValidity :
    LeafFacts leaf4399Box leaf4399Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4399Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715403264) }) = true
      norm_num [leaf4399Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4399CertificateValid :
    WideCertificateValid leaf4399Box leaf4399Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi286ValidityFacts
    leaf4399LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4399CoverageChecked :
    coverageCheck (innerAD leaf4399Box) leaf4399InnerLog = true := by
  rfl'

private theorem leaf4399InnerLogValid :
    leaf4399InnerLog.Valid 8 (innerAD leaf4399Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4399CoverageChecked

private noncomputable def leaf4399InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814729/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4399InputLogOnePlusV_eq :
    leaf4399InputLogOnePlusV = outerEnclosure 24
      (leaf4399Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4399RoundedFacts : LeafRoundedFacts 8
    leaf4399Certificate.logOnePlusV leaf4399InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4399InputLogOnePlusV_eq }

private noncomputable def leaf4399Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi286InputQChi innerPair108Input
    leaf4399InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4399LowerChecked :
    lowerCheck 24 leaf4399Box leaf4399Inputs = true := by
  rfl'

private theorem leaf4399CoversExact : CoversExact 8
    leaf4399Box leaf4399Certificate leaf4399InnerLog leaf4399Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi286RoundedFacts
    innerPair108RoundedFacts leaf4399RoundedFacts (by rfl)

private theorem leaf4399FlatSound : Sound leaf4399Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4399CertificateValid
    leaf4399InnerLogValid leaf4399CoversExact leaf4399LowerChecked

private noncomputable def leaf4400Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (39/128), chiHi := (79/256) }

private noncomputable def leaf4400Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871271/536870912) }, vSqrt := { lower := (65529/65536), upper := (22906164565/22905130496) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1047987387/536870912) }, upper := { exponent := 0, mantissa := (16171/8192) } }, logOuter := sk137LogOuterCertificate, logK := sk137LogKCertificate, logChi := chi287LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (45811295061/45810260992) } }, logDArg := sk137LogDArgCertificate }

private noncomputable def leaf4400InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4400LocalValidity :
    LeafFacts leaf4400Box leaf4400Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4400Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22906164565/22905130496) }) = true
      norm_num [leaf4400Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4400CertificateValid :
    WideCertificateValid leaf4400Box leaf4400Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk137ValidityFacts chi287ValidityFacts
    leaf4400LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4400CoverageChecked :
    coverageCheck (innerAD leaf4400Box) leaf4400InnerLog = true := by
  rfl'

private theorem leaf4400InnerLogValid :
    leaf4400InnerLog.Valid 8 (innerAD leaf4400Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4400CoverageChecked

private noncomputable def leaf4400InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629459/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4400InputLogOnePlusV_eq :
    leaf4400InputLogOnePlusV = outerEnclosure 24
      (leaf4400Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4400RoundedFacts : LeafRoundedFacts 8
    leaf4400Certificate.logOnePlusV leaf4400InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4400InputLogOnePlusV_eq }

private noncomputable def leaf4400Inputs : Inputs :=
  inputsOfCaches globalInput sk137RoundedInputs
    chi287InputQChi innerPair108Input
    leaf4400InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4400LowerChecked :
    lowerCheck 24 leaf4400Box leaf4400Inputs = true := by
  rfl'

private theorem leaf4400CoversExact : CoversExact 8
    leaf4400Box leaf4400Certificate leaf4400InnerLog leaf4400Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk137RoundedFacts chi287RoundedFacts
    innerPair108RoundedFacts leaf4400RoundedFacts (by rfl)

private theorem leaf4400FlatSound : Sound leaf4400Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4400CertificateValid
    leaf4400InnerLogValid leaf4400CoversExact leaf4400LowerChecked

private noncomputable def leaf4401Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (79/256), chiHi := (5/16) }

private noncomputable def leaf4401Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871273/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357669888) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1054540585/536870912) }, upper := { exponent := 0, mantissa := (1017/512) } }, logOuter := sk137LogOuterCertificate, logK := sk137LogKCertificate, logChi := chi288LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716392447/68715339776) } }, logDArg := sk137LogDArgCertificate }

private noncomputable def leaf4401InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4401LocalValidity :
    LeafFacts leaf4401Box leaf4401Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4401Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357669888) }) = true
      norm_num [leaf4401Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4401CertificateValid :
    WideCertificateValid leaf4401Box leaf4401Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk137ValidityFacts chi288ValidityFacts
    leaf4401LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4401CoverageChecked :
    coverageCheck (innerAD leaf4401Box) leaf4401InnerLog = true := by
  rfl'

private theorem leaf4401InnerLogValid :
    leaf4401InnerLog.Valid 8 (innerAD leaf4401Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4401CoverageChecked

private noncomputable def leaf4401InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814669/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4401InputLogOnePlusV_eq :
    leaf4401InputLogOnePlusV = outerEnclosure 24
      (leaf4401Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4401RoundedFacts : LeafRoundedFacts 8
    leaf4401Certificate.logOnePlusV leaf4401InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4401InputLogOnePlusV_eq }

private noncomputable def leaf4401Inputs : Inputs :=
  inputsOfCaches globalInput sk137RoundedInputs
    chi288InputQChi innerPair108Input
    leaf4401InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4401LowerChecked :
    lowerCheck 24 leaf4401Box leaf4401Inputs = true := by
  rfl'

private theorem leaf4401CoversExact : CoversExact 8
    leaf4401Box leaf4401Certificate leaf4401InnerLog leaf4401Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk137RoundedFacts chi288RoundedFacts
    innerPair108RoundedFacts leaf4401RoundedFacts (by rfl)

private theorem leaf4401FlatSound : Sound leaf4401Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4401CertificateValid
    leaf4401InnerLogValid leaf4401CoversExact leaf4401LowerChecked

private noncomputable def leaf4402Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (39/128), chiHi := (79/256) }

private noncomputable def leaf4402Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871273/536870912) }, vSqrt := { lower := (65529/65536), upper := (13743698739/13743070208) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1053098881/536870912) }, upper := { exponent := 0, mantissa := (8125/4096) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi287LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (27486768947/27486140416) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf4402InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4402LocalValidity :
    LeafFacts leaf4402Box leaf4402Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4402Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (13743698739/13743070208) }) = true
      norm_num [leaf4402Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4402CertificateValid :
    WideCertificateValid leaf4402Box leaf4402Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi287ValidityFacts
    leaf4402LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4402CoverageChecked :
    coverageCheck (innerAD leaf4402Box) leaf4402InnerLog = true := by
  rfl'

private theorem leaf4402InnerLogValid :
    leaf4402InnerLog.Valid 8 (innerAD leaf4402Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4402CoverageChecked

private noncomputable def leaf4402InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453683/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf4402InputLogOnePlusV_eq :
    leaf4402InputLogOnePlusV = outerEnclosure 24
      (leaf4402Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4402RoundedFacts : LeafRoundedFacts 8
    leaf4402Certificate.logOnePlusV leaf4402InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4402InputLogOnePlusV_eq }

private noncomputable def leaf4402Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi287InputQChi innerPair108Input
    leaf4402InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4402LowerChecked :
    lowerCheck 24 leaf4402Box leaf4402Inputs = true := by
  rfl'

private theorem leaf4402CoversExact : CoversExact 8
    leaf4402Box leaf4402Certificate leaf4402InnerLog leaf4402Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi287RoundedFacts
    innerPair108RoundedFacts leaf4402RoundedFacts (by rfl)

private theorem leaf4402FlatSound : Sound leaf4402Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4402CertificateValid
    leaf4402InnerLogValid leaf4402CoversExact leaf4402LowerChecked

private noncomputable def leaf4403Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (79/256), chiHi := (5/16) }

private noncomputable def leaf4403Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871275/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357649408) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1059717611/536870912) }, upper := { exponent := 0, mantissa := (511/256) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi288LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716371967/68715298816) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf4403InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4403LocalValidity :
    LeafFacts leaf4403Box leaf4403Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4403Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357649408) }) = true
      norm_num [leaf4403Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4403CertificateValid :
    WideCertificateValid leaf4403Box leaf4403Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi288ValidityFacts
    leaf4403LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4403CoverageChecked :
    coverageCheck (innerAD leaf4403Box) leaf4403InnerLog = true := by
  rfl'

private theorem leaf4403InnerLogValid :
    leaf4403InnerLog.Valid 8 (innerAD leaf4403Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4403CoverageChecked

private noncomputable def leaf4403InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629343/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4403InputLogOnePlusV_eq :
    leaf4403InputLogOnePlusV = outerEnclosure 24
      (leaf4403Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4403RoundedFacts : LeafRoundedFacts 8
    leaf4403Certificate.logOnePlusV leaf4403InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4403InputLogOnePlusV_eq }

private noncomputable def leaf4403Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi288InputQChi innerPair108Input
    leaf4403InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4403LowerChecked :
    lowerCheck 24 leaf4403Box leaf4403Inputs = true := by
  rfl'

private theorem leaf4403CoversExact : CoversExact 8
    leaf4403Box leaf4403Certificate leaf4403InnerLog leaf4403Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi288RoundedFacts
    innerPair108RoundedFacts leaf4403RoundedFacts (by rfl)

private theorem leaf4403FlatSound : Sound leaf4403Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4403CertificateValid
    leaf4403InnerLogValid leaf4403CoversExact leaf4403LowerChecked

private noncomputable def leaf4404Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (19/64), chiHi := (77/256) }

private noncomputable def leaf4404Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871271/536870912) }, vSqrt := { lower := (65529/65536), upper := (22906164565/22905138688) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1044841851/536870912) }, upper := { exponent := 0, mantissa := (16123/8192) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi285LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (45811303253/45810277376) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf4404InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4404LocalValidity :
    LeafFacts leaf4404Box leaf4404Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4404Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22906164565/22905138688) }) = true
      norm_num [leaf4404Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4404CertificateValid :
    WideCertificateValid leaf4404Box leaf4404Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi285ValidityFacts
    leaf4404LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4404CoverageChecked :
    coverageCheck (innerAD leaf4404Box) leaf4404InnerLog = true := by
  rfl'

private theorem leaf4404InnerLogValid :
    leaf4404InnerLog.Valid 8 (innerAD leaf4404Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4404CoverageChecked

private noncomputable def leaf4404InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (726841/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf4404InputLogOnePlusV_eq :
    leaf4404InputLogOnePlusV = outerEnclosure 24
      (leaf4404Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4404RoundedFacts : LeafRoundedFacts 8
    leaf4404Certificate.logOnePlusV leaf4404InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4404InputLogOnePlusV_eq }

private noncomputable def leaf4404Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi285InputQChi innerPair108Input
    leaf4404InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4404LowerChecked :
    lowerCheck 24 leaf4404Box leaf4404Inputs = true := by
  rfl'

private theorem leaf4404CoversExact : CoversExact 8
    leaf4404Box leaf4404Certificate leaf4404InnerLog leaf4404Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi285RoundedFacts
    innerPair108RoundedFacts leaf4404RoundedFacts (by rfl)

private theorem leaf4404FlatSound : Sound leaf4404Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4404CertificateValid
    leaf4404InnerLogValid leaf4404CoversExact leaf4404LowerChecked

private noncomputable def leaf4405Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (77/256), chiHi := (39/128) }

private noncomputable def leaf4405Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871273/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715363328) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1051526113/536870912) }, upper := { exponent := 0, mantissa := (8113/4096) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi286LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137433857023/137430726656) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf4405InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4405LocalValidity :
    LeafFacts leaf4405Box leaf4405Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4405Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715363328) }) = true
      norm_num [leaf4405Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4405CertificateValid :
    WideCertificateValid leaf4405Box leaf4405Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi286ValidityFacts
    leaf4405LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4405CoverageChecked :
    coverageCheck (innerAD leaf4405Box) leaf4405InnerLog = true := by
  rfl'

private theorem leaf4405InnerLogValid :
    leaf4405InnerLog.Valid 8 (innerAD leaf4405Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4405CoverageChecked

private noncomputable def leaf4405InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629463/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4405InputLogOnePlusV_eq :
    leaf4405InputLogOnePlusV = outerEnclosure 24
      (leaf4405Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4405RoundedFacts : LeafRoundedFacts 8
    leaf4405Certificate.logOnePlusV leaf4405InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4405InputLogOnePlusV_eq }

private noncomputable def leaf4405Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi286InputQChi innerPair108Input
    leaf4405InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4405LowerChecked :
    lowerCheck 24 leaf4405Box leaf4405Inputs = true := by
  rfl'

private theorem leaf4405CoversExact : CoversExact 8
    leaf4405Box leaf4405Certificate leaf4405InnerLog leaf4405Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi286RoundedFacts
    innerPair108RoundedFacts leaf4405RoundedFacts (by rfl)

private theorem leaf4405FlatSound : Sound leaf4405Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4405CertificateValid
    leaf4405InnerLogValid leaf4405CoversExact leaf4405LowerChecked

private noncomputable def leaf4406Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (19/64), chiHi := (77/256) }

private noncomputable def leaf4406Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871273/536870912) }, vSqrt := { lower := (65529/65536), upper := (13743698739/13743075328) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1049822281/536870912) }, upper := { exponent := 0, mantissa := (2025/1024) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi285LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (27486774067/27486150656) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf4406InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4406LocalValidity :
    LeafFacts leaf4406Box leaf4406Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4406Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (13743698739/13743075328) }) = true
      norm_num [leaf4406Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4406CertificateValid :
    WideCertificateValid leaf4406Box leaf4406Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi285ValidityFacts
    leaf4406LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4406CoverageChecked :
    coverageCheck (innerAD leaf4406Box) leaf4406InnerLog = true := by
  rfl'

private theorem leaf4406InnerLogValid :
    leaf4406InnerLog.Valid 8 (innerAD leaf4406Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4406CoverageChecked

private noncomputable def leaf4406InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629461/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4406InputLogOnePlusV_eq :
    leaf4406InputLogOnePlusV = outerEnclosure 24
      (leaf4406Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4406RoundedFacts : LeafRoundedFacts 8
    leaf4406Certificate.logOnePlusV leaf4406InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4406InputLogOnePlusV_eq }

private noncomputable def leaf4406Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi285InputQChi innerPair108Input
    leaf4406InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4406LowerChecked :
    lowerCheck 24 leaf4406Box leaf4406Inputs = true := by
  rfl'

private theorem leaf4406CoversExact : CoversExact 8
    leaf4406Box leaf4406Certificate leaf4406InnerLog leaf4406Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi285RoundedFacts
    innerPair108RoundedFacts leaf4406RoundedFacts (by rfl)

private theorem leaf4406FlatSound : Sound leaf4406Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4406CertificateValid
    leaf4406InnerLogValid leaf4406CoversExact leaf4406LowerChecked

private noncomputable def leaf4407Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (77/256), chiHi := (39/128) }

private noncomputable def leaf4407Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871275/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357661696) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1056572075/536870912) }, upper := { exponent := 0, mantissa := (1019/512) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi286LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716384255/68715323392) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf4407InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4407LocalValidity :
    LeafFacts leaf4407Box leaf4407Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4407Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357661696) }) = true
      norm_num [leaf4407Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4407CertificateValid :
    WideCertificateValid leaf4407Box leaf4407Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi286ValidityFacts
    leaf4407LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4407CoverageChecked :
    coverageCheck (innerAD leaf4407Box) leaf4407InnerLog = true := by
  rfl'

private theorem leaf4407InnerLogValid :
    leaf4407InnerLog.Valid 8 (innerAD leaf4407Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4407CoverageChecked

private noncomputable def leaf4407InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907335/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4407InputLogOnePlusV_eq :
    leaf4407InputLogOnePlusV = outerEnclosure 24
      (leaf4407Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4407RoundedFacts : LeafRoundedFacts 8
    leaf4407Certificate.logOnePlusV leaf4407InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4407InputLogOnePlusV_eq }

private noncomputable def leaf4407Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi286InputQChi innerPair108Input
    leaf4407InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4407LowerChecked :
    lowerCheck 24 leaf4407Box leaf4407Inputs = true := by
  rfl'

private theorem leaf4407CoversExact : CoversExact 8
    leaf4407Box leaf4407Certificate leaf4407InnerLog leaf4407Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi286RoundedFacts
    innerPair108RoundedFacts leaf4407RoundedFacts (by rfl)

private theorem leaf4407FlatSound : Sound leaf4407Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4407CertificateValid
    leaf4407InnerLogValid leaf4407CoversExact leaf4407LowerChecked

private noncomputable def leaf4408Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (39/128), chiHi := (79/256) }

private noncomputable def leaf4408Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871275/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357655296) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1058210375/536870912) }, upper := { exponent := 0, mantissa := (16329/8192) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi287LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716377855/68715310592) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf4408InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4408LocalValidity :
    LeafFacts leaf4408Box leaf4408Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4408Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357655296) }) = true
      norm_num [leaf4408Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4408CertificateValid :
    WideCertificateValid leaf4408Box leaf4408Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi287ValidityFacts
    leaf4408LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4408CoverageChecked :
    coverageCheck (innerAD leaf4408Box) leaf4408InnerLog = true := by
  rfl'

private theorem leaf4408InnerLogValid :
    leaf4408InnerLog.Valid 8 (innerAD leaf4408Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4408CoverageChecked

private noncomputable def leaf4408InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629341/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4408InputLogOnePlusV_eq :
    leaf4408InputLogOnePlusV = outerEnclosure 24
      (leaf4408Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4408RoundedFacts : LeafRoundedFacts 8
    leaf4408Certificate.logOnePlusV leaf4408InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4408InputLogOnePlusV_eq }

private noncomputable def leaf4408Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi287InputQChi innerPair108Input
    leaf4408InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4408LowerChecked :
    lowerCheck 24 leaf4408Box leaf4408Inputs = true := by
  rfl'

private theorem leaf4408CoversExact : CoversExact 8
    leaf4408Box leaf4408Certificate leaf4408InnerLog leaf4408Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi287RoundedFacts
    innerPair108RoundedFacts leaf4408RoundedFacts (by rfl)

private theorem leaf4408FlatSound : Sound leaf4408Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4408CertificateValid
    leaf4408InnerLogValid leaf4408CoversExact leaf4408LowerChecked

private noncomputable def leaf4409Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (79/256), chiHi := (5/16) }

private noncomputable def leaf4409Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871277/536870912) }, vSqrt := { lower := (65529/65536), upper := (4908388937/4908232704) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1064894637/536870912) }, upper := { exponent := 1, mantissa := (1027/1024) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi288LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (9816621641/9816465408) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf4409InnerLog : WideLogData :=
  innerPair321Data

set_option maxRecDepth 1000000 in
private theorem leaf4409LocalValidity :
    LeafFacts leaf4409Box leaf4409Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4409Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4908388937/4908232704) }) = true
      norm_num [leaf4409Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4409CertificateValid :
    WideCertificateValid leaf4409Box leaf4409Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi288ValidityFacts
    leaf4409LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4409CoverageChecked :
    coverageCheck (innerAD leaf4409Box) leaf4409InnerLog = true := by
  rfl'

private theorem leaf4409InnerLogValid :
    leaf4409InnerLog.Valid 8 (innerAD leaf4409Box) :=
  wideLogDataValid_of_cachedCheck endpoint85PositiveFacts
    endpoint283PositiveFacts.valid leaf4409CoverageChecked

private noncomputable def leaf4409InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907337/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4409InputLogOnePlusV_eq :
    leaf4409InputLogOnePlusV = outerEnclosure 24
      (leaf4409Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4409RoundedFacts : LeafRoundedFacts 8
    leaf4409Certificate.logOnePlusV leaf4409InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4409InputLogOnePlusV_eq }

private noncomputable def leaf4409Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi288InputQChi innerPair321Input
    leaf4409InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4409LowerChecked :
    lowerCheck 24 leaf4409Box leaf4409Inputs = true := by
  rfl'

private theorem leaf4409CoversExact : CoversExact 8
    leaf4409Box leaf4409Certificate leaf4409InnerLog leaf4409Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi288RoundedFacts
    innerPair321RoundedFacts leaf4409RoundedFacts (by rfl)

private theorem leaf4409FlatSound : Sound leaf4409Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4409CertificateValid
    leaf4409InnerLogValid leaf4409CoversExact leaf4409LowerChecked

private noncomputable def leaf4410Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (39/128), chiHi := (79/256) }

private noncomputable def leaf4410Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871277/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357635072) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1063321869/536870912) }, upper := { exponent := 1, mantissa := (2051/2048) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi287LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716357631/68715270144) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf4410InnerLog : WideLogData :=
  innerPair321Data

set_option maxRecDepth 1000000 in
private theorem leaf4410LocalValidity :
    LeafFacts leaf4410Box leaf4410Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4410Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357635072) }) = true
      norm_num [leaf4410Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4410CertificateValid :
    WideCertificateValid leaf4410Box leaf4410Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi287ValidityFacts
    leaf4410LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4410CoverageChecked :
    coverageCheck (innerAD leaf4410Box) leaf4410InnerLog = true := by
  rfl'

private theorem leaf4410InnerLogValid :
    leaf4410InnerLog.Valid 8 (innerAD leaf4410Box) :=
  wideLogDataValid_of_cachedCheck endpoint85PositiveFacts
    endpoint283PositiveFacts.valid leaf4410CoverageChecked

private noncomputable def leaf4410InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814673/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4410InputLogOnePlusV_eq :
    leaf4410InputLogOnePlusV = outerEnclosure 24
      (leaf4410Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4410RoundedFacts : LeafRoundedFacts 8
    leaf4410Certificate.logOnePlusV leaf4410InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4410InputLogOnePlusV_eq }

private noncomputable def leaf4410Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi287InputQChi innerPair321Input
    leaf4410InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4410LowerChecked :
    lowerCheck 24 leaf4410Box leaf4410Inputs = true := by
  rfl'

private theorem leaf4410CoversExact : CoversExact 8
    leaf4410Box leaf4410Certificate leaf4410InnerLog leaf4410Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi287RoundedFacts
    innerPair321RoundedFacts leaf4410RoundedFacts (by rfl)

private theorem leaf4410FlatSound : Sound leaf4410Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4410CertificateValid
    leaf4410InnerLogValid leaf4410CoversExact leaf4410LowerChecked

private noncomputable def leaf4411Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (79/256), chiHi := (5/16) }

private noncomputable def leaf4411Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871279/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357608448) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1070071663/536870912) }, upper := { exponent := 1, mantissa := (129/128) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi288LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716331007/68715216896) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf4411InnerLog : WideLogData :=
  innerPair533Data

set_option maxRecDepth 1000000 in
private theorem leaf4411LocalValidity :
    LeafFacts leaf4411Box leaf4411Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4411Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357608448) }) = true
      norm_num [leaf4411Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4411CertificateValid :
    WideCertificateValid leaf4411Box leaf4411Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi288ValidityFacts
    leaf4411LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4411CoverageChecked :
    coverageCheck (innerAD leaf4411Box) leaf4411InnerLog = true := by
  rfl'

private theorem leaf4411InnerLogValid :
    leaf4411InnerLog.Valid 8 (innerAD leaf4411Box) :=
  wideLogDataValid_of_cachedCheck endpoint267PositiveFacts
    endpoint283PositiveFacts.valid leaf4411CoverageChecked

private noncomputable def leaf4411InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629353/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4411InputLogOnePlusV_eq :
    leaf4411InputLogOnePlusV = outerEnclosure 24
      (leaf4411Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4411RoundedFacts : LeafRoundedFacts 8
    leaf4411Certificate.logOnePlusV leaf4411InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4411InputLogOnePlusV_eq }

private noncomputable def leaf4411Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi288InputQChi innerPair533Input
    leaf4411InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4411LowerChecked :
    lowerCheck 24 leaf4411Box leaf4411Inputs = true := by
  rfl'

private theorem leaf4411CoversExact : CoversExact 8
    leaf4411Box leaf4411Certificate leaf4411InnerLog leaf4411Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi288RoundedFacts
    innerPair533RoundedFacts leaf4411RoundedFacts (by rfl)

private theorem leaf4411FlatSound : Sound leaf4411Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4411CertificateValid
    leaf4411InnerLogValid leaf4411CoversExact leaf4411LowerChecked

private noncomputable def component89Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (9/32), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component89Node0_sound : Sound component89Node0Box :=
  sound_of_literal_split component89Node0Box leaf4354Box leaf4355Box
    .chi (73/256) (by rfl) (by rfl)
    leaf4354FlatSound leaf4355FlatSound

private noncomputable def component89Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (9/32), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component89Node1_sound : Sound component89Node1Box :=
  sound_of_literal_split component89Node1Box leaf4356Box leaf4357Box
    .chi (73/256) (by rfl) (by rfl)
    leaf4356FlatSound leaf4357FlatSound

private noncomputable def component89Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (9/32), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component89Node2_sound : Sound component89Node2Box :=
  sound_of_literal_split component89Node2Box component89Node0Box component89Node1Box
    .k (97/32) (by rfl) (by rfl)
    component89Node0_sound component89Node1_sound

private noncomputable def component89Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (37/128), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component89Node3_sound : Sound component89Node3Box :=
  sound_of_literal_split component89Node3Box leaf4359Box leaf4360Box
    .chi (75/256) (by rfl) (by rfl)
    leaf4359FlatSound leaf4360FlatSound

private noncomputable def component89Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (37/128), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component89Node4_sound : Sound component89Node4Box :=
  sound_of_literal_split component89Node4Box leaf4358Box component89Node3Box
    .k (97/32) (by rfl) (by rfl)
    leaf4358FlatSound component89Node3_sound

private noncomputable def component89Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (9/32), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component89Node5_sound : Sound component89Node5Box :=
  sound_of_literal_split component89Node5Box component89Node2Box component89Node4Box
    .chi (37/128) (by rfl) (by rfl)
    component89Node2_sound component89Node4_sound

private noncomputable def component89Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (9/32), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component89Node6_sound : Sound component89Node6Box :=
  sound_of_literal_split component89Node6Box leaf4361Box leaf4362Box
    .chi (73/256) (by rfl) (by rfl)
    leaf4361FlatSound leaf4362FlatSound

private noncomputable def component89Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (9/32), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component89Node7_sound : Sound component89Node7Box :=
  sound_of_literal_split component89Node7Box leaf4363Box leaf4364Box
    .chi (73/256) (by rfl) (by rfl)
    leaf4363FlatSound leaf4364FlatSound

private noncomputable def component89Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (9/32), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component89Node8_sound : Sound component89Node8Box :=
  sound_of_literal_split component89Node8Box component89Node6Box component89Node7Box
    .k (99/32) (by rfl) (by rfl)
    component89Node6_sound component89Node7_sound

private noncomputable def component89Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (37/128), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component89Node9_sound : Sound component89Node9Box :=
  sound_of_literal_split component89Node9Box leaf4365Box leaf4366Box
    .chi (75/256) (by rfl) (by rfl)
    leaf4365FlatSound leaf4366FlatSound

private noncomputable def component89Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (37/128), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component89Node10_sound : Sound component89Node10Box :=
  sound_of_literal_split component89Node10Box leaf4367Box leaf4368Box
    .chi (75/256) (by rfl) (by rfl)
    leaf4367FlatSound leaf4368FlatSound

private noncomputable def component89Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (37/128), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component89Node11_sound : Sound component89Node11Box :=
  sound_of_literal_split component89Node11Box component89Node9Box component89Node10Box
    .k (99/32) (by rfl) (by rfl)
    component89Node9_sound component89Node10_sound

private noncomputable def component89Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (9/32), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component89Node12_sound : Sound component89Node12Box :=
  sound_of_literal_split component89Node12Box component89Node8Box component89Node11Box
    .chi (37/128) (by rfl) (by rfl)
    component89Node8_sound component89Node11_sound

private noncomputable def component89Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (9/32), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component89Node13_sound : Sound component89Node13Box :=
  sound_of_literal_split component89Node13Box component89Node5Box component89Node12Box
    .k (49/16) (by rfl) (by rfl)
    component89Node5_sound component89Node12_sound

private noncomputable def component89Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (19/64), chiHi := (39/128) }

set_option maxRecDepth 1000000 in
private theorem component89Node14_sound : Sound component89Node14Box :=
  sound_of_literal_split component89Node14Box leaf4369Box leaf4370Box
    .k (97/32) (by rfl) (by rfl)
    leaf4369FlatSound leaf4370FlatSound

private noncomputable def component89Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (39/128), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component89Node15_sound : Sound component89Node15Box :=
  sound_of_literal_split component89Node15Box leaf4371Box leaf4372Box
    .k (97/32) (by rfl) (by rfl)
    leaf4371FlatSound leaf4372FlatSound

private noncomputable def component89Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (19/64), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component89Node16_sound : Sound component89Node16Box :=
  sound_of_literal_split component89Node16Box component89Node14Box component89Node15Box
    .chi (39/128) (by rfl) (by rfl)
    component89Node14_sound component89Node15_sound

private noncomputable def component89Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (19/64), chiHi := (39/128) }

set_option maxRecDepth 1000000 in
private theorem component89Node17_sound : Sound component89Node17Box :=
  sound_of_literal_split component89Node17Box leaf4373Box leaf4374Box
    .chi (77/256) (by rfl) (by rfl)
    leaf4373FlatSound leaf4374FlatSound

private noncomputable def component89Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (19/64), chiHi := (39/128) }

set_option maxRecDepth 1000000 in
private theorem component89Node18_sound : Sound component89Node18Box :=
  sound_of_literal_split component89Node18Box leaf4375Box leaf4376Box
    .chi (77/256) (by rfl) (by rfl)
    leaf4375FlatSound leaf4376FlatSound

private noncomputable def component89Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (19/64), chiHi := (39/128) }

set_option maxRecDepth 1000000 in
private theorem component89Node19_sound : Sound component89Node19Box :=
  sound_of_literal_split component89Node19Box component89Node17Box component89Node18Box
    .k (99/32) (by rfl) (by rfl)
    component89Node17_sound component89Node18_sound

private noncomputable def component89Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (39/128), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component89Node20_sound : Sound component89Node20Box :=
  sound_of_literal_split component89Node20Box leaf4378Box leaf4379Box
    .chi (79/256) (by rfl) (by rfl)
    leaf4378FlatSound leaf4379FlatSound

private noncomputable def component89Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (39/128), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component89Node21_sound : Sound component89Node21Box :=
  sound_of_literal_split component89Node21Box leaf4377Box component89Node20Box
    .k (99/32) (by rfl) (by rfl)
    leaf4377FlatSound component89Node20_sound

private noncomputable def component89Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (19/64), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component89Node22_sound : Sound component89Node22Box :=
  sound_of_literal_split component89Node22Box component89Node19Box component89Node21Box
    .chi (39/128) (by rfl) (by rfl)
    component89Node19_sound component89Node21_sound

private noncomputable def component89Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (19/64), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component89Node23_sound : Sound component89Node23Box :=
  sound_of_literal_split component89Node23Box component89Node16Box component89Node22Box
    .k (49/16) (by rfl) (by rfl)
    component89Node16_sound component89Node22_sound

private noncomputable def component89Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (9/32), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component89Node24_sound : Sound component89Node24Box :=
  sound_of_literal_split component89Node24Box component89Node13Box component89Node23Box
    .chi (19/64) (by rfl) (by rfl)
    component89Node13_sound component89Node23_sound

private noncomputable def component89Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (9/32), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component89Node25_sound : Sound component89Node25Box :=
  sound_of_literal_split component89Node25Box leaf4380Box leaf4381Box
    .chi (73/256) (by rfl) (by rfl)
    leaf4380FlatSound leaf4381FlatSound

private noncomputable def component89Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (9/32), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component89Node26_sound : Sound component89Node26Box :=
  sound_of_literal_split component89Node26Box leaf4382Box leaf4383Box
    .chi (73/256) (by rfl) (by rfl)
    leaf4382FlatSound leaf4383FlatSound

private noncomputable def component89Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (9/32), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component89Node27_sound : Sound component89Node27Box :=
  sound_of_literal_split component89Node27Box component89Node25Box component89Node26Box
    .k (101/32) (by rfl) (by rfl)
    component89Node25_sound component89Node26_sound

private noncomputable def component89Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (37/128), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component89Node28_sound : Sound component89Node28Box :=
  sound_of_literal_split component89Node28Box leaf4384Box leaf4385Box
    .chi (75/256) (by rfl) (by rfl)
    leaf4384FlatSound leaf4385FlatSound

private noncomputable def component89Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (37/128), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component89Node29_sound : Sound component89Node29Box :=
  sound_of_literal_split component89Node29Box leaf4386Box leaf4387Box
    .chi (75/256) (by rfl) (by rfl)
    leaf4386FlatSound leaf4387FlatSound

private noncomputable def component89Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (37/128), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component89Node30_sound : Sound component89Node30Box :=
  sound_of_literal_split component89Node30Box component89Node28Box component89Node29Box
    .k (101/32) (by rfl) (by rfl)
    component89Node28_sound component89Node29_sound

private noncomputable def component89Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (9/32), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component89Node31_sound : Sound component89Node31Box :=
  sound_of_literal_split component89Node31Box component89Node27Box component89Node30Box
    .chi (37/128) (by rfl) (by rfl)
    component89Node27_sound component89Node30_sound

private noncomputable def component89Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (9/32), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component89Node32_sound : Sound component89Node32Box :=
  sound_of_literal_split component89Node32Box leaf4388Box leaf4389Box
    .chi (73/256) (by rfl) (by rfl)
    leaf4388FlatSound leaf4389FlatSound

private noncomputable def component89Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (9/32), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component89Node33_sound : Sound component89Node33Box :=
  sound_of_literal_split component89Node33Box leaf4390Box leaf4391Box
    .chi (73/256) (by rfl) (by rfl)
    leaf4390FlatSound leaf4391FlatSound

private noncomputable def component89Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (9/32), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component89Node34_sound : Sound component89Node34Box :=
  sound_of_literal_split component89Node34Box component89Node32Box component89Node33Box
    .k (103/32) (by rfl) (by rfl)
    component89Node32_sound component89Node33_sound

private noncomputable def component89Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (37/128), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component89Node35_sound : Sound component89Node35Box :=
  sound_of_literal_split component89Node35Box leaf4392Box leaf4393Box
    .chi (75/256) (by rfl) (by rfl)
    leaf4392FlatSound leaf4393FlatSound

private noncomputable def component89Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (37/128), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component89Node36_sound : Sound component89Node36Box :=
  sound_of_literal_split component89Node36Box leaf4394Box leaf4395Box
    .chi (75/256) (by rfl) (by rfl)
    leaf4394FlatSound leaf4395FlatSound

private noncomputable def component89Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (37/128), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component89Node37_sound : Sound component89Node37Box :=
  sound_of_literal_split component89Node37Box component89Node35Box component89Node36Box
    .k (103/32) (by rfl) (by rfl)
    component89Node35_sound component89Node36_sound

private noncomputable def component89Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (9/32), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component89Node38_sound : Sound component89Node38Box :=
  sound_of_literal_split component89Node38Box component89Node34Box component89Node37Box
    .chi (37/128) (by rfl) (by rfl)
    component89Node34_sound component89Node37_sound

private noncomputable def component89Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (9/32), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component89Node39_sound : Sound component89Node39Box :=
  sound_of_literal_split component89Node39Box component89Node31Box component89Node38Box
    .k (51/16) (by rfl) (by rfl)
    component89Node31_sound component89Node38_sound

private noncomputable def component89Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (19/64), chiHi := (39/128) }

set_option maxRecDepth 1000000 in
private theorem component89Node40_sound : Sound component89Node40Box :=
  sound_of_literal_split component89Node40Box leaf4396Box leaf4397Box
    .chi (77/256) (by rfl) (by rfl)
    leaf4396FlatSound leaf4397FlatSound

private noncomputable def component89Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (19/64), chiHi := (39/128) }

set_option maxRecDepth 1000000 in
private theorem component89Node41_sound : Sound component89Node41Box :=
  sound_of_literal_split component89Node41Box leaf4398Box leaf4399Box
    .chi (77/256) (by rfl) (by rfl)
    leaf4398FlatSound leaf4399FlatSound

private noncomputable def component89Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (19/64), chiHi := (39/128) }

set_option maxRecDepth 1000000 in
private theorem component89Node42_sound : Sound component89Node42Box :=
  sound_of_literal_split component89Node42Box component89Node40Box component89Node41Box
    .k (101/32) (by rfl) (by rfl)
    component89Node40_sound component89Node41_sound

private noncomputable def component89Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (39/128), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component89Node43_sound : Sound component89Node43Box :=
  sound_of_literal_split component89Node43Box leaf4400Box leaf4401Box
    .chi (79/256) (by rfl) (by rfl)
    leaf4400FlatSound leaf4401FlatSound

private noncomputable def component89Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (39/128), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component89Node44_sound : Sound component89Node44Box :=
  sound_of_literal_split component89Node44Box leaf4402Box leaf4403Box
    .chi (79/256) (by rfl) (by rfl)
    leaf4402FlatSound leaf4403FlatSound

private noncomputable def component89Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (39/128), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component89Node45_sound : Sound component89Node45Box :=
  sound_of_literal_split component89Node45Box component89Node43Box component89Node44Box
    .k (101/32) (by rfl) (by rfl)
    component89Node43_sound component89Node44_sound

private noncomputable def component89Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (19/64), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component89Node46_sound : Sound component89Node46Box :=
  sound_of_literal_split component89Node46Box component89Node42Box component89Node45Box
    .chi (39/128) (by rfl) (by rfl)
    component89Node42_sound component89Node45_sound

private noncomputable def component89Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (19/64), chiHi := (39/128) }

set_option maxRecDepth 1000000 in
private theorem component89Node47_sound : Sound component89Node47Box :=
  sound_of_literal_split component89Node47Box leaf4404Box leaf4405Box
    .chi (77/256) (by rfl) (by rfl)
    leaf4404FlatSound leaf4405FlatSound

private noncomputable def component89Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (19/64), chiHi := (39/128) }

set_option maxRecDepth 1000000 in
private theorem component89Node48_sound : Sound component89Node48Box :=
  sound_of_literal_split component89Node48Box leaf4406Box leaf4407Box
    .chi (77/256) (by rfl) (by rfl)
    leaf4406FlatSound leaf4407FlatSound

private noncomputable def component89Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (19/64), chiHi := (39/128) }

set_option maxRecDepth 1000000 in
private theorem component89Node49_sound : Sound component89Node49Box :=
  sound_of_literal_split component89Node49Box component89Node47Box component89Node48Box
    .k (103/32) (by rfl) (by rfl)
    component89Node47_sound component89Node48_sound

private noncomputable def component89Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (39/128), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component89Node50_sound : Sound component89Node50Box :=
  sound_of_literal_split component89Node50Box leaf4408Box leaf4409Box
    .chi (79/256) (by rfl) (by rfl)
    leaf4408FlatSound leaf4409FlatSound

private noncomputable def component89Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (39/128), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component89Node51_sound : Sound component89Node51Box :=
  sound_of_literal_split component89Node51Box leaf4410Box leaf4411Box
    .chi (79/256) (by rfl) (by rfl)
    leaf4410FlatSound leaf4411FlatSound

private noncomputable def component89Node52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (39/128), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component89Node52_sound : Sound component89Node52Box :=
  sound_of_literal_split component89Node52Box component89Node50Box component89Node51Box
    .k (103/32) (by rfl) (by rfl)
    component89Node50_sound component89Node51_sound

private noncomputable def component89Node53Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (19/64), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component89Node53_sound : Sound component89Node53Box :=
  sound_of_literal_split component89Node53Box component89Node49Box component89Node52Box
    .chi (39/128) (by rfl) (by rfl)
    component89Node49_sound component89Node52_sound

private noncomputable def component89Node54Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (19/64), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component89Node54_sound : Sound component89Node54Box :=
  sound_of_literal_split component89Node54Box component89Node46Box component89Node53Box
    .k (51/16) (by rfl) (by rfl)
    component89Node46_sound component89Node53_sound

private noncomputable def component89Node55Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (9/32), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component89Node55_sound : Sound component89Node55Box :=
  sound_of_literal_split component89Node55Box component89Node39Box component89Node54Box
    .chi (19/64) (by rfl) (by rfl)
    component89Node39_sound component89Node54_sound

noncomputable def component89Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (13/4), chiLo := (9/32), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
theorem component89_sound : Sound component89Box :=
  sound_of_literal_split component89Box component89Node24Box component89Node55Box
    .k (25/8) (by rfl) (by rfl)
    component89Node24_sound component89Node55_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
