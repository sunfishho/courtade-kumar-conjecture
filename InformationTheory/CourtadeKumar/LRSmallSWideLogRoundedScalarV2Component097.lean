import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch5
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch5
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

private noncomputable def leaf4699Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (11/32), chiHi := (45/128) }

private noncomputable def leaf4699Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435755/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357319168) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (568276823/536870912) }, upper := { exponent := 1, mantissa := (8821/8192) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi253LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716041727/68714638336) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf4699InnerLog : WideLogData :=
  innerPair614Data

set_option maxRecDepth 1000000 in
private theorem leaf4699LocalValidity :
    LeafFacts leaf4699Box leaf4699Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4699Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357319168) }) = true
      norm_num [leaf4699Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4699CertificateValid :
    WideCertificateValid leaf4699Box leaf4699Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi253ValidityFacts
    leaf4699LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4699CoverageChecked :
    coverageCheck (innerAD leaf4699Box) leaf4699InnerLog = true := by
  rfl'

private theorem leaf4699InnerLogValid :
    leaf4699InnerLog.Valid 8 (innerAD leaf4699Box) :=
  wideLogDataValid_of_cachedCheck endpoint338PositiveFacts
    endpoint339PositiveFacts.valid leaf4699CoverageChecked

private noncomputable def leaf4699InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629423/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4699InputLogOnePlusV_eq :
    leaf4699InputLogOnePlusV = outerEnclosure 24
      (leaf4699Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4699RoundedFacts : LeafRoundedFacts 8
    leaf4699Certificate.logOnePlusV leaf4699InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4699InputLogOnePlusV_eq }

private noncomputable def leaf4699Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi253InputQChi innerPair614Input
    leaf4699InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4699LowerChecked :
    lowerCheck 24 leaf4699Box leaf4699Inputs = true := by
  rfl'

private theorem leaf4699CoversExact : CoversExact 8
    leaf4699Box leaf4699Certificate leaf4699InnerLog leaf4699Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi253RoundedFacts
    innerPair614RoundedFacts leaf4699RoundedFacts (by rfl)

private theorem leaf4699FlatSound : Sound leaf4699Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4699CertificateValid
    leaf4699InnerLogValid leaf4699CoversExact leaf4699LowerChecked

private noncomputable def leaf4700Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (11/32), chiHi := (89/256) }

private noncomputable def leaf4700Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871301/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357323264) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1142353437/1073741824) }, upper := { exponent := 1, mantissa := (8813/8192) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi297LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716045823/68714646528) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf4700InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf4700LocalValidity :
    LeafFacts leaf4700Box leaf4700Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4700Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357323264) }) = true
      norm_num [leaf4700Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4700CertificateValid :
    WideCertificateValid leaf4700Box leaf4700Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi297ValidityFacts
    leaf4700LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4700CoverageChecked :
    coverageCheck (innerAD leaf4700Box) leaf4700InnerLog = true := by
  rfl'

private theorem leaf4700InnerLogValid :
    leaf4700InnerLog.Valid 8 (innerAD leaf4700Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf4700CoverageChecked

private noncomputable def leaf4700InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814711/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4700InputLogOnePlusV_eq :
    leaf4700InputLogOnePlusV = outerEnclosure 24
      (leaf4700Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4700RoundedFacts : LeafRoundedFacts 8
    leaf4700Certificate.logOnePlusV leaf4700InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4700InputLogOnePlusV_eq }

private noncomputable def leaf4700Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi297InputQChi innerPair249Input
    leaf4700InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4700LowerChecked :
    lowerCheck 24 leaf4700Box leaf4700Inputs = true := by
  rfl'

private theorem leaf4700CoversExact : CoversExact 8
    leaf4700Box leaf4700Certificate leaf4700InnerLog leaf4700Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi297RoundedFacts
    innerPair249RoundedFacts leaf4700RoundedFacts (by rfl)

private theorem leaf4700FlatSound : Sound leaf4700Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4700CertificateValid
    leaf4700InnerLogValid leaf4700CoversExact leaf4700LowerChecked

private noncomputable def leaf4701Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (89/256), chiHi := (45/128) }

private noncomputable def leaf4701Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871303/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357296128) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1149234295/1073741824) }, upper := { exponent := 1, mantissa := (4433/4096) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi298LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716018687/68714592256) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf4701InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf4701LocalValidity :
    LeafFacts leaf4701Box leaf4701Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4701Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357296128) }) = true
      norm_num [leaf4701Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4701CertificateValid :
    WideCertificateValid leaf4701Box leaf4701Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi298ValidityFacts
    leaf4701LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4701CoverageChecked :
    coverageCheck (innerAD leaf4701Box) leaf4701InnerLog = true := by
  rfl'

private theorem leaf4701InnerLogValid :
    leaf4701InnerLog.Valid 8 (innerAD leaf4701Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf4701CoverageChecked

private noncomputable def leaf4701InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629429/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4701InputLogOnePlusV_eq :
    leaf4701InputLogOnePlusV = outerEnclosure 24
      (leaf4701Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4701RoundedFacts : LeafRoundedFacts 8
    leaf4701Certificate.logOnePlusV leaf4701InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4701InputLogOnePlusV_eq }

private noncomputable def leaf4701Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi298InputQChi innerPair249Input
    leaf4701InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4701LowerChecked :
    lowerCheck 24 leaf4701Box leaf4701Inputs = true := by
  rfl'

private theorem leaf4701CoversExact : CoversExact 8
    leaf4701Box leaf4701Certificate leaf4701InnerLog leaf4701Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi298RoundedFacts
    innerPair249RoundedFacts leaf4701RoundedFacts (by rfl)

private theorem leaf4701FlatSound : Sound leaf4701Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4701CertificateValid
    leaf4701InnerLogValid leaf4701CoversExact leaf4701LowerChecked

private noncomputable def leaf4702Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (45/128), chiHi := (23/64) }

private noncomputable def leaf4702Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435757/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357265408) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (575092149/536870912) }, upper := { exponent := 1, mantissa := (4463/4096) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi254LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715987967/68714530816) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf4702InnerLog : WideLogData :=
  innerPair555Data

set_option maxRecDepth 1000000 in
private theorem leaf4702LocalValidity :
    LeafFacts leaf4702Box leaf4702Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4702Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357265408) }) = true
      norm_num [leaf4702Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4702CertificateValid :
    WideCertificateValid leaf4702Box leaf4702Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi254ValidityFacts
    leaf4702LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4702CoverageChecked :
    coverageCheck (innerAD leaf4702Box) leaf4702InnerLog = true := by
  rfl'

private theorem leaf4702InnerLogValid :
    leaf4702InnerLog.Valid 8 (innerAD leaf4702Box) :=
  wideLogDataValid_of_cachedCheck endpoint289PositiveFacts
    endpoint340PositiveFacts.valid leaf4702CoverageChecked

private noncomputable def leaf4702InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629437/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4702InputLogOnePlusV_eq :
    leaf4702InputLogOnePlusV = outerEnclosure 24
      (leaf4702Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4702RoundedFacts : LeafRoundedFacts 8
    leaf4702Certificate.logOnePlusV leaf4702InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4702InputLogOnePlusV_eq }

private noncomputable def leaf4702Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi254InputQChi innerPair555Input
    leaf4702InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4702LowerChecked :
    lowerCheck 24 leaf4702Box leaf4702Inputs = true := by
  rfl'

private theorem leaf4702CoversExact : CoversExact 8
    leaf4702Box leaf4702Certificate leaf4702InnerLog leaf4702Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi254RoundedFacts
    innerPair555RoundedFacts leaf4702RoundedFacts (by rfl)

private theorem leaf4702FlatSound : Sound leaf4702Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4702CertificateValid
    leaf4702InnerLogValid leaf4702CoversExact leaf4702LowerChecked

private noncomputable def leaf4703Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (45/128), chiHi := (23/64) }

private noncomputable def leaf4703Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435759/268435456) }, vSqrt := { lower := (65529/65536), upper := (4908388937/4908177408) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (578041087/536870912) }, upper := { exponent := 1, mantissa := (2243/2048) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi254LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (9816566345/9816354816) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf4703InnerLog : WideLogData :=
  innerPair615Data

set_option maxRecDepth 1000000 in
private theorem leaf4703LocalValidity :
    LeafFacts leaf4703Box leaf4703Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4703Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4908388937/4908177408) }) = true
      norm_num [leaf4703Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4703CertificateValid :
    WideCertificateValid leaf4703Box leaf4703Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi254ValidityFacts
    leaf4703LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4703CoverageChecked :
    coverageCheck (innerAD leaf4703Box) leaf4703InnerLog = true := by
  rfl'

private theorem leaf4703InnerLogValid :
    leaf4703InnerLog.Valid 8 (innerAD leaf4703Box) :=
  wideLogDataValid_of_cachedCheck endpoint341PositiveFacts
    endpoint342PositiveFacts.valid leaf4703CoverageChecked

private noncomputable def leaf4703InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814721/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4703InputLogOnePlusV_eq :
    leaf4703InputLogOnePlusV = outerEnclosure 24
      (leaf4703Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4703RoundedFacts : LeafRoundedFacts 8
    leaf4703Certificate.logOnePlusV leaf4703InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4703InputLogOnePlusV_eq }

private noncomputable def leaf4703Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi254InputQChi innerPair615Input
    leaf4703InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4703LowerChecked :
    lowerCheck 24 leaf4703Box leaf4703Inputs = true := by
  rfl'

private theorem leaf4703CoversExact : CoversExact 8
    leaf4703Box leaf4703Certificate leaf4703InnerLog leaf4703Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi254RoundedFacts
    innerPair615RoundedFacts leaf4703RoundedFacts (by rfl)

private theorem leaf4703FlatSound : Sound leaf4703Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4703CertificateValid
    leaf4703InnerLogValid leaf4703CoversExact leaf4703LowerChecked

private noncomputable def leaf4704Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (11/32), chiHi := (89/256) }

private noncomputable def leaf4704Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871303/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357300480) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1148120251/1073741824) }, upper := { exponent := 1, mantissa := (17715/16384) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi297LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716023039/68714600960) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf4704InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf4704LocalValidity :
    LeafFacts leaf4704Box leaf4704Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4704Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357300480) }) = true
      norm_num [leaf4704Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4704CertificateValid :
    WideCertificateValid leaf4704Box leaf4704Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi297ValidityFacts
    leaf4704LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4704CoverageChecked :
    coverageCheck (innerAD leaf4704Box) leaf4704InnerLog = true := by
  rfl'

private theorem leaf4704InnerLogValid :
    leaf4704InnerLog.Valid 8 (innerAD leaf4704Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf4704CoverageChecked

private noncomputable def leaf4704InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907357/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4704InputLogOnePlusV_eq :
    leaf4704InputLogOnePlusV = outerEnclosure 24
      (leaf4704Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4704RoundedFacts : LeafRoundedFacts 8
    leaf4704Certificate.logOnePlusV leaf4704InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4704InputLogOnePlusV_eq }

private noncomputable def leaf4704Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi297InputQChi innerPair249Input
    leaf4704InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4704LowerChecked :
    lowerCheck 24 leaf4704Box leaf4704Inputs = true := by
  rfl'

private theorem leaf4704CoversExact : CoversExact 8
    leaf4704Box leaf4704Certificate leaf4704InnerLog leaf4704Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi297RoundedFacts
    innerPair249RoundedFacts leaf4704RoundedFacts (by rfl)

private theorem leaf4704FlatSound : Sound leaf4704Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4704CertificateValid
    leaf4704InnerLogValid leaf4704CoversExact leaf4704LowerChecked

private noncomputable def leaf4705Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (89/256), chiHi := (45/128) }

private noncomputable def leaf4705Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871305/536870912) }, vSqrt := { lower := (65529/65536), upper := (2021101327/2021016064) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1155066641/1073741824) }, upper := { exponent := 1, mantissa := (8911/8192) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi298LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (4042117391/4042032128) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf4705InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf4705LocalValidity :
    LeafFacts leaf4705Box leaf4705Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4705Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (2021101327/2021016064) }) = true
      norm_num [leaf4705Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4705CertificateValid :
    WideCertificateValid leaf4705Box leaf4705Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi298ValidityFacts
    leaf4705LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4705CoverageChecked :
    coverageCheck (innerAD leaf4705Box) leaf4705InnerLog = true := by
  rfl'

private theorem leaf4705InnerLogValid :
    leaf4705InnerLog.Valid 8 (innerAD leaf4705Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf4705CoverageChecked

private noncomputable def leaf4705InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629435/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4705InputLogOnePlusV_eq :
    leaf4705InputLogOnePlusV = outerEnclosure 24
      (leaf4705Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4705RoundedFacts : LeafRoundedFacts 8
    leaf4705Certificate.logOnePlusV leaf4705InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4705InputLogOnePlusV_eq }

private noncomputable def leaf4705Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi298InputQChi innerPair249Input
    leaf4705InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4705LowerChecked :
    lowerCheck 24 leaf4705Box leaf4705Inputs = true := by
  rfl'

private theorem leaf4705CoversExact : CoversExact 8
    leaf4705Box leaf4705Certificate leaf4705InnerLog leaf4705Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi298RoundedFacts
    innerPair249RoundedFacts leaf4705RoundedFacts (by rfl)

private theorem leaf4705FlatSound : Sound leaf4705Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4705CertificateValid
    leaf4705InnerLogValid leaf4705CoversExact leaf4705LowerChecked

private noncomputable def leaf4706Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (11/32), chiHi := (89/256) }

private noncomputable def leaf4706Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871305/536870912) }, vSqrt := { lower := (65529/65536), upper := (4908388937/4908182528) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1153887065/1073741824) }, upper := { exponent := 1, mantissa := (4451/4096) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi297LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (9816571465/9816365056) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf4706InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf4706LocalValidity :
    LeafFacts leaf4706Box leaf4706Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4706Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4908388937/4908182528) }) = true
      norm_num [leaf4706Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4706CertificateValid :
    WideCertificateValid leaf4706Box leaf4706Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi297ValidityFacts
    leaf4706LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4706CoverageChecked :
    coverageCheck (innerAD leaf4706Box) leaf4706InnerLog = true := by
  rfl'

private theorem leaf4706InnerLogValid :
    leaf4706InnerLog.Valid 8 (innerAD leaf4706Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf4706CoverageChecked

private noncomputable def leaf4706InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814717/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4706InputLogOnePlusV_eq :
    leaf4706InputLogOnePlusV = outerEnclosure 24
      (leaf4706Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4706RoundedFacts : LeafRoundedFacts 8
    leaf4706Certificate.logOnePlusV leaf4706InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4706InputLogOnePlusV_eq }

private noncomputable def leaf4706Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi297InputQChi innerPair249Input
    leaf4706InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4706LowerChecked :
    lowerCheck 24 leaf4706Box leaf4706Inputs = true := by
  rfl'

private theorem leaf4706CoversExact : CoversExact 8
    leaf4706Box leaf4706Certificate leaf4706InnerLog leaf4706Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi297RoundedFacts
    innerPair249RoundedFacts leaf4706RoundedFacts (by rfl)

private theorem leaf4706FlatSound : Sound leaf4706Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4706CertificateValid
    leaf4706InnerLogValid leaf4706CoversExact leaf4706LowerChecked

private noncomputable def leaf4707Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (89/256), chiHi := (45/128) }

private noncomputable def leaf4707Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871307/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357250048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1160898987/1073741824) }, upper := { exponent := 1, mantissa := (2239/2048) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi298LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715972607/68714500096) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf4707InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf4707LocalValidity :
    LeafFacts leaf4707Box leaf4707Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4707Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357250048) }) = true
      norm_num [leaf4707Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4707CertificateValid :
    WideCertificateValid leaf4707Box leaf4707Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi298ValidityFacts
    leaf4707LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4707CoverageChecked :
    coverageCheck (innerAD leaf4707Box) leaf4707InnerLog = true := by
  rfl'

private theorem leaf4707InnerLogValid :
    leaf4707InnerLog.Valid 8 (innerAD leaf4707Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf4707CoverageChecked

private noncomputable def leaf4707InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (90855/131072) }

set_option maxRecDepth 1000000 in
private theorem leaf4707InputLogOnePlusV_eq :
    leaf4707InputLogOnePlusV = outerEnclosure 24
      (leaf4707Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4707RoundedFacts : LeafRoundedFacts 8
    leaf4707Certificate.logOnePlusV leaf4707InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4707InputLogOnePlusV_eq }

private noncomputable def leaf4707Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi298InputQChi innerPair249Input
    leaf4707InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4707LowerChecked :
    lowerCheck 24 leaf4707Box leaf4707Inputs = true := by
  rfl'

private theorem leaf4707CoversExact : CoversExact 8
    leaf4707Box leaf4707Certificate leaf4707InnerLog leaf4707Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi298RoundedFacts
    innerPair249RoundedFacts leaf4707RoundedFacts (by rfl)

private theorem leaf4707FlatSound : Sound leaf4707Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4707CertificateValid
    leaf4707InnerLogValid leaf4707CoversExact leaf4707LowerChecked

private noncomputable def leaf4708Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (45/128), chiHi := (23/64) }

private noncomputable def leaf4708Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435761/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357218304) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (580990025/536870912) }, upper := { exponent := 1, mantissa := (4509/4096) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi254LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715940863/68714436608) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf4708InnerLog : WideLogData :=
  innerPair617Data

set_option maxRecDepth 1000000 in
private theorem leaf4708LocalValidity :
    LeafFacts leaf4708Box leaf4708Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4708Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357218304) }) = true
      norm_num [leaf4708Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4708CertificateValid :
    WideCertificateValid leaf4708Box leaf4708Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi254ValidityFacts
    leaf4708LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4708CoverageChecked :
    coverageCheck (innerAD leaf4708Box) leaf4708InnerLog = true := by
  rfl'

private theorem leaf4708InnerLogValid :
    leaf4708InnerLog.Valid 8 (innerAD leaf4708Box) :=
  wideLogDataValid_of_cachedCheck endpoint343PositiveFacts
    endpoint344PositiveFacts.valid leaf4708CoverageChecked

private noncomputable def leaf4708InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453681/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf4708InputLogOnePlusV_eq :
    leaf4708InputLogOnePlusV = outerEnclosure 24
      (leaf4708Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4708RoundedFacts : LeafRoundedFacts 8
    leaf4708Certificate.logOnePlusV leaf4708InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4708InputLogOnePlusV_eq }

private noncomputable def leaf4708Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi254InputQChi innerPair617Input
    leaf4708InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4708LowerChecked :
    lowerCheck 24 leaf4708Box leaf4708Inputs = true := by
  rfl'

private theorem leaf4708CoversExact : CoversExact 8
    leaf4708Box leaf4708Certificate leaf4708InnerLog leaf4708Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi254RoundedFacts
    innerPair617RoundedFacts leaf4708RoundedFacts (by rfl)

private theorem leaf4708FlatSound : Sound leaf4708Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4708CertificateValid
    leaf4708InnerLogValid leaf4708CoversExact leaf4708LowerChecked

private noncomputable def leaf4709Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (45/128), chiHi := (91/256) }

private noncomputable def leaf4709Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871309/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357222400) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1167910909/1073741824) }, upper := { exponent := 1, mantissa := (4505/4096) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi299LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715944959/68714444800) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf4709InnerLog : WideLogData :=
  innerPair250Data

set_option maxRecDepth 1000000 in
private theorem leaf4709LocalValidity :
    LeafFacts leaf4709Box leaf4709Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4709Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357222400) }) = true
      norm_num [leaf4709Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4709CertificateValid :
    WideCertificateValid leaf4709Box leaf4709Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi299ValidityFacts
    leaf4709LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4709CoverageChecked :
    coverageCheck (innerAD leaf4709Box) leaf4709InnerLog = true := by
  rfl'

private theorem leaf4709InnerLogValid :
    leaf4709InnerLog.Valid 8 (innerAD leaf4709Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint75PositiveFacts.valid leaf4709CoverageChecked

private noncomputable def leaf4709InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629447/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4709InputLogOnePlusV_eq :
    leaf4709InputLogOnePlusV = outerEnclosure 24
      (leaf4709Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4709RoundedFacts : LeafRoundedFacts 8
    leaf4709Certificate.logOnePlusV leaf4709InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4709InputLogOnePlusV_eq }

private noncomputable def leaf4709Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi299InputQChi innerPair250Input
    leaf4709InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4709LowerChecked :
    lowerCheck 24 leaf4709Box leaf4709Inputs = true := by
  rfl'

private theorem leaf4709CoversExact : CoversExact 8
    leaf4709Box leaf4709Certificate leaf4709InnerLog leaf4709Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi299RoundedFacts
    innerPair250RoundedFacts leaf4709RoundedFacts (by rfl)

private theorem leaf4709FlatSound : Sound leaf4709Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4709CertificateValid
    leaf4709InnerLogValid leaf4709CoversExact leaf4709LowerChecked

private noncomputable def leaf4710Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (91/256), chiHi := (23/64) }

private noncomputable def leaf4710Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871311/536870912) }, vSqrt := { lower := (65529/65536), upper := (2021101327/2021011456) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1174922831/1073741824) }, upper := { exponent := 1, mantissa := (1133/1024) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi300LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (4042112783/4042022912) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf4710InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf4710LocalValidity :
    LeafFacts leaf4710Box leaf4710Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4710Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (2021101327/2021011456) }) = true
      norm_num [leaf4710Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4710CertificateValid :
    WideCertificateValid leaf4710Box leaf4710Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi300ValidityFacts
    leaf4710LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4710CoverageChecked :
    coverageCheck (innerAD leaf4710Box) leaf4710InnerLog = true := by
  rfl'

private theorem leaf4710InnerLogValid :
    leaf4710InnerLog.Valid 8 (innerAD leaf4710Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf4710CoverageChecked

private noncomputable def leaf4710InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814727/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4710InputLogOnePlusV_eq :
    leaf4710InputLogOnePlusV = outerEnclosure 24
      (leaf4710Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4710RoundedFacts : LeafRoundedFacts 8
    leaf4710Certificate.logOnePlusV leaf4710InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4710InputLogOnePlusV_eq }

private noncomputable def leaf4710Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi300InputQChi innerPair256Input
    leaf4710InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4710LowerChecked :
    lowerCheck 24 leaf4710Box leaf4710Inputs = true := by
  rfl'

private theorem leaf4710CoversExact : CoversExact 8
    leaf4710Box leaf4710Certificate leaf4710InnerLog leaf4710Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi300RoundedFacts
    innerPair256RoundedFacts leaf4710RoundedFacts (by rfl)

private theorem leaf4710FlatSound : Sound leaf4710Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4710CertificateValid
    leaf4710InnerLogValid leaf4710CoversExact leaf4710LowerChecked

private noncomputable def leaf4711Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (23/64), chiHi := (47/128) }

private noncomputable def leaf4711Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435759/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357211648) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (581907475/536870912) }, upper := { exponent := 1, mantissa := (9031/8192) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi255LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715934207/68714423296) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf4711InnerLog : WideLogData :=
  innerPair619Data

set_option maxRecDepth 1000000 in
private theorem leaf4711LocalValidity :
    LeafFacts leaf4711Box leaf4711Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4711Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357211648) }) = true
      norm_num [leaf4711Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4711CertificateValid :
    WideCertificateValid leaf4711Box leaf4711Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi255ValidityFacts
    leaf4711LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4711CoverageChecked :
    coverageCheck (innerAD leaf4711Box) leaf4711InnerLog = true := by
  rfl'

private theorem leaf4711InnerLogValid :
    leaf4711InnerLog.Valid 8 (innerAD leaf4711Box) :=
  wideLogDataValid_of_cachedCheck endpoint345PositiveFacts
    endpoint346PositiveFacts.valid leaf4711CoverageChecked

private noncomputable def leaf4711InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814725/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4711InputLogOnePlusV_eq :
    leaf4711InputLogOnePlusV = outerEnclosure 24
      (leaf4711Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4711RoundedFacts : LeafRoundedFacts 8
    leaf4711Certificate.logOnePlusV leaf4711InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4711InputLogOnePlusV_eq }

private noncomputable def leaf4711Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi255InputQChi innerPair619Input
    leaf4711InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4711LowerChecked :
    lowerCheck 24 leaf4711Box leaf4711Inputs = true := by
  rfl'

private theorem leaf4711CoversExact : CoversExact 8
    leaf4711Box leaf4711Certificate leaf4711InnerLog leaf4711Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi255RoundedFacts
    innerPair619RoundedFacts leaf4711RoundedFacts (by rfl)

private theorem leaf4711FlatSound : Sound leaf4711Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4711CertificateValid
    leaf4711InnerLogValid leaf4711CoversExact leaf4711LowerChecked

private noncomputable def leaf4712Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (23/64), chiHi := (47/128) }

private noncomputable def leaf4712Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435761/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357187584) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (584921945/536870912) }, upper := { exponent := 1, mantissa := (4539/4096) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi255LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715910143/68714375168) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf4712InnerLog : WideLogData :=
  innerPair611Data

set_option maxRecDepth 1000000 in
private theorem leaf4712LocalValidity :
    LeafFacts leaf4712Box leaf4712Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4712Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357187584) }) = true
      norm_num [leaf4712Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4712CertificateValid :
    WideCertificateValid leaf4712Box leaf4712Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi255ValidityFacts
    leaf4712LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4712CoverageChecked :
    coverageCheck (innerAD leaf4712Box) leaf4712InnerLog = true := by
  rfl'

private theorem leaf4712InnerLogValid :
    leaf4712InnerLog.Valid 8 (innerAD leaf4712Box) :=
  wideLogDataValid_of_cachedCheck endpoint337PositiveFacts
    endpoint80PositiveFacts.valid leaf4712CoverageChecked

private noncomputable def leaf4712InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (726841/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf4712InputLogOnePlusV_eq :
    leaf4712InputLogOnePlusV = outerEnclosure 24
      (leaf4712Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4712RoundedFacts : LeafRoundedFacts 8
    leaf4712Certificate.logOnePlusV leaf4712InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4712InputLogOnePlusV_eq }

private noncomputable def leaf4712Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi255InputQChi innerPair611Input
    leaf4712InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4712LowerChecked :
    lowerCheck 24 leaf4712Box leaf4712Inputs = true := by
  rfl'

private theorem leaf4712CoversExact : CoversExact 8
    leaf4712Box leaf4712Certificate leaf4712InnerLog leaf4712Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi255RoundedFacts
    innerPair611RoundedFacts leaf4712RoundedFacts (by rfl)

private theorem leaf4712FlatSound : Sound leaf4712Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4712CertificateValid
    leaf4712InnerLogValid leaf4712CoversExact leaf4712LowerChecked

private noncomputable def leaf4713Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (47/128), chiHi := (3/8) }

private noncomputable def leaf4713Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435761/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357157888) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (588722801/536870912) }, upper := { exponent := 1, mantissa := (571/512) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi256LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715880447/68714315776) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf4713InnerLog : WideLogData :=
  innerPair262Data

set_option maxRecDepth 1000000 in
private theorem leaf4713LocalValidity :
    LeafFacts leaf4713Box leaf4713Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4713Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357157888) }) = true
      norm_num [leaf4713Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4713CertificateValid :
    WideCertificateValid leaf4713Box leaf4713Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi256ValidityFacts
    leaf4713LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4713CoverageChecked :
    coverageCheck (innerAD leaf4713Box) leaf4713InnerLog = true := by
  rfl'

private theorem leaf4713InnerLogValid :
    leaf4713InnerLog.Valid 8 (innerAD leaf4713Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint347PositiveFacts.valid leaf4713CoverageChecked

private noncomputable def leaf4713InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629463/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4713InputLogOnePlusV_eq :
    leaf4713InputLogOnePlusV = outerEnclosure 24
      (leaf4713Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4713RoundedFacts : LeafRoundedFacts 8
    leaf4713Certificate.logOnePlusV leaf4713InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4713InputLogOnePlusV_eq }

private noncomputable def leaf4713Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi256InputQChi innerPair262Input
    leaf4713InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4713LowerChecked :
    lowerCheck 24 leaf4713Box leaf4713Inputs = true := by
  rfl'

private theorem leaf4713CoversExact : CoversExact 8
    leaf4713Box leaf4713Certificate leaf4713InnerLog leaf4713Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi256RoundedFacts
    innerPair262RoundedFacts leaf4713RoundedFacts (by rfl)

private theorem leaf4713FlatSound : Sound leaf4713Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4713CertificateValid
    leaf4713InnerLogValid leaf4713CoversExact leaf4713LowerChecked

private noncomputable def leaf4714Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (47/128), chiHi := (3/8) }

private noncomputable def leaf4714Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435763/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357133312) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (591802803/536870912) }, upper := { exponent := 1, mantissa := (287/256) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi256LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715855871/68714266624) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf4714InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf4714LocalValidity :
    LeafFacts leaf4714Box leaf4714Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4714Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357133312) }) = true
      norm_num [leaf4714Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4714CertificateValid :
    WideCertificateValid leaf4714Box leaf4714Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi256ValidityFacts
    leaf4714LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4714CoverageChecked :
    coverageCheck (innerAD leaf4714Box) leaf4714InnerLog = true := by
  rfl'

private theorem leaf4714InnerLogValid :
    leaf4714InnerLog.Valid 8 (innerAD leaf4714Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf4714CoverageChecked

private noncomputable def leaf4714InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629469/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4714InputLogOnePlusV_eq :
    leaf4714InputLogOnePlusV = outerEnclosure 24
      (leaf4714Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4714RoundedFacts : LeafRoundedFacts 8
    leaf4714Certificate.logOnePlusV leaf4714InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4714InputLogOnePlusV_eq }

private noncomputable def leaf4714Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi256InputQChi innerPair256Input
    leaf4714InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4714LowerChecked :
    lowerCheck 24 leaf4714Box leaf4714Inputs = true := by
  rfl'

private theorem leaf4714CoversExact : CoversExact 8
    leaf4714Box leaf4714Certificate leaf4714InnerLog leaf4714Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi256RoundedFacts
    innerPair256RoundedFacts leaf4714RoundedFacts (by rfl)

private theorem leaf4714FlatSound : Sound leaf4714Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4714CertificateValid
    leaf4714InnerLogValid leaf4714CoversExact leaf4714LowerChecked

private noncomputable def leaf4715Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (23/64), chiHi := (47/128) }

private noncomputable def leaf4715Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435763/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357163520) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (587936415/536870912) }, upper := { exponent := 1, mantissa := (9125/8192) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi255LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715886079/68714327040) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf4715InnerLog : WideLogData :=
  innerPair263Data

set_option maxRecDepth 1000000 in
private theorem leaf4715LocalValidity :
    LeafFacts leaf4715Box leaf4715Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4715Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357163520) }) = true
      norm_num [leaf4715Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4715CertificateValid :
    WideCertificateValid leaf4715Box leaf4715Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi255ValidityFacts
    leaf4715LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4715CoverageChecked :
    coverageCheck (innerAD leaf4715Box) leaf4715InnerLog = true := by
  rfl'

private theorem leaf4715InnerLogValid :
    leaf4715InnerLog.Valid 8 (innerAD leaf4715Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint348PositiveFacts.valid leaf4715CoverageChecked

private noncomputable def leaf4715InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629461/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4715InputLogOnePlusV_eq :
    leaf4715InputLogOnePlusV = outerEnclosure 24
      (leaf4715Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4715RoundedFacts : LeafRoundedFacts 8
    leaf4715Certificate.logOnePlusV leaf4715InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4715InputLogOnePlusV_eq }

private noncomputable def leaf4715Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi255InputQChi innerPair263Input
    leaf4715InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4715LowerChecked :
    lowerCheck 24 leaf4715Box leaf4715Inputs = true := by
  rfl'

private theorem leaf4715CoversExact : CoversExact 8
    leaf4715Box leaf4715Certificate leaf4715InnerLog leaf4715Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi255RoundedFacts
    innerPair263RoundedFacts leaf4715RoundedFacts (by rfl)

private theorem leaf4715FlatSound : Sound leaf4715Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4715CertificateValid
    leaf4715InnerLogValid leaf4715CoversExact leaf4715LowerChecked

private noncomputable def leaf4716Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (23/64), chiHi := (47/128) }

private noncomputable def leaf4716Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435765/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357139456) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (590950885/536870912) }, upper := { exponent := 1, mantissa := (2293/2048) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi255LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715862015/68714278912) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf4716InnerLog : WideLogData :=
  innerPair623Data

set_option maxRecDepth 1000000 in
private theorem leaf4716LocalValidity :
    LeafFacts leaf4716Box leaf4716Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4716Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357139456) }) = true
      norm_num [leaf4716Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4716CertificateValid :
    WideCertificateValid leaf4716Box leaf4716Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi255ValidityFacts
    leaf4716LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4716CoverageChecked :
    coverageCheck (innerAD leaf4716Box) leaf4716InnerLog = true := by
  rfl'

private theorem leaf4716InnerLogValid :
    leaf4716InnerLog.Valid 8 (innerAD leaf4716Box) :=
  wideLogDataValid_of_cachedCheck endpoint349PositiveFacts
    endpoint350PositiveFacts.valid leaf4716CoverageChecked

private noncomputable def leaf4716InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629467/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4716InputLogOnePlusV_eq :
    leaf4716InputLogOnePlusV = outerEnclosure 24
      (leaf4716Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4716RoundedFacts : LeafRoundedFacts 8
    leaf4716Certificate.logOnePlusV leaf4716InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4716InputLogOnePlusV_eq }

private noncomputable def leaf4716Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi255InputQChi innerPair623Input
    leaf4716InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4716LowerChecked :
    lowerCheck 24 leaf4716Box leaf4716Inputs = true := by
  rfl'

private theorem leaf4716CoversExact : CoversExact 8
    leaf4716Box leaf4716Certificate leaf4716InnerLog leaf4716Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi255RoundedFacts
    innerPair623RoundedFacts leaf4716RoundedFacts (by rfl)

private theorem leaf4716FlatSound : Sound leaf4716Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4716CertificateValid
    leaf4716InnerLogValid leaf4716CoversExact leaf4716LowerChecked

private noncomputable def leaf4717Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (47/128), chiHi := (3/8) }

private noncomputable def leaf4717Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435765/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357108736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (594882805/536870912) }, upper := { exponent := 1, mantissa := (577/512) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi256LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715831295/68714217472) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf4717InnerLog : WideLogData :=
  innerPair556Data

set_option maxRecDepth 1000000 in
private theorem leaf4717LocalValidity :
    LeafFacts leaf4717Box leaf4717Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4717Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357108736) }) = true
      norm_num [leaf4717Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4717CertificateValid :
    WideCertificateValid leaf4717Box leaf4717Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi256ValidityFacts
    leaf4717LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4717CoverageChecked :
    coverageCheck (innerAD leaf4717Box) leaf4717InnerLog = true := by
  rfl'

private theorem leaf4717InnerLogValid :
    leaf4717InnerLog.Valid 8 (innerAD leaf4717Box) :=
  wideLogDataValid_of_cachedCheck endpoint291PositiveFacts
    endpoint292PositiveFacts.valid leaf4717CoverageChecked

private noncomputable def leaf4717InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629475/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4717InputLogOnePlusV_eq :
    leaf4717InputLogOnePlusV = outerEnclosure 24
      (leaf4717Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4717RoundedFacts : LeafRoundedFacts 8
    leaf4717Certificate.logOnePlusV leaf4717InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4717InputLogOnePlusV_eq }

private noncomputable def leaf4717Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi256InputQChi innerPair556Input
    leaf4717InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4717LowerChecked :
    lowerCheck 24 leaf4717Box leaf4717Inputs = true := by
  rfl'

private theorem leaf4717CoversExact : CoversExact 8
    leaf4717Box leaf4717Certificate leaf4717InnerLog leaf4717Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi256RoundedFacts
    innerPair556RoundedFacts leaf4717RoundedFacts (by rfl)

private theorem leaf4717FlatSound : Sound leaf4717Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4717CertificateValid
    leaf4717InnerLogValid leaf4717CoversExact leaf4717LowerChecked

private noncomputable def leaf4718Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (47/128), chiHi := (3/8) }

private noncomputable def leaf4718Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435767/268435456) }, vSqrt := { lower := (65529/65536), upper := (4908388937/4908154880) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (597962807/536870912) }, upper := { exponent := 1, mantissa := (145/128) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi256LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (9816543817/9816309760) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf4718InnerLog : WideLogData :=
  innerPair300Data

set_option maxRecDepth 1000000 in
private theorem leaf4718LocalValidity :
    LeafFacts leaf4718Box leaf4718Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4718Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4908388937/4908154880) }) = true
      norm_num [leaf4718Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4718CertificateValid :
    WideCertificateValid leaf4718Box leaf4718Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi256ValidityFacts
    leaf4718LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4718CoverageChecked :
    coverageCheck (innerAD leaf4718Box) leaf4718InnerLog = true := by
  rfl'

private theorem leaf4718InnerLogValid :
    leaf4718InnerLog.Valid 8 (innerAD leaf4718Box) :=
  wideLogDataValid_of_cachedCheck endpoint80PositiveFacts
    endpoint292PositiveFacts.valid leaf4718CoverageChecked

private noncomputable def leaf4718InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629481/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4718InputLogOnePlusV_eq :
    leaf4718InputLogOnePlusV = outerEnclosure 24
      (leaf4718Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4718RoundedFacts : LeafRoundedFacts 8
    leaf4718Certificate.logOnePlusV leaf4718InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4718InputLogOnePlusV_eq }

private noncomputable def leaf4718Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi256InputQChi innerPair300Input
    leaf4718InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4718LowerChecked :
    lowerCheck 24 leaf4718Box leaf4718Inputs = true := by
  rfl'

private theorem leaf4718CoversExact : CoversExact 8
    leaf4718Box leaf4718Certificate leaf4718InnerLog leaf4718Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi256RoundedFacts
    innerPair300RoundedFacts leaf4718RoundedFacts (by rfl)

private theorem leaf4718FlatSound : Sound leaf4718Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4718CertificateValid
    leaf4718InnerLogValid leaf4718CoversExact leaf4718LowerChecked

private noncomputable def leaf4719Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (11/32), chiHi := (89/256) }

private noncomputable def leaf4719Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871307/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357254912) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1159653879/1073741824) }, upper := { exponent := 1, mantissa := (17893/16384) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi297LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715977471/68714509824) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf4719InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf4719LocalValidity :
    LeafFacts leaf4719Box leaf4719Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4719Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357254912) }) = true
      norm_num [leaf4719Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4719CertificateValid :
    WideCertificateValid leaf4719Box leaf4719Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi297ValidityFacts
    leaf4719LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4719CoverageChecked :
    coverageCheck (innerAD leaf4719Box) leaf4719InnerLog = true := by
  rfl'

private theorem leaf4719InnerLogValid :
    leaf4719InnerLog.Valid 8 (innerAD leaf4719Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf4719CoverageChecked

private noncomputable def leaf4719InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629439/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4719InputLogOnePlusV_eq :
    leaf4719InputLogOnePlusV = outerEnclosure 24
      (leaf4719Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4719RoundedFacts : LeafRoundedFacts 8
    leaf4719Certificate.logOnePlusV leaf4719InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4719InputLogOnePlusV_eq }

private noncomputable def leaf4719Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi297InputQChi innerPair249Input
    leaf4719InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4719LowerChecked :
    lowerCheck 24 leaf4719Box leaf4719Inputs = true := by
  rfl'

private theorem leaf4719CoversExact : CoversExact 8
    leaf4719Box leaf4719Certificate leaf4719InnerLog leaf4719Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi297RoundedFacts
    innerPair249RoundedFacts leaf4719RoundedFacts (by rfl)

private theorem leaf4719FlatSound : Sound leaf4719Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4719CertificateValid
    leaf4719InnerLogValid leaf4719CoversExact leaf4719LowerChecked

private noncomputable def leaf4720Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (89/256), chiHi := (45/128) }

private noncomputable def leaf4720Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871309/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357227008) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1166731333/1073741824) }, upper := { exponent := 1, mantissa := (9001/8192) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi298LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715949567/68714454016) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf4720InnerLog : WideLogData :=
  innerPair612Data

set_option maxRecDepth 1000000 in
private theorem leaf4720LocalValidity :
    LeafFacts leaf4720Box leaf4720Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4720Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357227008) }) = true
      norm_num [leaf4720Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4720CertificateValid :
    WideCertificateValid leaf4720Box leaf4720Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi298ValidityFacts
    leaf4720LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4720CoverageChecked :
    coverageCheck (innerAD leaf4720Box) leaf4720InnerLog = true := by
  rfl'

private theorem leaf4720InnerLogValid :
    leaf4720InnerLog.Valid 8 (innerAD leaf4720Box) :=
  wideLogDataValid_of_cachedCheck endpoint337PositiveFacts
    endpoint291PositiveFacts.valid leaf4720CoverageChecked

private noncomputable def leaf4720InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814723/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4720InputLogOnePlusV_eq :
    leaf4720InputLogOnePlusV = outerEnclosure 24
      (leaf4720Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4720RoundedFacts : LeafRoundedFacts 8
    leaf4720Certificate.logOnePlusV leaf4720InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4720InputLogOnePlusV_eq }

private noncomputable def leaf4720Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi298InputQChi innerPair612Input
    leaf4720InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4720LowerChecked :
    lowerCheck 24 leaf4720Box leaf4720Inputs = true := by
  rfl'

private theorem leaf4720CoversExact : CoversExact 8
    leaf4720Box leaf4720Certificate leaf4720InnerLog leaf4720Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi298RoundedFacts
    innerPair612RoundedFacts leaf4720RoundedFacts (by rfl)

private theorem leaf4720FlatSound : Sound leaf4720Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4720CertificateValid
    leaf4720InnerLogValid leaf4720CoversExact leaf4720LowerChecked

private noncomputable def leaf4721Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (11/32), chiHi := (89/256) }

private noncomputable def leaf4721Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871309/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357232128) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1165420693/1073741824) }, upper := { exponent := 1, mantissa := (8991/8192) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi297LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715954687/68714464256) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf4721InnerLog : WideLogData :=
  innerPair332Data

set_option maxRecDepth 1000000 in
private theorem leaf4721LocalValidity :
    LeafFacts leaf4721Box leaf4721Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4721Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357232128) }) = true
      norm_num [leaf4721Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4721CertificateValid :
    WideCertificateValid leaf4721Box leaf4721Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi297ValidityFacts
    leaf4721LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4721CoverageChecked :
    coverageCheck (innerAD leaf4721Box) leaf4721InnerLog = true := by
  rfl'

private theorem leaf4721InnerLogValid :
    leaf4721InnerLog.Valid 8 (innerAD leaf4721Box) :=
  wideLogDataValid_of_cachedCheck endpoint88PositiveFacts
    endpoint291PositiveFacts.valid leaf4721CoverageChecked

private noncomputable def leaf4721InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629445/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4721InputLogOnePlusV_eq :
    leaf4721InputLogOnePlusV = outerEnclosure 24
      (leaf4721Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4721RoundedFacts : LeafRoundedFacts 8
    leaf4721Certificate.logOnePlusV leaf4721InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4721InputLogOnePlusV_eq }

private noncomputable def leaf4721Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi297InputQChi innerPair332Input
    leaf4721InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4721LowerChecked :
    lowerCheck 24 leaf4721Box leaf4721Inputs = true := by
  rfl'

private theorem leaf4721CoversExact : CoversExact 8
    leaf4721Box leaf4721Certificate leaf4721InnerLog leaf4721Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi297RoundedFacts
    innerPair332RoundedFacts leaf4721RoundedFacts (by rfl)

private theorem leaf4721FlatSound : Sound leaf4721Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4721CertificateValid
    leaf4721InnerLogValid leaf4721CoversExact leaf4721LowerChecked

private noncomputable def leaf4722Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (89/256), chiHi := (45/128) }

private noncomputable def leaf4722Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871311/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357203968) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1172563679/1073741824) }, upper := { exponent := 1, mantissa := (4523/4096) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi298LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715926527/68714407936) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf4722InnerLog : WideLogData :=
  innerPair250Data

set_option maxRecDepth 1000000 in
private theorem leaf4722LocalValidity :
    LeafFacts leaf4722Box leaf4722Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4722Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357203968) }) = true
      norm_num [leaf4722Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4722CertificateValid :
    WideCertificateValid leaf4722Box leaf4722Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi298ValidityFacts
    leaf4722LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4722CoverageChecked :
    coverageCheck (innerAD leaf4722Box) leaf4722InnerLog = true := by
  rfl'

private theorem leaf4722InnerLogValid :
    leaf4722InnerLog.Valid 8 (innerAD leaf4722Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint75PositiveFacts.valid leaf4722CoverageChecked

private noncomputable def leaf4722InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907363/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4722InputLogOnePlusV_eq :
    leaf4722InputLogOnePlusV = outerEnclosure 24
      (leaf4722Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4722RoundedFacts : LeafRoundedFacts 8
    leaf4722Certificate.logOnePlusV leaf4722InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4722InputLogOnePlusV_eq }

private noncomputable def leaf4722Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi298InputQChi innerPair250Input
    leaf4722InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4722LowerChecked :
    lowerCheck 24 leaf4722Box leaf4722Inputs = true := by
  rfl'

private theorem leaf4722CoversExact : CoversExact 8
    leaf4722Box leaf4722Certificate leaf4722InnerLog leaf4722Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi298RoundedFacts
    innerPair250RoundedFacts leaf4722RoundedFacts (by rfl)

private theorem leaf4722FlatSound : Sound leaf4722Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4722CertificateValid
    leaf4722InnerLogValid leaf4722CoversExact leaf4722LowerChecked

private noncomputable def leaf4723Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (45/128), chiHi := (91/256) }

private noncomputable def leaf4723Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871311/536870912) }, vSqrt := { lower := (65529/65536), upper := (2021101327/2021011712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1173808787/1073741824) }, upper := { exponent := 1, mantissa := (18111/16384) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi299LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (4042113039/4042023424) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf4723InnerLog : WideLogData :=
  innerPair250Data

set_option maxRecDepth 1000000 in
private theorem leaf4723LocalValidity :
    LeafFacts leaf4723Box leaf4723Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4723Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (2021101327/2021011712) }) = true
      norm_num [leaf4723Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4723CertificateValid :
    WideCertificateValid leaf4723Box leaf4723Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi299ValidityFacts
    leaf4723LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4723CoverageChecked :
    coverageCheck (innerAD leaf4723Box) leaf4723InnerLog = true := by
  rfl'

private theorem leaf4723InnerLogValid :
    leaf4723InnerLog.Valid 8 (innerAD leaf4723Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint75PositiveFacts.valid leaf4723CoverageChecked

private noncomputable def leaf4723InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629453/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4723InputLogOnePlusV_eq :
    leaf4723InputLogOnePlusV = outerEnclosure 24
      (leaf4723Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4723RoundedFacts : LeafRoundedFacts 8
    leaf4723Certificate.logOnePlusV leaf4723InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4723InputLogOnePlusV_eq }

private noncomputable def leaf4723Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi299InputQChi innerPair250Input
    leaf4723InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4723LowerChecked :
    lowerCheck 24 leaf4723Box leaf4723Inputs = true := by
  rfl'

private theorem leaf4723CoversExact : CoversExact 8
    leaf4723Box leaf4723Certificate leaf4723InnerLog leaf4723Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi299RoundedFacts
    innerPair250RoundedFacts leaf4723RoundedFacts (by rfl)

private theorem leaf4723FlatSound : Sound leaf4723Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4723CertificateValid
    leaf4723InnerLogValid leaf4723CoversExact leaf4723LowerChecked

private noncomputable def leaf4724Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (91/256), chiHi := (23/64) }

private noncomputable def leaf4724Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871313/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357171200) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1180886241/1073741824) }, upper := { exponent := 1, mantissa := (4555/4096) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi300LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715893759/68714342400) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf4724InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf4724LocalValidity :
    LeafFacts leaf4724Box leaf4724Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4724Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357171200) }) = true
      norm_num [leaf4724Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4724CertificateValid :
    WideCertificateValid leaf4724Box leaf4724Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi300ValidityFacts
    leaf4724LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4724CoverageChecked :
    coverageCheck (innerAD leaf4724Box) leaf4724InnerLog = true := by
  rfl'

private theorem leaf4724InnerLogValid :
    leaf4724InnerLog.Valid 8 (innerAD leaf4724Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf4724CoverageChecked

private noncomputable def leaf4724InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907365/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4724InputLogOnePlusV_eq :
    leaf4724InputLogOnePlusV = outerEnclosure 24
      (leaf4724Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4724RoundedFacts : LeafRoundedFacts 8
    leaf4724Certificate.logOnePlusV leaf4724InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4724InputLogOnePlusV_eq }

private noncomputable def leaf4724Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi300InputQChi innerPair256Input
    leaf4724InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4724LowerChecked :
    lowerCheck 24 leaf4724Box leaf4724Inputs = true := by
  rfl'

private theorem leaf4724CoversExact : CoversExact 8
    leaf4724Box leaf4724Certificate leaf4724InnerLog leaf4724Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi300RoundedFacts
    innerPair256RoundedFacts leaf4724RoundedFacts (by rfl)

private theorem leaf4724FlatSound : Sound leaf4724Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4724CertificateValid
    leaf4724InnerLogValid leaf4724CoversExact leaf4724LowerChecked

private noncomputable def leaf4725Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (45/128), chiHi := (91/256) }

private noncomputable def leaf4725Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871313/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357175808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1179706665/1073741824) }, upper := { exponent := 1, mantissa := (9101/8192) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi299LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715898367/68714351616) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf4725InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf4725LocalValidity :
    LeafFacts leaf4725Box leaf4725Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4725Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357175808) }) = true
      norm_num [leaf4725Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4725CertificateValid :
    WideCertificateValid leaf4725Box leaf4725Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi299ValidityFacts
    leaf4725LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4725CoverageChecked :
    coverageCheck (innerAD leaf4725Box) leaf4725InnerLog = true := by
  rfl'

private theorem leaf4725InnerLogValid :
    leaf4725InnerLog.Valid 8 (innerAD leaf4725Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf4725CoverageChecked

private noncomputable def leaf4725InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814729/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4725InputLogOnePlusV_eq :
    leaf4725InputLogOnePlusV = outerEnclosure 24
      (leaf4725Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4725RoundedFacts : LeafRoundedFacts 8
    leaf4725Certificate.logOnePlusV leaf4725InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4725InputLogOnePlusV_eq }

private noncomputable def leaf4725Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi299InputQChi innerPair256Input
    leaf4725InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4725LowerChecked :
    lowerCheck 24 leaf4725Box leaf4725Inputs = true := by
  rfl'

private theorem leaf4725CoversExact : CoversExact 8
    leaf4725Box leaf4725Certificate leaf4725InnerLog leaf4725Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi299RoundedFacts
    innerPair256RoundedFacts leaf4725RoundedFacts (by rfl)

private theorem leaf4725FlatSound : Sound leaf4725Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4725CertificateValid
    leaf4725InnerLogValid leaf4725CoversExact leaf4725LowerChecked

private noncomputable def leaf4726Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (91/256), chiHi := (23/64) }

private noncomputable def leaf4726Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871315/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357147648) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1186849651/1073741824) }, upper := { exponent := 1, mantissa := (2289/2048) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi300LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715870207/68714295296) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf4726InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf4726LocalValidity :
    LeafFacts leaf4726Box leaf4726Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4726Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357147648) }) = true
      norm_num [leaf4726Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4726CertificateValid :
    WideCertificateValid leaf4726Box leaf4726Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi300ValidityFacts
    leaf4726LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4726CoverageChecked :
    coverageCheck (innerAD leaf4726Box) leaf4726InnerLog = true := by
  rfl'

private theorem leaf4726InnerLogValid :
    leaf4726InnerLog.Valid 8 (innerAD leaf4726Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf4726CoverageChecked

private noncomputable def leaf4726InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629465/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4726InputLogOnePlusV_eq :
    leaf4726InputLogOnePlusV = outerEnclosure 24
      (leaf4726Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4726RoundedFacts : LeafRoundedFacts 8
    leaf4726Certificate.logOnePlusV leaf4726InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4726InputLogOnePlusV_eq }

private noncomputable def leaf4726Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi300InputQChi innerPair256Input
    leaf4726InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4726LowerChecked :
    lowerCheck 24 leaf4726Box leaf4726Inputs = true := by
  rfl'

private theorem leaf4726CoversExact : CoversExact 8
    leaf4726Box leaf4726Certificate leaf4726InnerLog leaf4726Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi300RoundedFacts
    innerPair256RoundedFacts leaf4726RoundedFacts (by rfl)

private theorem leaf4726FlatSound : Sound leaf4726Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4726CertificateValid
    leaf4726InnerLogValid leaf4726CoversExact leaf4726LowerChecked

private noncomputable def leaf4727Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (11/32), chiHi := (89/256) }

private noncomputable def leaf4727Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871311/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357209344) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1171187507/1073741824) }, upper := { exponent := 1, mantissa := (18071/16384) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi297LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715931903/68714418688) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf4727InnerLog : WideLogData :=
  innerPair611Data

set_option maxRecDepth 1000000 in
private theorem leaf4727LocalValidity :
    LeafFacts leaf4727Box leaf4727Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4727Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357209344) }) = true
      norm_num [leaf4727Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4727CertificateValid :
    WideCertificateValid leaf4727Box leaf4727Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi297ValidityFacts
    leaf4727LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4727CoverageChecked :
    coverageCheck (innerAD leaf4727Box) leaf4727InnerLog = true := by
  rfl'

private theorem leaf4727InnerLogValid :
    leaf4727InnerLog.Valid 8 (innerAD leaf4727Box) :=
  wideLogDataValid_of_cachedCheck endpoint337PositiveFacts
    endpoint80PositiveFacts.valid leaf4727CoverageChecked

private noncomputable def leaf4727InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814725/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4727InputLogOnePlusV_eq :
    leaf4727InputLogOnePlusV = outerEnclosure 24
      (leaf4727Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4727RoundedFacts : LeafRoundedFacts 8
    leaf4727Certificate.logOnePlusV leaf4727InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4727InputLogOnePlusV_eq }

private noncomputable def leaf4727Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi297InputQChi innerPair611Input
    leaf4727InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4727LowerChecked :
    lowerCheck 24 leaf4727Box leaf4727Inputs = true := by
  rfl'

private theorem leaf4727CoversExact : CoversExact 8
    leaf4727Box leaf4727Certificate leaf4727InnerLog leaf4727Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi297RoundedFacts
    innerPair611RoundedFacts leaf4727RoundedFacts (by rfl)

private theorem leaf4727FlatSound : Sound leaf4727Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4727CertificateValid
    leaf4727InnerLogValid leaf4727CoversExact leaf4727LowerChecked

private noncomputable def leaf4728Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (89/256), chiHi := (45/128) }

private noncomputable def leaf4728Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871313/536870912) }, vSqrt := { lower := (65529/65536), upper := (4908388937/4908168704) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1178396025/1073741824) }, upper := { exponent := 1, mantissa := (9091/8192) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi298LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (9816557641/9816337408) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf4728InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf4728LocalValidity :
    LeafFacts leaf4728Box leaf4728Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4728Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4908388937/4908168704) }) = true
      norm_num [leaf4728Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4728CertificateValid :
    WideCertificateValid leaf4728Box leaf4728Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi298ValidityFacts
    leaf4728LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4728CoverageChecked :
    coverageCheck (innerAD leaf4728Box) leaf4728InnerLog = true := by
  rfl'

private theorem leaf4728InnerLogValid :
    leaf4728InnerLog.Valid 8 (innerAD leaf4728Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf4728CoverageChecked

private noncomputable def leaf4728InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629457/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4728InputLogOnePlusV_eq :
    leaf4728InputLogOnePlusV = outerEnclosure 24
      (leaf4728Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4728RoundedFacts : LeafRoundedFacts 8
    leaf4728Certificate.logOnePlusV leaf4728InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4728InputLogOnePlusV_eq }

private noncomputable def leaf4728Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi298InputQChi innerPair256Input
    leaf4728InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4728LowerChecked :
    lowerCheck 24 leaf4728Box leaf4728Inputs = true := by
  rfl'

private theorem leaf4728CoversExact : CoversExact 8
    leaf4728Box leaf4728Certificate leaf4728InnerLog leaf4728Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi298RoundedFacts
    innerPair256RoundedFacts leaf4728RoundedFacts (by rfl)

private theorem leaf4728FlatSound : Sound leaf4728Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4728CertificateValid
    leaf4728InnerLogValid leaf4728CoversExact leaf4728LowerChecked

private noncomputable def leaf4729Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (11/32), chiHi := (89/256) }

private noncomputable def leaf4729Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871313/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357186560) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1176954321/1073741824) }, upper := { exponent := 1, mantissa := (1135/1024) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi297LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715909119/68714373120) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf4729InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf4729LocalValidity :
    LeafFacts leaf4729Box leaf4729Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4729Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357186560) }) = true
      norm_num [leaf4729Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4729CertificateValid :
    WideCertificateValid leaf4729Box leaf4729Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi297ValidityFacts
    leaf4729LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4729CoverageChecked :
    coverageCheck (innerAD leaf4729Box) leaf4729InnerLog = true := by
  rfl'

private theorem leaf4729InnerLogValid :
    leaf4729InnerLog.Valid 8 (innerAD leaf4729Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf4729CoverageChecked

private noncomputable def leaf4729InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726841/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf4729InputLogOnePlusV_eq :
    leaf4729InputLogOnePlusV = outerEnclosure 24
      (leaf4729Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4729RoundedFacts : LeafRoundedFacts 8
    leaf4729Certificate.logOnePlusV leaf4729InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4729InputLogOnePlusV_eq }

private noncomputable def leaf4729Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi297InputQChi innerPair256Input
    leaf4729InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4729LowerChecked :
    lowerCheck 24 leaf4729Box leaf4729Inputs = true := by
  rfl'

private theorem leaf4729CoversExact : CoversExact 8
    leaf4729Box leaf4729Certificate leaf4729InnerLog leaf4729Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi297RoundedFacts
    innerPair256RoundedFacts leaf4729RoundedFacts (by rfl)

private theorem leaf4729FlatSound : Sound leaf4729Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4729CertificateValid
    leaf4729InnerLogValid leaf4729CoversExact leaf4729LowerChecked

private noncomputable def leaf4730Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (89/256), chiHi := (45/128) }

private noncomputable def leaf4730Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871315/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357157888) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1184228371/1073741824) }, upper := { exponent := 1, mantissa := (571/512) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi298LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715880447/68714315776) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf4730InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf4730LocalValidity :
    LeafFacts leaf4730Box leaf4730Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4730Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357157888) }) = true
      norm_num [leaf4730Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4730CertificateValid :
    WideCertificateValid leaf4730Box leaf4730Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi298ValidityFacts
    leaf4730LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4730CoverageChecked :
    coverageCheck (innerAD leaf4730Box) leaf4730InnerLog = true := by
  rfl'

private theorem leaf4730InnerLogValid :
    leaf4730InnerLog.Valid 8 (innerAD leaf4730Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf4730CoverageChecked

private noncomputable def leaf4730InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629463/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4730InputLogOnePlusV_eq :
    leaf4730InputLogOnePlusV = outerEnclosure 24
      (leaf4730Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4730RoundedFacts : LeafRoundedFacts 8
    leaf4730Certificate.logOnePlusV leaf4730InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4730InputLogOnePlusV_eq }

private noncomputable def leaf4730Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi298InputQChi innerPair256Input
    leaf4730InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4730LowerChecked :
    lowerCheck 24 leaf4730Box leaf4730Inputs = true := by
  rfl'

private theorem leaf4730CoversExact : CoversExact 8
    leaf4730Box leaf4730Certificate leaf4730InnerLog leaf4730Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi298RoundedFacts
    innerPair256RoundedFacts leaf4730RoundedFacts (by rfl)

private theorem leaf4730FlatSound : Sound leaf4730Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4730CertificateValid
    leaf4730InnerLogValid leaf4730CoversExact leaf4730LowerChecked

private noncomputable def leaf4731Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (45/128), chiHi := (91/256) }

private noncomputable def leaf4731Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871315/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357152512) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1185604543/1073741824) }, upper := { exponent := 1, mantissa := (18293/16384) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi299LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715875071/68714305024) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf4731InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf4731LocalValidity :
    LeafFacts leaf4731Box leaf4731Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4731Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357152512) }) = true
      norm_num [leaf4731Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4731CertificateValid :
    WideCertificateValid leaf4731Box leaf4731Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi299ValidityFacts
    leaf4731LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4731CoverageChecked :
    coverageCheck (innerAD leaf4731Box) leaf4731InnerLog = true := by
  rfl'

private theorem leaf4731InnerLogValid :
    leaf4731InnerLog.Valid 8 (innerAD leaf4731Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf4731CoverageChecked

private noncomputable def leaf4731InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453683/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf4731InputLogOnePlusV_eq :
    leaf4731InputLogOnePlusV = outerEnclosure 24
      (leaf4731Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4731RoundedFacts : LeafRoundedFacts 8
    leaf4731Certificate.logOnePlusV leaf4731InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4731InputLogOnePlusV_eq }

private noncomputable def leaf4731Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi299InputQChi innerPair256Input
    leaf4731InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4731LowerChecked :
    lowerCheck 24 leaf4731Box leaf4731Inputs = true := by
  rfl'

private theorem leaf4731CoversExact : CoversExact 8
    leaf4731Box leaf4731Certificate leaf4731InnerLog leaf4731Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi299RoundedFacts
    innerPair256RoundedFacts leaf4731RoundedFacts (by rfl)

private theorem leaf4731FlatSound : Sound leaf4731Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4731CertificateValid
    leaf4731InnerLogValid leaf4731CoversExact leaf4731LowerChecked

private noncomputable def leaf4732Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (91/256), chiHi := (23/64) }

private noncomputable def leaf4732Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871317/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357124096) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1192813061/1073741824) }, upper := { exponent := 1, mantissa := (4601/4096) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi300LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715846655/68714248192) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf4732InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf4732LocalValidity :
    LeafFacts leaf4732Box leaf4732Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4732Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357124096) }) = true
      norm_num [leaf4732Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4732CertificateValid :
    WideCertificateValid leaf4732Box leaf4732Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi300ValidityFacts
    leaf4732LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4732CoverageChecked :
    coverageCheck (innerAD leaf4732Box) leaf4732InnerLog = true := by
  rfl'

private theorem leaf4732InnerLogValid :
    leaf4732InnerLog.Valid 8 (innerAD leaf4732Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf4732CoverageChecked

private noncomputable def leaf4732InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629471/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4732InputLogOnePlusV_eq :
    leaf4732InputLogOnePlusV = outerEnclosure 24
      (leaf4732Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4732RoundedFacts : LeafRoundedFacts 8
    leaf4732Certificate.logOnePlusV leaf4732InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4732InputLogOnePlusV_eq }

private noncomputable def leaf4732Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi300InputQChi innerPair256Input
    leaf4732InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4732LowerChecked :
    lowerCheck 24 leaf4732Box leaf4732Inputs = true := by
  rfl'

private theorem leaf4732CoversExact : CoversExact 8
    leaf4732Box leaf4732Certificate leaf4732InnerLog leaf4732Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi300RoundedFacts
    innerPair256RoundedFacts leaf4732RoundedFacts (by rfl)

private theorem leaf4732FlatSound : Sound leaf4732Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4732CertificateValid
    leaf4732InnerLogValid leaf4732CoversExact leaf4732LowerChecked

private noncomputable def leaf4733Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (45/128), chiHi := (91/256) }

private noncomputable def leaf4733Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871317/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357129216) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1191502421/1073741824) }, upper := { exponent := 1, mantissa := (1149/1024) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi299LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715851775/68714258432) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf4733InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf4733LocalValidity :
    LeafFacts leaf4733Box leaf4733Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4733Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357129216) }) = true
      norm_num [leaf4733Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4733CertificateValid :
    WideCertificateValid leaf4733Box leaf4733Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi299ValidityFacts
    leaf4733LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4733CoverageChecked :
    coverageCheck (innerAD leaf4733Box) leaf4733InnerLog = true := by
  rfl'

private theorem leaf4733InnerLogValid :
    leaf4733InnerLog.Valid 8 (innerAD leaf4733Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf4733CoverageChecked

private noncomputable def leaf4733InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814735/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4733InputLogOnePlusV_eq :
    leaf4733InputLogOnePlusV = outerEnclosure 24
      (leaf4733Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4733RoundedFacts : LeafRoundedFacts 8
    leaf4733Certificate.logOnePlusV leaf4733InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4733InputLogOnePlusV_eq }

private noncomputable def leaf4733Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi299InputQChi innerPair256Input
    leaf4733InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4733LowerChecked :
    lowerCheck 24 leaf4733Box leaf4733Inputs = true := by
  rfl'

private theorem leaf4733CoversExact : CoversExact 8
    leaf4733Box leaf4733Certificate leaf4733InnerLog leaf4733Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi299RoundedFacts
    innerPair256RoundedFacts leaf4733RoundedFacts (by rfl)

private theorem leaf4733FlatSound : Sound leaf4733Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4733CertificateValid
    leaf4733InnerLogValid leaf4733CoversExact leaf4733LowerChecked

private noncomputable def leaf4734Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (91/256), chiHi := (23/64) }

private noncomputable def leaf4734Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871319/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357100544) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1198776471/1073741824) }, upper := { exponent := 1, mantissa := (289/256) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi300LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715823103/68714201088) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf4734InnerLog : WideLogData :=
  innerPair300Data

set_option maxRecDepth 1000000 in
private theorem leaf4734LocalValidity :
    LeafFacts leaf4734Box leaf4734Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4734Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357100544) }) = true
      norm_num [leaf4734Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4734CertificateValid :
    WideCertificateValid leaf4734Box leaf4734Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi300ValidityFacts
    leaf4734LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4734CoverageChecked :
    coverageCheck (innerAD leaf4734Box) leaf4734InnerLog = true := by
  rfl'

private theorem leaf4734InnerLogValid :
    leaf4734InnerLog.Valid 8 (innerAD leaf4734Box) :=
  wideLogDataValid_of_cachedCheck endpoint80PositiveFacts
    endpoint292PositiveFacts.valid leaf4734CoverageChecked

private noncomputable def leaf4734InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629477/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4734InputLogOnePlusV_eq :
    leaf4734InputLogOnePlusV = outerEnclosure 24
      (leaf4734Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4734RoundedFacts : LeafRoundedFacts 8
    leaf4734Certificate.logOnePlusV leaf4734InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4734InputLogOnePlusV_eq }

private noncomputable def leaf4734Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi300InputQChi innerPair300Input
    leaf4734InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4734LowerChecked :
    lowerCheck 24 leaf4734Box leaf4734Inputs = true := by
  rfl'

private theorem leaf4734CoversExact : CoversExact 8
    leaf4734Box leaf4734Certificate leaf4734InnerLog leaf4734Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi300RoundedFacts
    innerPair300RoundedFacts leaf4734RoundedFacts (by rfl)

private theorem leaf4734FlatSound : Sound leaf4734Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4734CertificateValid
    leaf4734InnerLogValid leaf4734CoversExact leaf4734LowerChecked

private noncomputable def leaf4735Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (23/64), chiHi := (93/256) }

private noncomputable def leaf4735Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871315/536870912) }, vSqrt := { lower := (65529/65536), upper := (4908388937/4908163328) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1187963695/1073741824) }, upper := { exponent := 1, mantissa := (18329/16384) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi301LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (9816552265/9816326656) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf4735InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf4735LocalValidity :
    LeafFacts leaf4735Box leaf4735Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4735Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4908388937/4908163328) }) = true
      norm_num [leaf4735Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4735CertificateValid :
    WideCertificateValid leaf4735Box leaf4735Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi301ValidityFacts
    leaf4735LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4735CoverageChecked :
    coverageCheck (innerAD leaf4735Box) leaf4735InnerLog = true := by
  rfl'

private theorem leaf4735InnerLogValid :
    leaf4735InnerLog.Valid 8 (innerAD leaf4735Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf4735CoverageChecked

private noncomputable def leaf4735InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814733/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4735InputLogOnePlusV_eq :
    leaf4735InputLogOnePlusV = outerEnclosure 24
      (leaf4735Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4735RoundedFacts : LeafRoundedFacts 8
    leaf4735Certificate.logOnePlusV leaf4735InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4735InputLogOnePlusV_eq }

private noncomputable def leaf4735Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi301InputQChi innerPair256Input
    leaf4735InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4735LowerChecked :
    lowerCheck 24 leaf4735Box leaf4735Inputs = true := by
  rfl'

private theorem leaf4735CoversExact : CoversExact 8
    leaf4735Box leaf4735Certificate leaf4735InnerLog leaf4735Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi301RoundedFacts
    innerPair256RoundedFacts leaf4735RoundedFacts (by rfl)

private theorem leaf4735FlatSound : Sound leaf4735Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4735CertificateValid
    leaf4735InnerLogValid leaf4735CoversExact leaf4735LowerChecked

private noncomputable def leaf4736Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (93/256), chiHi := (47/128) }

private noncomputable def leaf4736Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871317/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357115392) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1195041149/1073741824) }, upper := { exponent := 1, mantissa := (9219/8192) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi302LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715837951/68714230784) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf4736InnerLog : WideLogData :=
  innerPair300Data

set_option maxRecDepth 1000000 in
private theorem leaf4736LocalValidity :
    LeafFacts leaf4736Box leaf4736Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4736Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357115392) }) = true
      norm_num [leaf4736Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4736CertificateValid :
    WideCertificateValid leaf4736Box leaf4736Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi302ValidityFacts
    leaf4736LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4736CoverageChecked :
    coverageCheck (innerAD leaf4736Box) leaf4736InnerLog = true := by
  rfl'

private theorem leaf4736InnerLogValid :
    leaf4736InnerLog.Valid 8 (innerAD leaf4736Box) :=
  wideLogDataValid_of_cachedCheck endpoint80PositiveFacts
    endpoint292PositiveFacts.valid leaf4736CoverageChecked

private noncomputable def leaf4736InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629473/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4736InputLogOnePlusV_eq :
    leaf4736InputLogOnePlusV = outerEnclosure 24
      (leaf4736Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4736RoundedFacts : LeafRoundedFacts 8
    leaf4736Certificate.logOnePlusV leaf4736InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4736InputLogOnePlusV_eq }

private noncomputable def leaf4736Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi302InputQChi innerPair300Input
    leaf4736InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4736LowerChecked :
    lowerCheck 24 leaf4736Box leaf4736Inputs = true := by
  rfl'

private theorem leaf4736CoversExact : CoversExact 8
    leaf4736Box leaf4736Certificate leaf4736InnerLog leaf4736Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi302RoundedFacts
    innerPair300RoundedFacts leaf4736RoundedFacts (by rfl)

private theorem leaf4736FlatSound : Sound leaf4736Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4736CertificateValid
    leaf4736InnerLogValid leaf4736CoversExact leaf4736LowerChecked

private noncomputable def leaf4737Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (23/64), chiHi := (93/256) }

private noncomputable def leaf4737Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871317/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357119488) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1193992637/1073741824) }, upper := { exponent := 1, mantissa := (9211/8192) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi301LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715842047/68714238976) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf4737InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf4737LocalValidity :
    LeafFacts leaf4737Box leaf4737Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4737Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357119488) }) = true
      norm_num [leaf4737Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4737CertificateValid :
    WideCertificateValid leaf4737Box leaf4737Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi301ValidityFacts
    leaf4737LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4737CoverageChecked :
    coverageCheck (innerAD leaf4737Box) leaf4737InnerLog = true := by
  rfl'

private theorem leaf4737InnerLogValid :
    leaf4737InnerLog.Valid 8 (innerAD leaf4737Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf4737CoverageChecked

private noncomputable def leaf4737InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (363421/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf4737InputLogOnePlusV_eq :
    leaf4737InputLogOnePlusV = outerEnclosure 24
      (leaf4737Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4737RoundedFacts : LeafRoundedFacts 8
    leaf4737Certificate.logOnePlusV leaf4737InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4737InputLogOnePlusV_eq }

private noncomputable def leaf4737Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi301InputQChi innerPair256Input
    leaf4737InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4737LowerChecked :
    lowerCheck 24 leaf4737Box leaf4737Inputs = true := by
  rfl'

private theorem leaf4737CoversExact : CoversExact 8
    leaf4737Box leaf4737Certificate leaf4737InnerLog leaf4737Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi301RoundedFacts
    innerPair256RoundedFacts leaf4737RoundedFacts (by rfl)

private theorem leaf4737FlatSound : Sound leaf4737Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4737CertificateValid
    leaf4737InnerLogValid leaf4737CoversExact leaf4737LowerChecked

private noncomputable def leaf4738Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (93/256), chiHi := (47/128) }

private noncomputable def leaf4738Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871319/536870912) }, vSqrt := { lower := (65529/65536), upper := (4908388937/4908155904) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1201135623/1073741824) }, upper := { exponent := 1, mantissa := (4633/4096) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi302LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (9816544841/9816311808) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf4738InnerLog : WideLogData :=
  innerPair257Data

set_option maxRecDepth 1000000 in
private theorem leaf4738LocalValidity :
    LeafFacts leaf4738Box leaf4738Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4738Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4908388937/4908155904) }) = true
      norm_num [leaf4738Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4738CertificateValid :
    WideCertificateValid leaf4738Box leaf4738Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi302ValidityFacts
    leaf4738LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4738CoverageChecked :
    coverageCheck (innerAD leaf4738Box) leaf4738InnerLog = true := by
  rfl'

private theorem leaf4738InnerLogValid :
    leaf4738InnerLog.Valid 8 (innerAD leaf4738Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint76PositiveFacts.valid leaf4738CoverageChecked

private noncomputable def leaf4738InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629479/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4738InputLogOnePlusV_eq :
    leaf4738InputLogOnePlusV = outerEnclosure 24
      (leaf4738Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4738RoundedFacts : LeafRoundedFacts 8
    leaf4738Certificate.logOnePlusV leaf4738InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4738InputLogOnePlusV_eq }

private noncomputable def leaf4738Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi302InputQChi innerPair257Input
    leaf4738InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4738LowerChecked :
    lowerCheck 24 leaf4738Box leaf4738Inputs = true := by
  rfl'

private theorem leaf4738CoversExact : CoversExact 8
    leaf4738Box leaf4738Certificate leaf4738InnerLog leaf4738Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi302RoundedFacts
    innerPair257RoundedFacts leaf4738RoundedFacts (by rfl)

private theorem leaf4738FlatSound : Sound leaf4738Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4738CertificateValid
    leaf4738InnerLogValid leaf4738CoversExact leaf4738LowerChecked

private noncomputable def leaf4739Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (47/128), chiHi := (3/8) }

private noncomputable def leaf4739Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435769/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357059584) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (601042809/536870912) }, upper := { exponent := 1, mantissa := (583/512) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi256LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715782143/68714119168) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf4739InnerLog : WideLogData :=
  innerPair622Data

set_option maxRecDepth 1000000 in
private theorem leaf4739LocalValidity :
    LeafFacts leaf4739Box leaf4739Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4739Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357059584) }) = true
      norm_num [leaf4739Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4739CertificateValid :
    WideCertificateValid leaf4739Box leaf4739Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi256ValidityFacts
    leaf4739LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4739CoverageChecked :
    coverageCheck (innerAD leaf4739Box) leaf4739InnerLog = true := by
  rfl'

private theorem leaf4739InnerLogValid :
    leaf4739InnerLog.Valid 8 (innerAD leaf4739Box) :=
  wideLogDataValid_of_cachedCheck endpoint347PositiveFacts
    endpoint295PositiveFacts.valid leaf4739CoverageChecked

private noncomputable def leaf4739InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629487/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4739InputLogOnePlusV_eq :
    leaf4739InputLogOnePlusV = outerEnclosure 24
      (leaf4739Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4739RoundedFacts : LeafRoundedFacts 8
    leaf4739Certificate.logOnePlusV leaf4739InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4739InputLogOnePlusV_eq }

private noncomputable def leaf4739Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi256InputQChi innerPair622Input
    leaf4739InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4739LowerChecked :
    lowerCheck 24 leaf4739Box leaf4739Inputs = true := by
  rfl'

private theorem leaf4739CoversExact : CoversExact 8
    leaf4739Box leaf4739Certificate leaf4739InnerLog leaf4739Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi256RoundedFacts
    innerPair622RoundedFacts leaf4739RoundedFacts (by rfl)

private theorem leaf4739FlatSound : Sound leaf4739Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4739CertificateValid
    leaf4739InnerLogValid leaf4739CoversExact leaf4739LowerChecked

private noncomputable def leaf4740Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (47/128), chiHi := (3/8) }

private noncomputable def leaf4740Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435771/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357035008) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (604122811/536870912) }, upper := { exponent := 1, mantissa := (293/256) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi256LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715757567/68714070016) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf4740InnerLog : WideLogData :=
  innerPair268Data

set_option maxRecDepth 1000000 in
private theorem leaf4740LocalValidity :
    LeafFacts leaf4740Box leaf4740Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4740Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357035008) }) = true
      norm_num [leaf4740Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4740CertificateValid :
    WideCertificateValid leaf4740Box leaf4740Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi256ValidityFacts
    leaf4740LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4740CoverageChecked :
    coverageCheck (innerAD leaf4740Box) leaf4740InnerLog = true := by
  rfl'

private theorem leaf4740InnerLogValid :
    leaf4740InnerLog.Valid 8 (innerAD leaf4740Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint294PositiveFacts.valid leaf4740CoverageChecked

private noncomputable def leaf4740InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629493/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4740InputLogOnePlusV_eq :
    leaf4740InputLogOnePlusV = outerEnclosure 24
      (leaf4740Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4740RoundedFacts : LeafRoundedFacts 8
    leaf4740Certificate.logOnePlusV leaf4740InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4740InputLogOnePlusV_eq }

private noncomputable def leaf4740Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi256InputQChi innerPair268Input
    leaf4740InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4740LowerChecked :
    lowerCheck 24 leaf4740Box leaf4740Inputs = true := by
  rfl'

private theorem leaf4740CoversExact : CoversExact 8
    leaf4740Box leaf4740Certificate leaf4740InnerLog leaf4740Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi256RoundedFacts
    innerPair268RoundedFacts leaf4740RoundedFacts (by rfl)

private theorem leaf4740FlatSound : Sound leaf4740Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4740CertificateValid
    leaf4740InnerLogValid leaf4740CoversExact leaf4740LowerChecked

private noncomputable def leaf4741Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (23/64), chiHi := (93/256) }

private noncomputable def leaf4741Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871319/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357095680) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1200021579/1073741824) }, upper := { exponent := 1, mantissa := (18515/16384) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi301LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715818239/68714191360) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf4741InnerLog : WideLogData :=
  innerPair621Data

set_option maxRecDepth 1000000 in
private theorem leaf4741LocalValidity :
    LeafFacts leaf4741Box leaf4741Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4741Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357095680) }) = true
      norm_num [leaf4741Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4741CertificateValid :
    WideCertificateValid leaf4741Box leaf4741Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi301ValidityFacts
    leaf4741LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4741CoverageChecked :
    coverageCheck (innerAD leaf4741Box) leaf4741InnerLog = true := by
  rfl'

private theorem leaf4741InnerLogValid :
    leaf4741InnerLog.Valid 8 (innerAD leaf4741Box) :=
  wideLogDataValid_of_cachedCheck endpoint347PositiveFacts
    endpoint292PositiveFacts.valid leaf4741CoverageChecked

private noncomputable def leaf4741InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814739/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4741InputLogOnePlusV_eq :
    leaf4741InputLogOnePlusV = outerEnclosure 24
      (leaf4741Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4741RoundedFacts : LeafRoundedFacts 8
    leaf4741Certificate.logOnePlusV leaf4741InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4741InputLogOnePlusV_eq }

private noncomputable def leaf4741Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi301InputQChi innerPair621Input
    leaf4741InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4741LowerChecked :
    lowerCheck 24 leaf4741Box leaf4741Inputs = true := by
  rfl'

private theorem leaf4741CoversExact : CoversExact 8
    leaf4741Box leaf4741Certificate leaf4741InnerLog leaf4741Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi301RoundedFacts
    innerPair621RoundedFacts leaf4741RoundedFacts (by rfl)

private theorem leaf4741FlatSound : Sound leaf4741Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4741CertificateValid
    leaf4741InnerLogValid leaf4741CoversExact leaf4741LowerChecked

private noncomputable def leaf4742Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (93/256), chiHi := (47/128) }

private noncomputable def leaf4742Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871321/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357067264) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1207230097/1073741824) }, upper := { exponent := 1, mantissa := (9313/8192) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi302LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715789823/68714134528) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf4742InnerLog : WideLogData :=
  innerPair257Data

set_option maxRecDepth 1000000 in
private theorem leaf4742LocalValidity :
    LeafFacts leaf4742Box leaf4742Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4742Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357067264) }) = true
      norm_num [leaf4742Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4742CertificateValid :
    WideCertificateValid leaf4742Box leaf4742Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi302ValidityFacts
    leaf4742LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4742CoverageChecked :
    coverageCheck (innerAD leaf4742Box) leaf4742InnerLog = true := by
  rfl'

private theorem leaf4742InnerLogValid :
    leaf4742InnerLog.Valid 8 (innerAD leaf4742Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint76PositiveFacts.valid leaf4742CoverageChecked

private noncomputable def leaf4742InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629485/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4742InputLogOnePlusV_eq :
    leaf4742InputLogOnePlusV = outerEnclosure 24
      (leaf4742Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4742RoundedFacts : LeafRoundedFacts 8
    leaf4742Certificate.logOnePlusV leaf4742InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4742InputLogOnePlusV_eq }

private noncomputable def leaf4742Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi302InputQChi innerPair257Input
    leaf4742InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4742LowerChecked :
    lowerCheck 24 leaf4742Box leaf4742Inputs = true := by
  rfl'

private theorem leaf4742CoversExact : CoversExact 8
    leaf4742Box leaf4742Certificate leaf4742InnerLog leaf4742Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi302RoundedFacts
    innerPair257RoundedFacts leaf4742RoundedFacts (by rfl)

private theorem leaf4742FlatSound : Sound leaf4742Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4742CertificateValid
    leaf4742InnerLogValid leaf4742CoversExact leaf4742LowerChecked

private noncomputable def leaf4743Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (23/64), chiHi := (93/256) }

private noncomputable def leaf4743Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871321/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357071872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1206050521/1073741824) }, upper := { exponent := 1, mantissa := (1163/1024) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi301LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715794431/68714143744) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf4743InnerLog : WideLogData :=
  innerPair257Data

set_option maxRecDepth 1000000 in
private theorem leaf4743LocalValidity :
    LeafFacts leaf4743Box leaf4743Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4743Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357071872) }) = true
      norm_num [leaf4743Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4743CertificateValid :
    WideCertificateValid leaf4743Box leaf4743Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi301ValidityFacts
    leaf4743LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4743CoverageChecked :
    coverageCheck (innerAD leaf4743Box) leaf4743InnerLog = true := by
  rfl'

private theorem leaf4743InnerLogValid :
    leaf4743InnerLog.Valid 8 (innerAD leaf4743Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint76PositiveFacts.valid leaf4743CoverageChecked

private noncomputable def leaf4743InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907371/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4743InputLogOnePlusV_eq :
    leaf4743InputLogOnePlusV = outerEnclosure 24
      (leaf4743Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4743RoundedFacts : LeafRoundedFacts 8
    leaf4743Certificate.logOnePlusV leaf4743InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4743InputLogOnePlusV_eq }

private noncomputable def leaf4743Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi301InputQChi innerPair257Input
    leaf4743InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4743LowerChecked :
    lowerCheck 24 leaf4743Box leaf4743Inputs = true := by
  rfl'

private theorem leaf4743CoversExact : CoversExact 8
    leaf4743Box leaf4743Certificate leaf4743InnerLog leaf4743Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi301RoundedFacts
    innerPair257RoundedFacts leaf4743RoundedFacts (by rfl)

private theorem leaf4743FlatSound : Sound leaf4743Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4743CertificateValid
    leaf4743InnerLogValid leaf4743CoversExact leaf4743LowerChecked

private noncomputable def leaf4744Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (93/256), chiHi := (47/128) }

private noncomputable def leaf4744Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871323/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357043200) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1213324571/1073741824) }, upper := { exponent := 1, mantissa := (585/512) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi302LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715765759/68714086400) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf4744InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf4744LocalValidity :
    LeafFacts leaf4744Box leaf4744Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4744Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357043200) }) = true
      norm_num [leaf4744Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4744CertificateValid :
    WideCertificateValid leaf4744Box leaf4744Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi302ValidityFacts
    leaf4744LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4744CoverageChecked :
    coverageCheck (innerAD leaf4744Box) leaf4744InnerLog = true := by
  rfl'

private theorem leaf4744InnerLogValid :
    leaf4744InnerLog.Valid 8 (innerAD leaf4744Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf4744CoverageChecked

private noncomputable def leaf4744InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629491/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4744InputLogOnePlusV_eq :
    leaf4744InputLogOnePlusV = outerEnclosure 24
      (leaf4744Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4744RoundedFacts : LeafRoundedFacts 8
    leaf4744Certificate.logOnePlusV leaf4744InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4744InputLogOnePlusV_eq }

private noncomputable def leaf4744Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi302InputQChi innerPair264Input
    leaf4744InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4744LowerChecked :
    lowerCheck 24 leaf4744Box leaf4744Inputs = true := by
  rfl'

private theorem leaf4744CoversExact : CoversExact 8
    leaf4744Box leaf4744Certificate leaf4744InnerLog leaf4744Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi302RoundedFacts
    innerPair264RoundedFacts leaf4744RoundedFacts (by rfl)

private theorem leaf4744FlatSound : Sound leaf4744Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4744CertificateValid
    leaf4744InnerLogValid leaf4744CoversExact leaf4744LowerChecked

private noncomputable def leaf4745Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (47/128), chiHi := (95/256) }

private noncomputable def leaf4745Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871323/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357038848) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1214438615/1073741824) }, upper := { exponent := 1, mantissa := (18737/16384) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi303LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715761407/68714077696) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf4745InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf4745LocalValidity :
    LeafFacts leaf4745Box leaf4745Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4745Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357038848) }) = true
      norm_num [leaf4745Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4745CertificateValid :
    WideCertificateValid leaf4745Box leaf4745Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi303ValidityFacts
    leaf4745LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4745CoverageChecked :
    coverageCheck (innerAD leaf4745Box) leaf4745InnerLog = true := by
  rfl'

private theorem leaf4745InnerLogValid :
    leaf4745InnerLog.Valid 8 (innerAD leaf4745Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf4745CoverageChecked

private noncomputable def leaf4745InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907373/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4745InputLogOnePlusV_eq :
    leaf4745InputLogOnePlusV = outerEnclosure 24
      (leaf4745Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4745RoundedFacts : LeafRoundedFacts 8
    leaf4745Certificate.logOnePlusV leaf4745InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4745InputLogOnePlusV_eq }

private noncomputable def leaf4745Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi303InputQChi innerPair264Input
    leaf4745InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4745LowerChecked :
    lowerCheck 24 leaf4745Box leaf4745Inputs = true := by
  rfl'

private theorem leaf4745CoversExact : CoversExact 8
    leaf4745Box leaf4745Certificate leaf4745InnerLog leaf4745Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi303RoundedFacts
    innerPair264RoundedFacts leaf4745RoundedFacts (by rfl)

private theorem leaf4745FlatSound : Sound leaf4745Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4745CertificateValid
    leaf4745InnerLogValid leaf4745CoversExact leaf4745LowerChecked

private noncomputable def leaf4746Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (95/256), chiHi := (3/8) }

private noncomputable def leaf4746Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871325/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357010432) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1221647133/1073741824) }, upper := { exponent := 1, mantissa := (589/512) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi304LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715732991/68714020864) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf4746InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf4746LocalValidity :
    LeafFacts leaf4746Box leaf4746Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4746Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357010432) }) = true
      norm_num [leaf4746Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4746CertificateValid :
    WideCertificateValid leaf4746Box leaf4746Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi304ValidityFacts
    leaf4746LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4746CoverageChecked :
    coverageCheck (innerAD leaf4746Box) leaf4746InnerLog = true := by
  rfl'

private theorem leaf4746InnerLogValid :
    leaf4746InnerLog.Valid 8 (innerAD leaf4746Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf4746CoverageChecked

private noncomputable def leaf4746InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629499/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4746InputLogOnePlusV_eq :
    leaf4746InputLogOnePlusV = outerEnclosure 24
      (leaf4746Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4746RoundedFacts : LeafRoundedFacts 8
    leaf4746Certificate.logOnePlusV leaf4746InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4746InputLogOnePlusV_eq }

private noncomputable def leaf4746Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi304InputQChi innerPair264Input
    leaf4746InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4746LowerChecked :
    lowerCheck 24 leaf4746Box leaf4746Inputs = true := by
  rfl'

private theorem leaf4746CoversExact : CoversExact 8
    leaf4746Box leaf4746Certificate leaf4746InnerLog leaf4746Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi304RoundedFacts
    innerPair264RoundedFacts leaf4746RoundedFacts (by rfl)

private theorem leaf4746FlatSound : Sound leaf4746Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4746CertificateValid
    leaf4746InnerLogValid leaf4746CoversExact leaf4746LowerChecked

private noncomputable def leaf4747Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (47/128), chiHi := (95/256) }

private noncomputable def leaf4747Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871325/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357014528) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1220598621/1073741824) }, upper := { exponent := 1, mantissa := (1177/1024) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi303LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715737087/68714029056) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf4747InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf4747LocalValidity :
    LeafFacts leaf4747Box leaf4747Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4747Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357014528) }) = true
      norm_num [leaf4747Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4747CertificateValid :
    WideCertificateValid leaf4747Box leaf4747Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi303ValidityFacts
    leaf4747LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4747CoverageChecked :
    coverageCheck (innerAD leaf4747Box) leaf4747InnerLog = true := by
  rfl'

private theorem leaf4747InnerLogValid :
    leaf4747InnerLog.Valid 8 (innerAD leaf4747Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf4747CoverageChecked

private noncomputable def leaf4747InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814749/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4747InputLogOnePlusV_eq :
    leaf4747InputLogOnePlusV = outerEnclosure 24
      (leaf4747Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4747RoundedFacts : LeafRoundedFacts 8
    leaf4747Certificate.logOnePlusV leaf4747InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4747InputLogOnePlusV_eq }

private noncomputable def leaf4747Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi303InputQChi innerPair264Input
    leaf4747InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4747LowerChecked :
    lowerCheck 24 leaf4747Box leaf4747Inputs = true := by
  rfl'

private theorem leaf4747CoversExact : CoversExact 8
    leaf4747Box leaf4747Certificate leaf4747InnerLog leaf4747Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi303RoundedFacts
    innerPair264RoundedFacts leaf4747RoundedFacts (by rfl)

private theorem leaf4747FlatSound : Sound leaf4747Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4747CertificateValid
    leaf4747InnerLogValid leaf4747CoversExact leaf4747LowerChecked

private noncomputable def leaf4748Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (95/256), chiHi := (3/8) }

private noncomputable def leaf4748Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871327/536870912) }, vSqrt := { lower := (8191/8192), upper := (2021101327/2020999168) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1227872671/1073741824) }, upper := { exponent := 1, mantissa := (37/32) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi304LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (4042100495/4041998336) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf4748InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf4748LocalValidity :
    LeafFacts leaf4748Box leaf4748Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4748Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (2021101327/2020999168) }) = true
      norm_num [leaf4748Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4748CertificateValid :
    WideCertificateValid leaf4748Box leaf4748Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi304ValidityFacts
    leaf4748LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4748CoverageChecked :
    coverageCheck (innerAD leaf4748Box) leaf4748InnerLog = true := by
  rfl'

private theorem leaf4748InnerLogValid :
    leaf4748InnerLog.Valid 8 (innerAD leaf4748Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf4748CoverageChecked

private noncomputable def leaf4748InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629505/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4748InputLogOnePlusV_eq :
    leaf4748InputLogOnePlusV = outerEnclosure 24
      (leaf4748Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4748RoundedFacts : LeafRoundedFacts 8
    leaf4748Certificate.logOnePlusV leaf4748InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4748InputLogOnePlusV_eq }

private noncomputable def leaf4748Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi304InputQChi innerPair264Input
    leaf4748InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4748LowerChecked :
    lowerCheck 24 leaf4748Box leaf4748Inputs = true := by
  rfl'

private theorem leaf4748CoversExact : CoversExact 8
    leaf4748Box leaf4748Certificate leaf4748InnerLog leaf4748Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi304RoundedFacts
    innerPair264RoundedFacts leaf4748RoundedFacts (by rfl)

private theorem leaf4748FlatSound : Sound leaf4748Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4748CertificateValid
    leaf4748InnerLogValid leaf4748CoversExact leaf4748LowerChecked

private noncomputable def component97Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (11/32), chiHi := (45/128) }

set_option maxRecDepth 1000000 in
private theorem component97Node0_sound : Sound component97Node0Box :=
  sound_of_literal_split component97Node0Box leaf4700Box leaf4701Box
    .chi (89/256) (by rfl) (by rfl)
    leaf4700FlatSound leaf4701FlatSound

private noncomputable def component97Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (11/32), chiHi := (45/128) }

set_option maxRecDepth 1000000 in
private theorem component97Node1_sound : Sound component97Node1Box :=
  sound_of_literal_split component97Node1Box leaf4699Box component97Node0Box
    .k (105/32) (by rfl) (by rfl)
    leaf4699FlatSound component97Node0_sound

private noncomputable def component97Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (45/128), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component97Node2_sound : Sound component97Node2Box :=
  sound_of_literal_split component97Node2Box leaf4702Box leaf4703Box
    .k (105/32) (by rfl) (by rfl)
    leaf4702FlatSound leaf4703FlatSound

private noncomputable def component97Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (11/32), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component97Node3_sound : Sound component97Node3Box :=
  sound_of_literal_split component97Node3Box component97Node1Box component97Node2Box
    .chi (45/128) (by rfl) (by rfl)
    component97Node1_sound component97Node2_sound

private noncomputable def component97Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (11/32), chiHi := (45/128) }

set_option maxRecDepth 1000000 in
private theorem component97Node4_sound : Sound component97Node4Box :=
  sound_of_literal_split component97Node4Box leaf4704Box leaf4705Box
    .chi (89/256) (by rfl) (by rfl)
    leaf4704FlatSound leaf4705FlatSound

private noncomputable def component97Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (11/32), chiHi := (45/128) }

set_option maxRecDepth 1000000 in
private theorem component97Node5_sound : Sound component97Node5Box :=
  sound_of_literal_split component97Node5Box leaf4706Box leaf4707Box
    .chi (89/256) (by rfl) (by rfl)
    leaf4706FlatSound leaf4707FlatSound

private noncomputable def component97Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (11/32), chiHi := (45/128) }

set_option maxRecDepth 1000000 in
private theorem component97Node6_sound : Sound component97Node6Box :=
  sound_of_literal_split component97Node6Box component97Node4Box component97Node5Box
    .k (107/32) (by rfl) (by rfl)
    component97Node4_sound component97Node5_sound

private noncomputable def component97Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (45/128), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component97Node7_sound : Sound component97Node7Box :=
  sound_of_literal_split component97Node7Box leaf4709Box leaf4710Box
    .chi (91/256) (by rfl) (by rfl)
    leaf4709FlatSound leaf4710FlatSound

private noncomputable def component97Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (45/128), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component97Node8_sound : Sound component97Node8Box :=
  sound_of_literal_split component97Node8Box leaf4708Box component97Node7Box
    .k (107/32) (by rfl) (by rfl)
    leaf4708FlatSound component97Node7_sound

private noncomputable def component97Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (11/32), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component97Node9_sound : Sound component97Node9Box :=
  sound_of_literal_split component97Node9Box component97Node6Box component97Node8Box
    .chi (45/128) (by rfl) (by rfl)
    component97Node6_sound component97Node8_sound

private noncomputable def component97Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (11/32), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component97Node10_sound : Sound component97Node10Box :=
  sound_of_literal_split component97Node10Box component97Node3Box component97Node9Box
    .k (53/16) (by rfl) (by rfl)
    component97Node3_sound component97Node9_sound

private noncomputable def component97Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (23/64), chiHi := (47/128) }

set_option maxRecDepth 1000000 in
private theorem component97Node11_sound : Sound component97Node11Box :=
  sound_of_literal_split component97Node11Box leaf4711Box leaf4712Box
    .k (105/32) (by rfl) (by rfl)
    leaf4711FlatSound leaf4712FlatSound

private noncomputable def component97Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (47/128), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component97Node12_sound : Sound component97Node12Box :=
  sound_of_literal_split component97Node12Box leaf4713Box leaf4714Box
    .k (105/32) (by rfl) (by rfl)
    leaf4713FlatSound leaf4714FlatSound

private noncomputable def component97Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (23/64), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component97Node13_sound : Sound component97Node13Box :=
  sound_of_literal_split component97Node13Box component97Node11Box component97Node12Box
    .chi (47/128) (by rfl) (by rfl)
    component97Node11_sound component97Node12_sound

private noncomputable def component97Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (23/64), chiHi := (47/128) }

set_option maxRecDepth 1000000 in
private theorem component97Node14_sound : Sound component97Node14Box :=
  sound_of_literal_split component97Node14Box leaf4715Box leaf4716Box
    .k (107/32) (by rfl) (by rfl)
    leaf4715FlatSound leaf4716FlatSound

private noncomputable def component97Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (47/128), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component97Node15_sound : Sound component97Node15Box :=
  sound_of_literal_split component97Node15Box leaf4717Box leaf4718Box
    .k (107/32) (by rfl) (by rfl)
    leaf4717FlatSound leaf4718FlatSound

private noncomputable def component97Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (23/64), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component97Node16_sound : Sound component97Node16Box :=
  sound_of_literal_split component97Node16Box component97Node14Box component97Node15Box
    .chi (47/128) (by rfl) (by rfl)
    component97Node14_sound component97Node15_sound

private noncomputable def component97Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (23/64), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component97Node17_sound : Sound component97Node17Box :=
  sound_of_literal_split component97Node17Box component97Node13Box component97Node16Box
    .k (53/16) (by rfl) (by rfl)
    component97Node13_sound component97Node16_sound

private noncomputable def component97Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (11/32), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component97Node18_sound : Sound component97Node18Box :=
  sound_of_literal_split component97Node18Box component97Node10Box component97Node17Box
    .chi (23/64) (by rfl) (by rfl)
    component97Node10_sound component97Node17_sound

private noncomputable def component97Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (11/32), chiHi := (45/128) }

set_option maxRecDepth 1000000 in
private theorem component97Node19_sound : Sound component97Node19Box :=
  sound_of_literal_split component97Node19Box leaf4719Box leaf4720Box
    .chi (89/256) (by rfl) (by rfl)
    leaf4719FlatSound leaf4720FlatSound

private noncomputable def component97Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (11/32), chiHi := (45/128) }

set_option maxRecDepth 1000000 in
private theorem component97Node20_sound : Sound component97Node20Box :=
  sound_of_literal_split component97Node20Box leaf4721Box leaf4722Box
    .chi (89/256) (by rfl) (by rfl)
    leaf4721FlatSound leaf4722FlatSound

private noncomputable def component97Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (11/32), chiHi := (45/128) }

set_option maxRecDepth 1000000 in
private theorem component97Node21_sound : Sound component97Node21Box :=
  sound_of_literal_split component97Node21Box component97Node19Box component97Node20Box
    .k (109/32) (by rfl) (by rfl)
    component97Node19_sound component97Node20_sound

private noncomputable def component97Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (45/128), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component97Node22_sound : Sound component97Node22Box :=
  sound_of_literal_split component97Node22Box leaf4723Box leaf4724Box
    .chi (91/256) (by rfl) (by rfl)
    leaf4723FlatSound leaf4724FlatSound

private noncomputable def component97Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (45/128), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component97Node23_sound : Sound component97Node23Box :=
  sound_of_literal_split component97Node23Box leaf4725Box leaf4726Box
    .chi (91/256) (by rfl) (by rfl)
    leaf4725FlatSound leaf4726FlatSound

private noncomputable def component97Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (45/128), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component97Node24_sound : Sound component97Node24Box :=
  sound_of_literal_split component97Node24Box component97Node22Box component97Node23Box
    .k (109/32) (by rfl) (by rfl)
    component97Node22_sound component97Node23_sound

private noncomputable def component97Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (11/32), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component97Node25_sound : Sound component97Node25Box :=
  sound_of_literal_split component97Node25Box component97Node21Box component97Node24Box
    .chi (45/128) (by rfl) (by rfl)
    component97Node21_sound component97Node24_sound

private noncomputable def component97Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (11/32), chiHi := (45/128) }

set_option maxRecDepth 1000000 in
private theorem component97Node26_sound : Sound component97Node26Box :=
  sound_of_literal_split component97Node26Box leaf4727Box leaf4728Box
    .chi (89/256) (by rfl) (by rfl)
    leaf4727FlatSound leaf4728FlatSound

private noncomputable def component97Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (11/32), chiHi := (45/128) }

set_option maxRecDepth 1000000 in
private theorem component97Node27_sound : Sound component97Node27Box :=
  sound_of_literal_split component97Node27Box leaf4729Box leaf4730Box
    .chi (89/256) (by rfl) (by rfl)
    leaf4729FlatSound leaf4730FlatSound

private noncomputable def component97Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (11/32), chiHi := (45/128) }

set_option maxRecDepth 1000000 in
private theorem component97Node28_sound : Sound component97Node28Box :=
  sound_of_literal_split component97Node28Box component97Node26Box component97Node27Box
    .k (111/32) (by rfl) (by rfl)
    component97Node26_sound component97Node27_sound

private noncomputable def component97Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (45/128), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component97Node29_sound : Sound component97Node29Box :=
  sound_of_literal_split component97Node29Box leaf4731Box leaf4732Box
    .chi (91/256) (by rfl) (by rfl)
    leaf4731FlatSound leaf4732FlatSound

private noncomputable def component97Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (45/128), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component97Node30_sound : Sound component97Node30Box :=
  sound_of_literal_split component97Node30Box leaf4733Box leaf4734Box
    .chi (91/256) (by rfl) (by rfl)
    leaf4733FlatSound leaf4734FlatSound

private noncomputable def component97Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (45/128), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component97Node31_sound : Sound component97Node31Box :=
  sound_of_literal_split component97Node31Box component97Node29Box component97Node30Box
    .k (111/32) (by rfl) (by rfl)
    component97Node29_sound component97Node30_sound

private noncomputable def component97Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (11/32), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component97Node32_sound : Sound component97Node32Box :=
  sound_of_literal_split component97Node32Box component97Node28Box component97Node31Box
    .chi (45/128) (by rfl) (by rfl)
    component97Node28_sound component97Node31_sound

private noncomputable def component97Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (11/32), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component97Node33_sound : Sound component97Node33Box :=
  sound_of_literal_split component97Node33Box component97Node25Box component97Node32Box
    .k (55/16) (by rfl) (by rfl)
    component97Node25_sound component97Node32_sound

private noncomputable def component97Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (23/64), chiHi := (47/128) }

set_option maxRecDepth 1000000 in
private theorem component97Node34_sound : Sound component97Node34Box :=
  sound_of_literal_split component97Node34Box leaf4735Box leaf4736Box
    .chi (93/256) (by rfl) (by rfl)
    leaf4735FlatSound leaf4736FlatSound

private noncomputable def component97Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (23/64), chiHi := (47/128) }

set_option maxRecDepth 1000000 in
private theorem component97Node35_sound : Sound component97Node35Box :=
  sound_of_literal_split component97Node35Box leaf4737Box leaf4738Box
    .chi (93/256) (by rfl) (by rfl)
    leaf4737FlatSound leaf4738FlatSound

private noncomputable def component97Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (23/64), chiHi := (47/128) }

set_option maxRecDepth 1000000 in
private theorem component97Node36_sound : Sound component97Node36Box :=
  sound_of_literal_split component97Node36Box component97Node34Box component97Node35Box
    .k (109/32) (by rfl) (by rfl)
    component97Node34_sound component97Node35_sound

private noncomputable def component97Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (47/128), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component97Node37_sound : Sound component97Node37Box :=
  sound_of_literal_split component97Node37Box leaf4739Box leaf4740Box
    .k (109/32) (by rfl) (by rfl)
    leaf4739FlatSound leaf4740FlatSound

private noncomputable def component97Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (23/64), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component97Node38_sound : Sound component97Node38Box :=
  sound_of_literal_split component97Node38Box component97Node36Box component97Node37Box
    .chi (47/128) (by rfl) (by rfl)
    component97Node36_sound component97Node37_sound

private noncomputable def component97Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (23/64), chiHi := (47/128) }

set_option maxRecDepth 1000000 in
private theorem component97Node39_sound : Sound component97Node39Box :=
  sound_of_literal_split component97Node39Box leaf4741Box leaf4742Box
    .chi (93/256) (by rfl) (by rfl)
    leaf4741FlatSound leaf4742FlatSound

private noncomputable def component97Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (23/64), chiHi := (47/128) }

set_option maxRecDepth 1000000 in
private theorem component97Node40_sound : Sound component97Node40Box :=
  sound_of_literal_split component97Node40Box leaf4743Box leaf4744Box
    .chi (93/256) (by rfl) (by rfl)
    leaf4743FlatSound leaf4744FlatSound

private noncomputable def component97Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (23/64), chiHi := (47/128) }

set_option maxRecDepth 1000000 in
private theorem component97Node41_sound : Sound component97Node41Box :=
  sound_of_literal_split component97Node41Box component97Node39Box component97Node40Box
    .k (111/32) (by rfl) (by rfl)
    component97Node39_sound component97Node40_sound

private noncomputable def component97Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (47/128), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component97Node42_sound : Sound component97Node42Box :=
  sound_of_literal_split component97Node42Box leaf4745Box leaf4746Box
    .chi (95/256) (by rfl) (by rfl)
    leaf4745FlatSound leaf4746FlatSound

private noncomputable def component97Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (47/128), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component97Node43_sound : Sound component97Node43Box :=
  sound_of_literal_split component97Node43Box leaf4747Box leaf4748Box
    .chi (95/256) (by rfl) (by rfl)
    leaf4747FlatSound leaf4748FlatSound

private noncomputable def component97Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (47/128), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component97Node44_sound : Sound component97Node44Box :=
  sound_of_literal_split component97Node44Box component97Node42Box component97Node43Box
    .k (111/32) (by rfl) (by rfl)
    component97Node42_sound component97Node43_sound

private noncomputable def component97Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (23/64), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component97Node45_sound : Sound component97Node45Box :=
  sound_of_literal_split component97Node45Box component97Node41Box component97Node44Box
    .chi (47/128) (by rfl) (by rfl)
    component97Node41_sound component97Node44_sound

private noncomputable def component97Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (23/64), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component97Node46_sound : Sound component97Node46Box :=
  sound_of_literal_split component97Node46Box component97Node38Box component97Node45Box
    .k (55/16) (by rfl) (by rfl)
    component97Node38_sound component97Node45_sound

private noncomputable def component97Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (11/32), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component97Node47_sound : Sound component97Node47Box :=
  sound_of_literal_split component97Node47Box component97Node33Box component97Node46Box
    .chi (23/64) (by rfl) (by rfl)
    component97Node33_sound component97Node46_sound

noncomputable def component97Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (7/2), chiLo := (11/32), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
theorem component97_sound : Sound component97Box :=
  sound_of_literal_split component97Box component97Node18Box component97Node47Box
    .k (27/8) (by rfl) (by rfl)
    component97Node18_sound component97Node47_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
