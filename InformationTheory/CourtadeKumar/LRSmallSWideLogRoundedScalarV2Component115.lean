import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch5
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch6
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch10
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch4
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

private noncomputable def leaf5697Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (3/8), chiHi := (49/128) }

private noncomputable def leaf5697Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435763/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357104128) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (595538127/536870912) }, upper := { exponent := 1, mantissa := (9241/8192) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi259LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715826687/68714208256) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf5697InnerLog : WideLogData :=
  innerPair556Data

set_option maxRecDepth 1000000 in
private theorem leaf5697LocalValidity :
    LeafFacts leaf5697Box leaf5697Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5697Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357104128) }) = true
      norm_num [leaf5697Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5697CertificateValid :
    WideCertificateValid leaf5697Box leaf5697Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi259ValidityFacts
    leaf5697LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5697CoverageChecked :
    coverageCheck (innerAD leaf5697Box) leaf5697InnerLog = true := by
  rfl'

private theorem leaf5697InnerLogValid :
    leaf5697InnerLog.Valid 8 (innerAD leaf5697Box) :=
  wideLogDataValid_of_cachedCheck endpoint291PositiveFacts
    endpoint292PositiveFacts.valid leaf5697CoverageChecked

private noncomputable def leaf5697InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907369/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5697InputLogOnePlusV_eq :
    leaf5697InputLogOnePlusV = outerEnclosure 24
      (leaf5697Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5697RoundedFacts : LeafRoundedFacts 8
    leaf5697Certificate.logOnePlusV leaf5697InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5697InputLogOnePlusV_eq }

private noncomputable def leaf5697Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi259InputQChi innerPair556Input
    leaf5697InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5697LowerChecked :
    lowerCheck 24 leaf5697Box leaf5697Inputs = true := by
  rfl'

private theorem leaf5697CoversExact : CoversExact 8
    leaf5697Box leaf5697Certificate leaf5697InnerLog leaf5697Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi259RoundedFacts
    innerPair556RoundedFacts leaf5697RoundedFacts (by rfl)

private theorem leaf5697FlatSound : Sound leaf5697Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5697CertificateValid
    leaf5697InnerLogValid leaf5697CoversExact leaf5697LowerChecked

private noncomputable def leaf5698Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (3/8), chiHi := (49/128) }

private noncomputable def leaf5698Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435765/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357079040) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (598683661/536870912) }, upper := { exponent := 1, mantissa := (4645/4096) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi259LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715801599/68714158080) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf5698InnerLog : WideLogData :=
  innerPair301Data

set_option maxRecDepth 1000000 in
private theorem leaf5698LocalValidity :
    LeafFacts leaf5698Box leaf5698Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5698Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357079040) }) = true
      norm_num [leaf5698Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5698CertificateValid :
    WideCertificateValid leaf5698Box leaf5698Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi259ValidityFacts
    leaf5698LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5698CoverageChecked :
    coverageCheck (innerAD leaf5698Box) leaf5698InnerLog = true := by
  rfl'

private theorem leaf5698InnerLogValid :
    leaf5698InnerLog.Valid 8 (innerAD leaf5698Box) :=
  wideLogDataValid_of_cachedCheck endpoint80PositiveFacts
    endpoint295PositiveFacts.valid leaf5698CoverageChecked

private noncomputable def leaf5698InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814741/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5698InputLogOnePlusV_eq :
    leaf5698InputLogOnePlusV = outerEnclosure 24
      (leaf5698Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5698RoundedFacts : LeafRoundedFacts 8
    leaf5698Certificate.logOnePlusV leaf5698InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5698InputLogOnePlusV_eq }

private noncomputable def leaf5698Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi259InputQChi innerPair301Input
    leaf5698InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5698LowerChecked :
    lowerCheck 24 leaf5698Box leaf5698Inputs = true := by
  rfl'

private theorem leaf5698CoversExact : CoversExact 8
    leaf5698Box leaf5698Certificate leaf5698InnerLog leaf5698Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi259RoundedFacts
    innerPair301RoundedFacts leaf5698RoundedFacts (by rfl)

private theorem leaf5698FlatSound : Sound leaf5698Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5698CertificateValid
    leaf5698InnerLogValid leaf5698CoversExact leaf5698LowerChecked

private noncomputable def leaf5699Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (49/128), chiHi := (25/64) }

private noncomputable def leaf5699Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435765/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357050368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (602353453/536870912) }, upper := { exponent := 1, mantissa := (4673/4096) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi260LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715772927/68714100736) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf5699InnerLog : WideLogData :=
  innerPair257Data

set_option maxRecDepth 1000000 in
private theorem leaf5699LocalValidity :
    LeafFacts leaf5699Box leaf5699Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5699Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357050368) }) = true
      norm_num [leaf5699Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5699CertificateValid :
    WideCertificateValid leaf5699Box leaf5699Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi260ValidityFacts
    leaf5699LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5699CoverageChecked :
    coverageCheck (innerAD leaf5699Box) leaf5699InnerLog = true := by
  rfl'

private theorem leaf5699InnerLogValid :
    leaf5699InnerLog.Valid 8 (innerAD leaf5699Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint76PositiveFacts.valid leaf5699CoverageChecked

private noncomputable def leaf5699InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629489/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5699InputLogOnePlusV_eq :
    leaf5699InputLogOnePlusV = outerEnclosure 24
      (leaf5699Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5699RoundedFacts : LeafRoundedFacts 8
    leaf5699Certificate.logOnePlusV leaf5699InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5699InputLogOnePlusV_eq }

private noncomputable def leaf5699Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi260InputQChi innerPair257Input
    leaf5699InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5699LowerChecked :
    lowerCheck 24 leaf5699Box leaf5699Inputs = true := by
  rfl'

private theorem leaf5699CoversExact : CoversExact 8
    leaf5699Box leaf5699Certificate leaf5699InnerLog leaf5699Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi260RoundedFacts
    innerPair257RoundedFacts leaf5699RoundedFacts (by rfl)

private theorem leaf5699FlatSound : Sound leaf5699Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5699CertificateValid
    leaf5699InnerLogValid leaf5699CoversExact leaf5699LowerChecked

private noncomputable def leaf5700Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (49/128), chiHi := (25/64) }

private noncomputable def leaf5700Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435767/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357024768) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (605564519/536870912) }, upper := { exponent := 1, mantissa := (2349/2048) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi260LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715747327/68714049536) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf5700InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf5700LocalValidity :
    LeafFacts leaf5700Box leaf5700Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5700Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357024768) }) = true
      norm_num [leaf5700Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5700CertificateValid :
    WideCertificateValid leaf5700Box leaf5700Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi260ValidityFacts
    leaf5700LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5700CoverageChecked :
    coverageCheck (innerAD leaf5700Box) leaf5700InnerLog = true := by
  rfl'

private theorem leaf5700InnerLogValid :
    leaf5700InnerLog.Valid 8 (innerAD leaf5700Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf5700CoverageChecked

private noncomputable def leaf5700InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629495/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5700InputLogOnePlusV_eq :
    leaf5700InputLogOnePlusV = outerEnclosure 24
      (leaf5700Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5700RoundedFacts : LeafRoundedFacts 8
    leaf5700Certificate.logOnePlusV leaf5700InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5700InputLogOnePlusV_eq }

private noncomputable def leaf5700Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi260InputQChi innerPair264Input
    leaf5700InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5700LowerChecked :
    lowerCheck 24 leaf5700Box leaf5700Inputs = true := by
  rfl'

private theorem leaf5700CoversExact : CoversExact 8
    leaf5700Box leaf5700Certificate leaf5700InnerLog leaf5700Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi260RoundedFacts
    innerPair264RoundedFacts leaf5700RoundedFacts (by rfl)

private theorem leaf5700FlatSound : Sound leaf5700Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5700CertificateValid
    leaf5700InnerLogValid leaf5700CoversExact leaf5700LowerChecked

private noncomputable def leaf5701Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (3/8), chiHi := (49/128) }

private noncomputable def leaf5701Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435767/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357053952) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (601829195/536870912) }, upper := { exponent := 1, mantissa := (9339/8192) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi259LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715776511/68714107904) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf5701InnerLog : WideLogData :=
  innerPair622Data

set_option maxRecDepth 1000000 in
private theorem leaf5701LocalValidity :
    LeafFacts leaf5701Box leaf5701Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5701Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357053952) }) = true
      norm_num [leaf5701Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5701CertificateValid :
    WideCertificateValid leaf5701Box leaf5701Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi259ValidityFacts
    leaf5701LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5701CoverageChecked :
    coverageCheck (innerAD leaf5701Box) leaf5701InnerLog = true := by
  rfl'

private theorem leaf5701InnerLogValid :
    leaf5701InnerLog.Valid 8 (innerAD leaf5701Box) :=
  wideLogDataValid_of_cachedCheck endpoint347PositiveFacts
    endpoint295PositiveFacts.valid leaf5701CoverageChecked

private noncomputable def leaf5701InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (726843/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf5701InputLogOnePlusV_eq :
    leaf5701InputLogOnePlusV = outerEnclosure 24
      (leaf5701Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5701RoundedFacts : LeafRoundedFacts 8
    leaf5701Certificate.logOnePlusV leaf5701InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5701InputLogOnePlusV_eq }

private noncomputable def leaf5701Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi259InputQChi innerPair622Input
    leaf5701InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5701LowerChecked :
    lowerCheck 24 leaf5701Box leaf5701Inputs = true := by
  rfl'

private theorem leaf5701CoversExact : CoversExact 8
    leaf5701Box leaf5701Certificate leaf5701InnerLog leaf5701Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi259RoundedFacts
    innerPair622RoundedFacts leaf5701RoundedFacts (by rfl)

private theorem leaf5701FlatSound : Sound leaf5701Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5701CertificateValid
    leaf5701InnerLogValid leaf5701CoversExact leaf5701LowerChecked

private noncomputable def leaf5702Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (3/8), chiHi := (49/128) }

private noncomputable def leaf5702Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435769/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357028864) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (604974729/536870912) }, upper := { exponent := 1, mantissa := (2347/2048) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi259LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715751423/68714057728) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf5702InnerLog : WideLogData :=
  innerPair271Data

set_option maxRecDepth 1000000 in
private theorem leaf5702LocalValidity :
    LeafFacts leaf5702Box leaf5702Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5702Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357028864) }) = true
      norm_num [leaf5702Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5702CertificateValid :
    WideCertificateValid leaf5702Box leaf5702Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi259ValidityFacts
    leaf5702LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5702CoverageChecked :
    coverageCheck (innerAD leaf5702Box) leaf5702InnerLog = true := by
  rfl'

private theorem leaf5702InnerLogValid :
    leaf5702InnerLog.Valid 8 (innerAD leaf5702Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint298PositiveFacts.valid leaf5702CoverageChecked

private noncomputable def leaf5702InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814747/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5702InputLogOnePlusV_eq :
    leaf5702InputLogOnePlusV = outerEnclosure 24
      (leaf5702Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5702RoundedFacts : LeafRoundedFacts 8
    leaf5702Certificate.logOnePlusV leaf5702InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5702InputLogOnePlusV_eq }

private noncomputable def leaf5702Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi259InputQChi innerPair271Input
    leaf5702InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5702LowerChecked :
    lowerCheck 24 leaf5702Box leaf5702Inputs = true := by
  rfl'

private theorem leaf5702CoversExact : CoversExact 8
    leaf5702Box leaf5702Certificate leaf5702InnerLog leaf5702Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi259RoundedFacts
    innerPair271RoundedFacts leaf5702RoundedFacts (by rfl)

private theorem leaf5702FlatSound : Sound leaf5702Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5702CertificateValid
    leaf5702InnerLogValid leaf5702CoversExact leaf5702LowerChecked

private noncomputable def leaf5703Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (49/128), chiHi := (25/64) }

private noncomputable def leaf5703Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435769/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356999168) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (608775585/536870912) }, upper := { exponent := 1, mantissa := (4723/4096) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi260LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715721727/68713998336) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf5703InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf5703LocalValidity :
    LeafFacts leaf5703Box leaf5703Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5703Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356999168) }) = true
      norm_num [leaf5703Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5703CertificateValid :
    WideCertificateValid leaf5703Box leaf5703Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi260ValidityFacts
    leaf5703LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5703CoverageChecked :
    coverageCheck (innerAD leaf5703Box) leaf5703InnerLog = true := by
  rfl'

private theorem leaf5703InnerLogValid :
    leaf5703InnerLog.Valid 8 (innerAD leaf5703Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf5703CoverageChecked

private noncomputable def leaf5703InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814751/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5703InputLogOnePlusV_eq :
    leaf5703InputLogOnePlusV = outerEnclosure 24
      (leaf5703Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5703RoundedFacts : LeafRoundedFacts 8
    leaf5703Certificate.logOnePlusV leaf5703InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5703InputLogOnePlusV_eq }

private noncomputable def leaf5703Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi260InputQChi innerPair264Input
    leaf5703InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5703LowerChecked :
    lowerCheck 24 leaf5703Box leaf5703Inputs = true := by
  rfl'

private theorem leaf5703CoversExact : CoversExact 8
    leaf5703Box leaf5703Certificate leaf5703InnerLog leaf5703Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi260RoundedFacts
    innerPair264RoundedFacts leaf5703RoundedFacts (by rfl)

private theorem leaf5703FlatSound : Sound leaf5703Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5703CertificateValid
    leaf5703InnerLogValid leaf5703CoversExact leaf5703LowerChecked

private noncomputable def leaf5704Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (49/128), chiHi := (25/64) }

private noncomputable def leaf5704Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435771/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356973568) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (611986651/536870912) }, upper := { exponent := 1, mantissa := (1187/1024) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi260LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715696127/68713947136) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf5704InnerLog : WideLogData :=
  innerPair559Data

set_option maxRecDepth 1000000 in
private theorem leaf5704LocalValidity :
    LeafFacts leaf5704Box leaf5704Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5704Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356973568) }) = true
      norm_num [leaf5704Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5704CertificateValid :
    WideCertificateValid leaf5704Box leaf5704Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi260ValidityFacts
    leaf5704LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5704CoverageChecked :
    coverageCheck (innerAD leaf5704Box) leaf5704InnerLog = true := by
  rfl'

private theorem leaf5704InnerLogValid :
    leaf5704InnerLog.Valid 8 (innerAD leaf5704Box) :=
  wideLogDataValid_of_cachedCheck endpoint292PositiveFacts
    endpoint296PositiveFacts.valid leaf5704CoverageChecked

private noncomputable def leaf5704InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907377/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5704InputLogOnePlusV_eq :
    leaf5704InputLogOnePlusV = outerEnclosure 24
      (leaf5704Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5704RoundedFacts : LeafRoundedFacts 8
    leaf5704Certificate.logOnePlusV leaf5704InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5704InputLogOnePlusV_eq }

private noncomputable def leaf5704Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi260InputQChi innerPair559Input
    leaf5704InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5704LowerChecked :
    lowerCheck 24 leaf5704Box leaf5704Inputs = true := by
  rfl'

private theorem leaf5704CoversExact : CoversExact 8
    leaf5704Box leaf5704Certificate leaf5704InnerLog leaf5704Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi260RoundedFacts
    innerPair559RoundedFacts leaf5704RoundedFacts (by rfl)

private theorem leaf5704FlatSound : Sound leaf5704Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5704CertificateValid
    leaf5704InnerLogValid leaf5704CoversExact leaf5704LowerChecked

private noncomputable def leaf5705Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (25/64), chiHi := (51/128) }

private noncomputable def leaf5705Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435767/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356996608) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (609168779/536870912) }, upper := { exponent := 1, mantissa := (9451/8192) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi261LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715719167/68713993216) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf5705InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf5705LocalValidity :
    LeafFacts leaf5705Box leaf5705Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5705Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356996608) }) = true
      norm_num [leaf5705Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5705CertificateValid :
    WideCertificateValid leaf5705Box leaf5705Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi261ValidityFacts
    leaf5705LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5705CoverageChecked :
    coverageCheck (innerAD leaf5705Box) leaf5705InnerLog = true := by
  rfl'

private theorem leaf5705InnerLogValid :
    leaf5705InnerLog.Valid 8 (innerAD leaf5705Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf5705CoverageChecked

private noncomputable def leaf5705InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814751/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5705InputLogOnePlusV_eq :
    leaf5705InputLogOnePlusV = outerEnclosure 24
      (leaf5705Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5705RoundedFacts : LeafRoundedFacts 8
    leaf5705Certificate.logOnePlusV leaf5705InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5705InputLogOnePlusV_eq }

private noncomputable def leaf5705Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi261InputQChi innerPair264Input
    leaf5705InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5705LowerChecked :
    lowerCheck 24 leaf5705Box leaf5705Inputs = true := by
  rfl'

private theorem leaf5705CoversExact : CoversExact 8
    leaf5705Box leaf5705Certificate leaf5705InnerLog leaf5705Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi261RoundedFacts
    innerPair264RoundedFacts leaf5705RoundedFacts (by rfl)

private theorem leaf5705FlatSound : Sound leaf5705Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5705CertificateValid
    leaf5705InnerLogValid leaf5705CoversExact leaf5705LowerChecked

private noncomputable def leaf5706Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (25/64), chiHi := (51/128) }

private noncomputable def leaf5706Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435769/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356970496) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (612445377/536870912) }, upper := { exponent := 1, mantissa := (4751/4096) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi261LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715693055/68713940992) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf5706InnerLog : WideLogData :=
  innerPair563Data

set_option maxRecDepth 1000000 in
private theorem leaf5706LocalValidity :
    LeafFacts leaf5706Box leaf5706Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5706Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356970496) }) = true
      norm_num [leaf5706Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5706CertificateValid :
    WideCertificateValid leaf5706Box leaf5706Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi261ValidityFacts
    leaf5706LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5706CoverageChecked :
    coverageCheck (innerAD leaf5706Box) leaf5706InnerLog = true := by
  rfl'

private theorem leaf5706InnerLogValid :
    leaf5706InnerLog.Valid 8 (innerAD leaf5706Box) :=
  wideLogDataValid_of_cachedCheck endpoint295PositiveFacts
    endpoint296PositiveFacts.valid leaf5706CoverageChecked

private noncomputable def leaf5706InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629509/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5706InputLogOnePlusV_eq :
    leaf5706InputLogOnePlusV = outerEnclosure 24
      (leaf5706Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5706RoundedFacts : LeafRoundedFacts 8
    leaf5706Certificate.logOnePlusV leaf5706InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5706InputLogOnePlusV_eq }

private noncomputable def leaf5706Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi261InputQChi innerPair563Input
    leaf5706InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5706LowerChecked :
    lowerCheck 24 leaf5706Box leaf5706Inputs = true := by
  rfl'

private theorem leaf5706CoversExact : CoversExact 8
    leaf5706Box leaf5706Certificate leaf5706InnerLog leaf5706Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi261RoundedFacts
    innerPair563RoundedFacts leaf5706RoundedFacts (by rfl)

private theorem leaf5706FlatSound : Sound leaf5706Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5706CertificateValid
    leaf5706InnerLogValid leaf5706CoversExact leaf5706LowerChecked

private noncomputable def leaf5707Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (51/128), chiHi := (13/32) }

private noncomputable def leaf5707Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435769/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356942848) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (615984105/536870912) }, upper := { exponent := 1, mantissa := (2389/2048) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi262LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715665407/68713885696) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf5707InnerLog : WideLogData :=
  innerPair265Data

set_option maxRecDepth 1000000 in
private theorem leaf5707LocalValidity :
    LeafFacts leaf5707Box leaf5707Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5707Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356942848) }) = true
      norm_num [leaf5707Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5707CertificateValid :
    WideCertificateValid leaf5707Box leaf5707Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi262ValidityFacts
    leaf5707LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5707CoverageChecked :
    coverageCheck (innerAD leaf5707Box) leaf5707InnerLog = true := by
  rfl'

private theorem leaf5707InnerLogValid :
    leaf5707InnerLog.Valid 8 (innerAD leaf5707Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint77PositiveFacts.valid leaf5707CoverageChecked

private noncomputable def leaf5707InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629515/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5707InputLogOnePlusV_eq :
    leaf5707InputLogOnePlusV = outerEnclosure 24
      (leaf5707Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5707RoundedFacts : LeafRoundedFacts 8
    leaf5707Certificate.logOnePlusV leaf5707InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5707InputLogOnePlusV_eq }

private noncomputable def leaf5707Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi262InputQChi innerPair265Input
    leaf5707InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5707LowerChecked :
    lowerCheck 24 leaf5707Box leaf5707Inputs = true := by
  rfl'

private theorem leaf5707CoversExact : CoversExact 8
    leaf5707Box leaf5707Certificate leaf5707InnerLog leaf5707Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi262RoundedFacts
    innerPair265RoundedFacts leaf5707RoundedFacts (by rfl)

private theorem leaf5707FlatSound : Sound leaf5707Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5707CertificateValid
    leaf5707InnerLogValid leaf5707CoversExact leaf5707LowerChecked

private noncomputable def leaf5708Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (51/128), chiHi := (13/32) }

private noncomputable def leaf5708Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435771/268435456) }, vSqrt := { lower := (65529/65536), upper := (2021101327/2020995072) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (619326235/536870912) }, upper := { exponent := 1, mantissa := (1201/1024) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi262LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (4042096399/4041990144) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf5708InnerLog : WideLogData :=
  innerPair265Data

set_option maxRecDepth 1000000 in
private theorem leaf5708LocalValidity :
    LeafFacts leaf5708Box leaf5708Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5708Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (2021101327/2020995072) }) = true
      norm_num [leaf5708Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5708CertificateValid :
    WideCertificateValid leaf5708Box leaf5708Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi262ValidityFacts
    leaf5708LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5708CoverageChecked :
    coverageCheck (innerAD leaf5708Box) leaf5708InnerLog = true := by
  rfl'

private theorem leaf5708InnerLogValid :
    leaf5708InnerLog.Valid 8 (innerAD leaf5708Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint77PositiveFacts.valid leaf5708CoverageChecked

private noncomputable def leaf5708InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814761/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5708InputLogOnePlusV_eq :
    leaf5708InputLogOnePlusV = outerEnclosure 24
      (leaf5708Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5708RoundedFacts : LeafRoundedFacts 8
    leaf5708Certificate.logOnePlusV leaf5708InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5708InputLogOnePlusV_eq }

private noncomputable def leaf5708Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi262InputQChi innerPair265Input
    leaf5708InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5708LowerChecked :
    lowerCheck 24 leaf5708Box leaf5708Inputs = true := by
  rfl'

private theorem leaf5708CoversExact : CoversExact 8
    leaf5708Box leaf5708Certificate leaf5708InnerLog leaf5708Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi262RoundedFacts
    innerPair265RoundedFacts leaf5708RoundedFacts (by rfl)

private theorem leaf5708FlatSound : Sound leaf5708Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5708CertificateValid
    leaf5708InnerLogValid leaf5708CoversExact leaf5708LowerChecked

private noncomputable def leaf5709Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (25/64), chiHi := (51/128) }

private noncomputable def leaf5709Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435771/268435456) }, vSqrt := { lower := (65529/65536), upper := (4908388937/4908134912) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (615721975/536870912) }, upper := { exponent := 1, mantissa := (9553/8192) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi261LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (9816523849/9816269824) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf5709InnerLog : WideLogData :=
  innerPair564Data

set_option maxRecDepth 1000000 in
private theorem leaf5709LocalValidity :
    LeafFacts leaf5709Box leaf5709Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5709Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4908388937/4908134912) }) = true
      norm_num [leaf5709Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5709CertificateValid :
    WideCertificateValid leaf5709Box leaf5709Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi261ValidityFacts
    leaf5709LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5709CoverageChecked :
    coverageCheck (innerAD leaf5709Box) leaf5709InnerLog = true := by
  rfl'

private theorem leaf5709InnerLogValid :
    leaf5709InnerLog.Valid 8 (innerAD leaf5709Box) :=
  wideLogDataValid_of_cachedCheck endpoint295PositiveFacts
    endpoint297PositiveFacts.valid leaf5709CoverageChecked

private noncomputable def leaf5709InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629515/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5709InputLogOnePlusV_eq :
    leaf5709InputLogOnePlusV = outerEnclosure 24
      (leaf5709Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5709RoundedFacts : LeafRoundedFacts 8
    leaf5709Certificate.logOnePlusV leaf5709InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5709InputLogOnePlusV_eq }

private noncomputable def leaf5709Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi261InputQChi innerPair564Input
    leaf5709InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5709LowerChecked :
    lowerCheck 24 leaf5709Box leaf5709Inputs = true := by
  rfl'

private theorem leaf5709CoversExact : CoversExact 8
    leaf5709Box leaf5709Certificate leaf5709InnerLog leaf5709Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi261RoundedFacts
    innerPair564RoundedFacts leaf5709RoundedFacts (by rfl)

private theorem leaf5709FlatSound : Sound leaf5709Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5709CertificateValid
    leaf5709InnerLogValid leaf5709CoversExact leaf5709LowerChecked

private noncomputable def leaf5710Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (25/64), chiHi := (51/128) }

private noncomputable def leaf5710Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435773/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356918272) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (618998573/536870912) }, upper := { exponent := 1, mantissa := (2401/2048) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi261LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715640831/68713836544) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf5710InnerLog : WideLogData :=
  innerPair573Data

set_option maxRecDepth 1000000 in
private theorem leaf5710LocalValidity :
    LeafFacts leaf5710Box leaf5710Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5710Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356918272) }) = true
      norm_num [leaf5710Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5710CertificateValid :
    WideCertificateValid leaf5710Box leaf5710Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi261ValidityFacts
    leaf5710LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5710CoverageChecked :
    coverageCheck (innerAD leaf5710Box) leaf5710InnerLog = true := by
  rfl'

private theorem leaf5710InnerLogValid :
    leaf5710InnerLog.Valid 8 (innerAD leaf5710Box) :=
  wideLogDataValid_of_cachedCheck endpoint298PositiveFacts
    endpoint299PositiveFacts.valid leaf5710CoverageChecked

private noncomputable def leaf5710InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629521/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5710InputLogOnePlusV_eq :
    leaf5710InputLogOnePlusV = outerEnclosure 24
      (leaf5710Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5710RoundedFacts : LeafRoundedFacts 8
    leaf5710Certificate.logOnePlusV leaf5710InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5710InputLogOnePlusV_eq }

private noncomputable def leaf5710Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi261InputQChi innerPair573Input
    leaf5710InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5710LowerChecked :
    lowerCheck 24 leaf5710Box leaf5710Inputs = true := by
  rfl'

private theorem leaf5710CoversExact : CoversExact 8
    leaf5710Box leaf5710Certificate leaf5710InnerLog leaf5710Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi261RoundedFacts
    innerPair573RoundedFacts leaf5710RoundedFacts (by rfl)

private theorem leaf5710FlatSound : Sound leaf5710Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5710CertificateValid
    leaf5710InnerLogValid leaf5710CoversExact leaf5710LowerChecked

private noncomputable def leaf5711Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (51/128), chiHi := (13/32) }

private noncomputable def leaf5711Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435773/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356889600) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (622668365/536870912) }, upper := { exponent := 1, mantissa := (2415/2048) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi262LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715612159/68713779200) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf5711InnerLog : WideLogData :=
  innerPair272Data

set_option maxRecDepth 1000000 in
private theorem leaf5711LocalValidity :
    LeafFacts leaf5711Box leaf5711Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5711Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356889600) }) = true
      norm_num [leaf5711Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5711CertificateValid :
    WideCertificateValid leaf5711Box leaf5711Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi262ValidityFacts
    leaf5711LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5711CoverageChecked :
    coverageCheck (innerAD leaf5711Box) leaf5711InnerLog = true := by
  rfl'

private theorem leaf5711InnerLogValid :
    leaf5711InnerLog.Valid 8 (innerAD leaf5711Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint77PositiveFacts.valid leaf5711CoverageChecked

private noncomputable def leaf5711InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453691/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf5711InputLogOnePlusV_eq :
    leaf5711InputLogOnePlusV = outerEnclosure 24
      (leaf5711Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5711RoundedFacts : LeafRoundedFacts 8
    leaf5711Certificate.logOnePlusV leaf5711InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5711InputLogOnePlusV_eq }

private noncomputable def leaf5711Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi262InputQChi innerPair272Input
    leaf5711InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5711LowerChecked :
    lowerCheck 24 leaf5711Box leaf5711Inputs = true := by
  rfl'

private theorem leaf5711CoversExact : CoversExact 8
    leaf5711Box leaf5711Certificate leaf5711InnerLog leaf5711Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi262RoundedFacts
    innerPair272RoundedFacts leaf5711RoundedFacts (by rfl)

private theorem leaf5711FlatSound : Sound leaf5711Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5711CertificateValid
    leaf5711InnerLogValid leaf5711CoversExact leaf5711LowerChecked

private noncomputable def leaf5712Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (51/128), chiHi := (13/32) }

private noncomputable def leaf5712Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435775/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356862976) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (626010495/536870912) }, upper := { exponent := 1, mantissa := (607/512) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi262LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715585535/68713725952) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf5712InnerLog : WideLogData :=
  innerPair272Data

set_option maxRecDepth 1000000 in
private theorem leaf5712LocalValidity :
    LeafFacts leaf5712Box leaf5712Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5712Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356862976) }) = true
      norm_num [leaf5712Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5712CertificateValid :
    WideCertificateValid leaf5712Box leaf5712Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi262ValidityFacts
    leaf5712LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5712CoverageChecked :
    coverageCheck (innerAD leaf5712Box) leaf5712InnerLog = true := by
  rfl'

private theorem leaf5712InnerLogValid :
    leaf5712InnerLog.Valid 8 (innerAD leaf5712Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint77PositiveFacts.valid leaf5712CoverageChecked

private noncomputable def leaf5712InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629535/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5712InputLogOnePlusV_eq :
    leaf5712InputLogOnePlusV = outerEnclosure 24
      (leaf5712Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5712RoundedFacts : LeafRoundedFacts 8
    leaf5712Certificate.logOnePlusV leaf5712InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5712InputLogOnePlusV_eq }

private noncomputable def leaf5712Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi262InputQChi innerPair272Input
    leaf5712InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5712LowerChecked :
    lowerCheck 24 leaf5712Box leaf5712Inputs = true := by
  rfl'

private theorem leaf5712CoversExact : CoversExact 8
    leaf5712Box leaf5712Certificate leaf5712InnerLog leaf5712Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi262RoundedFacts
    innerPair272RoundedFacts leaf5712RoundedFacts (by rfl)

private theorem leaf5712FlatSound : Sound leaf5712Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5712CertificateValid
    leaf5712InnerLogValid leaf5712CoversExact leaf5712LowerChecked

private noncomputable def leaf5713Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (3/8), chiHi := (49/128) }

private noncomputable def leaf5713Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435771/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357003776) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (608120263/536870912) }, upper := { exponent := 1, mantissa := (9437/8192) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi259LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715726335/68714007552) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf5713InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf5713LocalValidity :
    LeafFacts leaf5713Box leaf5713Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5713Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357003776) }) = true
      norm_num [leaf5713Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5713CertificateValid :
    WideCertificateValid leaf5713Box leaf5713Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi259ValidityFacts
    leaf5713LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5713CoverageChecked :
    coverageCheck (innerAD leaf5713Box) leaf5713InnerLog = true := by
  rfl'

private theorem leaf5713InnerLogValid :
    leaf5713InnerLog.Valid 8 (innerAD leaf5713Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf5713CoverageChecked

private noncomputable def leaf5713InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907375/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5713InputLogOnePlusV_eq :
    leaf5713InputLogOnePlusV = outerEnclosure 24
      (leaf5713Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5713RoundedFacts : LeafRoundedFacts 8
    leaf5713Certificate.logOnePlusV leaf5713InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5713InputLogOnePlusV_eq }

private noncomputable def leaf5713Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi259InputQChi innerPair264Input
    leaf5713InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5713LowerChecked :
    lowerCheck 24 leaf5713Box leaf5713Inputs = true := by
  rfl'

private theorem leaf5713CoversExact : CoversExact 8
    leaf5713Box leaf5713Certificate leaf5713InnerLog leaf5713Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi259RoundedFacts
    innerPair264RoundedFacts leaf5713RoundedFacts (by rfl)

private theorem leaf5713FlatSound : Sound leaf5713Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5713CertificateValid
    leaf5713InnerLogValid leaf5713CoversExact leaf5713LowerChecked

private noncomputable def leaf5714Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (3/8), chiHi := (49/128) }

private noncomputable def leaf5714Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435773/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356978688) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (611265797/536870912) }, upper := { exponent := 1, mantissa := (4743/4096) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi259LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715701247/68713957376) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf5714InnerLog : WideLogData :=
  innerPair647Data

set_option maxRecDepth 1000000 in
private theorem leaf5714LocalValidity :
    LeafFacts leaf5714Box leaf5714Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5714Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356978688) }) = true
      norm_num [leaf5714Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5714CertificateValid :
    WideCertificateValid leaf5714Box leaf5714Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi259ValidityFacts
    leaf5714LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5714CoverageChecked :
    coverageCheck (innerAD leaf5714Box) leaf5714InnerLog = true := by
  rfl'

private theorem leaf5714InnerLogValid :
    leaf5714InnerLog.Valid 8 (innerAD leaf5714Box) :=
  wideLogDataValid_of_cachedCheck endpoint389PositiveFacts
    endpoint397PositiveFacts.valid leaf5714CoverageChecked

private noncomputable def leaf5714InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629507/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5714InputLogOnePlusV_eq :
    leaf5714InputLogOnePlusV = outerEnclosure 24
      (leaf5714Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5714RoundedFacts : LeafRoundedFacts 8
    leaf5714Certificate.logOnePlusV leaf5714InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5714InputLogOnePlusV_eq }

private noncomputable def leaf5714Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi259InputQChi innerPair647Input
    leaf5714InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5714LowerChecked :
    lowerCheck 24 leaf5714Box leaf5714Inputs = true := by
  rfl'

private theorem leaf5714CoversExact : CoversExact 8
    leaf5714Box leaf5714Certificate leaf5714InnerLog leaf5714Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi259RoundedFacts
    innerPair647RoundedFacts leaf5714RoundedFacts (by rfl)

private theorem leaf5714FlatSound : Sound leaf5714Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5714CertificateValid
    leaf5714InnerLogValid leaf5714CoversExact leaf5714LowerChecked

private noncomputable def leaf5715Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (49/128), chiHi := (25/64) }

private noncomputable def leaf5715Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435773/268435456) }, vSqrt := { lower := (65529/65536), upper := (4908388937/4908135424) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (615197717/536870912) }, upper := { exponent := 1, mantissa := (4773/4096) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi260LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (9816524361/9816270848) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf5715InnerLog : WideLogData :=
  innerPair564Data

set_option maxRecDepth 1000000 in
private theorem leaf5715LocalValidity :
    LeafFacts leaf5715Box leaf5715Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5715Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4908388937/4908135424) }) = true
      norm_num [leaf5715Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5715CertificateValid :
    WideCertificateValid leaf5715Box leaf5715Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi260ValidityFacts
    leaf5715LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5715CoverageChecked :
    coverageCheck (innerAD leaf5715Box) leaf5715InnerLog = true := by
  rfl'

private theorem leaf5715InnerLogValid :
    leaf5715InnerLog.Valid 8 (innerAD leaf5715Box) :=
  wideLogDataValid_of_cachedCheck endpoint295PositiveFacts
    endpoint297PositiveFacts.valid leaf5715CoverageChecked

private noncomputable def leaf5715InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814757/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5715InputLogOnePlusV_eq :
    leaf5715InputLogOnePlusV = outerEnclosure 24
      (leaf5715Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5715RoundedFacts : LeafRoundedFacts 8
    leaf5715Certificate.logOnePlusV leaf5715InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5715InputLogOnePlusV_eq }

private noncomputable def leaf5715Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi260InputQChi innerPair564Input
    leaf5715InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5715LowerChecked :
    lowerCheck 24 leaf5715Box leaf5715Inputs = true := by
  rfl'

private theorem leaf5715CoversExact : CoversExact 8
    leaf5715Box leaf5715Certificate leaf5715InnerLog leaf5715Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi260RoundedFacts
    innerPair564RoundedFacts leaf5715RoundedFacts (by rfl)

private theorem leaf5715FlatSound : Sound leaf5715Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5715CertificateValid
    leaf5715InnerLogValid leaf5715CoversExact leaf5715LowerChecked

private noncomputable def leaf5716Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (49/128), chiHi := (25/64) }

private noncomputable def leaf5716Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435775/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356922368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (618408783/536870912) }, upper := { exponent := 1, mantissa := (2399/2048) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi260LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715644927/68713844736) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf5716InnerLog : WideLogData :=
  innerPair572Data

set_option maxRecDepth 1000000 in
private theorem leaf5716LocalValidity :
    LeafFacts leaf5716Box leaf5716Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5716Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356922368) }) = true
      norm_num [leaf5716Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5716CertificateValid :
    WideCertificateValid leaf5716Box leaf5716Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi260ValidityFacts
    leaf5716LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5716CoverageChecked :
    coverageCheck (innerAD leaf5716Box) leaf5716InnerLog = true := by
  rfl'

private theorem leaf5716InnerLogValid :
    leaf5716InnerLog.Valid 8 (innerAD leaf5716Box) :=
  wideLogDataValid_of_cachedCheck endpoint298PositiveFacts
    endpoint297PositiveFacts.valid leaf5716CoverageChecked

private noncomputable def leaf5716InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (726845/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf5716InputLogOnePlusV_eq :
    leaf5716InputLogOnePlusV = outerEnclosure 24
      (leaf5716Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5716RoundedFacts : LeafRoundedFacts 8
    leaf5716Certificate.logOnePlusV leaf5716InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5716InputLogOnePlusV_eq }

private noncomputable def leaf5716Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi260InputQChi innerPair572Input
    leaf5716InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5716LowerChecked :
    lowerCheck 24 leaf5716Box leaf5716Inputs = true := by
  rfl'

private theorem leaf5716CoversExact : CoversExact 8
    leaf5716Box leaf5716Certificate leaf5716InnerLog leaf5716Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi260RoundedFacts
    innerPair572RoundedFacts leaf5716RoundedFacts (by rfl)

private theorem leaf5716FlatSound : Sound leaf5716Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5716CertificateValid
    leaf5716InnerLogValid leaf5716CoversExact leaf5716LowerChecked

private noncomputable def leaf5717Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (3/8), chiHi := (49/128) }

private noncomputable def leaf5717Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435775/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356953600) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (614411331/536870912) }, upper := { exponent := 1, mantissa := (9535/8192) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi259LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715676159/68713907200) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf5717InnerLog : WideLogData :=
  innerPair563Data

set_option maxRecDepth 1000000 in
private theorem leaf5717LocalValidity :
    LeafFacts leaf5717Box leaf5717Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5717Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356953600) }) = true
      norm_num [leaf5717Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5717CertificateValid :
    WideCertificateValid leaf5717Box leaf5717Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi259ValidityFacts
    leaf5717LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5717CoverageChecked :
    coverageCheck (innerAD leaf5717Box) leaf5717InnerLog = true := by
  rfl'

private theorem leaf5717InnerLogValid :
    leaf5717InnerLog.Valid 8 (innerAD leaf5717Box) :=
  wideLogDataValid_of_cachedCheck endpoint295PositiveFacts
    endpoint296PositiveFacts.valid leaf5717CoverageChecked

private noncomputable def leaf5717InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629513/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5717InputLogOnePlusV_eq :
    leaf5717InputLogOnePlusV = outerEnclosure 24
      (leaf5717Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5717RoundedFacts : LeafRoundedFacts 8
    leaf5717Certificate.logOnePlusV leaf5717InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5717InputLogOnePlusV_eq }

private noncomputable def leaf5717Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi259InputQChi innerPair563Input
    leaf5717InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5717LowerChecked :
    lowerCheck 24 leaf5717Box leaf5717Inputs = true := by
  rfl'

private theorem leaf5717CoversExact : CoversExact 8
    leaf5717Box leaf5717Certificate leaf5717InnerLog leaf5717Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi259RoundedFacts
    innerPair563RoundedFacts leaf5717RoundedFacts (by rfl)

private theorem leaf5717FlatSound : Sound leaf5717Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5717CertificateValid
    leaf5717InnerLogValid leaf5717CoversExact leaf5717LowerChecked

private noncomputable def leaf5718Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (3/8), chiHi := (49/128) }

private noncomputable def leaf5718Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435777/268435456) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356928512) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (617556865/536870912) }, upper := { exponent := 1, mantissa := (599/512) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi259LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715651071/68713857024) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf5718InnerLog : WideLogData :=
  innerPair574Data

set_option maxRecDepth 1000000 in
private theorem leaf5718LocalValidity :
    LeafFacts leaf5718Box leaf5718Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5718Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356928512) }) = true
      norm_num [leaf5718Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5718CertificateValid :
    WideCertificateValid leaf5718Box leaf5718Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi259ValidityFacts
    leaf5718LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5718CoverageChecked :
    coverageCheck (innerAD leaf5718Box) leaf5718InnerLog = true := by
  rfl'

private theorem leaf5718InnerLogValid :
    leaf5718InnerLog.Valid 8 (innerAD leaf5718Box) :=
  wideLogDataValid_of_cachedCheck endpoint298PositiveFacts
    endpoint306PositiveFacts.valid leaf5718CoverageChecked

private noncomputable def leaf5718InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629519/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5718InputLogOnePlusV_eq :
    leaf5718InputLogOnePlusV = outerEnclosure 24
      (leaf5718Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5718RoundedFacts : LeafRoundedFacts 8
    leaf5718Certificate.logOnePlusV leaf5718InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5718InputLogOnePlusV_eq }

private noncomputable def leaf5718Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi259InputQChi innerPair574Input
    leaf5718InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5718LowerChecked :
    lowerCheck 24 leaf5718Box leaf5718Inputs = true := by
  rfl'

private theorem leaf5718CoversExact : CoversExact 8
    leaf5718Box leaf5718Certificate leaf5718InnerLog leaf5718Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi259RoundedFacts
    innerPair574RoundedFacts leaf5718RoundedFacts (by rfl)

private theorem leaf5718FlatSound : Sound leaf5718Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5718CertificateValid
    leaf5718InnerLogValid leaf5718CoversExact leaf5718LowerChecked

private noncomputable def leaf5719Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (49/128), chiHi := (25/64) }

private noncomputable def leaf5719Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435777/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356896768) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (621619849/536870912) }, upper := { exponent := 1, mantissa := (4823/4096) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi260LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715619327/68713793536) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf5719InnerLog : WideLogData :=
  innerPair277Data

set_option maxRecDepth 1000000 in
private theorem leaf5719LocalValidity :
    LeafFacts leaf5719Box leaf5719Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5719Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356896768) }) = true
      norm_num [leaf5719Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5719CertificateValid :
    WideCertificateValid leaf5719Box leaf5719Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi260ValidityFacts
    leaf5719LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5719CoverageChecked :
    coverageCheck (innerAD leaf5719Box) leaf5719InnerLog = true := by
  rfl'

private theorem leaf5719InnerLogValid :
    leaf5719InnerLog.Valid 8 (innerAD leaf5719Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint299PositiveFacts.valid leaf5719CoverageChecked

private noncomputable def leaf5719InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629527/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5719InputLogOnePlusV_eq :
    leaf5719InputLogOnePlusV = outerEnclosure 24
      (leaf5719Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5719RoundedFacts : LeafRoundedFacts 8
    leaf5719Certificate.logOnePlusV leaf5719InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5719InputLogOnePlusV_eq }

private noncomputable def leaf5719Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi260InputQChi innerPair277Input
    leaf5719InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5719LowerChecked :
    lowerCheck 24 leaf5719Box leaf5719Inputs = true := by
  rfl'

private theorem leaf5719CoversExact : CoversExact 8
    leaf5719Box leaf5719Certificate leaf5719InnerLog leaf5719Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi260RoundedFacts
    innerPair277RoundedFacts leaf5719RoundedFacts (by rfl)

private theorem leaf5719FlatSound : Sound leaf5719Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5719CertificateValid
    leaf5719InnerLogValid leaf5719CoversExact leaf5719LowerChecked

private noncomputable def leaf5720Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (49/128), chiHi := (25/64) }

private noncomputable def leaf5720Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435779/268435456) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356871168) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (624830915/536870912) }, upper := { exponent := 1, mantissa := (303/256) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi260LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715593727/68713742336) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf5720InnerLog : WideLogData :=
  innerPair652Data

set_option maxRecDepth 1000000 in
private theorem leaf5720LocalValidity :
    LeafFacts leaf5720Box leaf5720Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5720Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356871168) }) = true
      norm_num [leaf5720Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5720CertificateValid :
    WideCertificateValid leaf5720Box leaf5720Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi260ValidityFacts
    leaf5720LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5720CoverageChecked :
    coverageCheck (innerAD leaf5720Box) leaf5720InnerLog = true := by
  rfl'

private theorem leaf5720InnerLogValid :
    leaf5720InnerLog.Valid 8 (innerAD leaf5720Box) :=
  wideLogDataValid_of_cachedCheck endpoint394PositiveFacts
    endpoint418PositiveFacts.valid leaf5720CoverageChecked

private noncomputable def leaf5720InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629533/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5720InputLogOnePlusV_eq :
    leaf5720InputLogOnePlusV = outerEnclosure 24
      (leaf5720Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5720RoundedFacts : LeafRoundedFacts 8
    leaf5720Certificate.logOnePlusV leaf5720InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5720InputLogOnePlusV_eq }

private noncomputable def leaf5720Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi260InputQChi innerPair652Input
    leaf5720InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5720LowerChecked :
    lowerCheck 24 leaf5720Box leaf5720Inputs = true := by
  rfl'

private theorem leaf5720CoversExact : CoversExact 8
    leaf5720Box leaf5720Certificate leaf5720InnerLog leaf5720Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi260RoundedFacts
    innerPair652RoundedFacts leaf5720RoundedFacts (by rfl)

private theorem leaf5720FlatSound : Sound leaf5720Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5720CertificateValid
    leaf5720InnerLogValid leaf5720CoversExact leaf5720LowerChecked

private noncomputable def leaf5721Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (25/64), chiHi := (51/128) }

private noncomputable def leaf5721Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435775/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356892160) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (622275171/536870912) }, upper := { exponent := 1, mantissa := (9655/8192) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi261LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715614719/68713784320) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf5721InnerLog : WideLogData :=
  innerPair272Data

set_option maxRecDepth 1000000 in
private theorem leaf5721LocalValidity :
    LeafFacts leaf5721Box leaf5721Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5721Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356892160) }) = true
      norm_num [leaf5721Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5721CertificateValid :
    WideCertificateValid leaf5721Box leaf5721Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi261ValidityFacts
    leaf5721LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5721CoverageChecked :
    coverageCheck (innerAD leaf5721Box) leaf5721InnerLog = true := by
  rfl'

private theorem leaf5721InnerLogValid :
    leaf5721InnerLog.Valid 8 (innerAD leaf5721Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint77PositiveFacts.valid leaf5721CoverageChecked

private noncomputable def leaf5721InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453691/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf5721InputLogOnePlusV_eq :
    leaf5721InputLogOnePlusV = outerEnclosure 24
      (leaf5721Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5721RoundedFacts : LeafRoundedFacts 8
    leaf5721Certificate.logOnePlusV leaf5721InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5721InputLogOnePlusV_eq }

private noncomputable def leaf5721Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi261InputQChi innerPair272Input
    leaf5721InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5721LowerChecked :
    lowerCheck 24 leaf5721Box leaf5721Inputs = true := by
  rfl'

private theorem leaf5721CoversExact : CoversExact 8
    leaf5721Box leaf5721Certificate leaf5721InnerLog leaf5721Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi261RoundedFacts
    innerPair272RoundedFacts leaf5721RoundedFacts (by rfl)

private theorem leaf5721FlatSound : Sound leaf5721Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5721CertificateValid
    leaf5721InnerLogValid leaf5721CoversExact leaf5721LowerChecked

private noncomputable def leaf5722Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (25/64), chiHi := (51/128) }

private noncomputable def leaf5722Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435777/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356866048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (625551769/536870912) }, upper := { exponent := 1, mantissa := (4853/4096) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi261LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715588607/68713732096) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf5722InnerLog : WideLogData :=
  innerPair272Data

set_option maxRecDepth 1000000 in
private theorem leaf5722LocalValidity :
    LeafFacts leaf5722Box leaf5722Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5722Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356866048) }) = true
      norm_num [leaf5722Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5722CertificateValid :
    WideCertificateValid leaf5722Box leaf5722Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi261ValidityFacts
    leaf5722LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5722CoverageChecked :
    coverageCheck (innerAD leaf5722Box) leaf5722InnerLog = true := by
  rfl'

private theorem leaf5722InnerLogValid :
    leaf5722InnerLog.Valid 8 (innerAD leaf5722Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint77PositiveFacts.valid leaf5722CoverageChecked

private noncomputable def leaf5722InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814767/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5722InputLogOnePlusV_eq :
    leaf5722InputLogOnePlusV = outerEnclosure 24
      (leaf5722Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5722RoundedFacts : LeafRoundedFacts 8
    leaf5722Certificate.logOnePlusV leaf5722InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5722InputLogOnePlusV_eq }

private noncomputable def leaf5722Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi261InputQChi innerPair272Input
    leaf5722InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5722LowerChecked :
    lowerCheck 24 leaf5722Box leaf5722Inputs = true := by
  rfl'

private theorem leaf5722CoversExact : CoversExact 8
    leaf5722Box leaf5722Certificate leaf5722InnerLog leaf5722Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi261RoundedFacts
    innerPair272RoundedFacts leaf5722RoundedFacts (by rfl)

private theorem leaf5722FlatSound : Sound leaf5722Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5722CertificateValid
    leaf5722InnerLogValid leaf5722CoversExact leaf5722LowerChecked

private noncomputable def leaf5723Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (51/128), chiHi := (13/32) }

private noncomputable def leaf5723Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435777/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356836352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (629352625/536870912) }, upper := { exponent := 1, mantissa := (2441/2048) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi262LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715558911/68713672704) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf5723InnerLog : WideLogData :=
  innerPair569Data

set_option maxRecDepth 1000000 in
private theorem leaf5723LocalValidity :
    LeafFacts leaf5723Box leaf5723Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5723Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356836352) }) = true
      norm_num [leaf5723Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5723CertificateValid :
    WideCertificateValid leaf5723Box leaf5723Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi262ValidityFacts
    leaf5723LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5723CoverageChecked :
    coverageCheck (innerAD leaf5723Box) leaf5723InnerLog = true := by
  rfl'

private theorem leaf5723InnerLogValid :
    leaf5723InnerLog.Valid 8 (innerAD leaf5723Box) :=
  wideLogDataValid_of_cachedCheck endpoint297PositiveFacts
    endpoint304PositiveFacts.valid leaf5723CoverageChecked

private noncomputable def leaf5723InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629541/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5723InputLogOnePlusV_eq :
    leaf5723InputLogOnePlusV = outerEnclosure 24
      (leaf5723Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5723RoundedFacts : LeafRoundedFacts 8
    leaf5723Certificate.logOnePlusV leaf5723InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5723InputLogOnePlusV_eq }

private noncomputable def leaf5723Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi262InputQChi innerPair569Input
    leaf5723InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5723LowerChecked :
    lowerCheck 24 leaf5723Box leaf5723Inputs = true := by
  rfl'

private theorem leaf5723CoversExact : CoversExact 8
    leaf5723Box leaf5723Certificate leaf5723InnerLog leaf5723Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi262RoundedFacts
    innerPair569RoundedFacts leaf5723RoundedFacts (by rfl)

private theorem leaf5723FlatSound : Sound leaf5723Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5723CertificateValid
    leaf5723InnerLogValid leaf5723CoversExact leaf5723LowerChecked

private noncomputable def leaf5724Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (51/128), chiHi := (13/32) }

private noncomputable def leaf5724Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435779/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356809728) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (632694755/536870912) }, upper := { exponent := 1, mantissa := (1227/1024) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi262LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715532287/68713619456) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf5724InnerLog : WideLogData :=
  innerPair570Data

set_option maxRecDepth 1000000 in
private theorem leaf5724LocalValidity :
    LeafFacts leaf5724Box leaf5724Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5724Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356809728) }) = true
      norm_num [leaf5724Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5724CertificateValid :
    WideCertificateValid leaf5724Box leaf5724Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi262ValidityFacts
    leaf5724LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5724CoverageChecked :
    coverageCheck (innerAD leaf5724Box) leaf5724InnerLog = true := by
  rfl'

private theorem leaf5724InnerLogValid :
    leaf5724InnerLog.Valid 8 (innerAD leaf5724Box) :=
  wideLogDataValid_of_cachedCheck endpoint297PositiveFacts
    endpoint305PositiveFacts.valid leaf5724CoverageChecked

private noncomputable def leaf5724InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907387/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5724InputLogOnePlusV_eq :
    leaf5724InputLogOnePlusV = outerEnclosure 24
      (leaf5724Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5724RoundedFacts : LeafRoundedFacts 8
    leaf5724Certificate.logOnePlusV leaf5724InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5724InputLogOnePlusV_eq }

private noncomputable def leaf5724Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi262InputQChi innerPair570Input
    leaf5724InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5724LowerChecked :
    lowerCheck 24 leaf5724Box leaf5724Inputs = true := by
  rfl'

private theorem leaf5724CoversExact : CoversExact 8
    leaf5724Box leaf5724Certificate leaf5724InnerLog leaf5724Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi262RoundedFacts
    innerPair570RoundedFacts leaf5724RoundedFacts (by rfl)

private theorem leaf5724FlatSound : Sound leaf5724Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5724CertificateValid
    leaf5724InnerLogValid leaf5724CoversExact leaf5724LowerChecked

private noncomputable def leaf5725Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (25/64), chiHi := (51/128) }

private noncomputable def leaf5725Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435779/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356839936) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (628828367/536870912) }, upper := { exponent := 1, mantissa := (9757/8192) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi261LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715562495/68713679872) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf5725InnerLog : WideLogData :=
  innerPair567Data

set_option maxRecDepth 1000000 in
private theorem leaf5725LocalValidity :
    LeafFacts leaf5725Box leaf5725Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5725Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356839936) }) = true
      norm_num [leaf5725Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5725CertificateValid :
    WideCertificateValid leaf5725Box leaf5725Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi261ValidityFacts
    leaf5725LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5725CoverageChecked :
    coverageCheck (innerAD leaf5725Box) leaf5725InnerLog = true := by
  rfl'

private theorem leaf5725InnerLogValid :
    leaf5725InnerLog.Valid 8 (innerAD leaf5725Box) :=
  wideLogDataValid_of_cachedCheck endpoint296PositiveFacts
    endpoint304PositiveFacts.valid leaf5725CoverageChecked

private noncomputable def leaf5725InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907385/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5725InputLogOnePlusV_eq :
    leaf5725InputLogOnePlusV = outerEnclosure 24
      (leaf5725Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5725RoundedFacts : LeafRoundedFacts 8
    leaf5725Certificate.logOnePlusV leaf5725InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5725InputLogOnePlusV_eq }

private noncomputable def leaf5725Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi261InputQChi innerPair567Input
    leaf5725InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5725LowerChecked :
    lowerCheck 24 leaf5725Box leaf5725Inputs = true := by
  rfl'

private theorem leaf5725CoversExact : CoversExact 8
    leaf5725Box leaf5725Certificate leaf5725InnerLog leaf5725Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi261RoundedFacts
    innerPair567RoundedFacts leaf5725RoundedFacts (by rfl)

private theorem leaf5725FlatSound : Sound leaf5725Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5725CertificateValid
    leaf5725InnerLogValid leaf5725CoversExact leaf5725LowerChecked

private noncomputable def leaf5726Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (25/64), chiHi := (51/128) }

private noncomputable def leaf5726Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435781/268435456) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356813824) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (632104965/536870912) }, upper := { exponent := 1, mantissa := (613/512) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi261LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715536383/68713627648) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf5726InnerLog : WideLogData :=
  innerPair570Data

set_option maxRecDepth 1000000 in
private theorem leaf5726LocalValidity :
    LeafFacts leaf5726Box leaf5726Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5726Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356813824) }) = true
      norm_num [leaf5726Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5726CertificateValid :
    WideCertificateValid leaf5726Box leaf5726Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi261ValidityFacts
    leaf5726LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5726CoverageChecked :
    coverageCheck (innerAD leaf5726Box) leaf5726InnerLog = true := by
  rfl'

private theorem leaf5726InnerLogValid :
    leaf5726InnerLog.Valid 8 (innerAD leaf5726Box) :=
  wideLogDataValid_of_cachedCheck endpoint297PositiveFacts
    endpoint305PositiveFacts.valid leaf5726CoverageChecked

private noncomputable def leaf5726InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629547/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5726InputLogOnePlusV_eq :
    leaf5726InputLogOnePlusV = outerEnclosure 24
      (leaf5726Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5726RoundedFacts : LeafRoundedFacts 8
    leaf5726Certificate.logOnePlusV leaf5726InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5726InputLogOnePlusV_eq }

private noncomputable def leaf5726Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi261InputQChi innerPair570Input
    leaf5726InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5726LowerChecked :
    lowerCheck 24 leaf5726Box leaf5726Inputs = true := by
  rfl'

private theorem leaf5726CoversExact : CoversExact 8
    leaf5726Box leaf5726Certificate leaf5726InnerLog leaf5726Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi261RoundedFacts
    innerPair570RoundedFacts leaf5726RoundedFacts (by rfl)

private theorem leaf5726FlatSound : Sound leaf5726Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5726CertificateValid
    leaf5726InnerLogValid leaf5726CoversExact leaf5726LowerChecked

private noncomputable def leaf5727Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (51/128), chiHi := (13/32) }

private noncomputable def leaf5727Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435781/268435456) }, vSqrt := { lower := (65529/65536), upper := (4908388937/4908111872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (636036885/536870912) }, upper := { exponent := 1, mantissa := (2467/2048) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi262LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (9816500809/9816223744) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf5727InnerLog : WideLogData :=
  innerPair577Data

set_option maxRecDepth 1000000 in
private theorem leaf5727LocalValidity :
    LeafFacts leaf5727Box leaf5727Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5727Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4908388937/4908111872) }) = true
      norm_num [leaf5727Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5727CertificateValid :
    WideCertificateValid leaf5727Box leaf5727Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi262ValidityFacts
    leaf5727LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5727CoverageChecked :
    coverageCheck (innerAD leaf5727Box) leaf5727InnerLog = true := by
  rfl'

private theorem leaf5727InnerLogValid :
    leaf5727InnerLog.Valid 8 (innerAD leaf5727Box) :=
  wideLogDataValid_of_cachedCheck endpoint299PositiveFacts
    endpoint308PositiveFacts.valid leaf5727CoverageChecked

private noncomputable def leaf5727InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814777/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5727InputLogOnePlusV_eq :
    leaf5727InputLogOnePlusV = outerEnclosure 24
      (leaf5727Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5727RoundedFacts : LeafRoundedFacts 8
    leaf5727Certificate.logOnePlusV leaf5727InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5727InputLogOnePlusV_eq }

private noncomputable def leaf5727Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi262InputQChi innerPair577Input
    leaf5727InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5727LowerChecked :
    lowerCheck 24 leaf5727Box leaf5727Inputs = true := by
  rfl'

private theorem leaf5727CoversExact : CoversExact 8
    leaf5727Box leaf5727Certificate leaf5727InnerLog leaf5727Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi262RoundedFacts
    innerPair577RoundedFacts leaf5727RoundedFacts (by rfl)

private theorem leaf5727FlatSound : Sound leaf5727Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5727CertificateValid
    leaf5727InnerLogValid leaf5727CoversExact leaf5727LowerChecked

private noncomputable def leaf5728Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (51/128), chiHi := (13/32) }

private noncomputable def leaf5728Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435783/268435456) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356756480) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (639379015/536870912) }, upper := { exponent := 1, mantissa := (155/128) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi262LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715479039/68713512960) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf5728InnerLog : WideLogData :=
  innerPair278Data

set_option maxRecDepth 1000000 in
private theorem leaf5728LocalValidity :
    LeafFacts leaf5728Box leaf5728Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5728Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356756480) }) = true
      norm_num [leaf5728Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5728CertificateValid :
    WideCertificateValid leaf5728Box leaf5728Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi262ValidityFacts
    leaf5728LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5728CoverageChecked :
    coverageCheck (innerAD leaf5728Box) leaf5728InnerLog = true := by
  rfl'

private theorem leaf5728InnerLogValid :
    leaf5728InnerLog.Valid 8 (innerAD leaf5728Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint78PositiveFacts.valid leaf5728CoverageChecked

private noncomputable def leaf5728InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629561/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5728InputLogOnePlusV_eq :
    leaf5728InputLogOnePlusV = outerEnclosure 24
      (leaf5728Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5728RoundedFacts : LeafRoundedFacts 8
    leaf5728Certificate.logOnePlusV leaf5728InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5728InputLogOnePlusV_eq }

private noncomputable def leaf5728Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi262InputQChi innerPair278Input
    leaf5728InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5728LowerChecked :
    lowerCheck 24 leaf5728Box leaf5728Inputs = true := by
  rfl'

private theorem leaf5728CoversExact : CoversExact 8
    leaf5728Box leaf5728Certificate leaf5728InnerLog leaf5728Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi262RoundedFacts
    innerPair278RoundedFacts leaf5728RoundedFacts (by rfl)

private theorem leaf5728FlatSound : Sound leaf5728Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5728CertificateValid
    leaf5728InnerLogValid leaf5728CoversExact leaf5728LowerChecked

private noncomputable def leaf5729Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (13/32), chiHi := (53/128) }

private noncomputable def leaf5729Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435771/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356889088) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (622799431/536870912) }, upper := { exponent := 1, mantissa := (9661/8192) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi263LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715611647/68713778176) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf5729InnerLog : WideLogData :=
  innerPair272Data

set_option maxRecDepth 1000000 in
private theorem leaf5729LocalValidity :
    LeafFacts leaf5729Box leaf5729Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5729Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356889088) }) = true
      norm_num [leaf5729Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5729CertificateValid :
    WideCertificateValid leaf5729Box leaf5729Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi263ValidityFacts
    leaf5729LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5729CoverageChecked :
    coverageCheck (innerAD leaf5729Box) leaf5729InnerLog = true := by
  rfl'

private theorem leaf5729InnerLogValid :
    leaf5729InnerLog.Valid 8 (innerAD leaf5729Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint77PositiveFacts.valid leaf5729CoverageChecked

private noncomputable def leaf5729InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453691/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf5729InputLogOnePlusV_eq :
    leaf5729InputLogOnePlusV = outerEnclosure 24
      (leaf5729Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5729RoundedFacts : LeafRoundedFacts 8
    leaf5729Certificate.logOnePlusV leaf5729InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5729InputLogOnePlusV_eq }

private noncomputable def leaf5729Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi263InputQChi innerPair272Input
    leaf5729InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5729LowerChecked :
    lowerCheck 24 leaf5729Box leaf5729Inputs = true := by
  rfl'

private theorem leaf5729CoversExact : CoversExact 8
    leaf5729Box leaf5729Certificate leaf5729InnerLog leaf5729Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi263RoundedFacts
    innerPair272RoundedFacts leaf5729RoundedFacts (by rfl)

private theorem leaf5729FlatSound : Sound leaf5729Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5729CertificateValid
    leaf5729InnerLogValid leaf5729CoversExact leaf5729LowerChecked

private noncomputable def leaf5730Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (13/32), chiHi := (53/128) }

private noncomputable def leaf5730Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435773/268435456) }, vSqrt := { lower := (65529/65536), upper := (4908388937/4908123136) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (626207093/536870912) }, upper := { exponent := 1, mantissa := (4857/4096) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi263LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (9816512073/9816246272) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf5730InnerLog : WideLogData :=
  innerPair272Data

set_option maxRecDepth 1000000 in
private theorem leaf5730LocalValidity :
    LeafFacts leaf5730Box leaf5730Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5730Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4908388937/4908123136) }) = true
      norm_num [leaf5730Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5730CertificateValid :
    WideCertificateValid leaf5730Box leaf5730Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi263ValidityFacts
    leaf5730LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5730CoverageChecked :
    coverageCheck (innerAD leaf5730Box) leaf5730InnerLog = true := by
  rfl'

private theorem leaf5730InnerLogValid :
    leaf5730InnerLog.Valid 8 (innerAD leaf5730Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint77PositiveFacts.valid leaf5730CoverageChecked

private noncomputable def leaf5730InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629535/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5730InputLogOnePlusV_eq :
    leaf5730InputLogOnePlusV = outerEnclosure 24
      (leaf5730Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5730RoundedFacts : LeafRoundedFacts 8
    leaf5730Certificate.logOnePlusV leaf5730InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5730InputLogOnePlusV_eq }

private noncomputable def leaf5730Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi263InputQChi innerPair272Input
    leaf5730InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5730LowerChecked :
    lowerCheck 24 leaf5730Box leaf5730Inputs = true := by
  rfl'

private theorem leaf5730CoversExact : CoversExact 8
    leaf5730Box leaf5730Certificate leaf5730InnerLog leaf5730Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi263RoundedFacts
    innerPair272RoundedFacts leaf5730RoundedFacts (by rfl)

private theorem leaf5730FlatSound : Sound leaf5730Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5730CertificateValid
    leaf5730InnerLogValid leaf5730CoversExact leaf5730LowerChecked

private noncomputable def leaf5731Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (53/128), chiHi := (27/64) }

private noncomputable def leaf5731Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435773/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356835328) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (629614757/536870912) }, upper := { exponent := 1, mantissa := (4883/4096) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi264LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715557887/68713670656) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf5731InnerLog : WideLogData :=
  innerPair273Data

set_option maxRecDepth 1000000 in
private theorem leaf5731LocalValidity :
    LeafFacts leaf5731Box leaf5731Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5731Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356835328) }) = true
      norm_num [leaf5731Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5731CertificateValid :
    WideCertificateValid leaf5731Box leaf5731Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi264ValidityFacts
    leaf5731LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5731CoverageChecked :
    coverageCheck (innerAD leaf5731Box) leaf5731InnerLog = true := by
  rfl'

private theorem leaf5731InnerLogValid :
    leaf5731InnerLog.Valid 8 (innerAD leaf5731Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint78PositiveFacts.valid leaf5731CoverageChecked

private noncomputable def leaf5731InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814771/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5731InputLogOnePlusV_eq :
    leaf5731InputLogOnePlusV = outerEnclosure 24
      (leaf5731Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5731RoundedFacts : LeafRoundedFacts 8
    leaf5731Certificate.logOnePlusV leaf5731InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5731InputLogOnePlusV_eq }

private noncomputable def leaf5731Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi264InputQChi innerPair273Input
    leaf5731InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5731LowerChecked :
    lowerCheck 24 leaf5731Box leaf5731Inputs = true := by
  rfl'

private theorem leaf5731CoversExact : CoversExact 8
    leaf5731Box leaf5731Certificate leaf5731InnerLog leaf5731Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi264RoundedFacts
    innerPair273RoundedFacts leaf5731RoundedFacts (by rfl)

private theorem leaf5731FlatSound : Sound leaf5731Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5731CertificateValid
    leaf5731InnerLogValid leaf5731CoversExact leaf5731LowerChecked

private noncomputable def leaf5732Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (53/128), chiHi := (27/64) }

private noncomputable def leaf5732Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435775/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356807680) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (633087951/536870912) }, upper := { exponent := 1, mantissa := (2455/2048) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi264LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715530239/68713615360) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf5732InnerLog : WideLogData :=
  innerPair273Data

set_option maxRecDepth 1000000 in
private theorem leaf5732LocalValidity :
    LeafFacts leaf5732Box leaf5732Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5732Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356807680) }) = true
      norm_num [leaf5732Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5732CertificateValid :
    WideCertificateValid leaf5732Box leaf5732Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi264ValidityFacts
    leaf5732LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5732CoverageChecked :
    coverageCheck (innerAD leaf5732Box) leaf5732InnerLog = true := by
  rfl'

private theorem leaf5732InnerLogValid :
    leaf5732InnerLog.Valid 8 (innerAD leaf5732Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint78PositiveFacts.valid leaf5732CoverageChecked

private noncomputable def leaf5732InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907387/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5732InputLogOnePlusV_eq :
    leaf5732InputLogOnePlusV = outerEnclosure 24
      (leaf5732Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5732RoundedFacts : LeafRoundedFacts 8
    leaf5732Certificate.logOnePlusV leaf5732InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5732InputLogOnePlusV_eq }

private noncomputable def leaf5732Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi264InputQChi innerPair273Input
    leaf5732InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5732LowerChecked :
    lowerCheck 24 leaf5732Box leaf5732Inputs = true := by
  rfl'

private theorem leaf5732CoversExact : CoversExact 8
    leaf5732Box leaf5732Certificate leaf5732InnerLog leaf5732Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi264RoundedFacts
    innerPair273RoundedFacts leaf5732RoundedFacts (by rfl)

private theorem leaf5732FlatSound : Sound leaf5732Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5732CertificateValid
    leaf5732InnerLogValid leaf5732CoversExact leaf5732LowerChecked

private noncomputable def leaf5733Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (13/32), chiHi := (53/128) }

private noncomputable def leaf5733Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435775/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356834816) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (629614755/536870912) }, upper := { exponent := 1, mantissa := (9767/8192) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi263LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715557375/68713669632) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf5733InnerLog : WideLogData :=
  innerPair569Data

set_option maxRecDepth 1000000 in
private theorem leaf5733LocalValidity :
    LeafFacts leaf5733Box leaf5733Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5733Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356834816) }) = true
      norm_num [leaf5733Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5733CertificateValid :
    WideCertificateValid leaf5733Box leaf5733Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi263ValidityFacts
    leaf5733LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5733CoverageChecked :
    coverageCheck (innerAD leaf5733Box) leaf5733InnerLog = true := by
  rfl'

private theorem leaf5733InnerLogValid :
    leaf5733InnerLog.Valid 8 (innerAD leaf5733Box) :=
  wideLogDataValid_of_cachedCheck endpoint297PositiveFacts
    endpoint304PositiveFacts.valid leaf5733CoverageChecked

private noncomputable def leaf5733InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814771/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5733InputLogOnePlusV_eq :
    leaf5733InputLogOnePlusV = outerEnclosure 24
      (leaf5733Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5733RoundedFacts : LeafRoundedFacts 8
    leaf5733Certificate.logOnePlusV leaf5733InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5733InputLogOnePlusV_eq }

private noncomputable def leaf5733Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi263InputQChi innerPair569Input
    leaf5733InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5733LowerChecked :
    lowerCheck 24 leaf5733Box leaf5733Inputs = true := by
  rfl'

private theorem leaf5733CoversExact : CoversExact 8
    leaf5733Box leaf5733Certificate leaf5733InnerLog leaf5733Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi263RoundedFacts
    innerPair569RoundedFacts leaf5733RoundedFacts (by rfl)

private theorem leaf5733FlatSound : Sound leaf5733Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5733CertificateValid
    leaf5733InnerLogValid leaf5733CoversExact leaf5733LowerChecked

private noncomputable def leaf5734Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (13/32), chiHi := (53/128) }

private noncomputable def leaf5734Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435777/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356807680) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (633022417/536870912) }, upper := { exponent := 1, mantissa := (2455/2048) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi263LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715530239/68713615360) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf5734InnerLog : WideLogData :=
  innerPair570Data

set_option maxRecDepth 1000000 in
private theorem leaf5734LocalValidity :
    LeafFacts leaf5734Box leaf5734Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5734Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356807680) }) = true
      norm_num [leaf5734Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5734CertificateValid :
    WideCertificateValid leaf5734Box leaf5734Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi263ValidityFacts
    leaf5734LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5734CoverageChecked :
    coverageCheck (innerAD leaf5734Box) leaf5734InnerLog = true := by
  rfl'

private theorem leaf5734InnerLogValid :
    leaf5734InnerLog.Valid 8 (innerAD leaf5734Box) :=
  wideLogDataValid_of_cachedCheck endpoint297PositiveFacts
    endpoint305PositiveFacts.valid leaf5734CoverageChecked

private noncomputable def leaf5734InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907387/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5734InputLogOnePlusV_eq :
    leaf5734InputLogOnePlusV = outerEnclosure 24
      (leaf5734Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5734RoundedFacts : LeafRoundedFacts 8
    leaf5734Certificate.logOnePlusV leaf5734InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5734InputLogOnePlusV_eq }

private noncomputable def leaf5734Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi263InputQChi innerPair570Input
    leaf5734InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5734LowerChecked :
    lowerCheck 24 leaf5734Box leaf5734Inputs = true := by
  rfl'

private theorem leaf5734CoversExact : CoversExact 8
    leaf5734Box leaf5734Certificate leaf5734InnerLog leaf5734Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi263RoundedFacts
    innerPair570RoundedFacts leaf5734RoundedFacts (by rfl)

private theorem leaf5734FlatSound : Sound leaf5734Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5734CertificateValid
    leaf5734InnerLogValid leaf5734CoversExact leaf5734LowerChecked

private noncomputable def leaf5735Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (53/128), chiHi := (27/64) }

private noncomputable def leaf5735Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435777/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356780032) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (636561145/536870912) }, upper := { exponent := 1, mantissa := (4937/4096) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi264LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715502591/68713560064) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf5735InnerLog : WideLogData :=
  innerPair273Data

set_option maxRecDepth 1000000 in
private theorem leaf5735LocalValidity :
    LeafFacts leaf5735Box leaf5735Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5735Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356780032) }) = true
      norm_num [leaf5735Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5735CertificateValid :
    WideCertificateValid leaf5735Box leaf5735Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi264ValidityFacts
    leaf5735LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5735CoverageChecked :
    coverageCheck (innerAD leaf5735Box) leaf5735InnerLog = true := by
  rfl'

private theorem leaf5735InnerLogValid :
    leaf5735InnerLog.Valid 8 (innerAD leaf5735Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint78PositiveFacts.valid leaf5735CoverageChecked

private noncomputable def leaf5735InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629555/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5735InputLogOnePlusV_eq :
    leaf5735InputLogOnePlusV = outerEnclosure 24
      (leaf5735Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5735RoundedFacts : LeafRoundedFacts 8
    leaf5735Certificate.logOnePlusV leaf5735InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5735InputLogOnePlusV_eq }

private noncomputable def leaf5735Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi264InputQChi innerPair273Input
    leaf5735InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5735LowerChecked :
    lowerCheck 24 leaf5735Box leaf5735Inputs = true := by
  rfl'

private theorem leaf5735CoversExact : CoversExact 8
    leaf5735Box leaf5735Certificate leaf5735InnerLog leaf5735Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi264RoundedFacts
    innerPair273RoundedFacts leaf5735RoundedFacts (by rfl)

private theorem leaf5735FlatSound : Sound leaf5735Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5735CertificateValid
    leaf5735InnerLogValid leaf5735CoversExact leaf5735LowerChecked

private noncomputable def leaf5736Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (53/128), chiHi := (27/64) }

private noncomputable def leaf5736Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435779/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356752384) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (640034339/536870912) }, upper := { exponent := 1, mantissa := (1241/1024) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi264LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715474943/68713504768) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf5736InnerLog : WideLogData :=
  innerPair278Data

set_option maxRecDepth 1000000 in
private theorem leaf5736LocalValidity :
    LeafFacts leaf5736Box leaf5736Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5736Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356752384) }) = true
      norm_num [leaf5736Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5736CertificateValid :
    WideCertificateValid leaf5736Box leaf5736Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi264ValidityFacts
    leaf5736LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5736CoverageChecked :
    coverageCheck (innerAD leaf5736Box) leaf5736InnerLog = true := by
  rfl'

private theorem leaf5736InnerLogValid :
    leaf5736InnerLog.Valid 8 (innerAD leaf5736Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint78PositiveFacts.valid leaf5736CoverageChecked

private noncomputable def leaf5736InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814781/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5736InputLogOnePlusV_eq :
    leaf5736InputLogOnePlusV = outerEnclosure 24
      (leaf5736Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5736RoundedFacts : LeafRoundedFacts 8
    leaf5736Certificate.logOnePlusV leaf5736InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5736InputLogOnePlusV_eq }

private noncomputable def leaf5736Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi264InputQChi innerPair278Input
    leaf5736InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5736LowerChecked :
    lowerCheck 24 leaf5736Box leaf5736Inputs = true := by
  rfl'

private theorem leaf5736CoversExact : CoversExact 8
    leaf5736Box leaf5736Certificate leaf5736InnerLog leaf5736Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi264RoundedFacts
    innerPair278RoundedFacts leaf5736RoundedFacts (by rfl)

private theorem leaf5736FlatSound : Sound leaf5736Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5736CertificateValid
    leaf5736InnerLogValid leaf5736CoversExact leaf5736LowerChecked

private noncomputable def leaf5737Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (27/64), chiHi := (55/128) }

private noncomputable def leaf5737Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435775/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356781568) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (636430083/536870912) }, upper := { exponent := 1, mantissa := (9871/8192) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi265LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715504127/68713563136) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf5737InnerLog : WideLogData :=
  innerPair273Data

set_option maxRecDepth 1000000 in
private theorem leaf5737LocalValidity :
    LeafFacts leaf5737Box leaf5737Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5737Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356781568) }) = true
      norm_num [leaf5737Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5737CertificateValid :
    WideCertificateValid leaf5737Box leaf5737Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi265ValidityFacts
    leaf5737LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5737CoverageChecked :
    coverageCheck (innerAD leaf5737Box) leaf5737InnerLog = true := by
  rfl'

private theorem leaf5737InnerLogValid :
    leaf5737InnerLog.Valid 8 (innerAD leaf5737Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint78PositiveFacts.valid leaf5737CoverageChecked

private noncomputable def leaf5737InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629555/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5737InputLogOnePlusV_eq :
    leaf5737InputLogOnePlusV = outerEnclosure 24
      (leaf5737Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5737RoundedFacts : LeafRoundedFacts 8
    leaf5737Certificate.logOnePlusV leaf5737InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5737InputLogOnePlusV_eq }

private noncomputable def leaf5737Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi265InputQChi innerPair273Input
    leaf5737InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5737LowerChecked :
    lowerCheck 24 leaf5737Box leaf5737Inputs = true := by
  rfl'

private theorem leaf5737CoversExact : CoversExact 8
    leaf5737Box leaf5737Certificate leaf5737InnerLog leaf5737Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi265RoundedFacts
    innerPair273RoundedFacts leaf5737RoundedFacts (by rfl)

private theorem leaf5737FlatSound : Sound leaf5737Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5737CertificateValid
    leaf5737InnerLogValid leaf5737CoversExact leaf5737LowerChecked

private noncomputable def leaf5738Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (27/64), chiHi := (55/128) }

private noncomputable def leaf5738Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435777/268435456) }, vSqrt := { lower := (65529/65536), upper := (1108345889/1108282368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (639968809/536870912) }, upper := { exponent := 1, mantissa := (4963/4096) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi265LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (2216628257/2216564736) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf5738InnerLog : WideLogData :=
  innerPair278Data

set_option maxRecDepth 1000000 in
private theorem leaf5738LocalValidity :
    LeafFacts leaf5738Box leaf5738Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5738Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (1108345889/1108282368) }) = true
      norm_num [leaf5738Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5738CertificateValid :
    WideCertificateValid leaf5738Box leaf5738Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi265ValidityFacts
    leaf5738LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5738CoverageChecked :
    coverageCheck (innerAD leaf5738Box) leaf5738InnerLog = true := by
  rfl'

private theorem leaf5738InnerLogValid :
    leaf5738InnerLog.Valid 8 (innerAD leaf5738Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint78PositiveFacts.valid leaf5738CoverageChecked

private noncomputable def leaf5738InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814781/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5738InputLogOnePlusV_eq :
    leaf5738InputLogOnePlusV = outerEnclosure 24
      (leaf5738Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5738RoundedFacts : LeafRoundedFacts 8
    leaf5738Certificate.logOnePlusV leaf5738InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5738InputLogOnePlusV_eq }

private noncomputable def leaf5738Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi265InputQChi innerPair278Input
    leaf5738InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5738LowerChecked :
    lowerCheck 24 leaf5738Box leaf5738Inputs = true := by
  rfl'

private theorem leaf5738CoversExact : CoversExact 8
    leaf5738Box leaf5738Certificate leaf5738InnerLog leaf5738Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi265RoundedFacts
    innerPair278RoundedFacts leaf5738RoundedFacts (by rfl)

private theorem leaf5738FlatSound : Sound leaf5738Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5738CertificateValid
    leaf5738InnerLogValid leaf5738CoversExact leaf5738LowerChecked

private noncomputable def leaf5739Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (55/128), chiHi := (7/16) }

private noncomputable def leaf5739Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435777/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356727808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (643245409/536870912) }, upper := { exponent := 1, mantissa := (1247/1024) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi266LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715450367/68713455616) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf5739InnerLog : WideLogData :=
  innerPair278Data

set_option maxRecDepth 1000000 in
private theorem leaf5739LocalValidity :
    LeafFacts leaf5739Box leaf5739Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5739Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356727808) }) = true
      norm_num [leaf5739Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5739CertificateValid :
    WideCertificateValid leaf5739Box leaf5739Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi266ValidityFacts
    leaf5739LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5739CoverageChecked :
    coverageCheck (innerAD leaf5739Box) leaf5739InnerLog = true := by
  rfl'

private theorem leaf5739InnerLogValid :
    leaf5739InnerLog.Valid 8 (innerAD leaf5739Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint78PositiveFacts.valid leaf5739CoverageChecked

private noncomputable def leaf5739InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11357/16384) }

set_option maxRecDepth 1000000 in
private theorem leaf5739InputLogOnePlusV_eq :
    leaf5739InputLogOnePlusV = outerEnclosure 24
      (leaf5739Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5739RoundedFacts : LeafRoundedFacts 8
    leaf5739Certificate.logOnePlusV leaf5739InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5739InputLogOnePlusV_eq }

private noncomputable def leaf5739Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi266InputQChi innerPair278Input
    leaf5739InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5739LowerChecked :
    lowerCheck 24 leaf5739Box leaf5739Inputs = true := by
  rfl'

private theorem leaf5739CoversExact : CoversExact 8
    leaf5739Box leaf5739Certificate leaf5739InnerLog leaf5739Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi266RoundedFacts
    innerPair278RoundedFacts leaf5739RoundedFacts (by rfl)

private theorem leaf5739FlatSound : Sound leaf5739Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5739CertificateValid
    leaf5739InnerLogValid leaf5739CoversExact leaf5739LowerChecked

private noncomputable def leaf5740Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (55/128), chiHi := (7/16) }

private noncomputable def leaf5740Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435779/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356699136) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (646849667/536870912) }, upper := { exponent := 1, mantissa := (627/512) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi266LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715421695/68713398272) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf5740InnerLog : WideLogData :=
  innerPair279Data

set_option maxRecDepth 1000000 in
private theorem leaf5740LocalValidity :
    LeafFacts leaf5740Box leaf5740Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5740Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356699136) }) = true
      norm_num [leaf5740Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5740CertificateValid :
    WideCertificateValid leaf5740Box leaf5740Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi266ValidityFacts
    leaf5740LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5740CoverageChecked :
    coverageCheck (innerAD leaf5740Box) leaf5740InnerLog = true := by
  rfl'

private theorem leaf5740InnerLogValid :
    leaf5740InnerLog.Valid 8 (innerAD leaf5740Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint79PositiveFacts.valid leaf5740CoverageChecked

private noncomputable def leaf5740InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629575/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5740InputLogOnePlusV_eq :
    leaf5740InputLogOnePlusV = outerEnclosure 24
      (leaf5740Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5740RoundedFacts : LeafRoundedFacts 8
    leaf5740Certificate.logOnePlusV leaf5740InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5740InputLogOnePlusV_eq }

private noncomputable def leaf5740Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi266InputQChi innerPair279Input
    leaf5740InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5740LowerChecked :
    lowerCheck 24 leaf5740Box leaf5740Inputs = true := by
  rfl'

private theorem leaf5740CoversExact : CoversExact 8
    leaf5740Box leaf5740Certificate leaf5740InnerLog leaf5740Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi266RoundedFacts
    innerPair279RoundedFacts leaf5740RoundedFacts (by rfl)

private theorem leaf5740FlatSound : Sound leaf5740Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5740CertificateValid
    leaf5740InnerLogValid leaf5740CoversExact leaf5740LowerChecked

private noncomputable def leaf5741Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (27/64), chiHi := (55/128) }

private noncomputable def leaf5741Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435779/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356725248) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (643507535/536870912) }, upper := { exponent := 1, mantissa := (9981/8192) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi265LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715447807/68713450496) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf5741InnerLog : WideLogData :=
  innerPair278Data

set_option maxRecDepth 1000000 in
private theorem leaf5741LocalValidity :
    LeafFacts leaf5741Box leaf5741Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5741Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356725248) }) = true
      norm_num [leaf5741Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5741CertificateValid :
    WideCertificateValid leaf5741Box leaf5741Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi265ValidityFacts
    leaf5741LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5741CoverageChecked :
    coverageCheck (innerAD leaf5741Box) leaf5741InnerLog = true := by
  rfl'

private theorem leaf5741InnerLogValid :
    leaf5741InnerLog.Valid 8 (innerAD leaf5741Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint78PositiveFacts.valid leaf5741CoverageChecked

private noncomputable def leaf5741InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11357/16384) }

set_option maxRecDepth 1000000 in
private theorem leaf5741InputLogOnePlusV_eq :
    leaf5741InputLogOnePlusV = outerEnclosure 24
      (leaf5741Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5741RoundedFacts : LeafRoundedFacts 8
    leaf5741Certificate.logOnePlusV leaf5741InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5741InputLogOnePlusV_eq }

private noncomputable def leaf5741Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi265InputQChi innerPair278Input
    leaf5741InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5741LowerChecked :
    lowerCheck 24 leaf5741Box leaf5741Inputs = true := by
  rfl'

private theorem leaf5741CoversExact : CoversExact 8
    leaf5741Box leaf5741Certificate leaf5741InnerLog leaf5741Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi265RoundedFacts
    innerPair278RoundedFacts leaf5741RoundedFacts (by rfl)

private theorem leaf5741FlatSound : Sound leaf5741Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5741CertificateValid
    leaf5741InnerLogValid leaf5741CoversExact leaf5741LowerChecked

private noncomputable def leaf5742Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (27/64), chiHi := (55/128) }

private noncomputable def leaf5742Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435781/268435456) }, vSqrt := { lower := (65529/65536), upper := (4908388937/4908099584) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (647046261/536870912) }, upper := { exponent := 1, mantissa := (2509/2048) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi265LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (9816488521/9816199168) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf5742InnerLog : WideLogData :=
  innerPair279Data

set_option maxRecDepth 1000000 in
private theorem leaf5742LocalValidity :
    LeafFacts leaf5742Box leaf5742Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5742Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4908388937/4908099584) }) = true
      norm_num [leaf5742Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5742CertificateValid :
    WideCertificateValid leaf5742Box leaf5742Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi265ValidityFacts
    leaf5742LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5742CoverageChecked :
    coverageCheck (innerAD leaf5742Box) leaf5742InnerLog = true := by
  rfl'

private theorem leaf5742InnerLogValid :
    leaf5742InnerLog.Valid 8 (innerAD leaf5742Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint79PositiveFacts.valid leaf5742CoverageChecked

private noncomputable def leaf5742InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629575/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5742InputLogOnePlusV_eq :
    leaf5742InputLogOnePlusV = outerEnclosure 24
      (leaf5742Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5742RoundedFacts : LeafRoundedFacts 8
    leaf5742Certificate.logOnePlusV leaf5742InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5742InputLogOnePlusV_eq }

private noncomputable def leaf5742Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi265InputQChi innerPair279Input
    leaf5742InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5742LowerChecked :
    lowerCheck 24 leaf5742Box leaf5742Inputs = true := by
  rfl'

private theorem leaf5742CoversExact : CoversExact 8
    leaf5742Box leaf5742Certificate leaf5742InnerLog leaf5742Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi265RoundedFacts
    innerPair279RoundedFacts leaf5742RoundedFacts (by rfl)

private theorem leaf5742FlatSound : Sound leaf5742Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5742CertificateValid
    leaf5742InnerLogValid leaf5742CoversExact leaf5742LowerChecked

private noncomputable def leaf5743Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (55/128), chiHi := (7/16) }

private noncomputable def leaf5743Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435781/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356670464) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (650453925/536870912) }, upper := { exponent := 1, mantissa := (1261/1024) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi266LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715393023/68713340928) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf5743InnerLog : WideLogData :=
  innerPair279Data

set_option maxRecDepth 1000000 in
private theorem leaf5743LocalValidity :
    LeafFacts leaf5743Box leaf5743Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5743Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356670464) }) = true
      norm_num [leaf5743Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5743CertificateValid :
    WideCertificateValid leaf5743Box leaf5743Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi266ValidityFacts
    leaf5743LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5743CoverageChecked :
    coverageCheck (innerAD leaf5743Box) leaf5743InnerLog = true := by
  rfl'

private theorem leaf5743InnerLogValid :
    leaf5743InnerLog.Valid 8 (innerAD leaf5743Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint79PositiveFacts.valid leaf5743CoverageChecked

private noncomputable def leaf5743InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814791/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5743InputLogOnePlusV_eq :
    leaf5743InputLogOnePlusV = outerEnclosure 24
      (leaf5743Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5743RoundedFacts : LeafRoundedFacts 8
    leaf5743Certificate.logOnePlusV leaf5743InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5743InputLogOnePlusV_eq }

private noncomputable def leaf5743Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi266InputQChi innerPair279Input
    leaf5743InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5743LowerChecked :
    lowerCheck 24 leaf5743Box leaf5743Inputs = true := by
  rfl'

private theorem leaf5743CoversExact : CoversExact 8
    leaf5743Box leaf5743Certificate leaf5743InnerLog leaf5743Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi266RoundedFacts
    innerPair279RoundedFacts leaf5743RoundedFacts (by rfl)

private theorem leaf5743FlatSound : Sound leaf5743Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5743CertificateValid
    leaf5743InnerLogValid leaf5743CoversExact leaf5743LowerChecked

private noncomputable def leaf5744Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (55/128), chiHi := (7/16) }

private noncomputable def leaf5744Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435783/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356641792) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (654058183/536870912) }, upper := { exponent := 1, mantissa := (317/256) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi266LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715364351/68713283584) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf5744InnerLog : WideLogData :=
  innerPair279Data

set_option maxRecDepth 1000000 in
private theorem leaf5744LocalValidity :
    LeafFacts leaf5744Box leaf5744Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5744Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356641792) }) = true
      norm_num [leaf5744Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5744CertificateValid :
    WideCertificateValid leaf5744Box leaf5744Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi266ValidityFacts
    leaf5744LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5744CoverageChecked :
    coverageCheck (innerAD leaf5744Box) leaf5744InnerLog = true := by
  rfl'

private theorem leaf5744InnerLogValid :
    leaf5744InnerLog.Valid 8 (innerAD leaf5744Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint79PositiveFacts.valid leaf5744CoverageChecked

private noncomputable def leaf5744InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629589/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5744InputLogOnePlusV_eq :
    leaf5744InputLogOnePlusV = outerEnclosure 24
      (leaf5744Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5744RoundedFacts : LeafRoundedFacts 8
    leaf5744Certificate.logOnePlusV leaf5744InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5744InputLogOnePlusV_eq }

private noncomputable def leaf5744Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi266InputQChi innerPair279Input
    leaf5744InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5744LowerChecked :
    lowerCheck 24 leaf5744Box leaf5744Inputs = true := by
  rfl'

private theorem leaf5744CoversExact : CoversExact 8
    leaf5744Box leaf5744Certificate leaf5744InnerLog leaf5744Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi266RoundedFacts
    innerPair279RoundedFacts leaf5744RoundedFacts (by rfl)

private theorem leaf5744FlatSound : Sound leaf5744Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5744CertificateValid
    leaf5744InnerLogValid leaf5744CoversExact leaf5744LowerChecked

private noncomputable def leaf5745Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (13/32), chiHi := (53/128) }

private noncomputable def leaf5745Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435779/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356780544) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (636430079/536870912) }, upper := { exponent := 1, mantissa := (9873/8192) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi263LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715503103/68713561088) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf5745InnerLog : WideLogData :=
  innerPair273Data

set_option maxRecDepth 1000000 in
private theorem leaf5745LocalValidity :
    LeafFacts leaf5745Box leaf5745Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5745Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356780544) }) = true
      norm_num [leaf5745Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5745CertificateValid :
    WideCertificateValid leaf5745Box leaf5745Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi263ValidityFacts
    leaf5745LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5745CoverageChecked :
    coverageCheck (innerAD leaf5745Box) leaf5745InnerLog = true := by
  rfl'

private theorem leaf5745InnerLogValid :
    leaf5745InnerLog.Valid 8 (innerAD leaf5745Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint78PositiveFacts.valid leaf5745CoverageChecked

private noncomputable def leaf5745InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629555/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5745InputLogOnePlusV_eq :
    leaf5745InputLogOnePlusV = outerEnclosure 24
      (leaf5745Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5745RoundedFacts : LeafRoundedFacts 8
    leaf5745Certificate.logOnePlusV leaf5745InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5745InputLogOnePlusV_eq }

private noncomputable def leaf5745Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi263InputQChi innerPair273Input
    leaf5745InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5745LowerChecked :
    lowerCheck 24 leaf5745Box leaf5745Inputs = true := by
  rfl'

private theorem leaf5745CoversExact : CoversExact 8
    leaf5745Box leaf5745Certificate leaf5745InnerLog leaf5745Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi263RoundedFacts
    innerPair273RoundedFacts leaf5745RoundedFacts (by rfl)

private theorem leaf5745FlatSound : Sound leaf5745Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5745CertificateValid
    leaf5745InnerLogValid leaf5745CoversExact leaf5745LowerChecked

private noncomputable def leaf5746Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (13/32), chiHi := (53/128) }

private noncomputable def leaf5746Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435781/268435456) }, vSqrt := { lower := (65529/65536), upper := (1108345889/1108282368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (639837741/536870912) }, upper := { exponent := 1, mantissa := (4963/4096) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi263LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (2216628257/2216564736) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf5746InnerLog : WideLogData :=
  innerPair278Data

set_option maxRecDepth 1000000 in
private theorem leaf5746LocalValidity :
    LeafFacts leaf5746Box leaf5746Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5746Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (1108345889/1108282368) }) = true
      norm_num [leaf5746Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5746CertificateValid :
    WideCertificateValid leaf5746Box leaf5746Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi263ValidityFacts
    leaf5746LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5746CoverageChecked :
    coverageCheck (innerAD leaf5746Box) leaf5746InnerLog = true := by
  rfl'

private theorem leaf5746InnerLogValid :
    leaf5746InnerLog.Valid 8 (innerAD leaf5746Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint78PositiveFacts.valid leaf5746CoverageChecked

private noncomputable def leaf5746InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814781/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5746InputLogOnePlusV_eq :
    leaf5746InputLogOnePlusV = outerEnclosure 24
      (leaf5746Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5746RoundedFacts : LeafRoundedFacts 8
    leaf5746Certificate.logOnePlusV leaf5746InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5746InputLogOnePlusV_eq }

private noncomputable def leaf5746Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi263InputQChi innerPair278Input
    leaf5746InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5746LowerChecked :
    lowerCheck 24 leaf5746Box leaf5746Inputs = true := by
  rfl'

private theorem leaf5746CoversExact : CoversExact 8
    leaf5746Box leaf5746Certificate leaf5746InnerLog leaf5746Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi263RoundedFacts
    innerPair278RoundedFacts leaf5746RoundedFacts (by rfl)

private theorem leaf5746FlatSound : Sound leaf5746Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5746CertificateValid
    leaf5746InnerLogValid leaf5746CoversExact leaf5746LowerChecked

private noncomputable def leaf5747Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (53/128), chiHi := (27/64) }

private noncomputable def leaf5747Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435781/268435456) }, vSqrt := { lower := (65529/65536), upper := (2021101327/2020983808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (643507533/536870912) }, upper := { exponent := 1, mantissa := (4991/4096) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi264LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (4042085135/4041967616) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf5747InnerLog : WideLogData :=
  innerPair278Data

set_option maxRecDepth 1000000 in
private theorem leaf5747LocalValidity :
    LeafFacts leaf5747Box leaf5747Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5747Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (2021101327/2020983808) }) = true
      norm_num [leaf5747Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5747CertificateValid :
    WideCertificateValid leaf5747Box leaf5747Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi264ValidityFacts
    leaf5747LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5747CoverageChecked :
    coverageCheck (innerAD leaf5747Box) leaf5747InnerLog = true := by
  rfl'

private theorem leaf5747InnerLogValid :
    leaf5747InnerLog.Valid 8 (innerAD leaf5747Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint78PositiveFacts.valid leaf5747CoverageChecked

private noncomputable def leaf5747InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629569/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5747InputLogOnePlusV_eq :
    leaf5747InputLogOnePlusV = outerEnclosure 24
      (leaf5747Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5747RoundedFacts : LeafRoundedFacts 8
    leaf5747Certificate.logOnePlusV leaf5747InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5747InputLogOnePlusV_eq }

private noncomputable def leaf5747Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi264InputQChi innerPair278Input
    leaf5747InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5747LowerChecked :
    lowerCheck 24 leaf5747Box leaf5747Inputs = true := by
  rfl'

private theorem leaf5747CoversExact : CoversExact 8
    leaf5747Box leaf5747Certificate leaf5747InnerLog leaf5747Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi264RoundedFacts
    innerPair278RoundedFacts leaf5747RoundedFacts (by rfl)

private theorem leaf5747FlatSound : Sound leaf5747Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5747CertificateValid
    leaf5747InnerLogValid leaf5747CoversExact leaf5747LowerChecked

private noncomputable def leaf5748Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (53/128), chiHi := (27/64) }

private noncomputable def leaf5748Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435783/268435456) }, vSqrt := { lower := (65529/65536), upper := (4908388937/4908099584) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (646980727/536870912) }, upper := { exponent := 1, mantissa := (2509/2048) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi264LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (9816488521/9816199168) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf5748InnerLog : WideLogData :=
  innerPair590Data

set_option maxRecDepth 1000000 in
private theorem leaf5748LocalValidity :
    LeafFacts leaf5748Box leaf5748Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5748Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4908388937/4908099584) }) = true
      norm_num [leaf5748Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5748CertificateValid :
    WideCertificateValid leaf5748Box leaf5748Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi264ValidityFacts
    leaf5748LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5748CoverageChecked :
    coverageCheck (innerAD leaf5748Box) leaf5748InnerLog = true := by
  rfl'

private theorem leaf5748InnerLogValid :
    leaf5748InnerLog.Valid 8 (innerAD leaf5748Box) :=
  wideLogDataValid_of_cachedCheck endpoint305PositiveFacts
    endpoint403PositiveFacts.valid leaf5748CoverageChecked

private noncomputable def leaf5748InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629575/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5748InputLogOnePlusV_eq :
    leaf5748InputLogOnePlusV = outerEnclosure 24
      (leaf5748Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5748RoundedFacts : LeafRoundedFacts 8
    leaf5748Certificate.logOnePlusV leaf5748InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5748InputLogOnePlusV_eq }

private noncomputable def leaf5748Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi264InputQChi innerPair590Input
    leaf5748InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5748LowerChecked :
    lowerCheck 24 leaf5748Box leaf5748Inputs = true := by
  rfl'

private theorem leaf5748CoversExact : CoversExact 8
    leaf5748Box leaf5748Certificate leaf5748InnerLog leaf5748Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi264RoundedFacts
    innerPair590RoundedFacts leaf5748RoundedFacts (by rfl)

private theorem leaf5748FlatSound : Sound leaf5748Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5748CertificateValid
    leaf5748InnerLogValid leaf5748CoversExact leaf5748LowerChecked

private noncomputable def leaf5749Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (13/32), chiHi := (53/128) }

private noncomputable def leaf5749Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435783/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356726272) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (643245403/536870912) }, upper := { exponent := 1, mantissa := (9979/8192) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi263LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715448831/68713452544) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf5749InnerLog : WideLogData :=
  innerPair278Data

set_option maxRecDepth 1000000 in
private theorem leaf5749LocalValidity :
    LeafFacts leaf5749Box leaf5749Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5749Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356726272) }) = true
      norm_num [leaf5749Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5749CertificateValid :
    WideCertificateValid leaf5749Box leaf5749Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi263ValidityFacts
    leaf5749LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5749CoverageChecked :
    coverageCheck (innerAD leaf5749Box) leaf5749InnerLog = true := by
  rfl'

private theorem leaf5749InnerLogValid :
    leaf5749InnerLog.Valid 8 (innerAD leaf5749Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint78PositiveFacts.valid leaf5749CoverageChecked

private noncomputable def leaf5749InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11357/16384) }

set_option maxRecDepth 1000000 in
private theorem leaf5749InputLogOnePlusV_eq :
    leaf5749InputLogOnePlusV = outerEnclosure 24
      (leaf5749Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5749RoundedFacts : LeafRoundedFacts 8
    leaf5749Certificate.logOnePlusV leaf5749InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5749InputLogOnePlusV_eq }

private noncomputable def leaf5749Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi263InputQChi innerPair278Input
    leaf5749InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5749LowerChecked :
    lowerCheck 24 leaf5749Box leaf5749Inputs = true := by
  rfl'

private theorem leaf5749CoversExact : CoversExact 8
    leaf5749Box leaf5749Certificate leaf5749InnerLog leaf5749Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi263RoundedFacts
    innerPair278RoundedFacts leaf5749RoundedFacts (by rfl)

private theorem leaf5749FlatSound : Sound leaf5749Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5749CertificateValid
    leaf5749InnerLogValid leaf5749CoversExact leaf5749LowerChecked

private noncomputable def leaf5750Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (13/32), chiHi := (53/128) }

private noncomputable def leaf5750Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435785/268435456) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356699136) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (646653065/536870912) }, upper := { exponent := 1, mantissa := (627/512) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi263LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715421695/68713398272) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf5750InnerLog : WideLogData :=
  innerPair590Data

set_option maxRecDepth 1000000 in
private theorem leaf5750LocalValidity :
    LeafFacts leaf5750Box leaf5750Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5750Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356699136) }) = true
      norm_num [leaf5750Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5750CertificateValid :
    WideCertificateValid leaf5750Box leaf5750Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi263ValidityFacts
    leaf5750LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5750CoverageChecked :
    coverageCheck (innerAD leaf5750Box) leaf5750InnerLog = true := by
  rfl'

private theorem leaf5750InnerLogValid :
    leaf5750InnerLog.Valid 8 (innerAD leaf5750Box) :=
  wideLogDataValid_of_cachedCheck endpoint305PositiveFacts
    endpoint403PositiveFacts.valid leaf5750CoverageChecked

private noncomputable def leaf5750InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629575/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5750InputLogOnePlusV_eq :
    leaf5750InputLogOnePlusV = outerEnclosure 24
      (leaf5750Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5750RoundedFacts : LeafRoundedFacts 8
    leaf5750Certificate.logOnePlusV leaf5750InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5750InputLogOnePlusV_eq }

private noncomputable def leaf5750Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi263InputQChi innerPair590Input
    leaf5750InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5750LowerChecked :
    lowerCheck 24 leaf5750Box leaf5750Inputs = true := by
  rfl'

private theorem leaf5750CoversExact : CoversExact 8
    leaf5750Box leaf5750Certificate leaf5750InnerLog leaf5750Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi263RoundedFacts
    innerPair590RoundedFacts leaf5750RoundedFacts (by rfl)

private theorem leaf5750FlatSound : Sound leaf5750Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5750CertificateValid
    leaf5750InnerLogValid leaf5750CoversExact leaf5750LowerChecked

private noncomputable def leaf5751Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (53/128), chiHi := (27/64) }

private noncomputable def leaf5751Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435785/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356669440) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (650453921/536870912) }, upper := { exponent := 1, mantissa := (5045/4096) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi264LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715391999/68713338880) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf5751InnerLog : WideLogData :=
  innerPair592Data

set_option maxRecDepth 1000000 in
private theorem leaf5751LocalValidity :
    LeafFacts leaf5751Box leaf5751Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5751Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356669440) }) = true
      norm_num [leaf5751Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5751CertificateValid :
    WideCertificateValid leaf5751Box leaf5751Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi264ValidityFacts
    leaf5751LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5751CoverageChecked :
    coverageCheck (innerAD leaf5751Box) leaf5751InnerLog = true := by
  rfl'

private theorem leaf5751InnerLogValid :
    leaf5751InnerLog.Valid 8 (innerAD leaf5751Box) :=
  wideLogDataValid_of_cachedCheck endpoint308PositiveFacts
    endpoint94PositiveFacts.valid leaf5751CoverageChecked

private noncomputable def leaf5751InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814791/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5751InputLogOnePlusV_eq :
    leaf5751InputLogOnePlusV = outerEnclosure 24
      (leaf5751Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5751RoundedFacts : LeafRoundedFacts 8
    leaf5751Certificate.logOnePlusV leaf5751InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5751InputLogOnePlusV_eq }

private noncomputable def leaf5751Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi264InputQChi innerPair592Input
    leaf5751InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5751LowerChecked :
    lowerCheck 24 leaf5751Box leaf5751Inputs = true := by
  rfl'

private theorem leaf5751CoversExact : CoversExact 8
    leaf5751Box leaf5751Certificate leaf5751InnerLog leaf5751Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi264RoundedFacts
    innerPair592RoundedFacts leaf5751RoundedFacts (by rfl)

private theorem leaf5751FlatSound : Sound leaf5751Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5751CertificateValid
    leaf5751InnerLogValid leaf5751CoversExact leaf5751LowerChecked

private noncomputable def leaf5752Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (53/128), chiHi := (27/64) }

private noncomputable def leaf5752Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435787/268435456) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356641792) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (653927115/536870912) }, upper := { exponent := 1, mantissa := (317/256) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi264LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715364351/68713283584) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf5752InnerLog : WideLogData :=
  innerPair279Data

set_option maxRecDepth 1000000 in
private theorem leaf5752LocalValidity :
    LeafFacts leaf5752Box leaf5752Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5752Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356641792) }) = true
      norm_num [leaf5752Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5752CertificateValid :
    WideCertificateValid leaf5752Box leaf5752Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi264ValidityFacts
    leaf5752LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5752CoverageChecked :
    coverageCheck (innerAD leaf5752Box) leaf5752InnerLog = true := by
  rfl'

private theorem leaf5752InnerLogValid :
    leaf5752InnerLog.Valid 8 (innerAD leaf5752Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint79PositiveFacts.valid leaf5752CoverageChecked

private noncomputable def leaf5752InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629589/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5752InputLogOnePlusV_eq :
    leaf5752InputLogOnePlusV = outerEnclosure 24
      (leaf5752Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5752RoundedFacts : LeafRoundedFacts 8
    leaf5752Certificate.logOnePlusV leaf5752InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5752InputLogOnePlusV_eq }

private noncomputable def leaf5752Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi264InputQChi innerPair279Input
    leaf5752InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5752LowerChecked :
    lowerCheck 24 leaf5752Box leaf5752Inputs = true := by
  rfl'

private theorem leaf5752CoversExact : CoversExact 8
    leaf5752Box leaf5752Certificate leaf5752InnerLog leaf5752Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi264RoundedFacts
    innerPair279RoundedFacts leaf5752RoundedFacts (by rfl)

private theorem leaf5752FlatSound : Sound leaf5752Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5752CertificateValid
    leaf5752InnerLogValid leaf5752CoversExact leaf5752LowerChecked

private noncomputable def leaf5753Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (27/64), chiHi := (55/128) }

private noncomputable def leaf5753Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435783/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356668928) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (650584987/536870912) }, upper := { exponent := 1, mantissa := (10091/8192) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi265LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715391487/68713337856) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf5753InnerLog : WideLogData :=
  innerPair279Data

set_option maxRecDepth 1000000 in
private theorem leaf5753LocalValidity :
    LeafFacts leaf5753Box leaf5753Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5753Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356668928) }) = true
      norm_num [leaf5753Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5753CertificateValid :
    WideCertificateValid leaf5753Box leaf5753Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi265ValidityFacts
    leaf5753LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5753CoverageChecked :
    coverageCheck (innerAD leaf5753Box) leaf5753InnerLog = true := by
  rfl'

private theorem leaf5753InnerLogValid :
    leaf5753InnerLog.Valid 8 (innerAD leaf5753Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint79PositiveFacts.valid leaf5753CoverageChecked

private noncomputable def leaf5753InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814791/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5753InputLogOnePlusV_eq :
    leaf5753InputLogOnePlusV = outerEnclosure 24
      (leaf5753Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5753RoundedFacts : LeafRoundedFacts 8
    leaf5753Certificate.logOnePlusV leaf5753InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5753InputLogOnePlusV_eq }

private noncomputable def leaf5753Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi265InputQChi innerPair279Input
    leaf5753InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5753LowerChecked :
    lowerCheck 24 leaf5753Box leaf5753Inputs = true := by
  rfl'

private theorem leaf5753CoversExact : CoversExact 8
    leaf5753Box leaf5753Certificate leaf5753InnerLog leaf5753Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi265RoundedFacts
    innerPair279RoundedFacts leaf5753RoundedFacts (by rfl)

private theorem leaf5753FlatSound : Sound leaf5753Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5753CertificateValid
    leaf5753InnerLogValid leaf5753CoversExact leaf5753LowerChecked

private noncomputable def leaf5754Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (27/64), chiHi := (55/128) }

private noncomputable def leaf5754Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435785/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356640768) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (654123713/536870912) }, upper := { exponent := 1, mantissa := (5073/4096) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi265LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715363327/68713281536) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf5754InnerLog : WideLogData :=
  innerPair279Data

set_option maxRecDepth 1000000 in
private theorem leaf5754LocalValidity :
    LeafFacts leaf5754Box leaf5754Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5754Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356640768) }) = true
      norm_num [leaf5754Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5754CertificateValid :
    WideCertificateValid leaf5754Box leaf5754Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi265ValidityFacts
    leaf5754LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5754CoverageChecked :
    coverageCheck (innerAD leaf5754Box) leaf5754InnerLog = true := by
  rfl'

private theorem leaf5754InnerLogValid :
    leaf5754InnerLog.Valid 8 (innerAD leaf5754Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint79PositiveFacts.valid leaf5754CoverageChecked

private noncomputable def leaf5754InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629589/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5754InputLogOnePlusV_eq :
    leaf5754InputLogOnePlusV = outerEnclosure 24
      (leaf5754Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5754RoundedFacts : LeafRoundedFacts 8
    leaf5754Certificate.logOnePlusV leaf5754InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5754InputLogOnePlusV_eq }

private noncomputable def leaf5754Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi265InputQChi innerPair279Input
    leaf5754InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5754LowerChecked :
    lowerCheck 24 leaf5754Box leaf5754Inputs = true := by
  rfl'

private theorem leaf5754CoversExact : CoversExact 8
    leaf5754Box leaf5754Certificate leaf5754InnerLog leaf5754Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi265RoundedFacts
    innerPair279RoundedFacts leaf5754RoundedFacts (by rfl)

private theorem leaf5754FlatSound : Sound leaf5754Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5754CertificateValid
    leaf5754InnerLogValid leaf5754CoversExact leaf5754LowerChecked

private noncomputable def leaf5755Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (55/128), chiHi := (7/16) }

private noncomputable def leaf5755Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435785/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68713226240) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (657662441/536870912) }, upper := { exponent := 1, mantissa := (1275/1024) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi266LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429622781/137426452480) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf5755InnerLog : WideLogData :=
  innerPair285Data

set_option maxRecDepth 1000000 in
private theorem leaf5755LocalValidity :
    LeafFacts leaf5755Box leaf5755Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5755Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68713226240) }) = true
      norm_num [leaf5755Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5755CertificateValid :
    WideCertificateValid leaf5755Box leaf5755Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi266ValidityFacts
    leaf5755LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5755CoverageChecked :
    coverageCheck (innerAD leaf5755Box) leaf5755InnerLog = true := by
  rfl'

private theorem leaf5755InnerLogValid :
    leaf5755InnerLog.Valid 8 (innerAD leaf5755Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint79PositiveFacts.valid leaf5755CoverageChecked

private noncomputable def leaf5755InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907367/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5755InputLogOnePlusV_eq :
    leaf5755InputLogOnePlusV = outerEnclosure 24
      (leaf5755Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5755RoundedFacts : LeafRoundedFacts 8
    leaf5755Certificate.logOnePlusV leaf5755InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5755InputLogOnePlusV_eq }

private noncomputable def leaf5755Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi266InputQChi innerPair285Input
    leaf5755InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5755LowerChecked :
    lowerCheck 24 leaf5755Box leaf5755Inputs = true := by
  rfl'

private theorem leaf5755CoversExact : CoversExact 8
    leaf5755Box leaf5755Certificate leaf5755InnerLog leaf5755Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi266RoundedFacts
    innerPair285RoundedFacts leaf5755RoundedFacts (by rfl)

private theorem leaf5755FlatSound : Sound leaf5755Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5755CertificateValid
    leaf5755InnerLogValid leaf5755CoversExact leaf5755LowerChecked

private noncomputable def leaf5756Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (55/128), chiHi := (7/16) }

private noncomputable def leaf5756Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435787/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68713168896) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (661266699/536870912) }, upper := { exponent := 1, mantissa := (641/512) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi266LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429565437/137426337792) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf5756InnerLog : WideLogData :=
  innerPair658Data

set_option maxRecDepth 1000000 in
private theorem leaf5756LocalValidity :
    LeafFacts leaf5756Box leaf5756Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5756Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68713168896) }) = true
      norm_num [leaf5756Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5756CertificateValid :
    WideCertificateValid leaf5756Box leaf5756Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi266ValidityFacts
    leaf5756LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5756CoverageChecked :
    coverageCheck (innerAD leaf5756Box) leaf5756InnerLog = true := by
  rfl'

private theorem leaf5756InnerLogValid :
    leaf5756InnerLog.Valid 8 (innerAD leaf5756Box) :=
  wideLogDataValid_of_cachedCheck endpoint403PositiveFacts
    endpoint419PositiveFacts.valid leaf5756CoverageChecked

private noncomputable def leaf5756InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629475/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5756InputLogOnePlusV_eq :
    leaf5756InputLogOnePlusV = outerEnclosure 24
      (leaf5756Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5756RoundedFacts : LeafRoundedFacts 8
    leaf5756Certificate.logOnePlusV leaf5756InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5756InputLogOnePlusV_eq }

private noncomputable def leaf5756Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi266InputQChi innerPair658Input
    leaf5756InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5756LowerChecked :
    lowerCheck 24 leaf5756Box leaf5756Inputs = true := by
  rfl'

private theorem leaf5756CoversExact : CoversExact 8
    leaf5756Box leaf5756Certificate leaf5756InnerLog leaf5756Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi266RoundedFacts
    innerPair658RoundedFacts leaf5756RoundedFacts (by rfl)

private theorem leaf5756FlatSound : Sound leaf5756Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5756CertificateValid
    leaf5756InnerLogValid leaf5756CoversExact leaf5756LowerChecked

private noncomputable def leaf5757Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (27/64), chiHi := (55/128) }

private noncomputable def leaf5757Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435787/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68713225216) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (657662439/536870912) }, upper := { exponent := 1, mantissa := (10201/8192) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi265LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429621757/137426450432) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf5757InnerLog : WideLogData :=
  innerPair285Data

set_option maxRecDepth 1000000 in
private theorem leaf5757LocalValidity :
    LeafFacts leaf5757Box leaf5757Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5757Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68713225216) }) = true
      norm_num [leaf5757Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5757CertificateValid :
    WideCertificateValid leaf5757Box leaf5757Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi265ValidityFacts
    leaf5757LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5757CoverageChecked :
    coverageCheck (innerAD leaf5757Box) leaf5757InnerLog = true := by
  rfl'

private theorem leaf5757InnerLogValid :
    leaf5757InnerLog.Valid 8 (innerAD leaf5757Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint79PositiveFacts.valid leaf5757CoverageChecked

private noncomputable def leaf5757InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907367/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5757InputLogOnePlusV_eq :
    leaf5757InputLogOnePlusV = outerEnclosure 24
      (leaf5757Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5757RoundedFacts : LeafRoundedFacts 8
    leaf5757Certificate.logOnePlusV leaf5757InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5757InputLogOnePlusV_eq }

private noncomputable def leaf5757Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi265InputQChi innerPair285Input
    leaf5757InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5757LowerChecked :
    lowerCheck 24 leaf5757Box leaf5757Inputs = true := by
  rfl'

private theorem leaf5757CoversExact : CoversExact 8
    leaf5757Box leaf5757Certificate leaf5757InnerLog leaf5757Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi265RoundedFacts
    innerPair285RoundedFacts leaf5757RoundedFacts (by rfl)

private theorem leaf5757FlatSound : Sound leaf5757Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5757CertificateValid
    leaf5757InnerLogValid leaf5757CoversExact leaf5757LowerChecked

private noncomputable def leaf5758Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (27/64), chiHi := (55/128) }

private noncomputable def leaf5758Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435789/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68713168896) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (661201165/536870912) }, upper := { exponent := 1, mantissa := (641/512) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi265LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429565437/137426337792) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf5758InnerLog : WideLogData :=
  innerPair658Data

set_option maxRecDepth 1000000 in
private theorem leaf5758LocalValidity :
    LeafFacts leaf5758Box leaf5758Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5758Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68713168896) }) = true
      norm_num [leaf5758Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5758CertificateValid :
    WideCertificateValid leaf5758Box leaf5758Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi265ValidityFacts
    leaf5758LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5758CoverageChecked :
    coverageCheck (innerAD leaf5758Box) leaf5758InnerLog = true := by
  rfl'

private theorem leaf5758InnerLogValid :
    leaf5758InnerLog.Valid 8 (innerAD leaf5758Box) :=
  wideLogDataValid_of_cachedCheck endpoint403PositiveFacts
    endpoint419PositiveFacts.valid leaf5758CoverageChecked

private noncomputable def leaf5758InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629475/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5758InputLogOnePlusV_eq :
    leaf5758InputLogOnePlusV = outerEnclosure 24
      (leaf5758Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5758RoundedFacts : LeafRoundedFacts 8
    leaf5758Certificate.logOnePlusV leaf5758InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5758InputLogOnePlusV_eq }

private noncomputable def leaf5758Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi265InputQChi innerPair658Input
    leaf5758InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5758LowerChecked :
    lowerCheck 24 leaf5758Box leaf5758Inputs = true := by
  rfl'

private theorem leaf5758CoversExact : CoversExact 8
    leaf5758Box leaf5758Certificate leaf5758InnerLog leaf5758Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi265RoundedFacts
    innerPair658RoundedFacts leaf5758RoundedFacts (by rfl)

private theorem leaf5758FlatSound : Sound leaf5758Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5758CertificateValid
    leaf5758InnerLogValid leaf5758CoversExact leaf5758LowerChecked

private noncomputable def leaf5759Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (55/128), chiHi := (7/16) }

private noncomputable def leaf5759Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435789/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68713111552) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (664870957/536870912) }, upper := { exponent := 1, mantissa := (1289/1024) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi266LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429508093/137426223104) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf5759InnerLog : WideLogData :=
  innerPair286Data

set_option maxRecDepth 1000000 in
private theorem leaf5759LocalValidity :
    LeafFacts leaf5759Box leaf5759Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5759Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68713111552) }) = true
      norm_num [leaf5759Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5759CertificateValid :
    WideCertificateValid leaf5759Box leaf5759Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi266ValidityFacts
    leaf5759LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5759CoverageChecked :
    coverageCheck (innerAD leaf5759Box) leaf5759InnerLog = true := by
  rfl'

private theorem leaf5759InnerLogValid :
    leaf5759InnerLog.Valid 8 (innerAD leaf5759Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint90PositiveFacts.valid leaf5759CoverageChecked

private noncomputable def leaf5759InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814741/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5759InputLogOnePlusV_eq :
    leaf5759InputLogOnePlusV = outerEnclosure 24
      (leaf5759Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5759RoundedFacts : LeafRoundedFacts 8
    leaf5759Certificate.logOnePlusV leaf5759InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5759InputLogOnePlusV_eq }

private noncomputable def leaf5759Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi266InputQChi innerPair286Input
    leaf5759InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5759LowerChecked :
    lowerCheck 24 leaf5759Box leaf5759Inputs = true := by
  rfl'

private theorem leaf5759CoversExact : CoversExact 8
    leaf5759Box leaf5759Certificate leaf5759InnerLog leaf5759Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi266RoundedFacts
    innerPair286RoundedFacts leaf5759RoundedFacts (by rfl)

private theorem leaf5759FlatSound : Sound leaf5759Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5759CertificateValid
    leaf5759InnerLogValid leaf5759CoversExact leaf5759LowerChecked

private noncomputable def leaf5760Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (55/128), chiHi := (7/16) }

private noncomputable def leaf5760Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435791/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68713054208) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (668475215/536870912) }, upper := { exponent := 1, mantissa := (81/64) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi266LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429450749/137426108416) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf5760InnerLog : WideLogData :=
  innerPair286Data

set_option maxRecDepth 1000000 in
private theorem leaf5760LocalValidity :
    LeafFacts leaf5760Box leaf5760Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5760Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68713054208) }) = true
      norm_num [leaf5760Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5760CertificateValid :
    WideCertificateValid leaf5760Box leaf5760Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi266ValidityFacts
    leaf5760LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5760CoverageChecked :
    coverageCheck (innerAD leaf5760Box) leaf5760InnerLog = true := by
  rfl'

private theorem leaf5760InnerLogValid :
    leaf5760InnerLog.Valid 8 (innerAD leaf5760Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint90PositiveFacts.valid leaf5760CoverageChecked

private noncomputable def leaf5760InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629489/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5760InputLogOnePlusV_eq :
    leaf5760InputLogOnePlusV = outerEnclosure 24
      (leaf5760Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5760RoundedFacts : LeafRoundedFacts 8
    leaf5760Certificate.logOnePlusV leaf5760InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5760InputLogOnePlusV_eq }

private noncomputable def leaf5760Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi266InputQChi innerPair286Input
    leaf5760InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5760LowerChecked :
    lowerCheck 24 leaf5760Box leaf5760Inputs = true := by
  rfl'

private theorem leaf5760CoversExact : CoversExact 8
    leaf5760Box leaf5760Certificate leaf5760InnerLog leaf5760Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi266RoundedFacts
    innerPair286RoundedFacts leaf5760RoundedFacts (by rfl)

private theorem leaf5760FlatSound : Sound leaf5760Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5760CertificateValid
    leaf5760InnerLogValid leaf5760CoversExact leaf5760LowerChecked

private noncomputable def component115Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (3/8), chiHi := (49/128) }

set_option maxRecDepth 1000000 in
private theorem component115Node0_sound : Sound component115Node0Box :=
  sound_of_literal_split component115Node0Box leaf5697Box leaf5698Box
    .k (105/32) (by rfl) (by rfl)
    leaf5697FlatSound leaf5698FlatSound

private noncomputable def component115Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (49/128), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component115Node1_sound : Sound component115Node1Box :=
  sound_of_literal_split component115Node1Box leaf5699Box leaf5700Box
    .k (105/32) (by rfl) (by rfl)
    leaf5699FlatSound leaf5700FlatSound

private noncomputable def component115Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (3/8), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component115Node2_sound : Sound component115Node2Box :=
  sound_of_literal_split component115Node2Box component115Node0Box component115Node1Box
    .chi (49/128) (by rfl) (by rfl)
    component115Node0_sound component115Node1_sound

private noncomputable def component115Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (3/8), chiHi := (49/128) }

set_option maxRecDepth 1000000 in
private theorem component115Node3_sound : Sound component115Node3Box :=
  sound_of_literal_split component115Node3Box leaf5701Box leaf5702Box
    .k (107/32) (by rfl) (by rfl)
    leaf5701FlatSound leaf5702FlatSound

private noncomputable def component115Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (49/128), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component115Node4_sound : Sound component115Node4Box :=
  sound_of_literal_split component115Node4Box leaf5703Box leaf5704Box
    .k (107/32) (by rfl) (by rfl)
    leaf5703FlatSound leaf5704FlatSound

private noncomputable def component115Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (3/8), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component115Node5_sound : Sound component115Node5Box :=
  sound_of_literal_split component115Node5Box component115Node3Box component115Node4Box
    .chi (49/128) (by rfl) (by rfl)
    component115Node3_sound component115Node4_sound

private noncomputable def component115Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (3/8), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component115Node6_sound : Sound component115Node6Box :=
  sound_of_literal_split component115Node6Box component115Node2Box component115Node5Box
    .k (53/16) (by rfl) (by rfl)
    component115Node2_sound component115Node5_sound

private noncomputable def component115Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (25/64), chiHi := (51/128) }

set_option maxRecDepth 1000000 in
private theorem component115Node7_sound : Sound component115Node7Box :=
  sound_of_literal_split component115Node7Box leaf5705Box leaf5706Box
    .k (105/32) (by rfl) (by rfl)
    leaf5705FlatSound leaf5706FlatSound

private noncomputable def component115Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (51/128), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component115Node8_sound : Sound component115Node8Box :=
  sound_of_literal_split component115Node8Box leaf5707Box leaf5708Box
    .k (105/32) (by rfl) (by rfl)
    leaf5707FlatSound leaf5708FlatSound

private noncomputable def component115Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (25/64), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component115Node9_sound : Sound component115Node9Box :=
  sound_of_literal_split component115Node9Box component115Node7Box component115Node8Box
    .chi (51/128) (by rfl) (by rfl)
    component115Node7_sound component115Node8_sound

private noncomputable def component115Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (25/64), chiHi := (51/128) }

set_option maxRecDepth 1000000 in
private theorem component115Node10_sound : Sound component115Node10Box :=
  sound_of_literal_split component115Node10Box leaf5709Box leaf5710Box
    .k (107/32) (by rfl) (by rfl)
    leaf5709FlatSound leaf5710FlatSound

private noncomputable def component115Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (51/128), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component115Node11_sound : Sound component115Node11Box :=
  sound_of_literal_split component115Node11Box leaf5711Box leaf5712Box
    .k (107/32) (by rfl) (by rfl)
    leaf5711FlatSound leaf5712FlatSound

private noncomputable def component115Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (25/64), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component115Node12_sound : Sound component115Node12Box :=
  sound_of_literal_split component115Node12Box component115Node10Box component115Node11Box
    .chi (51/128) (by rfl) (by rfl)
    component115Node10_sound component115Node11_sound

private noncomputable def component115Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (25/64), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component115Node13_sound : Sound component115Node13Box :=
  sound_of_literal_split component115Node13Box component115Node9Box component115Node12Box
    .k (53/16) (by rfl) (by rfl)
    component115Node9_sound component115Node12_sound

private noncomputable def component115Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (3/8), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component115Node14_sound : Sound component115Node14Box :=
  sound_of_literal_split component115Node14Box component115Node6Box component115Node13Box
    .chi (25/64) (by rfl) (by rfl)
    component115Node6_sound component115Node13_sound

private noncomputable def component115Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (3/8), chiHi := (49/128) }

set_option maxRecDepth 1000000 in
private theorem component115Node15_sound : Sound component115Node15Box :=
  sound_of_literal_split component115Node15Box leaf5713Box leaf5714Box
    .k (109/32) (by rfl) (by rfl)
    leaf5713FlatSound leaf5714FlatSound

private noncomputable def component115Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (49/128), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component115Node16_sound : Sound component115Node16Box :=
  sound_of_literal_split component115Node16Box leaf5715Box leaf5716Box
    .k (109/32) (by rfl) (by rfl)
    leaf5715FlatSound leaf5716FlatSound

private noncomputable def component115Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (3/8), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component115Node17_sound : Sound component115Node17Box :=
  sound_of_literal_split component115Node17Box component115Node15Box component115Node16Box
    .chi (49/128) (by rfl) (by rfl)
    component115Node15_sound component115Node16_sound

private noncomputable def component115Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (3/8), chiHi := (49/128) }

set_option maxRecDepth 1000000 in
private theorem component115Node18_sound : Sound component115Node18Box :=
  sound_of_literal_split component115Node18Box leaf5717Box leaf5718Box
    .k (111/32) (by rfl) (by rfl)
    leaf5717FlatSound leaf5718FlatSound

private noncomputable def component115Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (49/128), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component115Node19_sound : Sound component115Node19Box :=
  sound_of_literal_split component115Node19Box leaf5719Box leaf5720Box
    .k (111/32) (by rfl) (by rfl)
    leaf5719FlatSound leaf5720FlatSound

private noncomputable def component115Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (3/8), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component115Node20_sound : Sound component115Node20Box :=
  sound_of_literal_split component115Node20Box component115Node18Box component115Node19Box
    .chi (49/128) (by rfl) (by rfl)
    component115Node18_sound component115Node19_sound

private noncomputable def component115Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (3/8), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component115Node21_sound : Sound component115Node21Box :=
  sound_of_literal_split component115Node21Box component115Node17Box component115Node20Box
    .k (55/16) (by rfl) (by rfl)
    component115Node17_sound component115Node20_sound

private noncomputable def component115Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (25/64), chiHi := (51/128) }

set_option maxRecDepth 1000000 in
private theorem component115Node22_sound : Sound component115Node22Box :=
  sound_of_literal_split component115Node22Box leaf5721Box leaf5722Box
    .k (109/32) (by rfl) (by rfl)
    leaf5721FlatSound leaf5722FlatSound

private noncomputable def component115Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (51/128), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component115Node23_sound : Sound component115Node23Box :=
  sound_of_literal_split component115Node23Box leaf5723Box leaf5724Box
    .k (109/32) (by rfl) (by rfl)
    leaf5723FlatSound leaf5724FlatSound

private noncomputable def component115Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (25/64), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component115Node24_sound : Sound component115Node24Box :=
  sound_of_literal_split component115Node24Box component115Node22Box component115Node23Box
    .chi (51/128) (by rfl) (by rfl)
    component115Node22_sound component115Node23_sound

private noncomputable def component115Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (25/64), chiHi := (51/128) }

set_option maxRecDepth 1000000 in
private theorem component115Node25_sound : Sound component115Node25Box :=
  sound_of_literal_split component115Node25Box leaf5725Box leaf5726Box
    .k (111/32) (by rfl) (by rfl)
    leaf5725FlatSound leaf5726FlatSound

private noncomputable def component115Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (51/128), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component115Node26_sound : Sound component115Node26Box :=
  sound_of_literal_split component115Node26Box leaf5727Box leaf5728Box
    .k (111/32) (by rfl) (by rfl)
    leaf5727FlatSound leaf5728FlatSound

private noncomputable def component115Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (25/64), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component115Node27_sound : Sound component115Node27Box :=
  sound_of_literal_split component115Node27Box component115Node25Box component115Node26Box
    .chi (51/128) (by rfl) (by rfl)
    component115Node25_sound component115Node26_sound

private noncomputable def component115Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (25/64), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component115Node28_sound : Sound component115Node28Box :=
  sound_of_literal_split component115Node28Box component115Node24Box component115Node27Box
    .k (55/16) (by rfl) (by rfl)
    component115Node24_sound component115Node27_sound

private noncomputable def component115Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (3/8), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component115Node29_sound : Sound component115Node29Box :=
  sound_of_literal_split component115Node29Box component115Node21Box component115Node28Box
    .chi (25/64) (by rfl) (by rfl)
    component115Node21_sound component115Node28_sound

private noncomputable def component115Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (7/2), chiLo := (3/8), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component115Node30_sound : Sound component115Node30Box :=
  sound_of_literal_split component115Node30Box component115Node14Box component115Node29Box
    .k (27/8) (by rfl) (by rfl)
    component115Node14_sound component115Node29_sound

private noncomputable def component115Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (13/32), chiHi := (53/128) }

set_option maxRecDepth 1000000 in
private theorem component115Node31_sound : Sound component115Node31Box :=
  sound_of_literal_split component115Node31Box leaf5729Box leaf5730Box
    .k (105/32) (by rfl) (by rfl)
    leaf5729FlatSound leaf5730FlatSound

private noncomputable def component115Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (53/128), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component115Node32_sound : Sound component115Node32Box :=
  sound_of_literal_split component115Node32Box leaf5731Box leaf5732Box
    .k (105/32) (by rfl) (by rfl)
    leaf5731FlatSound leaf5732FlatSound

private noncomputable def component115Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (13/32), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component115Node33_sound : Sound component115Node33Box :=
  sound_of_literal_split component115Node33Box component115Node31Box component115Node32Box
    .chi (53/128) (by rfl) (by rfl)
    component115Node31_sound component115Node32_sound

private noncomputable def component115Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (13/32), chiHi := (53/128) }

set_option maxRecDepth 1000000 in
private theorem component115Node34_sound : Sound component115Node34Box :=
  sound_of_literal_split component115Node34Box leaf5733Box leaf5734Box
    .k (107/32) (by rfl) (by rfl)
    leaf5733FlatSound leaf5734FlatSound

private noncomputable def component115Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (53/128), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component115Node35_sound : Sound component115Node35Box :=
  sound_of_literal_split component115Node35Box leaf5735Box leaf5736Box
    .k (107/32) (by rfl) (by rfl)
    leaf5735FlatSound leaf5736FlatSound

private noncomputable def component115Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (13/32), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component115Node36_sound : Sound component115Node36Box :=
  sound_of_literal_split component115Node36Box component115Node34Box component115Node35Box
    .chi (53/128) (by rfl) (by rfl)
    component115Node34_sound component115Node35_sound

private noncomputable def component115Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (13/32), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component115Node37_sound : Sound component115Node37Box :=
  sound_of_literal_split component115Node37Box component115Node33Box component115Node36Box
    .k (53/16) (by rfl) (by rfl)
    component115Node33_sound component115Node36_sound

private noncomputable def component115Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (27/64), chiHi := (55/128) }

set_option maxRecDepth 1000000 in
private theorem component115Node38_sound : Sound component115Node38Box :=
  sound_of_literal_split component115Node38Box leaf5737Box leaf5738Box
    .k (105/32) (by rfl) (by rfl)
    leaf5737FlatSound leaf5738FlatSound

private noncomputable def component115Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (55/128), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component115Node39_sound : Sound component115Node39Box :=
  sound_of_literal_split component115Node39Box leaf5739Box leaf5740Box
    .k (105/32) (by rfl) (by rfl)
    leaf5739FlatSound leaf5740FlatSound

private noncomputable def component115Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (27/64), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component115Node40_sound : Sound component115Node40Box :=
  sound_of_literal_split component115Node40Box component115Node38Box component115Node39Box
    .chi (55/128) (by rfl) (by rfl)
    component115Node38_sound component115Node39_sound

private noncomputable def component115Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (27/64), chiHi := (55/128) }

set_option maxRecDepth 1000000 in
private theorem component115Node41_sound : Sound component115Node41Box :=
  sound_of_literal_split component115Node41Box leaf5741Box leaf5742Box
    .k (107/32) (by rfl) (by rfl)
    leaf5741FlatSound leaf5742FlatSound

private noncomputable def component115Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (55/128), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component115Node42_sound : Sound component115Node42Box :=
  sound_of_literal_split component115Node42Box leaf5743Box leaf5744Box
    .k (107/32) (by rfl) (by rfl)
    leaf5743FlatSound leaf5744FlatSound

private noncomputable def component115Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (27/64), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component115Node43_sound : Sound component115Node43Box :=
  sound_of_literal_split component115Node43Box component115Node41Box component115Node42Box
    .chi (55/128) (by rfl) (by rfl)
    component115Node41_sound component115Node42_sound

private noncomputable def component115Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (27/64), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component115Node44_sound : Sound component115Node44Box :=
  sound_of_literal_split component115Node44Box component115Node40Box component115Node43Box
    .k (53/16) (by rfl) (by rfl)
    component115Node40_sound component115Node43_sound

private noncomputable def component115Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (13/32), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component115Node45_sound : Sound component115Node45Box :=
  sound_of_literal_split component115Node45Box component115Node37Box component115Node44Box
    .chi (27/64) (by rfl) (by rfl)
    component115Node37_sound component115Node44_sound

private noncomputable def component115Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (13/32), chiHi := (53/128) }

set_option maxRecDepth 1000000 in
private theorem component115Node46_sound : Sound component115Node46Box :=
  sound_of_literal_split component115Node46Box leaf5745Box leaf5746Box
    .k (109/32) (by rfl) (by rfl)
    leaf5745FlatSound leaf5746FlatSound

private noncomputable def component115Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (53/128), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component115Node47_sound : Sound component115Node47Box :=
  sound_of_literal_split component115Node47Box leaf5747Box leaf5748Box
    .k (109/32) (by rfl) (by rfl)
    leaf5747FlatSound leaf5748FlatSound

private noncomputable def component115Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (13/32), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component115Node48_sound : Sound component115Node48Box :=
  sound_of_literal_split component115Node48Box component115Node46Box component115Node47Box
    .chi (53/128) (by rfl) (by rfl)
    component115Node46_sound component115Node47_sound

private noncomputable def component115Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (13/32), chiHi := (53/128) }

set_option maxRecDepth 1000000 in
private theorem component115Node49_sound : Sound component115Node49Box :=
  sound_of_literal_split component115Node49Box leaf5749Box leaf5750Box
    .k (111/32) (by rfl) (by rfl)
    leaf5749FlatSound leaf5750FlatSound

private noncomputable def component115Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (53/128), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component115Node50_sound : Sound component115Node50Box :=
  sound_of_literal_split component115Node50Box leaf5751Box leaf5752Box
    .k (111/32) (by rfl) (by rfl)
    leaf5751FlatSound leaf5752FlatSound

private noncomputable def component115Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (13/32), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component115Node51_sound : Sound component115Node51Box :=
  sound_of_literal_split component115Node51Box component115Node49Box component115Node50Box
    .chi (53/128) (by rfl) (by rfl)
    component115Node49_sound component115Node50_sound

private noncomputable def component115Node52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (13/32), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component115Node52_sound : Sound component115Node52Box :=
  sound_of_literal_split component115Node52Box component115Node48Box component115Node51Box
    .k (55/16) (by rfl) (by rfl)
    component115Node48_sound component115Node51_sound

private noncomputable def component115Node53Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (27/64), chiHi := (55/128) }

set_option maxRecDepth 1000000 in
private theorem component115Node53_sound : Sound component115Node53Box :=
  sound_of_literal_split component115Node53Box leaf5753Box leaf5754Box
    .k (109/32) (by rfl) (by rfl)
    leaf5753FlatSound leaf5754FlatSound

private noncomputable def component115Node54Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (55/128), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component115Node54_sound : Sound component115Node54Box :=
  sound_of_literal_split component115Node54Box leaf5755Box leaf5756Box
    .k (109/32) (by rfl) (by rfl)
    leaf5755FlatSound leaf5756FlatSound

private noncomputable def component115Node55Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (27/64), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component115Node55_sound : Sound component115Node55Box :=
  sound_of_literal_split component115Node55Box component115Node53Box component115Node54Box
    .chi (55/128) (by rfl) (by rfl)
    component115Node53_sound component115Node54_sound

private noncomputable def component115Node56Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (27/64), chiHi := (55/128) }

set_option maxRecDepth 1000000 in
private theorem component115Node56_sound : Sound component115Node56Box :=
  sound_of_literal_split component115Node56Box leaf5757Box leaf5758Box
    .k (111/32) (by rfl) (by rfl)
    leaf5757FlatSound leaf5758FlatSound

private noncomputable def component115Node57Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (55/128), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component115Node57_sound : Sound component115Node57Box :=
  sound_of_literal_split component115Node57Box leaf5759Box leaf5760Box
    .k (111/32) (by rfl) (by rfl)
    leaf5759FlatSound leaf5760FlatSound

private noncomputable def component115Node58Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (27/64), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component115Node58_sound : Sound component115Node58Box :=
  sound_of_literal_split component115Node58Box component115Node56Box component115Node57Box
    .chi (55/128) (by rfl) (by rfl)
    component115Node56_sound component115Node57_sound

private noncomputable def component115Node59Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (27/64), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component115Node59_sound : Sound component115Node59Box :=
  sound_of_literal_split component115Node59Box component115Node55Box component115Node58Box
    .k (55/16) (by rfl) (by rfl)
    component115Node55_sound component115Node58_sound

private noncomputable def component115Node60Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (13/32), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component115Node60_sound : Sound component115Node60Box :=
  sound_of_literal_split component115Node60Box component115Node52Box component115Node59Box
    .chi (27/64) (by rfl) (by rfl)
    component115Node52_sound component115Node59_sound

private noncomputable def component115Node61Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (7/2), chiLo := (13/32), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component115Node61_sound : Sound component115Node61Box :=
  sound_of_literal_split component115Node61Box component115Node45Box component115Node60Box
    .k (27/8) (by rfl) (by rfl)
    component115Node45_sound component115Node60_sound

noncomputable def component115Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (7/2), chiLo := (3/8), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
theorem component115_sound : Sound component115Box :=
  sound_of_literal_split component115Box component115Node30Box component115Node61Box
    .chi (13/32) (by rfl) (by rfl)
    component115Node30_sound component115Node61_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
