import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch5
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch8
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

private noncomputable def leaf5569Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (3/8), chiHi := (49/128) }

private noncomputable def leaf5569Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435747/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357304832) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (570373855/536870912) }, upper := { exponent := 1, mantissa := (8849/8192) } }, logOuter := sk133LogOuterCertificate, logK := sk133LogKCertificate, logChi := chi259LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716027391/68714609664) } }, logDArg := sk133LogDArgCertificate }

private noncomputable def leaf5569InnerLog : WideLogData :=
  innerPair243Data

set_option maxRecDepth 1000000 in
private theorem leaf5569LocalValidity :
    LeafFacts leaf5569Box leaf5569Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5569Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357304832) }) = true
      norm_num [leaf5569Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5569CertificateValid :
    WideCertificateValid leaf5569Box leaf5569Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk133ValidityFacts chi259ValidityFacts
    leaf5569LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5569CoverageChecked :
    coverageCheck (innerAD leaf5569Box) leaf5569InnerLog = true := by
  rfl'

private theorem leaf5569InnerLogValid :
    leaf5569InnerLog.Valid 8 (innerAD leaf5569Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint74PositiveFacts.valid leaf5569CoverageChecked

private noncomputable def leaf5569InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629427/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5569InputLogOnePlusV_eq :
    leaf5569InputLogOnePlusV = outerEnclosure 24
      (leaf5569Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5569RoundedFacts : LeafRoundedFacts 8
    leaf5569Certificate.logOnePlusV leaf5569InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5569InputLogOnePlusV_eq }

private noncomputable def leaf5569Inputs : Inputs :=
  inputsOfCaches globalInput sk133RoundedInputs
    chi259InputQChi innerPair243Input
    leaf5569InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5569LowerChecked :
    lowerCheck 24 leaf5569Box leaf5569Inputs = true := by
  rfl'

private theorem leaf5569CoversExact : CoversExact 8
    leaf5569Box leaf5569Certificate leaf5569InnerLog leaf5569Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk133RoundedFacts chi259RoundedFacts
    innerPair243RoundedFacts leaf5569RoundedFacts (by rfl)

private theorem leaf5569FlatSound : Sound leaf5569Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5569CertificateValid
    leaf5569InnerLogValid leaf5569CoversExact leaf5569LowerChecked

private noncomputable def leaf5570Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (3/8), chiHi := (49/128) }

private noncomputable def leaf5570Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435749/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357279744) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (573519389/536870912) }, upper := { exponent := 1, mantissa := (4449/4096) } }, logOuter := sk134LogOuterCertificate, logK := sk134LogKCertificate, logChi := chi259LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716002303/68714559488) } }, logDArg := sk134LogDArgCertificate }

private noncomputable def leaf5570InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf5570LocalValidity :
    LeafFacts leaf5570Box leaf5570Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5570Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357279744) }) = true
      norm_num [leaf5570Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5570CertificateValid :
    WideCertificateValid leaf5570Box leaf5570Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk134ValidityFacts chi259ValidityFacts
    leaf5570LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5570CoverageChecked :
    coverageCheck (innerAD leaf5570Box) leaf5570InnerLog = true := by
  rfl'

private theorem leaf5570InnerLogValid :
    leaf5570InnerLog.Valid 8 (innerAD leaf5570Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf5570CoverageChecked

private noncomputable def leaf5570InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629433/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5570InputLogOnePlusV_eq :
    leaf5570InputLogOnePlusV = outerEnclosure 24
      (leaf5570Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5570RoundedFacts : LeafRoundedFacts 8
    leaf5570Certificate.logOnePlusV leaf5570InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5570InputLogOnePlusV_eq }

private noncomputable def leaf5570Inputs : Inputs :=
  inputsOfCaches globalInput sk134RoundedInputs
    chi259InputQChi innerPair249Input
    leaf5570InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5570LowerChecked :
    lowerCheck 24 leaf5570Box leaf5570Inputs = true := by
  rfl'

private theorem leaf5570CoversExact : CoversExact 8
    leaf5570Box leaf5570Certificate leaf5570InnerLog leaf5570Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk134RoundedFacts chi259RoundedFacts
    innerPair249RoundedFacts leaf5570RoundedFacts (by rfl)

private theorem leaf5570FlatSound : Sound leaf5570Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5570CertificateValid
    leaf5570InnerLogValid leaf5570CoversExact leaf5570LowerChecked

private noncomputable def leaf5571Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (49/128), chiHi := (25/64) }

private noncomputable def leaf5571Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435749/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357255168) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (576664925/536870912) }, upper := { exponent := 1, mantissa := (4473/4096) } }, logOuter := sk133LogOuterCertificate, logK := sk133LogKCertificate, logChi := chi260LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715977727/68714510336) } }, logDArg := sk133LogDArgCertificate }

private noncomputable def leaf5571InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf5571LocalValidity :
    LeafFacts leaf5571Box leaf5571Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5571Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357255168) }) = true
      norm_num [leaf5571Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5571CertificateValid :
    WideCertificateValid leaf5571Box leaf5571Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk133ValidityFacts chi260ValidityFacts
    leaf5571LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5571CoverageChecked :
    coverageCheck (innerAD leaf5571Box) leaf5571InnerLog = true := by
  rfl'

private theorem leaf5571InnerLogValid :
    leaf5571InnerLog.Valid 8 (innerAD leaf5571Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf5571CoverageChecked

private noncomputable def leaf5571InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629439/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5571InputLogOnePlusV_eq :
    leaf5571InputLogOnePlusV = outerEnclosure 24
      (leaf5571Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5571RoundedFacts : LeafRoundedFacts 8
    leaf5571Certificate.logOnePlusV leaf5571InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5571InputLogOnePlusV_eq }

private noncomputable def leaf5571Inputs : Inputs :=
  inputsOfCaches globalInput sk133RoundedInputs
    chi260InputQChi innerPair249Input
    leaf5571InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5571LowerChecked :
    lowerCheck 24 leaf5571Box leaf5571Inputs = true := by
  rfl'

private theorem leaf5571CoversExact : CoversExact 8
    leaf5571Box leaf5571Certificate leaf5571InnerLog leaf5571Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk133RoundedFacts chi260RoundedFacts
    innerPair249RoundedFacts leaf5571RoundedFacts (by rfl)

private theorem leaf5571FlatSound : Sound leaf5571Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5571CertificateValid
    leaf5571InnerLogValid leaf5571CoversExact leaf5571LowerChecked

private noncomputable def leaf5572Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (49/128), chiHi := (25/64) }

private noncomputable def leaf5572Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435751/268435456) }, vSqrt := { lower := (65529/65536), upper := (65196817/65193984) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (579875991/536870912) }, upper := { exponent := 1, mantissa := (2249/2048) } }, logOuter := sk134LogOuterCertificate, logK := sk134LogKCertificate, logChi := chi260LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (130390801/130387968) } }, logDArg := sk134LogDArgCertificate }

private noncomputable def leaf5572InnerLog : WideLogData :=
  innerPair250Data

set_option maxRecDepth 1000000 in
private theorem leaf5572LocalValidity :
    LeafFacts leaf5572Box leaf5572Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5572Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (65196817/65193984) }) = true
      norm_num [leaf5572Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5572CertificateValid :
    WideCertificateValid leaf5572Box leaf5572Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk134ValidityFacts chi260ValidityFacts
    leaf5572LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5572CoverageChecked :
    coverageCheck (innerAD leaf5572Box) leaf5572InnerLog = true := by
  rfl'

private theorem leaf5572InnerLogValid :
    leaf5572InnerLog.Valid 8 (innerAD leaf5572Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint75PositiveFacts.valid leaf5572CoverageChecked

private noncomputable def leaf5572InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629445/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5572InputLogOnePlusV_eq :
    leaf5572InputLogOnePlusV = outerEnclosure 24
      (leaf5572Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5572RoundedFacts : LeafRoundedFacts 8
    leaf5572Certificate.logOnePlusV leaf5572InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5572InputLogOnePlusV_eq }

private noncomputable def leaf5572Inputs : Inputs :=
  inputsOfCaches globalInput sk134RoundedInputs
    chi260InputQChi innerPair250Input
    leaf5572InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5572LowerChecked :
    lowerCheck 24 leaf5572Box leaf5572Inputs = true := by
  rfl'

private theorem leaf5572CoversExact : CoversExact 8
    leaf5572Box leaf5572Certificate leaf5572InnerLog leaf5572Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk134RoundedFacts chi260RoundedFacts
    innerPair250RoundedFacts leaf5572RoundedFacts (by rfl)

private theorem leaf5572FlatSound : Sound leaf5572Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5572CertificateValid
    leaf5572InnerLogValid leaf5572CoversExact leaf5572LowerChecked

private noncomputable def leaf5573Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (3/8), chiHi := (49/128) }

private noncomputable def leaf5573Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435751/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357254656) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (576664923/536870912) }, upper := { exponent := 1, mantissa := (8947/8192) } }, logOuter := sk135LogOuterCertificate, logK := sk135LogKCertificate, logChi := chi259LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715977215/68714509312) } }, logDArg := sk135LogDArgCertificate }

private noncomputable def leaf5573InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf5573LocalValidity :
    LeafFacts leaf5573Box leaf5573Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5573Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357254656) }) = true
      norm_num [leaf5573Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5573CertificateValid :
    WideCertificateValid leaf5573Box leaf5573Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk135ValidityFacts chi259ValidityFacts
    leaf5573LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5573CoverageChecked :
    coverageCheck (innerAD leaf5573Box) leaf5573InnerLog = true := by
  rfl'

private theorem leaf5573InnerLogValid :
    leaf5573InnerLog.Valid 8 (innerAD leaf5573Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf5573CoverageChecked

private noncomputable def leaf5573InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629439/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5573InputLogOnePlusV_eq :
    leaf5573InputLogOnePlusV = outerEnclosure 24
      (leaf5573Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5573RoundedFacts : LeafRoundedFacts 8
    leaf5573Certificate.logOnePlusV leaf5573InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5573InputLogOnePlusV_eq }

private noncomputable def leaf5573Inputs : Inputs :=
  inputsOfCaches globalInput sk135RoundedInputs
    chi259InputQChi innerPair249Input
    leaf5573InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5573LowerChecked :
    lowerCheck 24 leaf5573Box leaf5573Inputs = true := by
  rfl'

private theorem leaf5573CoversExact : CoversExact 8
    leaf5573Box leaf5573Certificate leaf5573InnerLog leaf5573Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk135RoundedFacts chi259RoundedFacts
    innerPair249RoundedFacts leaf5573RoundedFacts (by rfl)

private theorem leaf5573FlatSound : Sound leaf5573Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5573CertificateValid
    leaf5573InnerLogValid leaf5573CoversExact leaf5573LowerChecked

private noncomputable def leaf5574Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (3/8), chiHi := (49/128) }

private noncomputable def leaf5574Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435753/268435456) }, vSqrt := { lower := (65529/65536), upper := (65196817/65193984) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (579810457/536870912) }, upper := { exponent := 1, mantissa := (2249/2048) } }, logOuter := sk136LogOuterCertificate, logK := sk136LogKCertificate, logChi := chi259LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (130390801/130387968) } }, logDArg := sk136LogDArgCertificate }

private noncomputable def leaf5574InnerLog : WideLogData :=
  innerPair332Data

set_option maxRecDepth 1000000 in
private theorem leaf5574LocalValidity :
    LeafFacts leaf5574Box leaf5574Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5574Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (65196817/65193984) }) = true
      norm_num [leaf5574Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5574CertificateValid :
    WideCertificateValid leaf5574Box leaf5574Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk136ValidityFacts chi259ValidityFacts
    leaf5574LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5574CoverageChecked :
    coverageCheck (innerAD leaf5574Box) leaf5574InnerLog = true := by
  rfl'

private theorem leaf5574InnerLogValid :
    leaf5574InnerLog.Valid 8 (innerAD leaf5574Box) :=
  wideLogDataValid_of_cachedCheck endpoint88PositiveFacts
    endpoint291PositiveFacts.valid leaf5574CoverageChecked

private noncomputable def leaf5574InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629445/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5574InputLogOnePlusV_eq :
    leaf5574InputLogOnePlusV = outerEnclosure 24
      (leaf5574Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5574RoundedFacts : LeafRoundedFacts 8
    leaf5574Certificate.logOnePlusV leaf5574InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5574InputLogOnePlusV_eq }

private noncomputable def leaf5574Inputs : Inputs :=
  inputsOfCaches globalInput sk136RoundedInputs
    chi259InputQChi innerPair332Input
    leaf5574InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5574LowerChecked :
    lowerCheck 24 leaf5574Box leaf5574Inputs = true := by
  rfl'

private theorem leaf5574CoversExact : CoversExact 8
    leaf5574Box leaf5574Certificate leaf5574InnerLog leaf5574Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk136RoundedFacts chi259RoundedFacts
    innerPair332RoundedFacts leaf5574RoundedFacts (by rfl)

private theorem leaf5574FlatSound : Sound leaf5574Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5574CertificateValid
    leaf5574InnerLogValid leaf5574CoversExact leaf5574LowerChecked

private noncomputable def leaf5575Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (49/128), chiHi := (25/64) }

private noncomputable def leaf5575Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435753/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357203968) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (583087057/536870912) }, upper := { exponent := 1, mantissa := (4523/4096) } }, logOuter := sk135LogOuterCertificate, logK := sk135LogKCertificate, logChi := chi260LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715926527/68714407936) } }, logDArg := sk135LogDArgCertificate }

private noncomputable def leaf5575InnerLog : WideLogData :=
  innerPair250Data

set_option maxRecDepth 1000000 in
private theorem leaf5575LocalValidity :
    LeafFacts leaf5575Box leaf5575Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5575Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357203968) }) = true
      norm_num [leaf5575Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5575CertificateValid :
    WideCertificateValid leaf5575Box leaf5575Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk135ValidityFacts chi260ValidityFacts
    leaf5575LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5575CoverageChecked :
    coverageCheck (innerAD leaf5575Box) leaf5575InnerLog = true := by
  rfl'

private theorem leaf5575InnerLogValid :
    leaf5575InnerLog.Valid 8 (innerAD leaf5575Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint75PositiveFacts.valid leaf5575CoverageChecked

private noncomputable def leaf5575InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907363/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5575InputLogOnePlusV_eq :
    leaf5575InputLogOnePlusV = outerEnclosure 24
      (leaf5575Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5575RoundedFacts : LeafRoundedFacts 8
    leaf5575Certificate.logOnePlusV leaf5575InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5575InputLogOnePlusV_eq }

private noncomputable def leaf5575Inputs : Inputs :=
  inputsOfCaches globalInput sk135RoundedInputs
    chi260InputQChi innerPair250Input
    leaf5575InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5575LowerChecked :
    lowerCheck 24 leaf5575Box leaf5575Inputs = true := by
  rfl'

private theorem leaf5575CoversExact : CoversExact 8
    leaf5575Box leaf5575Certificate leaf5575InnerLog leaf5575Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk135RoundedFacts chi260RoundedFacts
    innerPair250RoundedFacts leaf5575RoundedFacts (by rfl)

private theorem leaf5575FlatSound : Sound leaf5575Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5575CertificateValid
    leaf5575InnerLogValid leaf5575CoversExact leaf5575LowerChecked

private noncomputable def leaf5576Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (49/128), chiHi := (25/64) }

private noncomputable def leaf5576Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435755/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357178368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (586298123/536870912) }, upper := { exponent := 1, mantissa := (1137/1024) } }, logOuter := sk136LogOuterCertificate, logK := sk136LogKCertificate, logChi := chi260LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715900927/68714356736) } }, logDArg := sk136LogDArgCertificate }

private noncomputable def leaf5576InnerLog : WideLogData :=
  innerPair250Data

set_option maxRecDepth 1000000 in
private theorem leaf5576LocalValidity :
    LeafFacts leaf5576Box leaf5576Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5576Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357178368) }) = true
      norm_num [leaf5576Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5576CertificateValid :
    WideCertificateValid leaf5576Box leaf5576Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk136ValidityFacts chi260ValidityFacts
    leaf5576LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5576CoverageChecked :
    coverageCheck (innerAD leaf5576Box) leaf5576InnerLog = true := by
  rfl'

private theorem leaf5576InnerLogValid :
    leaf5576InnerLog.Valid 8 (innerAD leaf5576Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint75PositiveFacts.valid leaf5576CoverageChecked

private noncomputable def leaf5576InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814729/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5576InputLogOnePlusV_eq :
    leaf5576InputLogOnePlusV = outerEnclosure 24
      (leaf5576Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5576RoundedFacts : LeafRoundedFacts 8
    leaf5576Certificate.logOnePlusV leaf5576InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5576InputLogOnePlusV_eq }

private noncomputable def leaf5576Inputs : Inputs :=
  inputsOfCaches globalInput sk136RoundedInputs
    chi260InputQChi innerPair250Input
    leaf5576InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5576LowerChecked :
    lowerCheck 24 leaf5576Box leaf5576Inputs = true := by
  rfl'

private theorem leaf5576CoversExact : CoversExact 8
    leaf5576Box leaf5576Certificate leaf5576InnerLog leaf5576Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk136RoundedFacts chi260RoundedFacts
    innerPair250RoundedFacts leaf5576RoundedFacts (by rfl)

private theorem leaf5576FlatSound : Sound leaf5576Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5576CertificateValid
    leaf5576InnerLogValid leaf5576CoversExact leaf5576LowerChecked

private noncomputable def leaf5577Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (25/64), chiHi := (51/128) }

private noncomputable def leaf5577Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435751/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357205504) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (582955995/536870912) }, upper := { exponent := 1, mantissa := (9043/8192) } }, logOuter := sk133LogOuterCertificate, logK := sk133LogKCertificate, logChi := chi261LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715928063/68714411008) } }, logDArg := sk133LogDArgCertificate }

private noncomputable def leaf5577InnerLog : WideLogData :=
  innerPair250Data

set_option maxRecDepth 1000000 in
private theorem leaf5577LocalValidity :
    LeafFacts leaf5577Box leaf5577Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5577Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357205504) }) = true
      norm_num [leaf5577Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5577CertificateValid :
    WideCertificateValid leaf5577Box leaf5577Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk133ValidityFacts chi261ValidityFacts
    leaf5577LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5577CoverageChecked :
    coverageCheck (innerAD leaf5577Box) leaf5577InnerLog = true := by
  rfl'

private theorem leaf5577InnerLogValid :
    leaf5577InnerLog.Valid 8 (innerAD leaf5577Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint75PositiveFacts.valid leaf5577CoverageChecked

private noncomputable def leaf5577InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629451/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5577InputLogOnePlusV_eq :
    leaf5577InputLogOnePlusV = outerEnclosure 24
      (leaf5577Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5577RoundedFacts : LeafRoundedFacts 8
    leaf5577Certificate.logOnePlusV leaf5577InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5577InputLogOnePlusV_eq }

private noncomputable def leaf5577Inputs : Inputs :=
  inputsOfCaches globalInput sk133RoundedInputs
    chi261InputQChi innerPair250Input
    leaf5577InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5577LowerChecked :
    lowerCheck 24 leaf5577Box leaf5577Inputs = true := by
  rfl'

private theorem leaf5577CoversExact : CoversExact 8
    leaf5577Box leaf5577Certificate leaf5577InnerLog leaf5577Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk133RoundedFacts chi261RoundedFacts
    innerPair250RoundedFacts leaf5577RoundedFacts (by rfl)

private theorem leaf5577FlatSound : Sound leaf5577Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5577CertificateValid
    leaf5577InnerLogValid leaf5577CoversExact leaf5577LowerChecked

private noncomputable def leaf5578Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (25/64), chiHi := (51/128) }

private noncomputable def leaf5578Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435753/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357179392) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (586232593/536870912) }, upper := { exponent := 1, mantissa := (4547/4096) } }, logOuter := sk134LogOuterCertificate, logK := sk134LogKCertificate, logChi := chi261LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715901951/68714358784) } }, logDArg := sk134LogDArgCertificate }

private noncomputable def leaf5578InnerLog : WideLogData :=
  innerPair250Data

set_option maxRecDepth 1000000 in
private theorem leaf5578LocalValidity :
    LeafFacts leaf5578Box leaf5578Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5578Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357179392) }) = true
      norm_num [leaf5578Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5578CertificateValid :
    WideCertificateValid leaf5578Box leaf5578Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk134ValidityFacts chi261ValidityFacts
    leaf5578LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5578CoverageChecked :
    coverageCheck (innerAD leaf5578Box) leaf5578InnerLog = true := by
  rfl'

private theorem leaf5578InnerLogValid :
    leaf5578InnerLog.Valid 8 (innerAD leaf5578Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint75PositiveFacts.valid leaf5578CoverageChecked

private noncomputable def leaf5578InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814729/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5578InputLogOnePlusV_eq :
    leaf5578InputLogOnePlusV = outerEnclosure 24
      (leaf5578Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5578RoundedFacts : LeafRoundedFacts 8
    leaf5578Certificate.logOnePlusV leaf5578InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5578InputLogOnePlusV_eq }

private noncomputable def leaf5578Inputs : Inputs :=
  inputsOfCaches globalInput sk134RoundedInputs
    chi261InputQChi innerPair250Input
    leaf5578InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5578LowerChecked :
    lowerCheck 24 leaf5578Box leaf5578Inputs = true := by
  rfl'

private theorem leaf5578CoversExact : CoversExact 8
    leaf5578Box leaf5578Certificate leaf5578InnerLog leaf5578Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk134RoundedFacts chi261RoundedFacts
    innerPair250RoundedFacts leaf5578RoundedFacts (by rfl)

private theorem leaf5578FlatSound : Sound leaf5578Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5578CertificateValid
    leaf5578InnerLogValid leaf5578CoversExact leaf5578LowerChecked

private noncomputable def leaf5579Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (51/128), chiHi := (13/32) }

private noncomputable def leaf5579Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435753/268435456) }, vSqrt := { lower := (65529/65536), upper := (4908388937/4908165120) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (589247065/536870912) }, upper := { exponent := 1, mantissa := (2285/2048) } }, logOuter := sk133LogOuterCertificate, logK := sk133LogKCertificate, logChi := chi262LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (9816554057/9816330240) } }, logDArg := sk133LogDArgCertificate }

private noncomputable def leaf5579InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf5579LocalValidity :
    LeafFacts leaf5579Box leaf5579Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5579Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4908388937/4908165120) }) = true
      norm_num [leaf5579Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5579CertificateValid :
    WideCertificateValid leaf5579Box leaf5579Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk133ValidityFacts chi262ValidityFacts
    leaf5579LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5579CoverageChecked :
    coverageCheck (innerAD leaf5579Box) leaf5579InnerLog = true := by
  rfl'

private theorem leaf5579InnerLogValid :
    leaf5579InnerLog.Valid 8 (innerAD leaf5579Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf5579CoverageChecked

private noncomputable def leaf5579InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629463/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5579InputLogOnePlusV_eq :
    leaf5579InputLogOnePlusV = outerEnclosure 24
      (leaf5579Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5579RoundedFacts : LeafRoundedFacts 8
    leaf5579Certificate.logOnePlusV leaf5579InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5579InputLogOnePlusV_eq }

private noncomputable def leaf5579Inputs : Inputs :=
  inputsOfCaches globalInput sk133RoundedInputs
    chi262InputQChi innerPair256Input
    leaf5579InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5579LowerChecked :
    lowerCheck 24 leaf5579Box leaf5579Inputs = true := by
  rfl'

private theorem leaf5579CoversExact : CoversExact 8
    leaf5579Box leaf5579Certificate leaf5579InnerLog leaf5579Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk133RoundedFacts chi262RoundedFacts
    innerPair256RoundedFacts leaf5579RoundedFacts (by rfl)

private theorem leaf5579FlatSound : Sound leaf5579Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5579CertificateValid
    leaf5579InnerLogValid leaf5579CoversExact leaf5579LowerChecked

private noncomputable def leaf5580Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (51/128), chiHi := (13/32) }

private noncomputable def leaf5580Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435755/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357129216) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (592589195/536870912) }, upper := { exponent := 1, mantissa := (1149/1024) } }, logOuter := sk134LogOuterCertificate, logK := sk134LogKCertificate, logChi := chi262LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715851775/68714258432) } }, logDArg := sk134LogDArgCertificate }

private noncomputable def leaf5580InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf5580LocalValidity :
    LeafFacts leaf5580Box leaf5580Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5580Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357129216) }) = true
      norm_num [leaf5580Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5580CertificateValid :
    WideCertificateValid leaf5580Box leaf5580Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk134ValidityFacts chi262ValidityFacts
    leaf5580LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5580CoverageChecked :
    coverageCheck (innerAD leaf5580Box) leaf5580InnerLog = true := by
  rfl'

private theorem leaf5580InnerLogValid :
    leaf5580InnerLog.Valid 8 (innerAD leaf5580Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf5580CoverageChecked

private noncomputable def leaf5580InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814735/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5580InputLogOnePlusV_eq :
    leaf5580InputLogOnePlusV = outerEnclosure 24
      (leaf5580Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5580RoundedFacts : LeafRoundedFacts 8
    leaf5580Certificate.logOnePlusV leaf5580InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5580InputLogOnePlusV_eq }

private noncomputable def leaf5580Inputs : Inputs :=
  inputsOfCaches globalInput sk134RoundedInputs
    chi262InputQChi innerPair256Input
    leaf5580InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5580LowerChecked :
    lowerCheck 24 leaf5580Box leaf5580Inputs = true := by
  rfl'

private theorem leaf5580CoversExact : CoversExact 8
    leaf5580Box leaf5580Certificate leaf5580InnerLog leaf5580Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk134RoundedFacts chi262RoundedFacts
    innerPair256RoundedFacts leaf5580RoundedFacts (by rfl)

private theorem leaf5580FlatSound : Sound leaf5580Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5580CertificateValid
    leaf5580InnerLogValid leaf5580CoversExact leaf5580LowerChecked

private noncomputable def leaf5581Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (25/64), chiHi := (51/128) }

private noncomputable def leaf5581Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435755/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357153280) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (589509191/536870912) }, upper := { exponent := 1, mantissa := (9145/8192) } }, logOuter := sk135LogOuterCertificate, logK := sk135LogKCertificate, logChi := chi261LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715875839/68714306560) } }, logDArg := sk135LogDArgCertificate }

private noncomputable def leaf5581InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf5581LocalValidity :
    LeafFacts leaf5581Box leaf5581Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5581Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357153280) }) = true
      norm_num [leaf5581Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5581CertificateValid :
    WideCertificateValid leaf5581Box leaf5581Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk135ValidityFacts chi261ValidityFacts
    leaf5581LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5581CoverageChecked :
    coverageCheck (innerAD leaf5581Box) leaf5581InnerLog = true := by
  rfl'

private theorem leaf5581InnerLogValid :
    leaf5581InnerLog.Valid 8 (innerAD leaf5581Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf5581CoverageChecked

private noncomputable def leaf5581InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453683/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf5581InputLogOnePlusV_eq :
    leaf5581InputLogOnePlusV = outerEnclosure 24
      (leaf5581Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5581RoundedFacts : LeafRoundedFacts 8
    leaf5581Certificate.logOnePlusV leaf5581InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5581InputLogOnePlusV_eq }

private noncomputable def leaf5581Inputs : Inputs :=
  inputsOfCaches globalInput sk135RoundedInputs
    chi261InputQChi innerPair256Input
    leaf5581InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5581LowerChecked :
    lowerCheck 24 leaf5581Box leaf5581Inputs = true := by
  rfl'

private theorem leaf5581CoversExact : CoversExact 8
    leaf5581Box leaf5581Certificate leaf5581InnerLog leaf5581Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk135RoundedFacts chi261RoundedFacts
    innerPair256RoundedFacts leaf5581RoundedFacts (by rfl)

private theorem leaf5581FlatSound : Sound leaf5581Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5581CertificateValid
    leaf5581InnerLogValid leaf5581CoversExact leaf5581LowerChecked

private noncomputable def leaf5582Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (25/64), chiHi := (51/128) }

private noncomputable def leaf5582Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435757/268435456) }, vSqrt := { lower := (65529/65536), upper := (4908388937/4908161024) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (592785789/536870912) }, upper := { exponent := 1, mantissa := (2299/2048) } }, logOuter := sk136LogOuterCertificate, logK := sk136LogKCertificate, logChi := chi261LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (9816549961/9816322048) } }, logDArg := sk136LogDArgCertificate }

private noncomputable def leaf5582InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf5582LocalValidity :
    LeafFacts leaf5582Box leaf5582Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5582Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4908388937/4908161024) }) = true
      norm_num [leaf5582Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5582CertificateValid :
    WideCertificateValid leaf5582Box leaf5582Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk136ValidityFacts chi261ValidityFacts
    leaf5582LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5582CoverageChecked :
    coverageCheck (innerAD leaf5582Box) leaf5582InnerLog = true := by
  rfl'

private theorem leaf5582InnerLogValid :
    leaf5582InnerLog.Valid 8 (innerAD leaf5582Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf5582CoverageChecked

private noncomputable def leaf5582InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814735/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5582InputLogOnePlusV_eq :
    leaf5582InputLogOnePlusV = outerEnclosure 24
      (leaf5582Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5582RoundedFacts : LeafRoundedFacts 8
    leaf5582Certificate.logOnePlusV leaf5582InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5582InputLogOnePlusV_eq }

private noncomputable def leaf5582Inputs : Inputs :=
  inputsOfCaches globalInput sk136RoundedInputs
    chi261InputQChi innerPair256Input
    leaf5582InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5582LowerChecked :
    lowerCheck 24 leaf5582Box leaf5582Inputs = true := by
  rfl'

private theorem leaf5582CoversExact : CoversExact 8
    leaf5582Box leaf5582Certificate leaf5582InnerLog leaf5582Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk136RoundedFacts chi261RoundedFacts
    innerPair256RoundedFacts leaf5582RoundedFacts (by rfl)

private theorem leaf5582FlatSound : Sound leaf5582Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5582CertificateValid
    leaf5582InnerLogValid leaf5582CoversExact leaf5582LowerChecked

private noncomputable def leaf5583Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (51/128), chiHi := (13/32) }

private noncomputable def leaf5583Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435757/268435456) }, vSqrt := { lower := (65529/65536), upper := (1108345889/1108293632) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (595931325/536870912) }, upper := { exponent := 1, mantissa := (2311/2048) } }, logOuter := sk135LogOuterCertificate, logK := sk135LogKCertificate, logChi := chi262LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (2216639521/2216587264) } }, logDArg := sk135LogDArgCertificate }

private noncomputable def leaf5583InnerLog : WideLogData :=
  innerPair257Data

set_option maxRecDepth 1000000 in
private theorem leaf5583LocalValidity :
    LeafFacts leaf5583Box leaf5583Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5583Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (1108345889/1108293632) }) = true
      norm_num [leaf5583Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5583CertificateValid :
    WideCertificateValid leaf5583Box leaf5583Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk135ValidityFacts chi262ValidityFacts
    leaf5583LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5583CoverageChecked :
    coverageCheck (innerAD leaf5583Box) leaf5583InnerLog = true := by
  rfl'

private theorem leaf5583InnerLogValid :
    leaf5583InnerLog.Valid 8 (innerAD leaf5583Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint76PositiveFacts.valid leaf5583CoverageChecked

private noncomputable def leaf5583InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907369/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5583InputLogOnePlusV_eq :
    leaf5583InputLogOnePlusV = outerEnclosure 24
      (leaf5583Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5583RoundedFacts : LeafRoundedFacts 8
    leaf5583Certificate.logOnePlusV leaf5583InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5583InputLogOnePlusV_eq }

private noncomputable def leaf5583Inputs : Inputs :=
  inputsOfCaches globalInput sk135RoundedInputs
    chi262InputQChi innerPair257Input
    leaf5583InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5583LowerChecked :
    lowerCheck 24 leaf5583Box leaf5583Inputs = true := by
  rfl'

private theorem leaf5583CoversExact : CoversExact 8
    leaf5583Box leaf5583Certificate leaf5583InnerLog leaf5583Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk135RoundedFacts chi262RoundedFacts
    innerPair257RoundedFacts leaf5583RoundedFacts (by rfl)

private theorem leaf5583FlatSound : Sound leaf5583Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5583CertificateValid
    leaf5583InnerLogValid leaf5583CoversExact leaf5583LowerChecked

private noncomputable def leaf5584Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (51/128), chiHi := (13/32) }

private noncomputable def leaf5584Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435759/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357075968) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (599273455/536870912) }, upper := { exponent := 1, mantissa := (581/512) } }, logOuter := sk136LogOuterCertificate, logK := sk136LogKCertificate, logChi := chi262LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715798527/68714151936) } }, logDArg := sk136LogDArgCertificate }

private noncomputable def leaf5584InnerLog : WideLogData :=
  innerPair257Data

set_option maxRecDepth 1000000 in
private theorem leaf5584LocalValidity :
    LeafFacts leaf5584Box leaf5584Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5584Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357075968) }) = true
      norm_num [leaf5584Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5584CertificateValid :
    WideCertificateValid leaf5584Box leaf5584Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk136ValidityFacts chi262ValidityFacts
    leaf5584LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5584CoverageChecked :
    coverageCheck (innerAD leaf5584Box) leaf5584InnerLog = true := by
  rfl'

private theorem leaf5584InnerLogValid :
    leaf5584InnerLog.Valid 8 (innerAD leaf5584Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint76PositiveFacts.valid leaf5584CoverageChecked

private noncomputable def leaf5584InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629483/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5584InputLogOnePlusV_eq :
    leaf5584InputLogOnePlusV = outerEnclosure 24
      (leaf5584Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5584RoundedFacts : LeafRoundedFacts 8
    leaf5584Certificate.logOnePlusV leaf5584InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5584InputLogOnePlusV_eq }

private noncomputable def leaf5584Inputs : Inputs :=
  inputsOfCaches globalInput sk136RoundedInputs
    chi262InputQChi innerPair257Input
    leaf5584InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5584LowerChecked :
    lowerCheck 24 leaf5584Box leaf5584Inputs = true := by
  rfl'

private theorem leaf5584CoversExact : CoversExact 8
    leaf5584Box leaf5584Certificate leaf5584InnerLog leaf5584Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk136RoundedFacts chi262RoundedFacts
    innerPair257RoundedFacts leaf5584RoundedFacts (by rfl)

private theorem leaf5584FlatSound : Sound leaf5584Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5584CertificateValid
    leaf5584InnerLogValid leaf5584CoversExact leaf5584LowerChecked

private noncomputable def leaf5585Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (13/32), chiHi := (53/128) }

private noncomputable def leaf5585Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435755/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357106176) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (595538135/536870912) }, upper := { exponent := 1, mantissa := (9237/8192) } }, logOuter := sk133LogOuterCertificate, logK := sk133LogKCertificate, logChi := chi263LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715828735/68714212352) } }, logDArg := sk133LogDArgCertificate }

private noncomputable def leaf5585InnerLog : WideLogData :=
  innerPair257Data

set_option maxRecDepth 1000000 in
private theorem leaf5585LocalValidity :
    LeafFacts leaf5585Box leaf5585Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5585Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357106176) }) = true
      norm_num [leaf5585Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5585CertificateValid :
    WideCertificateValid leaf5585Box leaf5585Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk133ValidityFacts chi263ValidityFacts
    leaf5585LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5585CoverageChecked :
    coverageCheck (innerAD leaf5585Box) leaf5585InnerLog = true := by
  rfl'

private theorem leaf5585InnerLogValid :
    leaf5585InnerLog.Valid 8 (innerAD leaf5585Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint76PositiveFacts.valid leaf5585CoverageChecked

private noncomputable def leaf5585InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629475/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5585InputLogOnePlusV_eq :
    leaf5585InputLogOnePlusV = outerEnclosure 24
      (leaf5585Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5585RoundedFacts : LeafRoundedFacts 8
    leaf5585Certificate.logOnePlusV leaf5585InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5585InputLogOnePlusV_eq }

private noncomputable def leaf5585Inputs : Inputs :=
  inputsOfCaches globalInput sk133RoundedInputs
    chi263InputQChi innerPair257Input
    leaf5585InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5585LowerChecked :
    lowerCheck 24 leaf5585Box leaf5585Inputs = true := by
  rfl'

private theorem leaf5585CoversExact : CoversExact 8
    leaf5585Box leaf5585Certificate leaf5585InnerLog leaf5585Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk133RoundedFacts chi263RoundedFacts
    innerPair257RoundedFacts leaf5585RoundedFacts (by rfl)

private theorem leaf5585FlatSound : Sound leaf5585Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5585CertificateValid
    leaf5585InnerLogValid leaf5585CoversExact leaf5585LowerChecked

private noncomputable def leaf5586Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (13/32), chiHi := (53/128) }

private noncomputable def leaf5586Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435757/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357079040) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (598945797/536870912) }, upper := { exponent := 1, mantissa := (4645/4096) } }, logOuter := sk134LogOuterCertificate, logK := sk134LogKCertificate, logChi := chi263LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715801599/68714158080) } }, logDArg := sk134LogDArgCertificate }

private noncomputable def leaf5586InnerLog : WideLogData :=
  innerPair257Data

set_option maxRecDepth 1000000 in
private theorem leaf5586LocalValidity :
    LeafFacts leaf5586Box leaf5586Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5586Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357079040) }) = true
      norm_num [leaf5586Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5586CertificateValid :
    WideCertificateValid leaf5586Box leaf5586Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk134ValidityFacts chi263ValidityFacts
    leaf5586LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5586CoverageChecked :
    coverageCheck (innerAD leaf5586Box) leaf5586InnerLog = true := by
  rfl'

private theorem leaf5586InnerLogValid :
    leaf5586InnerLog.Valid 8 (innerAD leaf5586Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint76PositiveFacts.valid leaf5586CoverageChecked

private noncomputable def leaf5586InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814741/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5586InputLogOnePlusV_eq :
    leaf5586InputLogOnePlusV = outerEnclosure 24
      (leaf5586Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5586RoundedFacts : LeafRoundedFacts 8
    leaf5586Certificate.logOnePlusV leaf5586InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5586InputLogOnePlusV_eq }

private noncomputable def leaf5586Inputs : Inputs :=
  inputsOfCaches globalInput sk134RoundedInputs
    chi263InputQChi innerPair257Input
    leaf5586InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5586LowerChecked :
    lowerCheck 24 leaf5586Box leaf5586Inputs = true := by
  rfl'

private theorem leaf5586CoversExact : CoversExact 8
    leaf5586Box leaf5586Certificate leaf5586InnerLog leaf5586Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk134RoundedFacts chi263RoundedFacts
    innerPair257RoundedFacts leaf5586RoundedFacts (by rfl)

private theorem leaf5586FlatSound : Sound leaf5586Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5586CertificateValid
    leaf5586InnerLogValid leaf5586CoversExact leaf5586LowerChecked

private noncomputable def leaf5587Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (53/128), chiHi := (27/64) }

private noncomputable def leaf5587Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435757/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357056512) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (601829205/536870912) }, upper := { exponent := 1, mantissa := (4667/4096) } }, logOuter := sk133LogOuterCertificate, logK := sk133LogKCertificate, logChi := chi264LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715779071/68714113024) } }, logDArg := sk133LogDArgCertificate }

private noncomputable def leaf5587InnerLog : WideLogData :=
  innerPair257Data

set_option maxRecDepth 1000000 in
private theorem leaf5587LocalValidity :
    LeafFacts leaf5587Box leaf5587Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5587Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357056512) }) = true
      norm_num [leaf5587Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5587CertificateValid :
    WideCertificateValid leaf5587Box leaf5587Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk133ValidityFacts chi264ValidityFacts
    leaf5587LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5587CoverageChecked :
    coverageCheck (innerAD leaf5587Box) leaf5587InnerLog = true := by
  rfl'

private theorem leaf5587InnerLogValid :
    leaf5587InnerLog.Valid 8 (innerAD leaf5587Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint76PositiveFacts.valid leaf5587CoverageChecked

private noncomputable def leaf5587InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (726843/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf5587InputLogOnePlusV_eq :
    leaf5587InputLogOnePlusV = outerEnclosure 24
      (leaf5587Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5587RoundedFacts : LeafRoundedFacts 8
    leaf5587Certificate.logOnePlusV leaf5587InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5587InputLogOnePlusV_eq }

private noncomputable def leaf5587Inputs : Inputs :=
  inputsOfCaches globalInput sk133RoundedInputs
    chi264InputQChi innerPair257Input
    leaf5587InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5587LowerChecked :
    lowerCheck 24 leaf5587Box leaf5587Inputs = true := by
  rfl'

private theorem leaf5587CoversExact : CoversExact 8
    leaf5587Box leaf5587Certificate leaf5587InnerLog leaf5587Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk133RoundedFacts chi264RoundedFacts
    innerPair257RoundedFacts leaf5587RoundedFacts (by rfl)

private theorem leaf5587FlatSound : Sound leaf5587Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5587CertificateValid
    leaf5587InnerLogValid leaf5587CoversExact leaf5587LowerChecked

private noncomputable def leaf5588Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (53/128), chiHi := (27/64) }

private noncomputable def leaf5588Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435759/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357028864) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (605302399/536870912) }, upper := { exponent := 1, mantissa := (2347/2048) } }, logOuter := sk134LogOuterCertificate, logK := sk134LogKCertificate, logChi := chi264LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715751423/68714057728) } }, logDArg := sk134LogDArgCertificate }

private noncomputable def leaf5588InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf5588LocalValidity :
    LeafFacts leaf5588Box leaf5588Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5588Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357028864) }) = true
      norm_num [leaf5588Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5588CertificateValid :
    WideCertificateValid leaf5588Box leaf5588Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk134ValidityFacts chi264ValidityFacts
    leaf5588LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5588CoverageChecked :
    coverageCheck (innerAD leaf5588Box) leaf5588InnerLog = true := by
  rfl'

private theorem leaf5588InnerLogValid :
    leaf5588InnerLog.Valid 8 (innerAD leaf5588Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf5588CoverageChecked

private noncomputable def leaf5588InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814747/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5588InputLogOnePlusV_eq :
    leaf5588InputLogOnePlusV = outerEnclosure 24
      (leaf5588Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5588RoundedFacts : LeafRoundedFacts 8
    leaf5588Certificate.logOnePlusV leaf5588InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5588InputLogOnePlusV_eq }

private noncomputable def leaf5588Inputs : Inputs :=
  inputsOfCaches globalInput sk134RoundedInputs
    chi264InputQChi innerPair264Input
    leaf5588InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5588LowerChecked :
    lowerCheck 24 leaf5588Box leaf5588Inputs = true := by
  rfl'

private theorem leaf5588CoversExact : CoversExact 8
    leaf5588Box leaf5588Certificate leaf5588InnerLog leaf5588Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk134RoundedFacts chi264RoundedFacts
    innerPair264RoundedFacts leaf5588RoundedFacts (by rfl)

private theorem leaf5588FlatSound : Sound leaf5588Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5588CertificateValid
    leaf5588InnerLogValid leaf5588CoversExact leaf5588LowerChecked

private noncomputable def leaf5589Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (13/32), chiHi := (53/128) }

private noncomputable def leaf5589Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435759/268435456) }, vSqrt := { lower := (65529/65536), upper := (4908388937/4908150272) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (602353459/536870912) }, upper := { exponent := 1, mantissa := (9343/8192) } }, logOuter := sk135LogOuterCertificate, logK := sk135LogKCertificate, logChi := chi263LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (9816539209/9816300544) } }, logDArg := sk135LogDArgCertificate }

private noncomputable def leaf5589InnerLog : WideLogData :=
  innerPair257Data

set_option maxRecDepth 1000000 in
private theorem leaf5589LocalValidity :
    LeafFacts leaf5589Box leaf5589Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5589Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4908388937/4908150272) }) = true
      norm_num [leaf5589Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5589CertificateValid :
    WideCertificateValid leaf5589Box leaf5589Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk135ValidityFacts chi263ValidityFacts
    leaf5589LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5589CoverageChecked :
    coverageCheck (innerAD leaf5589Box) leaf5589InnerLog = true := by
  rfl'

private theorem leaf5589InnerLogValid :
    leaf5589InnerLog.Valid 8 (innerAD leaf5589Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint76PositiveFacts.valid leaf5589CoverageChecked

private noncomputable def leaf5589InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629489/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5589InputLogOnePlusV_eq :
    leaf5589InputLogOnePlusV = outerEnclosure 24
      (leaf5589Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5589RoundedFacts : LeafRoundedFacts 8
    leaf5589Certificate.logOnePlusV leaf5589InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5589InputLogOnePlusV_eq }

private noncomputable def leaf5589Inputs : Inputs :=
  inputsOfCaches globalInput sk135RoundedInputs
    chi263InputQChi innerPair257Input
    leaf5589InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5589LowerChecked :
    lowerCheck 24 leaf5589Box leaf5589Inputs = true := by
  rfl'

private theorem leaf5589CoversExact : CoversExact 8
    leaf5589Box leaf5589Certificate leaf5589InnerLog leaf5589Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk135RoundedFacts chi263RoundedFacts
    innerPair257RoundedFacts leaf5589RoundedFacts (by rfl)

private theorem leaf5589FlatSound : Sound leaf5589Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5589CertificateValid
    leaf5589InnerLogValid leaf5589CoversExact leaf5589LowerChecked

private noncomputable def leaf5590Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (13/32), chiHi := (53/128) }

private noncomputable def leaf5590Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435761/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357024768) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (605761121/536870912) }, upper := { exponent := 1, mantissa := (2349/2048) } }, logOuter := sk136LogOuterCertificate, logK := sk136LogKCertificate, logChi := chi263LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715747327/68714049536) } }, logDArg := sk136LogDArgCertificate }

private noncomputable def leaf5590InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf5590LocalValidity :
    LeafFacts leaf5590Box leaf5590Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5590Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357024768) }) = true
      norm_num [leaf5590Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5590CertificateValid :
    WideCertificateValid leaf5590Box leaf5590Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk136ValidityFacts chi263ValidityFacts
    leaf5590LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5590CoverageChecked :
    coverageCheck (innerAD leaf5590Box) leaf5590InnerLog = true := by
  rfl'

private theorem leaf5590InnerLogValid :
    leaf5590InnerLog.Valid 8 (innerAD leaf5590Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf5590CoverageChecked

private noncomputable def leaf5590InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629495/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5590InputLogOnePlusV_eq :
    leaf5590InputLogOnePlusV = outerEnclosure 24
      (leaf5590Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5590RoundedFacts : LeafRoundedFacts 8
    leaf5590Certificate.logOnePlusV leaf5590InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5590InputLogOnePlusV_eq }

private noncomputable def leaf5590Inputs : Inputs :=
  inputsOfCaches globalInput sk136RoundedInputs
    chi263InputQChi innerPair264Input
    leaf5590InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5590LowerChecked :
    lowerCheck 24 leaf5590Box leaf5590Inputs = true := by
  rfl'

private theorem leaf5590CoversExact : CoversExact 8
    leaf5590Box leaf5590Certificate leaf5590InnerLog leaf5590Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk136RoundedFacts chi263RoundedFacts
    innerPair264RoundedFacts leaf5590RoundedFacts (by rfl)

private theorem leaf5590FlatSound : Sound leaf5590Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5590CertificateValid
    leaf5590InnerLogValid leaf5590CoversExact leaf5590LowerChecked

private noncomputable def leaf5591Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (53/128), chiHi := (27/64) }

private noncomputable def leaf5591Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435761/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357001216) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (608775593/536870912) }, upper := { exponent := 1, mantissa := (4721/4096) } }, logOuter := sk135LogOuterCertificate, logK := sk135LogKCertificate, logChi := chi264LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715723775/68714002432) } }, logDArg := sk135LogDArgCertificate }

private noncomputable def leaf5591InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf5591LocalValidity :
    LeafFacts leaf5591Box leaf5591Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5591Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357001216) }) = true
      norm_num [leaf5591Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5591CertificateValid :
    WideCertificateValid leaf5591Box leaf5591Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk135ValidityFacts chi264ValidityFacts
    leaf5591LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5591CoverageChecked :
    coverageCheck (innerAD leaf5591Box) leaf5591InnerLog = true := by
  rfl'

private theorem leaf5591InnerLogValid :
    leaf5591InnerLog.Valid 8 (innerAD leaf5591Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf5591CoverageChecked

private noncomputable def leaf5591InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629501/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5591InputLogOnePlusV_eq :
    leaf5591InputLogOnePlusV = outerEnclosure 24
      (leaf5591Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5591RoundedFacts : LeafRoundedFacts 8
    leaf5591Certificate.logOnePlusV leaf5591InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5591InputLogOnePlusV_eq }

private noncomputable def leaf5591Inputs : Inputs :=
  inputsOfCaches globalInput sk135RoundedInputs
    chi264InputQChi innerPair264Input
    leaf5591InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5591LowerChecked :
    lowerCheck 24 leaf5591Box leaf5591Inputs = true := by
  rfl'

private theorem leaf5591CoversExact : CoversExact 8
    leaf5591Box leaf5591Certificate leaf5591InnerLog leaf5591Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk135RoundedFacts chi264RoundedFacts
    innerPair264RoundedFacts leaf5591RoundedFacts (by rfl)

private theorem leaf5591FlatSound : Sound leaf5591Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5591CertificateValid
    leaf5591InnerLogValid leaf5591CoversExact leaf5591LowerChecked

private noncomputable def leaf5592Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (53/128), chiHi := (27/64) }

private noncomputable def leaf5592Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435763/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356973568) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (612248787/536870912) }, upper := { exponent := 1, mantissa := (1187/1024) } }, logOuter := sk136LogOuterCertificate, logK := sk136LogKCertificate, logChi := chi264LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715696127/68713947136) } }, logDArg := sk136LogDArgCertificate }

private noncomputable def leaf5592InnerLog : WideLogData :=
  innerPair265Data

set_option maxRecDepth 1000000 in
private theorem leaf5592LocalValidity :
    LeafFacts leaf5592Box leaf5592Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5592Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356973568) }) = true
      norm_num [leaf5592Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5592CertificateValid :
    WideCertificateValid leaf5592Box leaf5592Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk136ValidityFacts chi264ValidityFacts
    leaf5592LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5592CoverageChecked :
    coverageCheck (innerAD leaf5592Box) leaf5592InnerLog = true := by
  rfl'

private theorem leaf5592InnerLogValid :
    leaf5592InnerLog.Valid 8 (innerAD leaf5592Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint77PositiveFacts.valid leaf5592CoverageChecked

private noncomputable def leaf5592InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907377/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5592InputLogOnePlusV_eq :
    leaf5592InputLogOnePlusV = outerEnclosure 24
      (leaf5592Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5592RoundedFacts : LeafRoundedFacts 8
    leaf5592Certificate.logOnePlusV leaf5592InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5592InputLogOnePlusV_eq }

private noncomputable def leaf5592Inputs : Inputs :=
  inputsOfCaches globalInput sk136RoundedInputs
    chi264InputQChi innerPair265Input
    leaf5592InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5592LowerChecked :
    lowerCheck 24 leaf5592Box leaf5592Inputs = true := by
  rfl'

private theorem leaf5592CoversExact : CoversExact 8
    leaf5592Box leaf5592Certificate leaf5592InnerLog leaf5592Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk136RoundedFacts chi264RoundedFacts
    innerPair265RoundedFacts leaf5592RoundedFacts (by rfl)

private theorem leaf5592FlatSound : Sound leaf5592Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5592CertificateValid
    leaf5592InnerLogValid leaf5592CoversExact leaf5592LowerChecked

private noncomputable def leaf5593Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (27/64), chiHi := (55/128) }

private noncomputable def leaf5593Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435759/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357006848) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (608120275/536870912) }, upper := { exponent := 1, mantissa := (9431/8192) } }, logOuter := sk133LogOuterCertificate, logK := sk133LogKCertificate, logChi := chi265LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715729407/68714013696) } }, logDArg := sk133LogDArgCertificate }

private noncomputable def leaf5593InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf5593LocalValidity :
    LeafFacts leaf5593Box leaf5593Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5593Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357006848) }) = true
      norm_num [leaf5593Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5593CertificateValid :
    WideCertificateValid leaf5593Box leaf5593Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk133ValidityFacts chi265ValidityFacts
    leaf5593LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5593CoverageChecked :
    coverageCheck (innerAD leaf5593Box) leaf5593InnerLog = true := by
  rfl'

private theorem leaf5593InnerLogValid :
    leaf5593InnerLog.Valid 8 (innerAD leaf5593Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf5593CoverageChecked

private noncomputable def leaf5593InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907375/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5593InputLogOnePlusV_eq :
    leaf5593InputLogOnePlusV = outerEnclosure 24
      (leaf5593Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5593RoundedFacts : LeafRoundedFacts 8
    leaf5593Certificate.logOnePlusV leaf5593InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5593InputLogOnePlusV_eq }

private noncomputable def leaf5593Inputs : Inputs :=
  inputsOfCaches globalInput sk133RoundedInputs
    chi265InputQChi innerPair264Input
    leaf5593InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5593LowerChecked :
    lowerCheck 24 leaf5593Box leaf5593Inputs = true := by
  rfl'

private theorem leaf5593CoversExact : CoversExact 8
    leaf5593Box leaf5593Certificate leaf5593InnerLog leaf5593Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk133RoundedFacts chi265RoundedFacts
    innerPair264RoundedFacts leaf5593RoundedFacts (by rfl)

private theorem leaf5593FlatSound : Sound leaf5593Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5593CertificateValid
    leaf5593InnerLogValid leaf5593CoversExact leaf5593LowerChecked

private noncomputable def leaf5594Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (27/64), chiHi := (55/128) }

private noncomputable def leaf5594Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435761/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356978688) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (611659001/536870912) }, upper := { exponent := 1, mantissa := (4743/4096) } }, logOuter := sk134LogOuterCertificate, logK := sk134LogKCertificate, logChi := chi265LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715701247/68713957376) } }, logDArg := sk134LogDArgCertificate }

private noncomputable def leaf5594InnerLog : WideLogData :=
  innerPair265Data

set_option maxRecDepth 1000000 in
private theorem leaf5594LocalValidity :
    LeafFacts leaf5594Box leaf5594Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5594Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356978688) }) = true
      norm_num [leaf5594Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5594CertificateValid :
    WideCertificateValid leaf5594Box leaf5594Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk134ValidityFacts chi265ValidityFacts
    leaf5594LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5594CoverageChecked :
    coverageCheck (innerAD leaf5594Box) leaf5594InnerLog = true := by
  rfl'

private theorem leaf5594InnerLogValid :
    leaf5594InnerLog.Valid 8 (innerAD leaf5594Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint77PositiveFacts.valid leaf5594CoverageChecked

private noncomputable def leaf5594InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629507/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5594InputLogOnePlusV_eq :
    leaf5594InputLogOnePlusV = outerEnclosure 24
      (leaf5594Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5594RoundedFacts : LeafRoundedFacts 8
    leaf5594Certificate.logOnePlusV leaf5594InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5594InputLogOnePlusV_eq }

private noncomputable def leaf5594Inputs : Inputs :=
  inputsOfCaches globalInput sk134RoundedInputs
    chi265InputQChi innerPair265Input
    leaf5594InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5594LowerChecked :
    lowerCheck 24 leaf5594Box leaf5594Inputs = true := by
  rfl'

private theorem leaf5594CoversExact : CoversExact 8
    leaf5594Box leaf5594Certificate leaf5594InnerLog leaf5594Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk134RoundedFacts chi265RoundedFacts
    innerPair265RoundedFacts leaf5594RoundedFacts (by rfl)

private theorem leaf5594FlatSound : Sound leaf5594Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5594CertificateValid
    leaf5594InnerLogValid leaf5594CoversExact leaf5594LowerChecked

private noncomputable def leaf5595Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (55/128), chiHi := (7/16) }

private noncomputable def leaf5595Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435761/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356957184) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (614411345/536870912) }, upper := { exponent := 1, mantissa := (1191/1024) } }, logOuter := sk133LogOuterCertificate, logK := sk133LogKCertificate, logChi := chi266LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715679743/68713914368) } }, logDArg := sk133LogDArgCertificate }

private noncomputable def leaf5595InnerLog : WideLogData :=
  innerPair265Data

set_option maxRecDepth 1000000 in
private theorem leaf5595LocalValidity :
    LeafFacts leaf5595Box leaf5595Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5595Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356957184) }) = true
      norm_num [leaf5595Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5595CertificateValid :
    WideCertificateValid leaf5595Box leaf5595Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk133ValidityFacts chi266ValidityFacts
    leaf5595LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5595CoverageChecked :
    coverageCheck (innerAD leaf5595Box) leaf5595InnerLog = true := by
  rfl'

private theorem leaf5595InnerLogValid :
    leaf5595InnerLog.Valid 8 (innerAD leaf5595Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint77PositiveFacts.valid leaf5595CoverageChecked

private noncomputable def leaf5595InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453689/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf5595InputLogOnePlusV_eq :
    leaf5595InputLogOnePlusV = outerEnclosure 24
      (leaf5595Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5595RoundedFacts : LeafRoundedFacts 8
    leaf5595Certificate.logOnePlusV leaf5595InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5595InputLogOnePlusV_eq }

private noncomputable def leaf5595Inputs : Inputs :=
  inputsOfCaches globalInput sk133RoundedInputs
    chi266InputQChi innerPair265Input
    leaf5595InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5595LowerChecked :
    lowerCheck 24 leaf5595Box leaf5595Inputs = true := by
  rfl'

private theorem leaf5595CoversExact : CoversExact 8
    leaf5595Box leaf5595Certificate leaf5595InnerLog leaf5595Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk133RoundedFacts chi266RoundedFacts
    innerPair265RoundedFacts leaf5595RoundedFacts (by rfl)

private theorem leaf5595FlatSound : Sound leaf5595Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5595CertificateValid
    leaf5595InnerLogValid leaf5595CoversExact leaf5595LowerChecked

private noncomputable def leaf5596Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (55/128), chiHi := (7/16) }

private noncomputable def leaf5596Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435763/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356928512) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (618015603/536870912) }, upper := { exponent := 1, mantissa := (599/512) } }, logOuter := sk134LogOuterCertificate, logK := sk134LogKCertificate, logChi := chi266LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715651071/68713857024) } }, logDArg := sk134LogDArgCertificate }

private noncomputable def leaf5596InnerLog : WideLogData :=
  innerPair265Data

set_option maxRecDepth 1000000 in
private theorem leaf5596LocalValidity :
    LeafFacts leaf5596Box leaf5596Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5596Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356928512) }) = true
      norm_num [leaf5596Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5596CertificateValid :
    WideCertificateValid leaf5596Box leaf5596Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk134ValidityFacts chi266ValidityFacts
    leaf5596LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5596CoverageChecked :
    coverageCheck (innerAD leaf5596Box) leaf5596InnerLog = true := by
  rfl'

private theorem leaf5596InnerLogValid :
    leaf5596InnerLog.Valid 8 (innerAD leaf5596Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint77PositiveFacts.valid leaf5596CoverageChecked

private noncomputable def leaf5596InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629519/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5596InputLogOnePlusV_eq :
    leaf5596InputLogOnePlusV = outerEnclosure 24
      (leaf5596Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5596RoundedFacts : LeafRoundedFacts 8
    leaf5596Certificate.logOnePlusV leaf5596InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5596InputLogOnePlusV_eq }

private noncomputable def leaf5596Inputs : Inputs :=
  inputsOfCaches globalInput sk134RoundedInputs
    chi266InputQChi innerPair265Input
    leaf5596InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5596LowerChecked :
    lowerCheck 24 leaf5596Box leaf5596Inputs = true := by
  rfl'

private theorem leaf5596CoversExact : CoversExact 8
    leaf5596Box leaf5596Certificate leaf5596InnerLog leaf5596Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk134RoundedFacts chi266RoundedFacts
    innerPair265RoundedFacts leaf5596RoundedFacts (by rfl)

private theorem leaf5596FlatSound : Sound leaf5596Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5596CertificateValid
    leaf5596InnerLogValid leaf5596CoversExact leaf5596LowerChecked

private noncomputable def leaf5597Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (27/64), chiHi := (55/128) }

private noncomputable def leaf5597Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435763/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356950528) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (615197727/536870912) }, upper := { exponent := 1, mantissa := (9541/8192) } }, logOuter := sk135LogOuterCertificate, logK := sk135LogKCertificate, logChi := chi265LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715673087/68713901056) } }, logDArg := sk135LogDArgCertificate }

private noncomputable def leaf5597InnerLog : WideLogData :=
  innerPair265Data

set_option maxRecDepth 1000000 in
private theorem leaf5597LocalValidity :
    LeafFacts leaf5597Box leaf5597Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5597Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356950528) }) = true
      norm_num [leaf5597Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5597CertificateValid :
    WideCertificateValid leaf5597Box leaf5597Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk135ValidityFacts chi265ValidityFacts
    leaf5597LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5597CoverageChecked :
    coverageCheck (innerAD leaf5597Box) leaf5597InnerLog = true := by
  rfl'

private theorem leaf5597InnerLogValid :
    leaf5597InnerLog.Valid 8 (innerAD leaf5597Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint77PositiveFacts.valid leaf5597CoverageChecked

private noncomputable def leaf5597InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629513/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5597InputLogOnePlusV_eq :
    leaf5597InputLogOnePlusV = outerEnclosure 24
      (leaf5597Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5597RoundedFacts : LeafRoundedFacts 8
    leaf5597Certificate.logOnePlusV leaf5597InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5597InputLogOnePlusV_eq }

private noncomputable def leaf5597Inputs : Inputs :=
  inputsOfCaches globalInput sk135RoundedInputs
    chi265InputQChi innerPair265Input
    leaf5597InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5597LowerChecked :
    lowerCheck 24 leaf5597Box leaf5597Inputs = true := by
  rfl'

private theorem leaf5597CoversExact : CoversExact 8
    leaf5597Box leaf5597Certificate leaf5597InnerLog leaf5597Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk135RoundedFacts chi265RoundedFacts
    innerPair265RoundedFacts leaf5597RoundedFacts (by rfl)

private theorem leaf5597FlatSound : Sound leaf5597Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5597CertificateValid
    leaf5597InnerLogValid leaf5597CoversExact leaf5597LowerChecked

private noncomputable def leaf5598Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (27/64), chiHi := (55/128) }

private noncomputable def leaf5598Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435765/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356922368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (618736453/536870912) }, upper := { exponent := 1, mantissa := (2399/2048) } }, logOuter := sk136LogOuterCertificate, logK := sk136LogKCertificate, logChi := chi265LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715644927/68713844736) } }, logDArg := sk136LogDArgCertificate }

private noncomputable def leaf5598InnerLog : WideLogData :=
  innerPair265Data

set_option maxRecDepth 1000000 in
private theorem leaf5598LocalValidity :
    LeafFacts leaf5598Box leaf5598Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5598Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356922368) }) = true
      norm_num [leaf5598Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5598CertificateValid :
    WideCertificateValid leaf5598Box leaf5598Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk136ValidityFacts chi265ValidityFacts
    leaf5598LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5598CoverageChecked :
    coverageCheck (innerAD leaf5598Box) leaf5598InnerLog = true := by
  rfl'

private theorem leaf5598InnerLogValid :
    leaf5598InnerLog.Valid 8 (innerAD leaf5598Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint77PositiveFacts.valid leaf5598CoverageChecked

private noncomputable def leaf5598InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (726845/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf5598InputLogOnePlusV_eq :
    leaf5598InputLogOnePlusV = outerEnclosure 24
      (leaf5598Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5598RoundedFacts : LeafRoundedFacts 8
    leaf5598Certificate.logOnePlusV leaf5598InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5598InputLogOnePlusV_eq }

private noncomputable def leaf5598Inputs : Inputs :=
  inputsOfCaches globalInput sk136RoundedInputs
    chi265InputQChi innerPair265Input
    leaf5598InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5598LowerChecked :
    lowerCheck 24 leaf5598Box leaf5598Inputs = true := by
  rfl'

private theorem leaf5598CoversExact : CoversExact 8
    leaf5598Box leaf5598Certificate leaf5598InnerLog leaf5598Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk136RoundedFacts chi265RoundedFacts
    innerPair265RoundedFacts leaf5598RoundedFacts (by rfl)

private theorem leaf5598FlatSound : Sound leaf5598Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5598CertificateValid
    leaf5598InnerLogValid leaf5598CoversExact leaf5598LowerChecked

private noncomputable def leaf5599Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (55/128), chiHi := (7/16) }

private noncomputable def leaf5599Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435765/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356899840) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (621619861/536870912) }, upper := { exponent := 1, mantissa := (1205/1024) } }, logOuter := sk135LogOuterCertificate, logK := sk135LogKCertificate, logChi := chi266LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715622399/68713799680) } }, logDArg := sk135LogDArgCertificate }

private noncomputable def leaf5599InnerLog : WideLogData :=
  innerPair272Data

set_option maxRecDepth 1000000 in
private theorem leaf5599LocalValidity :
    LeafFacts leaf5599Box leaf5599Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5599Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356899840) }) = true
      norm_num [leaf5599Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5599CertificateValid :
    WideCertificateValid leaf5599Box leaf5599Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk135ValidityFacts chi266ValidityFacts
    leaf5599LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5599CoverageChecked :
    coverageCheck (innerAD leaf5599Box) leaf5599InnerLog = true := by
  rfl'

private theorem leaf5599InnerLogValid :
    leaf5599InnerLog.Valid 8 (innerAD leaf5599Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint77PositiveFacts.valid leaf5599CoverageChecked

private noncomputable def leaf5599InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814763/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5599InputLogOnePlusV_eq :
    leaf5599InputLogOnePlusV = outerEnclosure 24
      (leaf5599Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5599RoundedFacts : LeafRoundedFacts 8
    leaf5599Certificate.logOnePlusV leaf5599InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5599InputLogOnePlusV_eq }

private noncomputable def leaf5599Inputs : Inputs :=
  inputsOfCaches globalInput sk135RoundedInputs
    chi266InputQChi innerPair272Input
    leaf5599InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5599LowerChecked :
    lowerCheck 24 leaf5599Box leaf5599Inputs = true := by
  rfl'

private theorem leaf5599CoversExact : CoversExact 8
    leaf5599Box leaf5599Certificate leaf5599InnerLog leaf5599Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk135RoundedFacts chi266RoundedFacts
    innerPair272RoundedFacts leaf5599RoundedFacts (by rfl)

private theorem leaf5599FlatSound : Sound leaf5599Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5599CertificateValid
    leaf5599InnerLogValid leaf5599CoversExact leaf5599LowerChecked

private noncomputable def leaf5600Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (55/128), chiHi := (7/16) }

private noncomputable def leaf5600Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435767/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356871168) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (625224119/536870912) }, upper := { exponent := 1, mantissa := (303/256) } }, logOuter := sk136LogOuterCertificate, logK := sk136LogKCertificate, logChi := chi266LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715593727/68713742336) } }, logDArg := sk136LogDArgCertificate }

private noncomputable def leaf5600InnerLog : WideLogData :=
  innerPair272Data

set_option maxRecDepth 1000000 in
private theorem leaf5600LocalValidity :
    LeafFacts leaf5600Box leaf5600Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5600Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356871168) }) = true
      norm_num [leaf5600Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5600CertificateValid :
    WideCertificateValid leaf5600Box leaf5600Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk136ValidityFacts chi266ValidityFacts
    leaf5600LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5600CoverageChecked :
    coverageCheck (innerAD leaf5600Box) leaf5600InnerLog = true := by
  rfl'

private theorem leaf5600InnerLogValid :
    leaf5600InnerLog.Valid 8 (innerAD leaf5600Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint77PositiveFacts.valid leaf5600CoverageChecked

private noncomputable def leaf5600InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629533/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5600InputLogOnePlusV_eq :
    leaf5600InputLogOnePlusV = outerEnclosure 24
      (leaf5600Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5600RoundedFacts : LeafRoundedFacts 8
    leaf5600Certificate.logOnePlusV leaf5600InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5600InputLogOnePlusV_eq }

private noncomputable def leaf5600Inputs : Inputs :=
  inputsOfCaches globalInput sk136RoundedInputs
    chi266InputQChi innerPair272Input
    leaf5600InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5600LowerChecked :
    lowerCheck 24 leaf5600Box leaf5600Inputs = true := by
  rfl'

private theorem leaf5600CoversExact : CoversExact 8
    leaf5600Box leaf5600Certificate leaf5600InnerLog leaf5600Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk136RoundedFacts chi266RoundedFacts
    innerPair272RoundedFacts leaf5600RoundedFacts (by rfl)

private theorem leaf5600FlatSound : Sound leaf5600Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5600CertificateValid
    leaf5600InnerLogValid leaf5600CoversExact leaf5600LowerChecked

private noncomputable def leaf5601Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (3/8), chiHi := (49/128) }

private noncomputable def leaf5601Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435755/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357204480) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (582955991/536870912) }, upper := { exponent := 1, mantissa := (9045/8192) } }, logOuter := sk137LogOuterCertificate, logK := sk137LogKCertificate, logChi := chi259LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715927039/68714408960) } }, logDArg := sk137LogDArgCertificate }

private noncomputable def leaf5601InnerLog : WideLogData :=
  innerPair331Data

set_option maxRecDepth 1000000 in
private theorem leaf5601LocalValidity :
    LeafFacts leaf5601Box leaf5601Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5601Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357204480) }) = true
      norm_num [leaf5601Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5601CertificateValid :
    WideCertificateValid leaf5601Box leaf5601Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk137ValidityFacts chi259ValidityFacts
    leaf5601LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5601CoverageChecked :
    coverageCheck (innerAD leaf5601Box) leaf5601InnerLog = true := by
  rfl'

private theorem leaf5601InnerLogValid :
    leaf5601InnerLog.Valid 8 (innerAD leaf5601Box) :=
  wideLogDataValid_of_cachedCheck endpoint88PositiveFacts
    endpoint80PositiveFacts.valid leaf5601CoverageChecked

private noncomputable def leaf5601InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629451/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5601InputLogOnePlusV_eq :
    leaf5601InputLogOnePlusV = outerEnclosure 24
      (leaf5601Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5601RoundedFacts : LeafRoundedFacts 8
    leaf5601Certificate.logOnePlusV leaf5601InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5601InputLogOnePlusV_eq }

private noncomputable def leaf5601Inputs : Inputs :=
  inputsOfCaches globalInput sk137RoundedInputs
    chi259InputQChi innerPair331Input
    leaf5601InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5601LowerChecked :
    lowerCheck 24 leaf5601Box leaf5601Inputs = true := by
  rfl'

private theorem leaf5601CoversExact : CoversExact 8
    leaf5601Box leaf5601Certificate leaf5601InnerLog leaf5601Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk137RoundedFacts chi259RoundedFacts
    innerPair331RoundedFacts leaf5601RoundedFacts (by rfl)

private theorem leaf5601FlatSound : Sound leaf5601Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5601CertificateValid
    leaf5601InnerLogValid leaf5601CoversExact leaf5601LowerChecked

private noncomputable def leaf5602Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (3/8), chiHi := (49/128) }

private noncomputable def leaf5602Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435757/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357179392) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (586101525/536870912) }, upper := { exponent := 1, mantissa := (4547/4096) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi259LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715901951/68714358784) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf5602InnerLog : WideLogData :=
  innerPair250Data

set_option maxRecDepth 1000000 in
private theorem leaf5602LocalValidity :
    LeafFacts leaf5602Box leaf5602Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5602Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357179392) }) = true
      norm_num [leaf5602Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5602CertificateValid :
    WideCertificateValid leaf5602Box leaf5602Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi259ValidityFacts
    leaf5602LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5602CoverageChecked :
    coverageCheck (innerAD leaf5602Box) leaf5602InnerLog = true := by
  rfl'

private theorem leaf5602InnerLogValid :
    leaf5602InnerLog.Valid 8 (innerAD leaf5602Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint75PositiveFacts.valid leaf5602CoverageChecked

private noncomputable def leaf5602InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814729/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5602InputLogOnePlusV_eq :
    leaf5602InputLogOnePlusV = outerEnclosure 24
      (leaf5602Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5602RoundedFacts : LeafRoundedFacts 8
    leaf5602Certificate.logOnePlusV leaf5602InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5602InputLogOnePlusV_eq }

private noncomputable def leaf5602Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi259InputQChi innerPair250Input
    leaf5602InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5602LowerChecked :
    lowerCheck 24 leaf5602Box leaf5602Inputs = true := by
  rfl'

private theorem leaf5602CoversExact : CoversExact 8
    leaf5602Box leaf5602Certificate leaf5602InnerLog leaf5602Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi259RoundedFacts
    innerPair250RoundedFacts leaf5602RoundedFacts (by rfl)

private theorem leaf5602FlatSound : Sound leaf5602Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5602CertificateValid
    leaf5602InnerLogValid leaf5602CoversExact leaf5602LowerChecked

private noncomputable def leaf5603Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (49/128), chiHi := (25/64) }

private noncomputable def leaf5603Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435757/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357152768) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (589509189/536870912) }, upper := { exponent := 1, mantissa := (4573/4096) } }, logOuter := sk137LogOuterCertificate, logK := sk137LogKCertificate, logChi := chi260LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715875327/68714305536) } }, logDArg := sk137LogDArgCertificate }

private noncomputable def leaf5603InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf5603LocalValidity :
    LeafFacts leaf5603Box leaf5603Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5603Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357152768) }) = true
      norm_num [leaf5603Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5603CertificateValid :
    WideCertificateValid leaf5603Box leaf5603Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk137ValidityFacts chi260ValidityFacts
    leaf5603LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5603CoverageChecked :
    coverageCheck (innerAD leaf5603Box) leaf5603InnerLog = true := by
  rfl'

private theorem leaf5603InnerLogValid :
    leaf5603InnerLog.Valid 8 (innerAD leaf5603Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf5603CoverageChecked

private noncomputable def leaf5603InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453683/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf5603InputLogOnePlusV_eq :
    leaf5603InputLogOnePlusV = outerEnclosure 24
      (leaf5603Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5603RoundedFacts : LeafRoundedFacts 8
    leaf5603Certificate.logOnePlusV leaf5603InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5603InputLogOnePlusV_eq }

private noncomputable def leaf5603Inputs : Inputs :=
  inputsOfCaches globalInput sk137RoundedInputs
    chi260InputQChi innerPair256Input
    leaf5603InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5603LowerChecked :
    lowerCheck 24 leaf5603Box leaf5603Inputs = true := by
  rfl'

private theorem leaf5603CoversExact : CoversExact 8
    leaf5603Box leaf5603Certificate leaf5603InnerLog leaf5603Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk137RoundedFacts chi260RoundedFacts
    innerPair256RoundedFacts leaf5603RoundedFacts (by rfl)

private theorem leaf5603FlatSound : Sound leaf5603Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5603CertificateValid
    leaf5603InnerLogValid leaf5603CoversExact leaf5603LowerChecked

private noncomputable def leaf5604Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (49/128), chiHi := (25/64) }

private noncomputable def leaf5604Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435759/268435456) }, vSqrt := { lower := (65529/65536), upper := (4908388937/4908161024) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (592720255/536870912) }, upper := { exponent := 1, mantissa := (2299/2048) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi260LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (9816549961/9816322048) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf5604InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf5604LocalValidity :
    LeafFacts leaf5604Box leaf5604Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5604Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4908388937/4908161024) }) = true
      norm_num [leaf5604Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5604CertificateValid :
    WideCertificateValid leaf5604Box leaf5604Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi260ValidityFacts
    leaf5604LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5604CoverageChecked :
    coverageCheck (innerAD leaf5604Box) leaf5604InnerLog = true := by
  rfl'

private theorem leaf5604InnerLogValid :
    leaf5604InnerLog.Valid 8 (innerAD leaf5604Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf5604CoverageChecked

private noncomputable def leaf5604InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814735/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5604InputLogOnePlusV_eq :
    leaf5604InputLogOnePlusV = outerEnclosure 24
      (leaf5604Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5604RoundedFacts : LeafRoundedFacts 8
    leaf5604Certificate.logOnePlusV leaf5604InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5604InputLogOnePlusV_eq }

private noncomputable def leaf5604Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi260InputQChi innerPair256Input
    leaf5604InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5604LowerChecked :
    lowerCheck 24 leaf5604Box leaf5604Inputs = true := by
  rfl'

private theorem leaf5604CoversExact : CoversExact 8
    leaf5604Box leaf5604Certificate leaf5604InnerLog leaf5604Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi260RoundedFacts
    innerPair256RoundedFacts leaf5604RoundedFacts (by rfl)

private theorem leaf5604FlatSound : Sound leaf5604Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5604CertificateValid
    leaf5604InnerLogValid leaf5604CoversExact leaf5604LowerChecked

private noncomputable def leaf5605Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (3/8), chiHi := (49/128) }

private noncomputable def leaf5605Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435759/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357154304) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (589247059/536870912) }, upper := { exponent := 1, mantissa := (9143/8192) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi259LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715876863/68714308608) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf5605InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf5605LocalValidity :
    LeafFacts leaf5605Box leaf5605Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5605Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357154304) }) = true
      norm_num [leaf5605Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5605CertificateValid :
    WideCertificateValid leaf5605Box leaf5605Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi259ValidityFacts
    leaf5605LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5605CoverageChecked :
    coverageCheck (innerAD leaf5605Box) leaf5605InnerLog = true := by
  rfl'

private theorem leaf5605InnerLogValid :
    leaf5605InnerLog.Valid 8 (innerAD leaf5605Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf5605CoverageChecked

private noncomputable def leaf5605InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453683/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf5605InputLogOnePlusV_eq :
    leaf5605InputLogOnePlusV = outerEnclosure 24
      (leaf5605Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5605RoundedFacts : LeafRoundedFacts 8
    leaf5605Certificate.logOnePlusV leaf5605InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5605InputLogOnePlusV_eq }

private noncomputable def leaf5605Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi259InputQChi innerPair256Input
    leaf5605InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5605LowerChecked :
    lowerCheck 24 leaf5605Box leaf5605Inputs = true := by
  rfl'

private theorem leaf5605CoversExact : CoversExact 8
    leaf5605Box leaf5605Certificate leaf5605InnerLog leaf5605Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi259RoundedFacts
    innerPair256RoundedFacts leaf5605RoundedFacts (by rfl)

private theorem leaf5605FlatSound : Sound leaf5605Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5605CertificateValid
    leaf5605InnerLogValid leaf5605CoversExact leaf5605LowerChecked

private noncomputable def leaf5606Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (3/8), chiHi := (49/128) }

private noncomputable def leaf5606Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435761/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357129216) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (592392593/536870912) }, upper := { exponent := 1, mantissa := (1149/1024) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi259LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715851775/68714258432) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf5606InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf5606LocalValidity :
    LeafFacts leaf5606Box leaf5606Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5606Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357129216) }) = true
      norm_num [leaf5606Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5606CertificateValid :
    WideCertificateValid leaf5606Box leaf5606Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi259ValidityFacts
    leaf5606LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5606CoverageChecked :
    coverageCheck (innerAD leaf5606Box) leaf5606InnerLog = true := by
  rfl'

private theorem leaf5606InnerLogValid :
    leaf5606InnerLog.Valid 8 (innerAD leaf5606Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf5606CoverageChecked

private noncomputable def leaf5606InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814735/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5606InputLogOnePlusV_eq :
    leaf5606InputLogOnePlusV = outerEnclosure 24
      (leaf5606Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5606RoundedFacts : LeafRoundedFacts 8
    leaf5606Certificate.logOnePlusV leaf5606InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5606InputLogOnePlusV_eq }

private noncomputable def leaf5606Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi259InputQChi innerPair256Input
    leaf5606InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5606LowerChecked :
    lowerCheck 24 leaf5606Box leaf5606Inputs = true := by
  rfl'

private theorem leaf5606CoversExact : CoversExact 8
    leaf5606Box leaf5606Certificate leaf5606InnerLog leaf5606Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi259RoundedFacts
    innerPair256RoundedFacts leaf5606RoundedFacts (by rfl)

private theorem leaf5606FlatSound : Sound leaf5606Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5606CertificateValid
    leaf5606InnerLogValid leaf5606CoversExact leaf5606LowerChecked

private noncomputable def leaf5607Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (49/128), chiHi := (25/64) }

private noncomputable def leaf5607Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435761/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357101568) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (595931321/536870912) }, upper := { exponent := 1, mantissa := (4623/4096) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi260LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715824127/68714203136) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf5607InnerLog : WideLogData :=
  innerPair300Data

set_option maxRecDepth 1000000 in
private theorem leaf5607LocalValidity :
    LeafFacts leaf5607Box leaf5607Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5607Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357101568) }) = true
      norm_num [leaf5607Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5607CertificateValid :
    WideCertificateValid leaf5607Box leaf5607Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi260ValidityFacts
    leaf5607LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5607CoverageChecked :
    coverageCheck (innerAD leaf5607Box) leaf5607InnerLog = true := by
  rfl'

private theorem leaf5607InnerLogValid :
    leaf5607InnerLog.Valid 8 (innerAD leaf5607Box) :=
  wideLogDataValid_of_cachedCheck endpoint80PositiveFacts
    endpoint292PositiveFacts.valid leaf5607CoverageChecked

private noncomputable def leaf5607InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629477/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5607InputLogOnePlusV_eq :
    leaf5607InputLogOnePlusV = outerEnclosure 24
      (leaf5607Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5607RoundedFacts : LeafRoundedFacts 8
    leaf5607Certificate.logOnePlusV leaf5607InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5607InputLogOnePlusV_eq }

private noncomputable def leaf5607Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi260InputQChi innerPair300Input
    leaf5607InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5607LowerChecked :
    lowerCheck 24 leaf5607Box leaf5607Inputs = true := by
  rfl'

private theorem leaf5607CoversExact : CoversExact 8
    leaf5607Box leaf5607Certificate leaf5607InnerLog leaf5607Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi260RoundedFacts
    innerPair300RoundedFacts leaf5607RoundedFacts (by rfl)

private theorem leaf5607FlatSound : Sound leaf5607Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5607CertificateValid
    leaf5607InnerLogValid leaf5607CoversExact leaf5607LowerChecked

private noncomputable def leaf5608Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (49/128), chiHi := (25/64) }

private noncomputable def leaf5608Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435763/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357075968) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (599142387/536870912) }, upper := { exponent := 1, mantissa := (581/512) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi260LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715798527/68714151936) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf5608InnerLog : WideLogData :=
  innerPair301Data

set_option maxRecDepth 1000000 in
private theorem leaf5608LocalValidity :
    LeafFacts leaf5608Box leaf5608Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5608Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357075968) }) = true
      norm_num [leaf5608Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5608CertificateValid :
    WideCertificateValid leaf5608Box leaf5608Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi260ValidityFacts
    leaf5608LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5608CoverageChecked :
    coverageCheck (innerAD leaf5608Box) leaf5608InnerLog = true := by
  rfl'

private theorem leaf5608InnerLogValid :
    leaf5608InnerLog.Valid 8 (innerAD leaf5608Box) :=
  wideLogDataValid_of_cachedCheck endpoint80PositiveFacts
    endpoint295PositiveFacts.valid leaf5608CoverageChecked

private noncomputable def leaf5608InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629483/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5608InputLogOnePlusV_eq :
    leaf5608InputLogOnePlusV = outerEnclosure 24
      (leaf5608Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5608RoundedFacts : LeafRoundedFacts 8
    leaf5608Certificate.logOnePlusV leaf5608InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5608InputLogOnePlusV_eq }

private noncomputable def leaf5608Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi260InputQChi innerPair301Input
    leaf5608InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5608LowerChecked :
    lowerCheck 24 leaf5608Box leaf5608Inputs = true := by
  rfl'

private theorem leaf5608CoversExact : CoversExact 8
    leaf5608Box leaf5608Certificate leaf5608InnerLog leaf5608Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi260RoundedFacts
    innerPair301RoundedFacts leaf5608RoundedFacts (by rfl)

private theorem leaf5608FlatSound : Sound leaf5608Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5608CertificateValid
    leaf5608InnerLogValid leaf5608CoversExact leaf5608LowerChecked

private noncomputable def leaf5609Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (25/64), chiHi := (51/128) }

private noncomputable def leaf5609Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435759/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357101056) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (596062387/536870912) }, upper := { exponent := 1, mantissa := (9247/8192) } }, logOuter := sk137LogOuterCertificate, logK := sk137LogKCertificate, logChi := chi261LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715823615/68714202112) } }, logDArg := sk137LogDArgCertificate }

private noncomputable def leaf5609InnerLog : WideLogData :=
  innerPair300Data

set_option maxRecDepth 1000000 in
private theorem leaf5609LocalValidity :
    LeafFacts leaf5609Box leaf5609Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5609Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357101056) }) = true
      norm_num [leaf5609Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5609CertificateValid :
    WideCertificateValid leaf5609Box leaf5609Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk137ValidityFacts chi261ValidityFacts
    leaf5609LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5609CoverageChecked :
    coverageCheck (innerAD leaf5609Box) leaf5609InnerLog = true := by
  rfl'

private theorem leaf5609InnerLogValid :
    leaf5609InnerLog.Valid 8 (innerAD leaf5609Box) :=
  wideLogDataValid_of_cachedCheck endpoint80PositiveFacts
    endpoint292PositiveFacts.valid leaf5609CoverageChecked

private noncomputable def leaf5609InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629477/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5609InputLogOnePlusV_eq :
    leaf5609InputLogOnePlusV = outerEnclosure 24
      (leaf5609Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5609RoundedFacts : LeafRoundedFacts 8
    leaf5609Certificate.logOnePlusV leaf5609InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5609InputLogOnePlusV_eq }

private noncomputable def leaf5609Inputs : Inputs :=
  inputsOfCaches globalInput sk137RoundedInputs
    chi261InputQChi innerPair300Input
    leaf5609InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5609LowerChecked :
    lowerCheck 24 leaf5609Box leaf5609Inputs = true := by
  rfl'

private theorem leaf5609CoversExact : CoversExact 8
    leaf5609Box leaf5609Certificate leaf5609InnerLog leaf5609Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk137RoundedFacts chi261RoundedFacts
    innerPair300RoundedFacts leaf5609RoundedFacts (by rfl)

private theorem leaf5609FlatSound : Sound leaf5609Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5609CertificateValid
    leaf5609InnerLogValid leaf5609CoversExact leaf5609LowerChecked

private noncomputable def leaf5610Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (25/64), chiHi := (51/128) }

private noncomputable def leaf5610Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435761/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357074944) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (599338985/536870912) }, upper := { exponent := 1, mantissa := (4649/4096) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi261LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715797503/68714149888) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf5610InnerLog : WideLogData :=
  innerPair257Data

set_option maxRecDepth 1000000 in
private theorem leaf5610LocalValidity :
    LeafFacts leaf5610Box leaf5610Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5610Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357074944) }) = true
      norm_num [leaf5610Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5610CertificateValid :
    WideCertificateValid leaf5610Box leaf5610Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi261ValidityFacts
    leaf5610LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5610CoverageChecked :
    coverageCheck (innerAD leaf5610Box) leaf5610InnerLog = true := by
  rfl'

private theorem leaf5610InnerLogValid :
    leaf5610InnerLog.Valid 8 (innerAD leaf5610Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint76PositiveFacts.valid leaf5610CoverageChecked

private noncomputable def leaf5610InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629483/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5610InputLogOnePlusV_eq :
    leaf5610InputLogOnePlusV = outerEnclosure 24
      (leaf5610Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5610RoundedFacts : LeafRoundedFacts 8
    leaf5610Certificate.logOnePlusV leaf5610InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5610InputLogOnePlusV_eq }

private noncomputable def leaf5610Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi261InputQChi innerPair257Input
    leaf5610InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5610LowerChecked :
    lowerCheck 24 leaf5610Box leaf5610Inputs = true := by
  rfl'

private theorem leaf5610CoversExact : CoversExact 8
    leaf5610Box leaf5610Certificate leaf5610InnerLog leaf5610Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi261RoundedFacts
    innerPair257RoundedFacts leaf5610RoundedFacts (by rfl)

private theorem leaf5610FlatSound : Sound leaf5610Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5610CertificateValid
    leaf5610InnerLogValid leaf5610CoversExact leaf5610LowerChecked

private noncomputable def leaf5611Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (51/128), chiHi := (13/32) }

private noncomputable def leaf5611Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435761/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357049344) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (602615585/536870912) }, upper := { exponent := 1, mantissa := (2337/2048) } }, logOuter := sk137LogOuterCertificate, logK := sk137LogKCertificate, logChi := chi262LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715771903/68714098688) } }, logDArg := sk137LogDArgCertificate }

private noncomputable def leaf5611InnerLog : WideLogData :=
  innerPair257Data

set_option maxRecDepth 1000000 in
private theorem leaf5611LocalValidity :
    LeafFacts leaf5611Box leaf5611Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5611Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357049344) }) = true
      norm_num [leaf5611Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5611CertificateValid :
    WideCertificateValid leaf5611Box leaf5611Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk137ValidityFacts chi262ValidityFacts
    leaf5611LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5611CoverageChecked :
    coverageCheck (innerAD leaf5611Box) leaf5611InnerLog = true := by
  rfl'

private theorem leaf5611InnerLogValid :
    leaf5611InnerLog.Valid 8 (innerAD leaf5611Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint76PositiveFacts.valid leaf5611CoverageChecked

private noncomputable def leaf5611InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629489/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5611InputLogOnePlusV_eq :
    leaf5611InputLogOnePlusV = outerEnclosure 24
      (leaf5611Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5611RoundedFacts : LeafRoundedFacts 8
    leaf5611Certificate.logOnePlusV leaf5611InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5611InputLogOnePlusV_eq }

private noncomputable def leaf5611Inputs : Inputs :=
  inputsOfCaches globalInput sk137RoundedInputs
    chi262InputQChi innerPair257Input
    leaf5611InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5611LowerChecked :
    lowerCheck 24 leaf5611Box leaf5611Inputs = true := by
  rfl'

private theorem leaf5611CoversExact : CoversExact 8
    leaf5611Box leaf5611Certificate leaf5611InnerLog leaf5611Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk137RoundedFacts chi262RoundedFacts
    innerPair257RoundedFacts leaf5611RoundedFacts (by rfl)

private theorem leaf5611FlatSound : Sound leaf5611Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5611CertificateValid
    leaf5611InnerLogValid leaf5611CoversExact leaf5611LowerChecked

private noncomputable def leaf5612Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (51/128), chiHi := (13/32) }

private noncomputable def leaf5612Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435763/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357022720) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (605957715/536870912) }, upper := { exponent := 1, mantissa := (1175/1024) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi262LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715745279/68714045440) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf5612InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf5612LocalValidity :
    LeafFacts leaf5612Box leaf5612Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5612Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357022720) }) = true
      norm_num [leaf5612Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5612CertificateValid :
    WideCertificateValid leaf5612Box leaf5612Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi262ValidityFacts
    leaf5612LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5612CoverageChecked :
    coverageCheck (innerAD leaf5612Box) leaf5612InnerLog = true := by
  rfl'

private theorem leaf5612InnerLogValid :
    leaf5612InnerLog.Valid 8 (innerAD leaf5612Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf5612CoverageChecked

private noncomputable def leaf5612InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453687/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf5612InputLogOnePlusV_eq :
    leaf5612InputLogOnePlusV = outerEnclosure 24
      (leaf5612Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5612RoundedFacts : LeafRoundedFacts 8
    leaf5612Certificate.logOnePlusV leaf5612InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5612InputLogOnePlusV_eq }

private noncomputable def leaf5612Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi262InputQChi innerPair264Input
    leaf5612InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5612LowerChecked :
    lowerCheck 24 leaf5612Box leaf5612Inputs = true := by
  rfl'

private theorem leaf5612CoversExact : CoversExact 8
    leaf5612Box leaf5612Certificate leaf5612InnerLog leaf5612Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi262RoundedFacts
    innerPair264RoundedFacts leaf5612RoundedFacts (by rfl)

private theorem leaf5612FlatSound : Sound leaf5612Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5612CertificateValid
    leaf5612InnerLogValid leaf5612CoversExact leaf5612LowerChecked

private noncomputable def leaf5613Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (25/64), chiHi := (51/128) }

private noncomputable def leaf5613Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435763/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357048832) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (602615583/536870912) }, upper := { exponent := 1, mantissa := (9349/8192) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi261LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715771391/68714097664) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf5613InnerLog : WideLogData :=
  innerPair257Data

set_option maxRecDepth 1000000 in
private theorem leaf5613LocalValidity :
    LeafFacts leaf5613Box leaf5613Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5613Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357048832) }) = true
      norm_num [leaf5613Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5613CertificateValid :
    WideCertificateValid leaf5613Box leaf5613Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi261ValidityFacts
    leaf5613LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5613CoverageChecked :
    coverageCheck (innerAD leaf5613Box) leaf5613InnerLog = true := by
  rfl'

private theorem leaf5613InnerLogValid :
    leaf5613InnerLog.Valid 8 (innerAD leaf5613Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint76PositiveFacts.valid leaf5613CoverageChecked

private noncomputable def leaf5613InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629489/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5613InputLogOnePlusV_eq :
    leaf5613InputLogOnePlusV = outerEnclosure 24
      (leaf5613Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5613RoundedFacts : LeafRoundedFacts 8
    leaf5613Certificate.logOnePlusV leaf5613InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5613InputLogOnePlusV_eq }

private noncomputable def leaf5613Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi261InputQChi innerPair257Input
    leaf5613InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5613LowerChecked :
    lowerCheck 24 leaf5613Box leaf5613Inputs = true := by
  rfl'

private theorem leaf5613CoversExact : CoversExact 8
    leaf5613Box leaf5613Certificate leaf5613InnerLog leaf5613Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi261RoundedFacts
    innerPair257RoundedFacts leaf5613RoundedFacts (by rfl)

private theorem leaf5613FlatSound : Sound leaf5613Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5613CertificateValid
    leaf5613InnerLogValid leaf5613CoversExact leaf5613LowerChecked

private noncomputable def leaf5614Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (25/64), chiHi := (51/128) }

private noncomputable def leaf5614Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435765/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357022720) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (605892181/536870912) }, upper := { exponent := 1, mantissa := (1175/1024) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi261LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715745279/68714045440) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf5614InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf5614LocalValidity :
    LeafFacts leaf5614Box leaf5614Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5614Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357022720) }) = true
      norm_num [leaf5614Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5614CertificateValid :
    WideCertificateValid leaf5614Box leaf5614Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi261ValidityFacts
    leaf5614LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5614CoverageChecked :
    coverageCheck (innerAD leaf5614Box) leaf5614InnerLog = true := by
  rfl'

private theorem leaf5614InnerLogValid :
    leaf5614InnerLog.Valid 8 (innerAD leaf5614Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf5614CoverageChecked

private noncomputable def leaf5614InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453687/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf5614InputLogOnePlusV_eq :
    leaf5614InputLogOnePlusV = outerEnclosure 24
      (leaf5614Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5614RoundedFacts : LeafRoundedFacts 8
    leaf5614Certificate.logOnePlusV leaf5614InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5614InputLogOnePlusV_eq }

private noncomputable def leaf5614Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi261InputQChi innerPair264Input
    leaf5614InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5614LowerChecked :
    lowerCheck 24 leaf5614Box leaf5614Inputs = true := by
  rfl'

private theorem leaf5614CoversExact : CoversExact 8
    leaf5614Box leaf5614Certificate leaf5614InnerLog leaf5614Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi261RoundedFacts
    innerPair264RoundedFacts leaf5614RoundedFacts (by rfl)

private theorem leaf5614FlatSound : Sound leaf5614Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5614CertificateValid
    leaf5614InnerLogValid leaf5614CoversExact leaf5614LowerChecked

private noncomputable def leaf5615Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (51/128), chiHi := (13/32) }

private noncomputable def leaf5615Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435765/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356996096) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (609299845/536870912) }, upper := { exponent := 1, mantissa := (2363/2048) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi262LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715718655/68713992192) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf5615InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf5615LocalValidity :
    LeafFacts leaf5615Box leaf5615Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5615Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356996096) }) = true
      norm_num [leaf5615Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5615CertificateValid :
    WideCertificateValid leaf5615Box leaf5615Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi262ValidityFacts
    leaf5615LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5615CoverageChecked :
    coverageCheck (innerAD leaf5615Box) leaf5615InnerLog = true := by
  rfl'

private theorem leaf5615InnerLogValid :
    leaf5615InnerLog.Valid 8 (innerAD leaf5615Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf5615CoverageChecked

private noncomputable def leaf5615InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814751/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5615InputLogOnePlusV_eq :
    leaf5615InputLogOnePlusV = outerEnclosure 24
      (leaf5615Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5615RoundedFacts : LeafRoundedFacts 8
    leaf5615Certificate.logOnePlusV leaf5615InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5615InputLogOnePlusV_eq }

private noncomputable def leaf5615Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi262InputQChi innerPair264Input
    leaf5615InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5615LowerChecked :
    lowerCheck 24 leaf5615Box leaf5615Inputs = true := by
  rfl'

private theorem leaf5615CoversExact : CoversExact 8
    leaf5615Box leaf5615Certificate leaf5615InnerLog leaf5615Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi262RoundedFacts
    innerPair264RoundedFacts leaf5615RoundedFacts (by rfl)

private theorem leaf5615FlatSound : Sound leaf5615Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5615CertificateValid
    leaf5615InnerLogValid leaf5615CoversExact leaf5615LowerChecked

private noncomputable def leaf5616Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (51/128), chiHi := (13/32) }

private noncomputable def leaf5616Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435767/268435456) }, vSqrt := { lower := (65529/65536), upper := (4908388937/4908138496) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (612641975/536870912) }, upper := { exponent := 1, mantissa := (297/256) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi262LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (9816527433/9816276992) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf5616InnerLog : WideLogData :=
  innerPair563Data

set_option maxRecDepth 1000000 in
private theorem leaf5616LocalValidity :
    LeafFacts leaf5616Box leaf5616Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5616Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4908388937/4908138496) }) = true
      norm_num [leaf5616Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5616CertificateValid :
    WideCertificateValid leaf5616Box leaf5616Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi262ValidityFacts
    leaf5616LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5616CoverageChecked :
    coverageCheck (innerAD leaf5616Box) leaf5616InnerLog = true := by
  rfl'

private theorem leaf5616InnerLogValid :
    leaf5616InnerLog.Valid 8 (innerAD leaf5616Box) :=
  wideLogDataValid_of_cachedCheck endpoint295PositiveFacts
    endpoint296PositiveFacts.valid leaf5616CoverageChecked

private noncomputable def leaf5616InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629509/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5616InputLogOnePlusV_eq :
    leaf5616InputLogOnePlusV = outerEnclosure 24
      (leaf5616Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5616RoundedFacts : LeafRoundedFacts 8
    leaf5616Certificate.logOnePlusV leaf5616InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5616InputLogOnePlusV_eq }

private noncomputable def leaf5616Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi262InputQChi innerPair563Input
    leaf5616InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5616LowerChecked :
    lowerCheck 24 leaf5616Box leaf5616Inputs = true := by
  rfl'

private theorem leaf5616CoversExact : CoversExact 8
    leaf5616Box leaf5616Certificate leaf5616InnerLog leaf5616Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi262RoundedFacts
    innerPair563RoundedFacts leaf5616RoundedFacts (by rfl)

private theorem leaf5616FlatSound : Sound leaf5616Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5616CertificateValid
    leaf5616InnerLogValid leaf5616CoversExact leaf5616LowerChecked

private noncomputable def leaf5617Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (13/32), chiHi := (53/128) }

private noncomputable def leaf5617Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435763/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356997632) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (609168783/536870912) }, upper := { exponent := 1, mantissa := (9449/8192) } }, logOuter := sk137LogOuterCertificate, logK := sk137LogKCertificate, logChi := chi263LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715720191/68713995264) } }, logDArg := sk137LogDArgCertificate }

private noncomputable def leaf5617InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf5617LocalValidity :
    LeafFacts leaf5617Box leaf5617Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5617Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356997632) }) = true
      norm_num [leaf5617Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5617CertificateValid :
    WideCertificateValid leaf5617Box leaf5617Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk137ValidityFacts chi263ValidityFacts
    leaf5617LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5617CoverageChecked :
    coverageCheck (innerAD leaf5617Box) leaf5617InnerLog = true := by
  rfl'

private theorem leaf5617InnerLogValid :
    leaf5617InnerLog.Valid 8 (innerAD leaf5617Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf5617CoverageChecked

private noncomputable def leaf5617InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814751/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5617InputLogOnePlusV_eq :
    leaf5617InputLogOnePlusV = outerEnclosure 24
      (leaf5617Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5617RoundedFacts : LeafRoundedFacts 8
    leaf5617Certificate.logOnePlusV leaf5617InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5617InputLogOnePlusV_eq }

private noncomputable def leaf5617Inputs : Inputs :=
  inputsOfCaches globalInput sk137RoundedInputs
    chi263InputQChi innerPair264Input
    leaf5617InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5617LowerChecked :
    lowerCheck 24 leaf5617Box leaf5617Inputs = true := by
  rfl'

private theorem leaf5617CoversExact : CoversExact 8
    leaf5617Box leaf5617Certificate leaf5617InnerLog leaf5617Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk137RoundedFacts chi263RoundedFacts
    innerPair264RoundedFacts leaf5617RoundedFacts (by rfl)

private theorem leaf5617FlatSound : Sound leaf5617Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5617CertificateValid
    leaf5617InnerLogValid leaf5617CoversExact leaf5617LowerChecked

private noncomputable def leaf5618Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (13/32), chiHi := (53/128) }

private noncomputable def leaf5618Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435765/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356970496) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (612576445/536870912) }, upper := { exponent := 1, mantissa := (4751/4096) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi263LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715693055/68713940992) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf5618InnerLog : WideLogData :=
  innerPair265Data

set_option maxRecDepth 1000000 in
private theorem leaf5618LocalValidity :
    LeafFacts leaf5618Box leaf5618Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5618Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356970496) }) = true
      norm_num [leaf5618Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5618CertificateValid :
    WideCertificateValid leaf5618Box leaf5618Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi263ValidityFacts
    leaf5618LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5618CoverageChecked :
    coverageCheck (innerAD leaf5618Box) leaf5618InnerLog = true := by
  rfl'

private theorem leaf5618InnerLogValid :
    leaf5618InnerLog.Valid 8 (innerAD leaf5618Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint77PositiveFacts.valid leaf5618CoverageChecked

private noncomputable def leaf5618InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629509/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5618InputLogOnePlusV_eq :
    leaf5618InputLogOnePlusV = outerEnclosure 24
      (leaf5618Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5618RoundedFacts : LeafRoundedFacts 8
    leaf5618Certificate.logOnePlusV leaf5618InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5618InputLogOnePlusV_eq }

private noncomputable def leaf5618Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi263InputQChi innerPair265Input
    leaf5618InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5618LowerChecked :
    lowerCheck 24 leaf5618Box leaf5618Inputs = true := by
  rfl'

private theorem leaf5618CoversExact : CoversExact 8
    leaf5618Box leaf5618Certificate leaf5618InnerLog leaf5618Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi263RoundedFacts
    innerPair265RoundedFacts leaf5618RoundedFacts (by rfl)

private theorem leaf5618FlatSound : Sound leaf5618Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5618CertificateValid
    leaf5618InnerLogValid leaf5618CoversExact leaf5618LowerChecked

private noncomputable def leaf5619Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (53/128), chiHi := (27/64) }

private noncomputable def leaf5619Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435765/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356945920) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (615721981/536870912) }, upper := { exponent := 1, mantissa := (4775/4096) } }, logOuter := sk137LogOuterCertificate, logK := sk137LogKCertificate, logChi := chi264LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715668479/68713891840) } }, logDArg := sk137LogDArgCertificate }

private noncomputable def leaf5619InnerLog : WideLogData :=
  innerPair265Data

set_option maxRecDepth 1000000 in
private theorem leaf5619LocalValidity :
    LeafFacts leaf5619Box leaf5619Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5619Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356945920) }) = true
      norm_num [leaf5619Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5619CertificateValid :
    WideCertificateValid leaf5619Box leaf5619Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk137ValidityFacts chi264ValidityFacts
    leaf5619LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5619CoverageChecked :
    coverageCheck (innerAD leaf5619Box) leaf5619InnerLog = true := by
  rfl'

private theorem leaf5619InnerLogValid :
    leaf5619InnerLog.Valid 8 (innerAD leaf5619Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint77PositiveFacts.valid leaf5619CoverageChecked

private noncomputable def leaf5619InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629515/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5619InputLogOnePlusV_eq :
    leaf5619InputLogOnePlusV = outerEnclosure 24
      (leaf5619Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5619RoundedFacts : LeafRoundedFacts 8
    leaf5619Certificate.logOnePlusV leaf5619InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5619InputLogOnePlusV_eq }

private noncomputable def leaf5619Inputs : Inputs :=
  inputsOfCaches globalInput sk137RoundedInputs
    chi264InputQChi innerPair265Input
    leaf5619InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5619LowerChecked :
    lowerCheck 24 leaf5619Box leaf5619Inputs = true := by
  rfl'

private theorem leaf5619CoversExact : CoversExact 8
    leaf5619Box leaf5619Certificate leaf5619InnerLog leaf5619Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk137RoundedFacts chi264RoundedFacts
    innerPair265RoundedFacts leaf5619RoundedFacts (by rfl)

private theorem leaf5619FlatSound : Sound leaf5619Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5619CertificateValid
    leaf5619InnerLogValid leaf5619CoversExact leaf5619LowerChecked

private noncomputable def leaf5620Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (53/128), chiHi := (27/64) }

private noncomputable def leaf5620Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435767/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356918272) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (619195175/536870912) }, upper := { exponent := 1, mantissa := (2401/2048) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi264LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715640831/68713836544) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf5620InnerLog : WideLogData :=
  innerPair265Data

set_option maxRecDepth 1000000 in
private theorem leaf5620LocalValidity :
    LeafFacts leaf5620Box leaf5620Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5620Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356918272) }) = true
      norm_num [leaf5620Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5620CertificateValid :
    WideCertificateValid leaf5620Box leaf5620Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi264ValidityFacts
    leaf5620LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5620CoverageChecked :
    coverageCheck (innerAD leaf5620Box) leaf5620InnerLog = true := by
  rfl'

private theorem leaf5620InnerLogValid :
    leaf5620InnerLog.Valid 8 (innerAD leaf5620Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint77PositiveFacts.valid leaf5620CoverageChecked

private noncomputable def leaf5620InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629521/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5620InputLogOnePlusV_eq :
    leaf5620InputLogOnePlusV = outerEnclosure 24
      (leaf5620Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5620RoundedFacts : LeafRoundedFacts 8
    leaf5620Certificate.logOnePlusV leaf5620InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5620InputLogOnePlusV_eq }

private noncomputable def leaf5620Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi264InputQChi innerPair265Input
    leaf5620InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5620LowerChecked :
    lowerCheck 24 leaf5620Box leaf5620Inputs = true := by
  rfl'

private theorem leaf5620CoversExact : CoversExact 8
    leaf5620Box leaf5620Certificate leaf5620InnerLog leaf5620Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi264RoundedFacts
    innerPair265RoundedFacts leaf5620RoundedFacts (by rfl)

private theorem leaf5620FlatSound : Sound leaf5620Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5620CertificateValid
    leaf5620InnerLogValid leaf5620CoversExact leaf5620LowerChecked

private noncomputable def leaf5621Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (13/32), chiHi := (53/128) }

private noncomputable def leaf5621Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435767/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356943360) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (615984107/536870912) }, upper := { exponent := 1, mantissa := (9555/8192) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi263LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715665919/68713886720) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf5621InnerLog : WideLogData :=
  innerPair265Data

set_option maxRecDepth 1000000 in
private theorem leaf5621LocalValidity :
    LeafFacts leaf5621Box leaf5621Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5621Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356943360) }) = true
      norm_num [leaf5621Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5621CertificateValid :
    WideCertificateValid leaf5621Box leaf5621Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi263ValidityFacts
    leaf5621LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5621CoverageChecked :
    coverageCheck (innerAD leaf5621Box) leaf5621InnerLog = true := by
  rfl'

private theorem leaf5621InnerLogValid :
    leaf5621InnerLog.Valid 8 (innerAD leaf5621Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint77PositiveFacts.valid leaf5621CoverageChecked

private noncomputable def leaf5621InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629515/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5621InputLogOnePlusV_eq :
    leaf5621InputLogOnePlusV = outerEnclosure 24
      (leaf5621Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5621RoundedFacts : LeafRoundedFacts 8
    leaf5621Certificate.logOnePlusV leaf5621InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5621InputLogOnePlusV_eq }

private noncomputable def leaf5621Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi263InputQChi innerPair265Input
    leaf5621InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5621LowerChecked :
    lowerCheck 24 leaf5621Box leaf5621Inputs = true := by
  rfl'

private theorem leaf5621CoversExact : CoversExact 8
    leaf5621Box leaf5621Certificate leaf5621InnerLog leaf5621Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi263RoundedFacts
    innerPair265RoundedFacts leaf5621RoundedFacts (by rfl)

private theorem leaf5621FlatSound : Sound leaf5621Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5621CertificateValid
    leaf5621InnerLogValid leaf5621CoversExact leaf5621LowerChecked

private noncomputable def leaf5622Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (13/32), chiHi := (53/128) }

private noncomputable def leaf5622Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435769/268435456) }, vSqrt := { lower := (65529/65536), upper := (2021101327/2020995072) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (619391769/536870912) }, upper := { exponent := 1, mantissa := (1201/1024) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi263LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (4042096399/4041990144) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf5622InnerLog : WideLogData :=
  innerPair265Data

set_option maxRecDepth 1000000 in
private theorem leaf5622LocalValidity :
    LeafFacts leaf5622Box leaf5622Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5622Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (2021101327/2020995072) }) = true
      norm_num [leaf5622Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5622CertificateValid :
    WideCertificateValid leaf5622Box leaf5622Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi263ValidityFacts
    leaf5622LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5622CoverageChecked :
    coverageCheck (innerAD leaf5622Box) leaf5622InnerLog = true := by
  rfl'

private theorem leaf5622InnerLogValid :
    leaf5622InnerLog.Valid 8 (innerAD leaf5622Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint77PositiveFacts.valid leaf5622CoverageChecked

private noncomputable def leaf5622InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814761/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5622InputLogOnePlusV_eq :
    leaf5622InputLogOnePlusV = outerEnclosure 24
      (leaf5622Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5622RoundedFacts : LeafRoundedFacts 8
    leaf5622Certificate.logOnePlusV leaf5622InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5622InputLogOnePlusV_eq }

private noncomputable def leaf5622Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi263InputQChi innerPair265Input
    leaf5622InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5622LowerChecked :
    lowerCheck 24 leaf5622Box leaf5622Inputs = true := by
  rfl'

private theorem leaf5622CoversExact : CoversExact 8
    leaf5622Box leaf5622Certificate leaf5622InnerLog leaf5622Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi263RoundedFacts
    innerPair265RoundedFacts leaf5622RoundedFacts (by rfl)

private theorem leaf5622FlatSound : Sound leaf5622Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5622CertificateValid
    leaf5622InnerLogValid leaf5622CoversExact leaf5622LowerChecked

private noncomputable def leaf5623Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (53/128), chiHi := (27/64) }

private noncomputable def leaf5623Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435769/268435456) }, vSqrt := { lower := (65529/65536), upper := (4908388937/4908127232) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (622668369/536870912) }, upper := { exponent := 1, mantissa := (4829/4096) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi264LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (9816516169/9816254464) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf5623InnerLog : WideLogData :=
  innerPair272Data

set_option maxRecDepth 1000000 in
private theorem leaf5623LocalValidity :
    LeafFacts leaf5623Box leaf5623Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5623Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4908388937/4908127232) }) = true
      norm_num [leaf5623Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5623CertificateValid :
    WideCertificateValid leaf5623Box leaf5623Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi264ValidityFacts
    leaf5623LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5623CoverageChecked :
    coverageCheck (innerAD leaf5623Box) leaf5623InnerLog = true := by
  rfl'

private theorem leaf5623InnerLogValid :
    leaf5623InnerLog.Valid 8 (innerAD leaf5623Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint77PositiveFacts.valid leaf5623CoverageChecked

private noncomputable def leaf5623InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453691/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf5623InputLogOnePlusV_eq :
    leaf5623InputLogOnePlusV = outerEnclosure 24
      (leaf5623Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5623RoundedFacts : LeafRoundedFacts 8
    leaf5623Certificate.logOnePlusV leaf5623InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5623InputLogOnePlusV_eq }

private noncomputable def leaf5623Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi264InputQChi innerPair272Input
    leaf5623InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5623LowerChecked :
    lowerCheck 24 leaf5623Box leaf5623Inputs = true := by
  rfl'

private theorem leaf5623CoversExact : CoversExact 8
    leaf5623Box leaf5623Certificate leaf5623InnerLog leaf5623Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi264RoundedFacts
    innerPair272RoundedFacts leaf5623RoundedFacts (by rfl)

private theorem leaf5623FlatSound : Sound leaf5623Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5623CertificateValid
    leaf5623InnerLogValid leaf5623CoversExact leaf5623LowerChecked

private noncomputable def leaf5624Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (53/128), chiHi := (27/64) }

private noncomputable def leaf5624Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435771/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356862976) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (626141563/536870912) }, upper := { exponent := 1, mantissa := (607/512) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi264LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715585535/68713725952) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf5624InnerLog : WideLogData :=
  innerPair272Data

set_option maxRecDepth 1000000 in
private theorem leaf5624LocalValidity :
    LeafFacts leaf5624Box leaf5624Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5624Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356862976) }) = true
      norm_num [leaf5624Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5624CertificateValid :
    WideCertificateValid leaf5624Box leaf5624Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi264ValidityFacts
    leaf5624LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5624CoverageChecked :
    coverageCheck (innerAD leaf5624Box) leaf5624InnerLog = true := by
  rfl'

private theorem leaf5624InnerLogValid :
    leaf5624InnerLog.Valid 8 (innerAD leaf5624Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint77PositiveFacts.valid leaf5624CoverageChecked

private noncomputable def leaf5624InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629535/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5624InputLogOnePlusV_eq :
    leaf5624InputLogOnePlusV = outerEnclosure 24
      (leaf5624Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5624RoundedFacts : LeafRoundedFacts 8
    leaf5624Certificate.logOnePlusV leaf5624InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5624InputLogOnePlusV_eq }

private noncomputable def leaf5624Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi264InputQChi innerPair272Input
    leaf5624InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5624LowerChecked :
    lowerCheck 24 leaf5624Box leaf5624Inputs = true := by
  rfl'

private theorem leaf5624CoversExact : CoversExact 8
    leaf5624Box leaf5624Certificate leaf5624InnerLog leaf5624Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi264RoundedFacts
    innerPair272RoundedFacts leaf5624RoundedFacts (by rfl)

private theorem leaf5624FlatSound : Sound leaf5624Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5624CertificateValid
    leaf5624InnerLogValid leaf5624CoversExact leaf5624LowerChecked

private noncomputable def leaf5625Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (27/64), chiHi := (55/128) }

private noncomputable def leaf5625Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435767/268435456) }, vSqrt := { lower := (65529/65536), upper := (4908388937/4908127744) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (622275179/536870912) }, upper := { exponent := 1, mantissa := (9651/8192) } }, logOuter := sk137LogOuterCertificate, logK := sk137LogKCertificate, logChi := chi265LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (9816516681/9816255488) } }, logDArg := sk137LogDArgCertificate }

private noncomputable def leaf5625InnerLog : WideLogData :=
  innerPair272Data

set_option maxRecDepth 1000000 in
private theorem leaf5625LocalValidity :
    LeafFacts leaf5625Box leaf5625Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5625Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4908388937/4908127744) }) = true
      norm_num [leaf5625Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5625CertificateValid :
    WideCertificateValid leaf5625Box leaf5625Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk137ValidityFacts chi265ValidityFacts
    leaf5625LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5625CoverageChecked :
    coverageCheck (innerAD leaf5625Box) leaf5625InnerLog = true := by
  rfl'

private theorem leaf5625InnerLogValid :
    leaf5625InnerLog.Valid 8 (innerAD leaf5625Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint77PositiveFacts.valid leaf5625CoverageChecked

private noncomputable def leaf5625InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629527/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5625InputLogOnePlusV_eq :
    leaf5625InputLogOnePlusV = outerEnclosure 24
      (leaf5625Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5625RoundedFacts : LeafRoundedFacts 8
    leaf5625Certificate.logOnePlusV leaf5625InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5625InputLogOnePlusV_eq }

private noncomputable def leaf5625Inputs : Inputs :=
  inputsOfCaches globalInput sk137RoundedInputs
    chi265InputQChi innerPair272Input
    leaf5625InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5625LowerChecked :
    lowerCheck 24 leaf5625Box leaf5625Inputs = true := by
  rfl'

private theorem leaf5625CoversExact : CoversExact 8
    leaf5625Box leaf5625Certificate leaf5625InnerLog leaf5625Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk137RoundedFacts chi265RoundedFacts
    innerPair272RoundedFacts leaf5625RoundedFacts (by rfl)

private theorem leaf5625FlatSound : Sound leaf5625Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5625CertificateValid
    leaf5625InnerLogValid leaf5625CoversExact leaf5625LowerChecked

private noncomputable def leaf5626Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (27/64), chiHi := (55/128) }

private noncomputable def leaf5626Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435769/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356866048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (625813905/536870912) }, upper := { exponent := 1, mantissa := (4853/4096) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi265LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715588607/68713732096) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf5626InnerLog : WideLogData :=
  innerPair272Data

set_option maxRecDepth 1000000 in
private theorem leaf5626LocalValidity :
    LeafFacts leaf5626Box leaf5626Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5626Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356866048) }) = true
      norm_num [leaf5626Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5626CertificateValid :
    WideCertificateValid leaf5626Box leaf5626Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi265ValidityFacts
    leaf5626LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5626CoverageChecked :
    coverageCheck (innerAD leaf5626Box) leaf5626InnerLog = true := by
  rfl'

private theorem leaf5626InnerLogValid :
    leaf5626InnerLog.Valid 8 (innerAD leaf5626Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint77PositiveFacts.valid leaf5626CoverageChecked

private noncomputable def leaf5626InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814767/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5626InputLogOnePlusV_eq :
    leaf5626InputLogOnePlusV = outerEnclosure 24
      (leaf5626Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5626RoundedFacts : LeafRoundedFacts 8
    leaf5626Certificate.logOnePlusV leaf5626InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5626InputLogOnePlusV_eq }

private noncomputable def leaf5626Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi265InputQChi innerPair272Input
    leaf5626InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5626LowerChecked :
    lowerCheck 24 leaf5626Box leaf5626Inputs = true := by
  rfl'

private theorem leaf5626CoversExact : CoversExact 8
    leaf5626Box leaf5626Certificate leaf5626InnerLog leaf5626Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi265RoundedFacts
    innerPair272RoundedFacts leaf5626RoundedFacts (by rfl)

private theorem leaf5626FlatSound : Sound leaf5626Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5626CertificateValid
    leaf5626InnerLogValid leaf5626CoversExact leaf5626LowerChecked

private noncomputable def leaf5627Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (55/128), chiHi := (7/16) }

private noncomputable def leaf5627Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435769/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356842496) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (628828377/536870912) }, upper := { exponent := 1, mantissa := (1219/1024) } }, logOuter := sk137LogOuterCertificate, logK := sk137LogKCertificate, logChi := chi266LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715565055/68713684992) } }, logDArg := sk137LogDArgCertificate }

private noncomputable def leaf5627InnerLog : WideLogData :=
  innerPair273Data

set_option maxRecDepth 1000000 in
private theorem leaf5627LocalValidity :
    LeafFacts leaf5627Box leaf5627Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5627Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356842496) }) = true
      norm_num [leaf5627Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5627CertificateValid :
    WideCertificateValid leaf5627Box leaf5627Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk137ValidityFacts chi266ValidityFacts
    leaf5627LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5627CoverageChecked :
    coverageCheck (innerAD leaf5627Box) leaf5627InnerLog = true := by
  rfl'

private theorem leaf5627InnerLogValid :
    leaf5627InnerLog.Valid 8 (innerAD leaf5627Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint78PositiveFacts.valid leaf5627CoverageChecked

private noncomputable def leaf5627InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907385/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5627InputLogOnePlusV_eq :
    leaf5627InputLogOnePlusV = outerEnclosure 24
      (leaf5627Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5627RoundedFacts : LeafRoundedFacts 8
    leaf5627Certificate.logOnePlusV leaf5627InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5627InputLogOnePlusV_eq }

private noncomputable def leaf5627Inputs : Inputs :=
  inputsOfCaches globalInput sk137RoundedInputs
    chi266InputQChi innerPair273Input
    leaf5627InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5627LowerChecked :
    lowerCheck 24 leaf5627Box leaf5627Inputs = true := by
  rfl'

private theorem leaf5627CoversExact : CoversExact 8
    leaf5627Box leaf5627Certificate leaf5627InnerLog leaf5627Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk137RoundedFacts chi266RoundedFacts
    innerPair273RoundedFacts leaf5627RoundedFacts (by rfl)

private theorem leaf5627FlatSound : Sound leaf5627Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5627CertificateValid
    leaf5627InnerLogValid leaf5627CoversExact leaf5627LowerChecked

private noncomputable def leaf5628Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (55/128), chiHi := (7/16) }

private noncomputable def leaf5628Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435771/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356813824) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (632432635/536870912) }, upper := { exponent := 1, mantissa := (613/512) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi266LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715536383/68713627648) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf5628InnerLog : WideLogData :=
  innerPair273Data

set_option maxRecDepth 1000000 in
private theorem leaf5628LocalValidity :
    LeafFacts leaf5628Box leaf5628Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5628Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356813824) }) = true
      norm_num [leaf5628Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5628CertificateValid :
    WideCertificateValid leaf5628Box leaf5628Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi266ValidityFacts
    leaf5628LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5628CoverageChecked :
    coverageCheck (innerAD leaf5628Box) leaf5628InnerLog = true := by
  rfl'

private theorem leaf5628InnerLogValid :
    leaf5628InnerLog.Valid 8 (innerAD leaf5628Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint78PositiveFacts.valid leaf5628CoverageChecked

private noncomputable def leaf5628InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629547/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5628InputLogOnePlusV_eq :
    leaf5628InputLogOnePlusV = outerEnclosure 24
      (leaf5628Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5628RoundedFacts : LeafRoundedFacts 8
    leaf5628Certificate.logOnePlusV leaf5628InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5628InputLogOnePlusV_eq }

private noncomputable def leaf5628Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi266InputQChi innerPair273Input
    leaf5628InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5628LowerChecked :
    lowerCheck 24 leaf5628Box leaf5628Inputs = true := by
  rfl'

private theorem leaf5628CoversExact : CoversExact 8
    leaf5628Box leaf5628Certificate leaf5628InnerLog leaf5628Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi266RoundedFacts
    innerPair273RoundedFacts leaf5628RoundedFacts (by rfl)

private theorem leaf5628FlatSound : Sound leaf5628Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5628CertificateValid
    leaf5628InnerLogValid leaf5628CoversExact leaf5628LowerChecked

private noncomputable def leaf5629Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (27/64), chiHi := (55/128) }

private noncomputable def leaf5629Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435771/268435456) }, vSqrt := { lower := (65529/65536), upper := (2021101327/2020990464) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (629352631/536870912) }, upper := { exponent := 1, mantissa := (9761/8192) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi265LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (4042091791/4041980928) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf5629InnerLog : WideLogData :=
  innerPair273Data

set_option maxRecDepth 1000000 in
private theorem leaf5629LocalValidity :
    LeafFacts leaf5629Box leaf5629Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5629Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (2021101327/2020990464) }) = true
      norm_num [leaf5629Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5629CertificateValid :
    WideCertificateValid leaf5629Box leaf5629Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi265ValidityFacts
    leaf5629LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5629CoverageChecked :
    coverageCheck (innerAD leaf5629Box) leaf5629InnerLog = true := by
  rfl'

private theorem leaf5629InnerLogValid :
    leaf5629InnerLog.Valid 8 (innerAD leaf5629Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint78PositiveFacts.valid leaf5629CoverageChecked

private noncomputable def leaf5629InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629541/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5629InputLogOnePlusV_eq :
    leaf5629InputLogOnePlusV = outerEnclosure 24
      (leaf5629Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5629RoundedFacts : LeafRoundedFacts 8
    leaf5629Certificate.logOnePlusV leaf5629InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5629InputLogOnePlusV_eq }

private noncomputable def leaf5629Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi265InputQChi innerPair273Input
    leaf5629InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5629LowerChecked :
    lowerCheck 24 leaf5629Box leaf5629Inputs = true := by
  rfl'

private theorem leaf5629CoversExact : CoversExact 8
    leaf5629Box leaf5629Certificate leaf5629InnerLog leaf5629Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi265RoundedFacts
    innerPair273RoundedFacts leaf5629RoundedFacts (by rfl)

private theorem leaf5629FlatSound : Sound leaf5629Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5629CertificateValid
    leaf5629InnerLogValid leaf5629CoversExact leaf5629LowerChecked

private noncomputable def leaf5630Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (27/64), chiHi := (55/128) }

private noncomputable def leaf5630Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435773/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356809728) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (632891357/536870912) }, upper := { exponent := 1, mantissa := (1227/1024) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi265LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715532287/68713619456) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf5630InnerLog : WideLogData :=
  innerPair273Data

set_option maxRecDepth 1000000 in
private theorem leaf5630LocalValidity :
    LeafFacts leaf5630Box leaf5630Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5630Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356809728) }) = true
      norm_num [leaf5630Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5630CertificateValid :
    WideCertificateValid leaf5630Box leaf5630Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi265ValidityFacts
    leaf5630LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5630CoverageChecked :
    coverageCheck (innerAD leaf5630Box) leaf5630InnerLog = true := by
  rfl'

private theorem leaf5630InnerLogValid :
    leaf5630InnerLog.Valid 8 (innerAD leaf5630Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint78PositiveFacts.valid leaf5630CoverageChecked

private noncomputable def leaf5630InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907387/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5630InputLogOnePlusV_eq :
    leaf5630InputLogOnePlusV = outerEnclosure 24
      (leaf5630Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5630RoundedFacts : LeafRoundedFacts 8
    leaf5630Certificate.logOnePlusV leaf5630InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5630InputLogOnePlusV_eq }

private noncomputable def leaf5630Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi265InputQChi innerPair273Input
    leaf5630InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5630LowerChecked :
    lowerCheck 24 leaf5630Box leaf5630Inputs = true := by
  rfl'

private theorem leaf5630CoversExact : CoversExact 8
    leaf5630Box leaf5630Certificate leaf5630InnerLog leaf5630Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi265RoundedFacts
    innerPair273RoundedFacts leaf5630RoundedFacts (by rfl)

private theorem leaf5630FlatSound : Sound leaf5630Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5630CertificateValid
    leaf5630InnerLogValid leaf5630CoversExact leaf5630LowerChecked

private noncomputable def leaf5631Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (55/128), chiHi := (7/16) }

private noncomputable def leaf5631Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435773/268435456) }, vSqrt := { lower := (65529/65536), upper := (1108345889/1108283392) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (636036893/536870912) }, upper := { exponent := 1, mantissa := (1233/1024) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi266LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (2216629281/2216566784) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf5631InnerLog : WideLogData :=
  innerPair273Data

set_option maxRecDepth 1000000 in
private theorem leaf5631LocalValidity :
    LeafFacts leaf5631Box leaf5631Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5631Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (1108345889/1108283392) }) = true
      norm_num [leaf5631Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5631CertificateValid :
    WideCertificateValid leaf5631Box leaf5631Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi266ValidityFacts
    leaf5631LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5631CoverageChecked :
    coverageCheck (innerAD leaf5631Box) leaf5631InnerLog = true := by
  rfl'

private theorem leaf5631InnerLogValid :
    leaf5631InnerLog.Valid 8 (innerAD leaf5631Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint78PositiveFacts.valid leaf5631CoverageChecked

private noncomputable def leaf5631InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814777/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5631InputLogOnePlusV_eq :
    leaf5631InputLogOnePlusV = outerEnclosure 24
      (leaf5631Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5631RoundedFacts : LeafRoundedFacts 8
    leaf5631Certificate.logOnePlusV leaf5631InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5631InputLogOnePlusV_eq }

private noncomputable def leaf5631Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi266InputQChi innerPair273Input
    leaf5631InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5631LowerChecked :
    lowerCheck 24 leaf5631Box leaf5631Inputs = true := by
  rfl'

private theorem leaf5631CoversExact : CoversExact 8
    leaf5631Box leaf5631Certificate leaf5631InnerLog leaf5631Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi266RoundedFacts
    innerPair273RoundedFacts leaf5631RoundedFacts (by rfl)

private theorem leaf5631FlatSound : Sound leaf5631Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5631CertificateValid
    leaf5631InnerLogValid leaf5631CoversExact leaf5631LowerChecked

private noncomputable def leaf5632Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (55/128), chiHi := (7/16) }

private noncomputable def leaf5632Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435775/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356756480) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (639641151/536870912) }, upper := { exponent := 1, mantissa := (155/128) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi266LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715479039/68713512960) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf5632InnerLog : WideLogData :=
  innerPair278Data

set_option maxRecDepth 1000000 in
private theorem leaf5632LocalValidity :
    LeafFacts leaf5632Box leaf5632Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5632Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356756480) }) = true
      norm_num [leaf5632Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5632CertificateValid :
    WideCertificateValid leaf5632Box leaf5632Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi266ValidityFacts
    leaf5632LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5632CoverageChecked :
    coverageCheck (innerAD leaf5632Box) leaf5632InnerLog = true := by
  rfl'

private theorem leaf5632InnerLogValid :
    leaf5632InnerLog.Valid 8 (innerAD leaf5632Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint78PositiveFacts.valid leaf5632CoverageChecked

private noncomputable def leaf5632InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629561/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5632InputLogOnePlusV_eq :
    leaf5632InputLogOnePlusV = outerEnclosure 24
      (leaf5632Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5632RoundedFacts : LeafRoundedFacts 8
    leaf5632Certificate.logOnePlusV leaf5632InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5632InputLogOnePlusV_eq }

private noncomputable def leaf5632Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi266InputQChi innerPair278Input
    leaf5632InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5632LowerChecked :
    lowerCheck 24 leaf5632Box leaf5632Inputs = true := by
  rfl'

private theorem leaf5632CoversExact : CoversExact 8
    leaf5632Box leaf5632Certificate leaf5632InnerLog leaf5632Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi266RoundedFacts
    innerPair278RoundedFacts leaf5632RoundedFacts (by rfl)

private theorem leaf5632FlatSound : Sound leaf5632Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5632CertificateValid
    leaf5632InnerLogValid leaf5632CoversExact leaf5632LowerChecked

private noncomputable def component113Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (3/8), chiHi := (49/128) }

set_option maxRecDepth 1000000 in
private theorem component113Node0_sound : Sound component113Node0Box :=
  sound_of_literal_split component113Node0Box leaf5569Box leaf5570Box
    .k (97/32) (by rfl) (by rfl)
    leaf5569FlatSound leaf5570FlatSound

private noncomputable def component113Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (49/128), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component113Node1_sound : Sound component113Node1Box :=
  sound_of_literal_split component113Node1Box leaf5571Box leaf5572Box
    .k (97/32) (by rfl) (by rfl)
    leaf5571FlatSound leaf5572FlatSound

private noncomputable def component113Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (3/8), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component113Node2_sound : Sound component113Node2Box :=
  sound_of_literal_split component113Node2Box component113Node0Box component113Node1Box
    .chi (49/128) (by rfl) (by rfl)
    component113Node0_sound component113Node1_sound

private noncomputable def component113Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (3/8), chiHi := (49/128) }

set_option maxRecDepth 1000000 in
private theorem component113Node3_sound : Sound component113Node3Box :=
  sound_of_literal_split component113Node3Box leaf5573Box leaf5574Box
    .k (99/32) (by rfl) (by rfl)
    leaf5573FlatSound leaf5574FlatSound

private noncomputable def component113Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (49/128), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component113Node4_sound : Sound component113Node4Box :=
  sound_of_literal_split component113Node4Box leaf5575Box leaf5576Box
    .k (99/32) (by rfl) (by rfl)
    leaf5575FlatSound leaf5576FlatSound

private noncomputable def component113Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (3/8), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component113Node5_sound : Sound component113Node5Box :=
  sound_of_literal_split component113Node5Box component113Node3Box component113Node4Box
    .chi (49/128) (by rfl) (by rfl)
    component113Node3_sound component113Node4_sound

private noncomputable def component113Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (3/8), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component113Node6_sound : Sound component113Node6Box :=
  sound_of_literal_split component113Node6Box component113Node2Box component113Node5Box
    .k (49/16) (by rfl) (by rfl)
    component113Node2_sound component113Node5_sound

private noncomputable def component113Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (25/64), chiHi := (51/128) }

set_option maxRecDepth 1000000 in
private theorem component113Node7_sound : Sound component113Node7Box :=
  sound_of_literal_split component113Node7Box leaf5577Box leaf5578Box
    .k (97/32) (by rfl) (by rfl)
    leaf5577FlatSound leaf5578FlatSound

private noncomputable def component113Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (51/128), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component113Node8_sound : Sound component113Node8Box :=
  sound_of_literal_split component113Node8Box leaf5579Box leaf5580Box
    .k (97/32) (by rfl) (by rfl)
    leaf5579FlatSound leaf5580FlatSound

private noncomputable def component113Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (25/64), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component113Node9_sound : Sound component113Node9Box :=
  sound_of_literal_split component113Node9Box component113Node7Box component113Node8Box
    .chi (51/128) (by rfl) (by rfl)
    component113Node7_sound component113Node8_sound

private noncomputable def component113Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (25/64), chiHi := (51/128) }

set_option maxRecDepth 1000000 in
private theorem component113Node10_sound : Sound component113Node10Box :=
  sound_of_literal_split component113Node10Box leaf5581Box leaf5582Box
    .k (99/32) (by rfl) (by rfl)
    leaf5581FlatSound leaf5582FlatSound

private noncomputable def component113Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (51/128), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component113Node11_sound : Sound component113Node11Box :=
  sound_of_literal_split component113Node11Box leaf5583Box leaf5584Box
    .k (99/32) (by rfl) (by rfl)
    leaf5583FlatSound leaf5584FlatSound

private noncomputable def component113Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (25/64), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component113Node12_sound : Sound component113Node12Box :=
  sound_of_literal_split component113Node12Box component113Node10Box component113Node11Box
    .chi (51/128) (by rfl) (by rfl)
    component113Node10_sound component113Node11_sound

private noncomputable def component113Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (25/64), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component113Node13_sound : Sound component113Node13Box :=
  sound_of_literal_split component113Node13Box component113Node9Box component113Node12Box
    .k (49/16) (by rfl) (by rfl)
    component113Node9_sound component113Node12_sound

private noncomputable def component113Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (3/8), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component113Node14_sound : Sound component113Node14Box :=
  sound_of_literal_split component113Node14Box component113Node6Box component113Node13Box
    .chi (25/64) (by rfl) (by rfl)
    component113Node6_sound component113Node13_sound

private noncomputable def component113Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (13/32), chiHi := (53/128) }

set_option maxRecDepth 1000000 in
private theorem component113Node15_sound : Sound component113Node15Box :=
  sound_of_literal_split component113Node15Box leaf5585Box leaf5586Box
    .k (97/32) (by rfl) (by rfl)
    leaf5585FlatSound leaf5586FlatSound

private noncomputable def component113Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (53/128), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component113Node16_sound : Sound component113Node16Box :=
  sound_of_literal_split component113Node16Box leaf5587Box leaf5588Box
    .k (97/32) (by rfl) (by rfl)
    leaf5587FlatSound leaf5588FlatSound

private noncomputable def component113Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (13/32), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component113Node17_sound : Sound component113Node17Box :=
  sound_of_literal_split component113Node17Box component113Node15Box component113Node16Box
    .chi (53/128) (by rfl) (by rfl)
    component113Node15_sound component113Node16_sound

private noncomputable def component113Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (13/32), chiHi := (53/128) }

set_option maxRecDepth 1000000 in
private theorem component113Node18_sound : Sound component113Node18Box :=
  sound_of_literal_split component113Node18Box leaf5589Box leaf5590Box
    .k (99/32) (by rfl) (by rfl)
    leaf5589FlatSound leaf5590FlatSound

private noncomputable def component113Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (53/128), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component113Node19_sound : Sound component113Node19Box :=
  sound_of_literal_split component113Node19Box leaf5591Box leaf5592Box
    .k (99/32) (by rfl) (by rfl)
    leaf5591FlatSound leaf5592FlatSound

private noncomputable def component113Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (13/32), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component113Node20_sound : Sound component113Node20Box :=
  sound_of_literal_split component113Node20Box component113Node18Box component113Node19Box
    .chi (53/128) (by rfl) (by rfl)
    component113Node18_sound component113Node19_sound

private noncomputable def component113Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (13/32), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component113Node21_sound : Sound component113Node21Box :=
  sound_of_literal_split component113Node21Box component113Node17Box component113Node20Box
    .k (49/16) (by rfl) (by rfl)
    component113Node17_sound component113Node20_sound

private noncomputable def component113Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (27/64), chiHi := (55/128) }

set_option maxRecDepth 1000000 in
private theorem component113Node22_sound : Sound component113Node22Box :=
  sound_of_literal_split component113Node22Box leaf5593Box leaf5594Box
    .k (97/32) (by rfl) (by rfl)
    leaf5593FlatSound leaf5594FlatSound

private noncomputable def component113Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (55/128), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component113Node23_sound : Sound component113Node23Box :=
  sound_of_literal_split component113Node23Box leaf5595Box leaf5596Box
    .k (97/32) (by rfl) (by rfl)
    leaf5595FlatSound leaf5596FlatSound

private noncomputable def component113Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (27/64), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component113Node24_sound : Sound component113Node24Box :=
  sound_of_literal_split component113Node24Box component113Node22Box component113Node23Box
    .chi (55/128) (by rfl) (by rfl)
    component113Node22_sound component113Node23_sound

private noncomputable def component113Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (27/64), chiHi := (55/128) }

set_option maxRecDepth 1000000 in
private theorem component113Node25_sound : Sound component113Node25Box :=
  sound_of_literal_split component113Node25Box leaf5597Box leaf5598Box
    .k (99/32) (by rfl) (by rfl)
    leaf5597FlatSound leaf5598FlatSound

private noncomputable def component113Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (55/128), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component113Node26_sound : Sound component113Node26Box :=
  sound_of_literal_split component113Node26Box leaf5599Box leaf5600Box
    .k (99/32) (by rfl) (by rfl)
    leaf5599FlatSound leaf5600FlatSound

private noncomputable def component113Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (27/64), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component113Node27_sound : Sound component113Node27Box :=
  sound_of_literal_split component113Node27Box component113Node25Box component113Node26Box
    .chi (55/128) (by rfl) (by rfl)
    component113Node25_sound component113Node26_sound

private noncomputable def component113Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (27/64), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component113Node28_sound : Sound component113Node28Box :=
  sound_of_literal_split component113Node28Box component113Node24Box component113Node27Box
    .k (49/16) (by rfl) (by rfl)
    component113Node24_sound component113Node27_sound

private noncomputable def component113Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (13/32), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component113Node29_sound : Sound component113Node29Box :=
  sound_of_literal_split component113Node29Box component113Node21Box component113Node28Box
    .chi (27/64) (by rfl) (by rfl)
    component113Node21_sound component113Node28_sound

private noncomputable def component113Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (3/8), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component113Node30_sound : Sound component113Node30Box :=
  sound_of_literal_split component113Node30Box component113Node14Box component113Node29Box
    .chi (13/32) (by rfl) (by rfl)
    component113Node14_sound component113Node29_sound

private noncomputable def component113Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (3/8), chiHi := (49/128) }

set_option maxRecDepth 1000000 in
private theorem component113Node31_sound : Sound component113Node31Box :=
  sound_of_literal_split component113Node31Box leaf5601Box leaf5602Box
    .k (101/32) (by rfl) (by rfl)
    leaf5601FlatSound leaf5602FlatSound

private noncomputable def component113Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (49/128), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component113Node32_sound : Sound component113Node32Box :=
  sound_of_literal_split component113Node32Box leaf5603Box leaf5604Box
    .k (101/32) (by rfl) (by rfl)
    leaf5603FlatSound leaf5604FlatSound

private noncomputable def component113Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (3/8), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component113Node33_sound : Sound component113Node33Box :=
  sound_of_literal_split component113Node33Box component113Node31Box component113Node32Box
    .chi (49/128) (by rfl) (by rfl)
    component113Node31_sound component113Node32_sound

private noncomputable def component113Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (3/8), chiHi := (49/128) }

set_option maxRecDepth 1000000 in
private theorem component113Node34_sound : Sound component113Node34Box :=
  sound_of_literal_split component113Node34Box leaf5605Box leaf5606Box
    .k (103/32) (by rfl) (by rfl)
    leaf5605FlatSound leaf5606FlatSound

private noncomputable def component113Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (49/128), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component113Node35_sound : Sound component113Node35Box :=
  sound_of_literal_split component113Node35Box leaf5607Box leaf5608Box
    .k (103/32) (by rfl) (by rfl)
    leaf5607FlatSound leaf5608FlatSound

private noncomputable def component113Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (3/8), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component113Node36_sound : Sound component113Node36Box :=
  sound_of_literal_split component113Node36Box component113Node34Box component113Node35Box
    .chi (49/128) (by rfl) (by rfl)
    component113Node34_sound component113Node35_sound

private noncomputable def component113Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (3/8), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component113Node37_sound : Sound component113Node37Box :=
  sound_of_literal_split component113Node37Box component113Node33Box component113Node36Box
    .k (51/16) (by rfl) (by rfl)
    component113Node33_sound component113Node36_sound

private noncomputable def component113Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (25/64), chiHi := (51/128) }

set_option maxRecDepth 1000000 in
private theorem component113Node38_sound : Sound component113Node38Box :=
  sound_of_literal_split component113Node38Box leaf5609Box leaf5610Box
    .k (101/32) (by rfl) (by rfl)
    leaf5609FlatSound leaf5610FlatSound

private noncomputable def component113Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (51/128), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component113Node39_sound : Sound component113Node39Box :=
  sound_of_literal_split component113Node39Box leaf5611Box leaf5612Box
    .k (101/32) (by rfl) (by rfl)
    leaf5611FlatSound leaf5612FlatSound

private noncomputable def component113Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (25/64), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component113Node40_sound : Sound component113Node40Box :=
  sound_of_literal_split component113Node40Box component113Node38Box component113Node39Box
    .chi (51/128) (by rfl) (by rfl)
    component113Node38_sound component113Node39_sound

private noncomputable def component113Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (25/64), chiHi := (51/128) }

set_option maxRecDepth 1000000 in
private theorem component113Node41_sound : Sound component113Node41Box :=
  sound_of_literal_split component113Node41Box leaf5613Box leaf5614Box
    .k (103/32) (by rfl) (by rfl)
    leaf5613FlatSound leaf5614FlatSound

private noncomputable def component113Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (51/128), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component113Node42_sound : Sound component113Node42Box :=
  sound_of_literal_split component113Node42Box leaf5615Box leaf5616Box
    .k (103/32) (by rfl) (by rfl)
    leaf5615FlatSound leaf5616FlatSound

private noncomputable def component113Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (25/64), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component113Node43_sound : Sound component113Node43Box :=
  sound_of_literal_split component113Node43Box component113Node41Box component113Node42Box
    .chi (51/128) (by rfl) (by rfl)
    component113Node41_sound component113Node42_sound

private noncomputable def component113Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (25/64), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component113Node44_sound : Sound component113Node44Box :=
  sound_of_literal_split component113Node44Box component113Node40Box component113Node43Box
    .k (51/16) (by rfl) (by rfl)
    component113Node40_sound component113Node43_sound

private noncomputable def component113Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (3/8), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component113Node45_sound : Sound component113Node45Box :=
  sound_of_literal_split component113Node45Box component113Node37Box component113Node44Box
    .chi (25/64) (by rfl) (by rfl)
    component113Node37_sound component113Node44_sound

private noncomputable def component113Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (13/32), chiHi := (53/128) }

set_option maxRecDepth 1000000 in
private theorem component113Node46_sound : Sound component113Node46Box :=
  sound_of_literal_split component113Node46Box leaf5617Box leaf5618Box
    .k (101/32) (by rfl) (by rfl)
    leaf5617FlatSound leaf5618FlatSound

private noncomputable def component113Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (53/128), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component113Node47_sound : Sound component113Node47Box :=
  sound_of_literal_split component113Node47Box leaf5619Box leaf5620Box
    .k (101/32) (by rfl) (by rfl)
    leaf5619FlatSound leaf5620FlatSound

private noncomputable def component113Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (13/32), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component113Node48_sound : Sound component113Node48Box :=
  sound_of_literal_split component113Node48Box component113Node46Box component113Node47Box
    .chi (53/128) (by rfl) (by rfl)
    component113Node46_sound component113Node47_sound

private noncomputable def component113Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (13/32), chiHi := (53/128) }

set_option maxRecDepth 1000000 in
private theorem component113Node49_sound : Sound component113Node49Box :=
  sound_of_literal_split component113Node49Box leaf5621Box leaf5622Box
    .k (103/32) (by rfl) (by rfl)
    leaf5621FlatSound leaf5622FlatSound

private noncomputable def component113Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (53/128), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component113Node50_sound : Sound component113Node50Box :=
  sound_of_literal_split component113Node50Box leaf5623Box leaf5624Box
    .k (103/32) (by rfl) (by rfl)
    leaf5623FlatSound leaf5624FlatSound

private noncomputable def component113Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (13/32), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component113Node51_sound : Sound component113Node51Box :=
  sound_of_literal_split component113Node51Box component113Node49Box component113Node50Box
    .chi (53/128) (by rfl) (by rfl)
    component113Node49_sound component113Node50_sound

private noncomputable def component113Node52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (13/32), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component113Node52_sound : Sound component113Node52Box :=
  sound_of_literal_split component113Node52Box component113Node48Box component113Node51Box
    .k (51/16) (by rfl) (by rfl)
    component113Node48_sound component113Node51_sound

private noncomputable def component113Node53Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (27/64), chiHi := (55/128) }

set_option maxRecDepth 1000000 in
private theorem component113Node53_sound : Sound component113Node53Box :=
  sound_of_literal_split component113Node53Box leaf5625Box leaf5626Box
    .k (101/32) (by rfl) (by rfl)
    leaf5625FlatSound leaf5626FlatSound

private noncomputable def component113Node54Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (55/128), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component113Node54_sound : Sound component113Node54Box :=
  sound_of_literal_split component113Node54Box leaf5627Box leaf5628Box
    .k (101/32) (by rfl) (by rfl)
    leaf5627FlatSound leaf5628FlatSound

private noncomputable def component113Node55Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (27/64), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component113Node55_sound : Sound component113Node55Box :=
  sound_of_literal_split component113Node55Box component113Node53Box component113Node54Box
    .chi (55/128) (by rfl) (by rfl)
    component113Node53_sound component113Node54_sound

private noncomputable def component113Node56Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (27/64), chiHi := (55/128) }

set_option maxRecDepth 1000000 in
private theorem component113Node56_sound : Sound component113Node56Box :=
  sound_of_literal_split component113Node56Box leaf5629Box leaf5630Box
    .k (103/32) (by rfl) (by rfl)
    leaf5629FlatSound leaf5630FlatSound

private noncomputable def component113Node57Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (55/128), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component113Node57_sound : Sound component113Node57Box :=
  sound_of_literal_split component113Node57Box leaf5631Box leaf5632Box
    .k (103/32) (by rfl) (by rfl)
    leaf5631FlatSound leaf5632FlatSound

private noncomputable def component113Node58Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (27/64), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component113Node58_sound : Sound component113Node58Box :=
  sound_of_literal_split component113Node58Box component113Node56Box component113Node57Box
    .chi (55/128) (by rfl) (by rfl)
    component113Node56_sound component113Node57_sound

private noncomputable def component113Node59Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (27/64), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component113Node59_sound : Sound component113Node59Box :=
  sound_of_literal_split component113Node59Box component113Node55Box component113Node58Box
    .k (51/16) (by rfl) (by rfl)
    component113Node55_sound component113Node58_sound

private noncomputable def component113Node60Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (13/32), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component113Node60_sound : Sound component113Node60Box :=
  sound_of_literal_split component113Node60Box component113Node52Box component113Node59Box
    .chi (27/64) (by rfl) (by rfl)
    component113Node52_sound component113Node59_sound

private noncomputable def component113Node61Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (3/8), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component113Node61_sound : Sound component113Node61Box :=
  sound_of_literal_split component113Node61Box component113Node45Box component113Node60Box
    .chi (13/32) (by rfl) (by rfl)
    component113Node45_sound component113Node60_sound

noncomputable def component113Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (13/4), chiLo := (3/8), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
theorem component113_sound : Sound component113Box :=
  sound_of_literal_split component113Box component113Node30Box component113Node61Box
    .k (25/8) (by rfl) (by rfl)
    component113Node30_sound component113Node61_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
