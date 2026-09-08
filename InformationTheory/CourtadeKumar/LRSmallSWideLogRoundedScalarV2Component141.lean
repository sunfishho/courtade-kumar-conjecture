import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch5
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch7
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch8
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch11
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch12
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch13
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

private noncomputable def leaf6934Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (9/16), chiHi := (73/128) }

private noncomputable def leaf6934Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435843/268435456) }, vSqrt := { lower := (8191/8192), upper := (5726278997/5725869312) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (834598783/536870912) }, upper := { exponent := 1, mantissa := (12929/8192) } }, logOuter := sk169LogOuterCertificate, logK := sk169LogKCertificate, logChi := chi335LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (11452148309/11451738624) } }, logDArg := sk169LogDArgCertificate }

private noncomputable def leaf6934InnerLog : WideLogData :=
  innerPair744Data

set_option maxRecDepth 1000000 in
private theorem leaf6934LocalValidity :
    LeafFacts leaf6934Box leaf6934Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6934Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5726278997/5725869312) }) = true
      norm_num [leaf6934Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6934CertificateValid :
    WideCertificateValid leaf6934Box leaf6934Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk169ValidityFacts chi335ValidityFacts
    leaf6934LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6934CoverageChecked :
    coverageCheck (innerAD leaf6934Box) leaf6934InnerLog = true := by
  rfl'

private theorem leaf6934InnerLogValid :
    leaf6934InnerLog.Valid 8 (innerAD leaf6934Box) :=
  wideLogDataValid_of_cachedCheck endpoint482PositiveFacts
    endpoint484PositiveFacts.valid leaf6934CoverageChecked

private noncomputable def leaf6934InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629681/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6934InputLogOnePlusV_eq :
    leaf6934InputLogOnePlusV = outerEnclosure 24
      (leaf6934Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6934RoundedFacts : LeafRoundedFacts 8
    leaf6934Certificate.logOnePlusV leaf6934InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6934InputLogOnePlusV_eq }

private noncomputable def leaf6934Inputs : Inputs :=
  inputsOfCaches globalInput sk169RoundedInputs
    chi335InputQChi innerPair744Input
    leaf6934InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6934LowerChecked :
    lowerCheck 24 leaf6934Box leaf6934Inputs = true := by
  rfl'

private theorem leaf6934CoversExact : CoversExact 8
    leaf6934Box leaf6934Certificate leaf6934InnerLog leaf6934Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk169RoundedFacts chi335RoundedFacts
    innerPair744RoundedFacts leaf6934RoundedFacts (by rfl)

private theorem leaf6934FlatSound : Sound leaf6934Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6934CertificateValid
    leaf6934InnerLogValid leaf6934CoversExact leaf6934LowerChecked

private noncomputable def leaf6935Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (9/16), chiHi := (73/128) }

private noncomputable def leaf6935Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435845/268435456) }, vSqrt := { lower := (8191/8192), upper := (17178836991/17177589248) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (839317085/536870912) }, upper := { exponent := 1, mantissa := (6501/4096) } }, logOuter := sk170LogOuterCertificate, logK := sk170LogKCertificate, logChi := chi335LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34356426239/34355178496) } }, logDArg := sk170LogDArgCertificate }

private noncomputable def leaf6935InnerLog : WideLogData :=
  innerPair748Data

set_option maxRecDepth 1000000 in
private theorem leaf6935LocalValidity :
    LeafFacts leaf6935Box leaf6935Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6935Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178836991/17177589248) }) = true
      norm_num [leaf6935Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6935CertificateValid :
    WideCertificateValid leaf6935Box leaf6935Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk170ValidityFacts chi335ValidityFacts
    leaf6935LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6935CoverageChecked :
    coverageCheck (innerAD leaf6935Box) leaf6935InnerLog = true := by
  rfl'

private theorem leaf6935InnerLogValid :
    leaf6935InnerLog.Valid 8 (innerAD leaf6935Box) :=
  wideLogDataValid_of_cachedCheck endpoint483PositiveFacts
    endpoint484PositiveFacts.valid leaf6935CoverageChecked

private noncomputable def leaf6935InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814845/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6935InputLogOnePlusV_eq :
    leaf6935InputLogOnePlusV = outerEnclosure 24
      (leaf6935Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6935RoundedFacts : LeafRoundedFacts 8
    leaf6935Certificate.logOnePlusV leaf6935InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6935InputLogOnePlusV_eq }

private noncomputable def leaf6935Inputs : Inputs :=
  inputsOfCaches globalInput sk170RoundedInputs
    chi335InputQChi innerPair748Input
    leaf6935InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6935LowerChecked :
    lowerCheck 24 leaf6935Box leaf6935Inputs = true := by
  rfl'

private theorem leaf6935CoversExact : CoversExact 8
    leaf6935Box leaf6935Certificate leaf6935InnerLog leaf6935Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk170RoundedFacts chi335RoundedFacts
    innerPair748RoundedFacts leaf6935RoundedFacts (by rfl)

private theorem leaf6935FlatSound : Sound leaf6935Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6935CertificateValid
    leaf6935InnerLogValid leaf6935CoversExact leaf6935LowerChecked

private noncomputable def leaf6936Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (73/128), chiHi := (37/64) }

private noncomputable def leaf6936Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435845/268435456) }, vSqrt := { lower := (8191/8192), upper := (17178836991/17177576960) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (842462621/536870912) }, upper := { exponent := 1, mantissa := (6525/4096) } }, logOuter := sk169LogOuterCertificate, logK := sk169LogKCertificate, logChi := chi336LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34356413951/34355153920) } }, logDArg := sk169LogDArgCertificate }

private noncomputable def leaf6936InnerLog : WideLogData :=
  innerPair748Data

set_option maxRecDepth 1000000 in
private theorem leaf6936LocalValidity :
    LeafFacts leaf6936Box leaf6936Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6936Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178836991/17177576960) }) = true
      norm_num [leaf6936Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6936CertificateValid :
    WideCertificateValid leaf6936Box leaf6936Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk169ValidityFacts chi336ValidityFacts
    leaf6936LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6936CoverageChecked :
    coverageCheck (innerAD leaf6936Box) leaf6936InnerLog = true := by
  rfl'

private theorem leaf6936InnerLogValid :
    leaf6936InnerLog.Valid 8 (innerAD leaf6936Box) :=
  wideLogDataValid_of_cachedCheck endpoint483PositiveFacts
    endpoint484PositiveFacts.valid leaf6936CoverageChecked

private noncomputable def leaf6936InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (90857/131072) }

set_option maxRecDepth 1000000 in
private theorem leaf6936InputLogOnePlusV_eq :
    leaf6936InputLogOnePlusV = outerEnclosure 24
      (leaf6936Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6936RoundedFacts : LeafRoundedFacts 8
    leaf6936Certificate.logOnePlusV leaf6936InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6936InputLogOnePlusV_eq }

private noncomputable def leaf6936Inputs : Inputs :=
  inputsOfCaches globalInput sk169RoundedInputs
    chi336InputQChi innerPair748Input
    leaf6936InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6936LowerChecked :
    lowerCheck 24 leaf6936Box leaf6936Inputs = true := by
  rfl'

private theorem leaf6936CoversExact : CoversExact 8
    leaf6936Box leaf6936Certificate leaf6936InnerLog leaf6936Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk169RoundedFacts chi336RoundedFacts
    innerPair748RoundedFacts leaf6936RoundedFacts (by rfl)

private theorem leaf6936FlatSound : Sound leaf6936Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6936CertificateValid
    leaf6936InnerLogValid leaf6936CoversExact leaf6936LowerChecked

private noncomputable def leaf6937Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (73/128), chiHi := (37/64) }

private noncomputable def leaf6937Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435847/268435456) }, vSqrt := { lower := (8191/8192), upper := (5726278997/5725852672) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (847246455/536870912) }, upper := { exponent := 1, mantissa := (3281/2048) } }, logOuter := sk170LogOuterCertificate, logK := sk170LogKCertificate, logChi := chi336LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (11452131669/11451705344) } }, logDArg := sk170LogDArgCertificate }

private noncomputable def leaf6937InnerLog : WideLogData :=
  innerPair749Data

set_option maxRecDepth 1000000 in
private theorem leaf6937LocalValidity :
    LeafFacts leaf6937Box leaf6937Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6937Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5726278997/5725852672) }) = true
      norm_num [leaf6937Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6937CertificateValid :
    WideCertificateValid leaf6937Box leaf6937Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk170ValidityFacts chi336ValidityFacts
    leaf6937LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6937CoverageChecked :
    coverageCheck (innerAD leaf6937Box) leaf6937InnerLog = true := by
  rfl'

private theorem leaf6937InnerLogValid :
    leaf6937InnerLog.Valid 8 (innerAD leaf6937Box) :=
  wideLogDataValid_of_cachedCheck endpoint483PositiveFacts
    endpoint485PositiveFacts.valid leaf6937CoverageChecked

private noncomputable def leaf6937InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629705/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6937InputLogOnePlusV_eq :
    leaf6937InputLogOnePlusV = outerEnclosure 24
      (leaf6937Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6937RoundedFacts : LeafRoundedFacts 8
    leaf6937Certificate.logOnePlusV leaf6937InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6937InputLogOnePlusV_eq }

private noncomputable def leaf6937Inputs : Inputs :=
  inputsOfCaches globalInput sk170RoundedInputs
    chi336InputQChi innerPair749Input
    leaf6937InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6937LowerChecked :
    lowerCheck 24 leaf6937Box leaf6937Inputs = true := by
  rfl'

private theorem leaf6937CoversExact : CoversExact 8
    leaf6937Box leaf6937Certificate leaf6937InnerLog leaf6937Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk170RoundedFacts chi336RoundedFacts
    innerPair749RoundedFacts leaf6937RoundedFacts (by rfl)

private theorem leaf6937FlatSound : Sound leaf6937Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6937CertificateValid
    leaf6937InnerLogValid leaf6937CoversExact leaf6937LowerChecked

private noncomputable def leaf6938Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (9/16), chiHi := (73/128) }

private noncomputable def leaf6938Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435847/268435456) }, vSqrt := { lower := (8191/8192), upper := (17178836991/17177570560) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (844035387/536870912) }, upper := { exponent := 1, mantissa := (13075/8192) } }, logOuter := sk171LogOuterCertificate, logK := sk171LogKCertificate, logChi := chi335LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34356407551/34355141120) } }, logDArg := sk171LogDArgCertificate }

private noncomputable def leaf6938InnerLog : WideLogData :=
  innerPair749Data

set_option maxRecDepth 1000000 in
private theorem leaf6938LocalValidity :
    LeafFacts leaf6938Box leaf6938Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6938Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178836991/17177570560) }) = true
      norm_num [leaf6938Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6938CertificateValid :
    WideCertificateValid leaf6938Box leaf6938Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk171ValidityFacts chi335ValidityFacts
    leaf6938LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6938CoverageChecked :
    coverageCheck (innerAD leaf6938Box) leaf6938InnerLog = true := by
  rfl'

private theorem leaf6938InnerLogValid :
    leaf6938InnerLog.Valid 8 (innerAD leaf6938Box) :=
  wideLogDataValid_of_cachedCheck endpoint483PositiveFacts
    endpoint485PositiveFacts.valid leaf6938CoverageChecked

private noncomputable def leaf6938InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629699/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6938InputLogOnePlusV_eq :
    leaf6938InputLogOnePlusV = outerEnclosure 24
      (leaf6938Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6938RoundedFacts : LeafRoundedFacts 8
    leaf6938Certificate.logOnePlusV leaf6938InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6938InputLogOnePlusV_eq }

private noncomputable def leaf6938Inputs : Inputs :=
  inputsOfCaches globalInput sk171RoundedInputs
    chi335InputQChi innerPair749Input
    leaf6938InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6938LowerChecked :
    lowerCheck 24 leaf6938Box leaf6938Inputs = true := by
  rfl'

private theorem leaf6938CoversExact : CoversExact 8
    leaf6938Box leaf6938Certificate leaf6938InnerLog leaf6938Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk171RoundedFacts chi335RoundedFacts
    innerPair749RoundedFacts leaf6938RoundedFacts (by rfl)

private theorem leaf6938FlatSound : Sound leaf6938Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6938CertificateValid
    leaf6938InnerLogValid leaf6938CoversExact leaf6938LowerChecked

private noncomputable def leaf6939Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (9/16), chiHi := (73/128) }

private noncomputable def leaf6939Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435849/268435456) }, vSqrt := { lower := (8191/8192), upper := (5726278997/5725850624) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (848753689/536870912) }, upper := { exponent := 1, mantissa := (3287/2048) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi335LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (11452129621/11451701248) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf6939InnerLog : WideLogData :=
  innerPair749Data

set_option maxRecDepth 1000000 in
private theorem leaf6939LocalValidity :
    LeafFacts leaf6939Box leaf6939Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6939Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5726278997/5725850624) }) = true
      norm_num [leaf6939Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6939CertificateValid :
    WideCertificateValid leaf6939Box leaf6939Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi335ValidityFacts
    leaf6939LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6939CoverageChecked :
    coverageCheck (innerAD leaf6939Box) leaf6939InnerLog = true := by
  rfl'

private theorem leaf6939InnerLogValid :
    leaf6939InnerLog.Valid 8 (innerAD leaf6939Box) :=
  wideLogDataValid_of_cachedCheck endpoint483PositiveFacts
    endpoint485PositiveFacts.valid leaf6939CoverageChecked

private noncomputable def leaf6939InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907427/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6939InputLogOnePlusV_eq :
    leaf6939InputLogOnePlusV = outerEnclosure 24
      (leaf6939Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6939RoundedFacts : LeafRoundedFacts 8
    leaf6939Certificate.logOnePlusV leaf6939InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6939InputLogOnePlusV_eq }

private noncomputable def leaf6939Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi335InputQChi innerPair749Input
    leaf6939InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6939LowerChecked :
    lowerCheck 24 leaf6939Box leaf6939Inputs = true := by
  rfl'

private theorem leaf6939CoversExact : CoversExact 8
    leaf6939Box leaf6939Certificate leaf6939InnerLog leaf6939Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi335RoundedFacts
    innerPair749RoundedFacts leaf6939RoundedFacts (by rfl)

private theorem leaf6939FlatSound : Sound leaf6939Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6939CertificateValid
    leaf6939InnerLogValid leaf6939CoversExact leaf6939LowerChecked

private noncomputable def leaf6940Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (73/128), chiHi := (37/64) }

private noncomputable def leaf6940Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435849/268435456) }, vSqrt := { lower := (8191/8192), upper := (17178836991/17177539072) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (852030289/536870912) }, upper := { exponent := 1, mantissa := (6599/4096) } }, logOuter := sk171LogOuterCertificate, logK := sk171LogKCertificate, logChi := chi336LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34356376063/34355078144) } }, logDArg := sk171LogDArgCertificate }

private noncomputable def leaf6940InnerLog : WideLogData :=
  innerPair749Data

set_option maxRecDepth 1000000 in
private theorem leaf6940LocalValidity :
    LeafFacts leaf6940Box leaf6940Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6940Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178836991/17177539072) }) = true
      norm_num [leaf6940Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6940CertificateValid :
    WideCertificateValid leaf6940Box leaf6940Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk171ValidityFacts chi336ValidityFacts
    leaf6940LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6940CoverageChecked :
    coverageCheck (innerAD leaf6940Box) leaf6940InnerLog = true := by
  rfl'

private theorem leaf6940InnerLogValid :
    leaf6940InnerLog.Valid 8 (innerAD leaf6940Box) :=
  wideLogDataValid_of_cachedCheck endpoint483PositiveFacts
    endpoint485PositiveFacts.valid leaf6940CoverageChecked

private noncomputable def leaf6940InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629715/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6940InputLogOnePlusV_eq :
    leaf6940InputLogOnePlusV = outerEnclosure 24
      (leaf6940Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6940RoundedFacts : LeafRoundedFacts 8
    leaf6940Certificate.logOnePlusV leaf6940InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6940InputLogOnePlusV_eq }

private noncomputable def leaf6940Inputs : Inputs :=
  inputsOfCaches globalInput sk171RoundedInputs
    chi336InputQChi innerPair749Input
    leaf6940InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6940LowerChecked :
    lowerCheck 24 leaf6940Box leaf6940Inputs = true := by
  rfl'

private theorem leaf6940CoversExact : CoversExact 8
    leaf6940Box leaf6940Certificate leaf6940InnerLog leaf6940Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk171RoundedFacts chi336RoundedFacts
    innerPair749RoundedFacts leaf6940RoundedFacts (by rfl)

private theorem leaf6940FlatSound : Sound leaf6940Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6940CertificateValid
    leaf6940InnerLogValid leaf6940CoversExact leaf6940LowerChecked

private noncomputable def leaf6941Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (73/128), chiHi := (37/64) }

private noncomputable def leaf6941Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435851/268435456) }, vSqrt := { lower := (8191/8192), upper := (135266433/135256064) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (856814123/536870912) }, upper := { exponent := 1, mantissa := (1659/1024) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi336LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (270522497/270512128) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf6941InnerLog : WideLogData :=
  innerPair754Data

set_option maxRecDepth 1000000 in
private theorem leaf6941LocalValidity :
    LeafFacts leaf6941Box leaf6941Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6941Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (135266433/135256064) }) = true
      norm_num [leaf6941Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6941CertificateValid :
    WideCertificateValid leaf6941Box leaf6941Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi336ValidityFacts
    leaf6941LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6941CoverageChecked :
    coverageCheck (innerAD leaf6941Box) leaf6941InnerLog = true := by
  rfl'

private theorem leaf6941InnerLogValid :
    leaf6941InnerLog.Valid 8 (innerAD leaf6941Box) :=
  wideLogDataValid_of_cachedCheck endpoint484PositiveFacts
    endpoint485PositiveFacts.valid leaf6941CoverageChecked

private noncomputable def leaf6941InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907431/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6941InputLogOnePlusV_eq :
    leaf6941InputLogOnePlusV = outerEnclosure 24
      (leaf6941Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6941RoundedFacts : LeafRoundedFacts 8
    leaf6941Certificate.logOnePlusV leaf6941InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6941InputLogOnePlusV_eq }

private noncomputable def leaf6941Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi336InputQChi innerPair754Input
    leaf6941InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6941LowerChecked :
    lowerCheck 24 leaf6941Box leaf6941Inputs = true := by
  rfl'

private theorem leaf6941CoversExact : CoversExact 8
    leaf6941Box leaf6941Certificate leaf6941InnerLog leaf6941Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi336RoundedFacts
    innerPair754RoundedFacts leaf6941RoundedFacts (by rfl)

private theorem leaf6941FlatSound : Sound leaf6941Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6941CertificateValid
    leaf6941InnerLogValid leaf6941CoversExact leaf6941LowerChecked

private noncomputable def leaf6942Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (37/64), chiHi := (75/128) }

private noncomputable def leaf6942Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134217999/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588763392) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (425146771/268435456) }, upper := { exponent := 1, mantissa := (6623/4096) } }, logOuter := sk157LogOuterCertificate, logK := sk157LogKCertificate, logChi := chi337LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178190079/17177526784) } }, logDArg := sk157LogDArgCertificate }

private noncomputable def leaf6942InnerLog : WideLogData :=
  innerPair784Data

set_option maxRecDepth 1000000 in
private theorem leaf6942LocalValidity :
    LeafFacts leaf6942Box leaf6942Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6942Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588763392) }) = true
      norm_num [leaf6942Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6942CertificateValid :
    WideCertificateValid leaf6942Box leaf6942Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk157ValidityFacts chi337ValidityFacts
    leaf6942LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6942CoverageChecked :
    coverageCheck (innerAD leaf6942Box) leaf6942InnerLog = true := by
  rfl'

private theorem leaf6942InnerLogValid :
    leaf6942InnerLog.Valid 8 (innerAD leaf6942Box) :=
  wideLogDataValid_of_cachedCheck endpoint492PositiveFacts
    endpoint496PositiveFacts.valid leaf6942CoverageChecked

private noncomputable def leaf6942InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629729/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6942InputLogOnePlusV_eq :
    leaf6942InputLogOnePlusV = outerEnclosure 24
      (leaf6942Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6942RoundedFacts : LeafRoundedFacts 8
    leaf6942Certificate.logOnePlusV leaf6942InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6942InputLogOnePlusV_eq }

private noncomputable def leaf6942Inputs : Inputs :=
  inputsOfCaches globalInput sk157RoundedInputs
    chi337InputQChi innerPair784Input
    leaf6942InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6942LowerChecked :
    lowerCheck 24 leaf6942Box leaf6942Inputs = true := by
  rfl'

private theorem leaf6942CoversExact : CoversExact 8
    leaf6942Box leaf6942Certificate leaf6942InnerLog leaf6942Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk157RoundedFacts chi337RoundedFacts
    innerPair784RoundedFacts leaf6942RoundedFacts (by rfl)

private theorem leaf6942FlatSound : Sound leaf6942Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6942CertificateValid
    leaf6942InnerLogValid leaf6942CoversExact leaf6942LowerChecked

private noncomputable def leaf6943Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (75/128), chiHi := (19/32) }

private noncomputable def leaf6943Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218001/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588747776) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (429078689/268435456) }, upper := { exponent := 1, mantissa := (1671/1024) } }, logOuter := sk157LogOuterCertificate, logK := sk157LogKCertificate, logChi := chi338LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178174463/17177495552) } }, logDArg := sk157LogDArgCertificate }

private noncomputable def leaf6943InnerLog : WideLogData :=
  innerPair759Data

set_option maxRecDepth 1000000 in
private theorem leaf6943LocalValidity :
    LeafFacts leaf6943Box leaf6943Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6943Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588747776) }) = true
      norm_num [leaf6943Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6943CertificateValid :
    WideCertificateValid leaf6943Box leaf6943Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk157ValidityFacts chi338ValidityFacts
    leaf6943LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6943CoverageChecked :
    coverageCheck (innerAD leaf6943Box) leaf6943InnerLog = true := by
  rfl'

private theorem leaf6943InnerLogValid :
    leaf6943InnerLog.Valid 8 (innerAD leaf6943Box) :=
  wideLogDataValid_of_cachedCheck endpoint484PositiveFacts
    endpoint554PositiveFacts.valid leaf6943CoverageChecked

private noncomputable def leaf6943InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726859/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf6943InputLogOnePlusV_eq :
    leaf6943InputLogOnePlusV = outerEnclosure 24
      (leaf6943Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6943RoundedFacts : LeafRoundedFacts 8
    leaf6943Certificate.logOnePlusV leaf6943InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6943InputLogOnePlusV_eq }

private noncomputable def leaf6943Inputs : Inputs :=
  inputsOfCaches globalInput sk157RoundedInputs
    chi338InputQChi innerPair759Input
    leaf6943InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6943LowerChecked :
    lowerCheck 24 leaf6943Box leaf6943Inputs = true := by
  rfl'

private theorem leaf6943CoversExact : CoversExact 8
    leaf6943Box leaf6943Certificate leaf6943InnerLog leaf6943Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk157RoundedFacts chi338RoundedFacts
    innerPair759RoundedFacts leaf6943RoundedFacts (by rfl)

private theorem leaf6943FlatSound : Sound leaf6943Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6943CertificateValid
    leaf6943InnerLogValid leaf6943CoversExact leaf6943LowerChecked

private noncomputable def leaf6944Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (37/64), chiHi := (75/128) }

private noncomputable def leaf6944Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218001/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588744192) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (429996137/268435456) }, upper := { exponent := 1, mantissa := (3349/2048) } }, logOuter := sk158LogOuterCertificate, logK := sk158LogKCertificate, logChi := chi337LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178170879/17177488384) } }, logDArg := sk158LogDArgCertificate }

private noncomputable def leaf6944InnerLog : WideLogData :=
  innerPair787Data

set_option maxRecDepth 1000000 in
private theorem leaf6944LocalValidity :
    LeafFacts leaf6944Box leaf6944Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6944Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588744192) }) = true
      norm_num [leaf6944Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6944CertificateValid :
    WideCertificateValid leaf6944Box leaf6944Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk158ValidityFacts chi337ValidityFacts
    leaf6944LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6944CoverageChecked :
    coverageCheck (innerAD leaf6944Box) leaf6944InnerLog = true := by
  rfl'

private theorem leaf6944InnerLogValid :
    leaf6944InnerLog.Valid 8 (innerAD leaf6944Box) :=
  wideLogDataValid_of_cachedCheck endpoint494PositiveFacts
    endpoint555PositiveFacts.valid leaf6944CoverageChecked

private noncomputable def leaf6944InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629747/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6944InputLogOnePlusV_eq :
    leaf6944InputLogOnePlusV = outerEnclosure 24
      (leaf6944Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6944RoundedFacts : LeafRoundedFacts 8
    leaf6944Certificate.logOnePlusV leaf6944InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6944InputLogOnePlusV_eq }

private noncomputable def leaf6944Inputs : Inputs :=
  inputsOfCaches globalInput sk158RoundedInputs
    chi337InputQChi innerPair787Input
    leaf6944InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6944LowerChecked :
    lowerCheck 24 leaf6944Box leaf6944Inputs = true := by
  rfl'

private theorem leaf6944CoversExact : CoversExact 8
    leaf6944Box leaf6944Certificate leaf6944InnerLog leaf6944Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk158RoundedFacts chi337RoundedFacts
    innerPair787RoundedFacts leaf6944RoundedFacts (by rfl)

private theorem leaf6944FlatSound : Sound leaf6944Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6944CertificateValid
    leaf6944InnerLogValid leaf6944CoversExact leaf6944LowerChecked

private noncomputable def leaf6945Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (75/128), chiHi := (19/32) }

private noncomputable def leaf6945Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218003/134217728) }, vSqrt := { lower := (8191/8192), upper := (2863142229/2862909440) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (433993587/268435456) }, upper := { exponent := 1, mantissa := (845/512) } }, logOuter := sk158LogOuterCertificate, logK := sk158LogKCertificate, logChi := chi338LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (5726051669/5725818880) } }, logDArg := sk158LogDArgCertificate }

private noncomputable def leaf6945InnerLog : WideLogData :=
  innerPair854Data

set_option maxRecDepth 1000000 in
private theorem leaf6945LocalValidity :
    LeafFacts leaf6945Box leaf6945Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6945Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (2863142229/2862909440) }) = true
      norm_num [leaf6945Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6945CertificateValid :
    WideCertificateValid leaf6945Box leaf6945Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk158ValidityFacts chi338ValidityFacts
    leaf6945LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6945CoverageChecked :
    coverageCheck (innerAD leaf6945Box) leaf6945InnerLog = true := by
  rfl'

private theorem leaf6945InnerLogValid :
    leaf6945InnerLog.Valid 8 (innerAD leaf6945Box) :=
  wideLogDataValid_of_cachedCheck endpoint556PositiveFacts
    endpoint557PositiveFacts.valid leaf6945CoverageChecked

private noncomputable def leaf6945InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629763/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6945InputLogOnePlusV_eq :
    leaf6945InputLogOnePlusV = outerEnclosure 24
      (leaf6945Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6945RoundedFacts : LeafRoundedFacts 8
    leaf6945Certificate.logOnePlusV leaf6945InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6945InputLogOnePlusV_eq }

private noncomputable def leaf6945Inputs : Inputs :=
  inputsOfCaches globalInput sk158RoundedInputs
    chi338InputQChi innerPair854Input
    leaf6945InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6945LowerChecked :
    lowerCheck 24 leaf6945Box leaf6945Inputs = true := by
  rfl'

private theorem leaf6945CoversExact : CoversExact 8
    leaf6945Box leaf6945Certificate leaf6945InnerLog leaf6945Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk158RoundedFacts chi338RoundedFacts
    innerPair854RoundedFacts leaf6945RoundedFacts (by rfl)

private theorem leaf6945FlatSound : Sound leaf6945Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6945CertificateValid
    leaf6945InnerLogValid leaf6945CoversExact leaf6945LowerChecked

private noncomputable def leaf6946Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (9/16), chiHi := (73/128) }

private noncomputable def leaf6946Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435851/268435456) }, vSqrt := { lower := (8191/8192), upper := (17178836991/17177533184) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (853471991/536870912) }, upper := { exponent := 1, mantissa := (13221/8192) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi335LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34356370175/34355066368) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf6946InnerLog : WideLogData :=
  innerPair749Data

set_option maxRecDepth 1000000 in
private theorem leaf6946LocalValidity :
    LeafFacts leaf6946Box leaf6946Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6946Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178836991/17177533184) }) = true
      norm_num [leaf6946Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6946CertificateValid :
    WideCertificateValid leaf6946Box leaf6946Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi335ValidityFacts
    leaf6946LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6946CoverageChecked :
    coverageCheck (innerAD leaf6946Box) leaf6946InnerLog = true := by
  rfl'

private theorem leaf6946InnerLogValid :
    leaf6946InnerLog.Valid 8 (innerAD leaf6946Box) :=
  wideLogDataValid_of_cachedCheck endpoint483PositiveFacts
    endpoint485PositiveFacts.valid leaf6946CoverageChecked

private noncomputable def leaf6946InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629717/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6946InputLogOnePlusV_eq :
    leaf6946InputLogOnePlusV = outerEnclosure 24
      (leaf6946Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6946RoundedFacts : LeafRoundedFacts 8
    leaf6946Certificate.logOnePlusV leaf6946InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6946InputLogOnePlusV_eq }

private noncomputable def leaf6946Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi335InputQChi innerPair749Input
    leaf6946InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6946LowerChecked :
    lowerCheck 24 leaf6946Box leaf6946Inputs = true := by
  rfl'

private theorem leaf6946CoversExact : CoversExact 8
    leaf6946Box leaf6946Certificate leaf6946InnerLog leaf6946Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi335RoundedFacts
    innerPair749RoundedFacts leaf6946RoundedFacts (by rfl)

private theorem leaf6946FlatSound : Sound leaf6946Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6946CertificateValid
    leaf6946InnerLogValid leaf6946CoversExact leaf6946LowerChecked

private noncomputable def leaf6947Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (9/16), chiHi := (73/128) }

private noncomputable def leaf6947Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435853/268435456) }, vSqrt := { lower := (8191/8192), upper := (17178836991/17177514496) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (858190293/536870912) }, upper := { exponent := 1, mantissa := (6647/4096) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi335LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34356351487/34355028992) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf6947InnerLog : WideLogData :=
  innerPair754Data

set_option maxRecDepth 1000000 in
private theorem leaf6947LocalValidity :
    LeafFacts leaf6947Box leaf6947Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6947Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178836991/17177514496) }) = true
      norm_num [leaf6947Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6947CertificateValid :
    WideCertificateValid leaf6947Box leaf6947Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi335ValidityFacts
    leaf6947LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6947CoverageChecked :
    coverageCheck (innerAD leaf6947Box) leaf6947InnerLog = true := by
  rfl'

private theorem leaf6947InnerLogValid :
    leaf6947InnerLog.Valid 8 (innerAD leaf6947Box) :=
  wideLogDataValid_of_cachedCheck endpoint484PositiveFacts
    endpoint485PositiveFacts.valid leaf6947CoverageChecked

private noncomputable def leaf6947InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629727/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6947InputLogOnePlusV_eq :
    leaf6947InputLogOnePlusV = outerEnclosure 24
      (leaf6947Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6947RoundedFacts : LeafRoundedFacts 8
    leaf6947Certificate.logOnePlusV leaf6947InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6947InputLogOnePlusV_eq }

private noncomputable def leaf6947Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi335InputQChi innerPair754Input
    leaf6947InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6947LowerChecked :
    lowerCheck 24 leaf6947Box leaf6947Inputs = true := by
  rfl'

private theorem leaf6947CoversExact : CoversExact 8
    leaf6947Box leaf6947Certificate leaf6947InnerLog leaf6947Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi335RoundedFacts
    innerPair754RoundedFacts leaf6947RoundedFacts (by rfl)

private theorem leaf6947FlatSound : Sound leaf6947Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6947CertificateValid
    leaf6947InnerLogValid leaf6947CoversExact leaf6947LowerChecked

private noncomputable def leaf6948Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (73/128), chiHi := (37/64) }

private noncomputable def leaf6948Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435853/268435456) }, vSqrt := { lower := (8191/8192), upper := (5726278997/5725833728) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (861597957/536870912) }, upper := { exponent := 1, mantissa := (6673/4096) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi336LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (11452112725/11451667456) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf6948InnerLog : WideLogData :=
  innerPair755Data

set_option maxRecDepth 1000000 in
private theorem leaf6948LocalValidity :
    LeafFacts leaf6948Box leaf6948Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6948Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5726278997/5725833728) }) = true
      norm_num [leaf6948Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6948CertificateValid :
    WideCertificateValid leaf6948Box leaf6948Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi336ValidityFacts
    leaf6948LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6948CoverageChecked :
    coverageCheck (innerAD leaf6948Box) leaf6948InnerLog = true := by
  rfl'

private theorem leaf6948InnerLogValid :
    leaf6948InnerLog.Valid 8 (innerAD leaf6948Box) :=
  wideLogDataValid_of_cachedCheck endpoint484PositiveFacts
    endpoint486PositiveFacts.valid leaf6948CoverageChecked

private noncomputable def leaf6948InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629733/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6948InputLogOnePlusV_eq :
    leaf6948InputLogOnePlusV = outerEnclosure 24
      (leaf6948Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6948RoundedFacts : LeafRoundedFacts 8
    leaf6948Certificate.logOnePlusV leaf6948InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6948InputLogOnePlusV_eq }

private noncomputable def leaf6948Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi336InputQChi innerPair755Input
    leaf6948InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6948LowerChecked :
    lowerCheck 24 leaf6948Box leaf6948Inputs = true := by
  rfl'

private theorem leaf6948CoversExact : CoversExact 8
    leaf6948Box leaf6948Certificate leaf6948InnerLog leaf6948Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi336RoundedFacts
    innerPair755RoundedFacts leaf6948RoundedFacts (by rfl)

private theorem leaf6948FlatSound : Sound leaf6948Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6948CertificateValid
    leaf6948InnerLogValid leaf6948CoversExact leaf6948LowerChecked

private noncomputable def leaf6949Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (73/128), chiHi := (37/64) }

private noncomputable def leaf6949Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435855/268435456) }, vSqrt := { lower := (8191/8192), upper := (17178836991/17177482240) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (866381791/536870912) }, upper := { exponent := 1, mantissa := (3355/2048) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi336LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34356319231/34354964480) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf6949InnerLog : WideLogData :=
  innerPair755Data

set_option maxRecDepth 1000000 in
private theorem leaf6949LocalValidity :
    LeafFacts leaf6949Box leaf6949Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6949Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178836991/17177482240) }) = true
      norm_num [leaf6949Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6949CertificateValid :
    WideCertificateValid leaf6949Box leaf6949Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi336ValidityFacts
    leaf6949LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6949CoverageChecked :
    coverageCheck (innerAD leaf6949Box) leaf6949InnerLog = true := by
  rfl'

private theorem leaf6949InnerLogValid :
    leaf6949InnerLog.Valid 8 (innerAD leaf6949Box) :=
  wideLogDataValid_of_cachedCheck endpoint484PositiveFacts
    endpoint486PositiveFacts.valid leaf6949CoverageChecked

private noncomputable def leaf6949InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814871/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6949InputLogOnePlusV_eq :
    leaf6949InputLogOnePlusV = outerEnclosure 24
      (leaf6949Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6949RoundedFacts : LeafRoundedFacts 8
    leaf6949Certificate.logOnePlusV leaf6949InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6949InputLogOnePlusV_eq }

private noncomputable def leaf6949Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi336InputQChi innerPair755Input
    leaf6949InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6949LowerChecked :
    lowerCheck 24 leaf6949Box leaf6949Inputs = true := by
  rfl'

private theorem leaf6949CoversExact : CoversExact 8
    leaf6949Box leaf6949Certificate leaf6949InnerLog leaf6949Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi336RoundedFacts
    innerPair755RoundedFacts leaf6949RoundedFacts (by rfl)

private theorem leaf6949FlatSound : Sound leaf6949Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6949CertificateValid
    leaf6949InnerLogValid leaf6949CoversExact leaf6949LowerChecked

private noncomputable def leaf6950Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (9/16), chiHi := (73/128) }

private noncomputable def leaf6950Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435855/268435456) }, vSqrt := { lower := (8191/8192), upper := (5726278997/5725831936) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (862908595/536870912) }, upper := { exponent := 1, mantissa := (13367/8192) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi335LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (11452110933/11451663872) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf6950InnerLog : WideLogData :=
  innerPair755Data

set_option maxRecDepth 1000000 in
private theorem leaf6950LocalValidity :
    LeafFacts leaf6950Box leaf6950Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6950Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5726278997/5725831936) }) = true
      norm_num [leaf6950Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6950CertificateValid :
    WideCertificateValid leaf6950Box leaf6950Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi335ValidityFacts
    leaf6950LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6950CoverageChecked :
    coverageCheck (innerAD leaf6950Box) leaf6950InnerLog = true := by
  rfl'

private theorem leaf6950InnerLogValid :
    leaf6950InnerLog.Valid 8 (innerAD leaf6950Box) :=
  wideLogDataValid_of_cachedCheck endpoint484PositiveFacts
    endpoint486PositiveFacts.valid leaf6950CoverageChecked

private noncomputable def leaf6950InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453717/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf6950InputLogOnePlusV_eq :
    leaf6950InputLogOnePlusV = outerEnclosure 24
      (leaf6950Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6950RoundedFacts : LeafRoundedFacts 8
    leaf6950Certificate.logOnePlusV leaf6950InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6950InputLogOnePlusV_eq }

private noncomputable def leaf6950Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi335InputQChi innerPair755Input
    leaf6950InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6950LowerChecked :
    lowerCheck 24 leaf6950Box leaf6950Inputs = true := by
  rfl'

private theorem leaf6950CoversExact : CoversExact 8
    leaf6950Box leaf6950Certificate leaf6950InnerLog leaf6950Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi335RoundedFacts
    innerPair755RoundedFacts leaf6950RoundedFacts (by rfl)

private theorem leaf6950FlatSound : Sound leaf6950Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6950CertificateValid
    leaf6950InnerLogValid leaf6950CoversExact leaf6950LowerChecked

private noncomputable def leaf6951Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (9/16), chiHi := (73/128) }

private noncomputable def leaf6951Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435857/268435456) }, vSqrt := { lower := (65527/65536), upper := (17178836991/17177477120) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (867626897/536870912) }, upper := { exponent := 1, mantissa := (105/64) } }, logOuter := sk176LogOuterCertificate, logK := sk176LogKCertificate, logChi := chi335LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (34356314111/34354954240) } }, logDArg := sk176LogDArgCertificate }

private noncomputable def leaf6951InnerLog : WideLogData :=
  innerPair755Data

set_option maxRecDepth 1000000 in
private theorem leaf6951LocalValidity :
    LeafFacts leaf6951Box leaf6951Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6951Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (17178836991/17177477120) }) = true
      norm_num [leaf6951Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6951CertificateValid :
    WideCertificateValid leaf6951Box leaf6951Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk176ValidityFacts chi335ValidityFacts
    leaf6951LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6951CoverageChecked :
    coverageCheck (innerAD leaf6951Box) leaf6951InnerLog = true := by
  rfl'

private theorem leaf6951InnerLogValid :
    leaf6951InnerLog.Valid 8 (innerAD leaf6951Box) :=
  wideLogDataValid_of_cachedCheck endpoint484PositiveFacts
    endpoint486PositiveFacts.valid leaf6951CoverageChecked

private noncomputable def leaf6951InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629745/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6951InputLogOnePlusV_eq :
    leaf6951InputLogOnePlusV = outerEnclosure 24
      (leaf6951Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6951RoundedFacts : LeafRoundedFacts 8
    leaf6951Certificate.logOnePlusV leaf6951InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6951InputLogOnePlusV_eq }

private noncomputable def leaf6951Inputs : Inputs :=
  inputsOfCaches globalInput sk176RoundedInputs
    chi335InputQChi innerPair755Input
    leaf6951InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6951LowerChecked :
    lowerCheck 24 leaf6951Box leaf6951Inputs = true := by
  rfl'

private theorem leaf6951CoversExact : CoversExact 8
    leaf6951Box leaf6951Certificate leaf6951InnerLog leaf6951Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk176RoundedFacts chi335RoundedFacts
    innerPair755RoundedFacts leaf6951RoundedFacts (by rfl)

private theorem leaf6951FlatSound : Sound leaf6951Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6951CertificateValid
    leaf6951InnerLogValid leaf6951CoversExact leaf6951LowerChecked

private noncomputable def leaf6952Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (73/128), chiHi := (37/64) }

private noncomputable def leaf6952Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435857/268435456) }, vSqrt := { lower := (8191/8192), upper := (17178836991/17177463296) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (871165625/536870912) }, upper := { exponent := 1, mantissa := (6747/4096) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi336LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34356300287/34354926592) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf6952InnerLog : WideLogData :=
  innerPair755Data

set_option maxRecDepth 1000000 in
private theorem leaf6952LocalValidity :
    LeafFacts leaf6952Box leaf6952Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6952Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178836991/17177463296) }) = true
      norm_num [leaf6952Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6952CertificateValid :
    WideCertificateValid leaf6952Box leaf6952Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi336ValidityFacts
    leaf6952LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6952CoverageChecked :
    coverageCheck (innerAD leaf6952Box) leaf6952InnerLog = true := by
  rfl'

private theorem leaf6952InnerLogValid :
    leaf6952InnerLog.Valid 8 (innerAD leaf6952Box) :=
  wideLogDataValid_of_cachedCheck endpoint484PositiveFacts
    endpoint486PositiveFacts.valid leaf6952CoverageChecked

private noncomputable def leaf6952InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453719/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf6952InputLogOnePlusV_eq :
    leaf6952InputLogOnePlusV = outerEnclosure 24
      (leaf6952Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6952RoundedFacts : LeafRoundedFacts 8
    leaf6952Certificate.logOnePlusV leaf6952InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6952InputLogOnePlusV_eq }

private noncomputable def leaf6952Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi336InputQChi innerPair755Input
    leaf6952InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6952LowerChecked :
    lowerCheck 24 leaf6952Box leaf6952Inputs = true := by
  rfl'

private theorem leaf6952CoversExact : CoversExact 8
    leaf6952Box leaf6952Certificate leaf6952InnerLog leaf6952Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi336RoundedFacts
    innerPair755RoundedFacts leaf6952RoundedFacts (by rfl)

private theorem leaf6952FlatSound : Sound leaf6952Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6952CertificateValid
    leaf6952InnerLogValid leaf6952CoversExact leaf6952LowerChecked

private noncomputable def leaf6953Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (73/128), chiHi := (37/64) }

private noncomputable def leaf6953Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435859/268435456) }, vSqrt := { lower := (65527/65536), upper := (5726278997/5725814784) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (875949459/536870912) }, upper := { exponent := 1, mantissa := (53/32) } }, logOuter := sk176LogOuterCertificate, logK := sk176LogKCertificate, logChi := chi336LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (11452093781/11451629568) } }, logDArg := sk176LogDArgCertificate }

private noncomputable def leaf6953InnerLog : WideLogData :=
  innerPair760Data

set_option maxRecDepth 1000000 in
private theorem leaf6953LocalValidity :
    LeafFacts leaf6953Box leaf6953Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6953Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (5726278997/5725814784) }) = true
      norm_num [leaf6953Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6953CertificateValid :
    WideCertificateValid leaf6953Box leaf6953Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk176ValidityFacts chi336ValidityFacts
    leaf6953LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6953CoverageChecked :
    coverageCheck (innerAD leaf6953Box) leaf6953InnerLog = true := by
  rfl'

private theorem leaf6953InnerLogValid :
    leaf6953InnerLog.Valid 8 (innerAD leaf6953Box) :=
  wideLogDataValid_of_cachedCheck endpoint485PositiveFacts
    endpoint486PositiveFacts.valid leaf6953CoverageChecked

private noncomputable def leaf6953InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629761/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6953InputLogOnePlusV_eq :
    leaf6953InputLogOnePlusV = outerEnclosure 24
      (leaf6953Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6953RoundedFacts : LeafRoundedFacts 8
    leaf6953Certificate.logOnePlusV leaf6953InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6953InputLogOnePlusV_eq }

private noncomputable def leaf6953Inputs : Inputs :=
  inputsOfCaches globalInput sk176RoundedInputs
    chi336InputQChi innerPair760Input
    leaf6953InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6953LowerChecked :
    lowerCheck 24 leaf6953Box leaf6953Inputs = true := by
  rfl'

private theorem leaf6953CoversExact : CoversExact 8
    leaf6953Box leaf6953Certificate leaf6953InnerLog leaf6953Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk176RoundedFacts chi336RoundedFacts
    innerPair760RoundedFacts leaf6953RoundedFacts (by rfl)

private theorem leaf6953FlatSound : Sound leaf6953Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6953CertificateValid
    leaf6953InnerLogValid leaf6953CoversExact leaf6953LowerChecked

private noncomputable def leaf6954Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (37/64), chiHi := (75/128) }

private noncomputable def leaf6954Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435855/268435456) }, vSqrt := { lower := (8191/8192), upper := (17178836991/17177469184) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (869723923/536870912) }, upper := { exponent := 1, mantissa := (13471/8192) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi337LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34356306175/34354938368) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf6954InnerLog : WideLogData :=
  innerPair755Data

set_option maxRecDepth 1000000 in
private theorem leaf6954LocalValidity :
    LeafFacts leaf6954Box leaf6954Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6954Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178836991/17177469184) }) = true
      norm_num [leaf6954Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6954CertificateValid :
    WideCertificateValid leaf6954Box leaf6954Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi337ValidityFacts
    leaf6954LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6954CoverageChecked :
    coverageCheck (innerAD leaf6954Box) leaf6954InnerLog = true := by
  rfl'

private theorem leaf6954InnerLogValid :
    leaf6954InnerLog.Valid 8 (innerAD leaf6954Box) :=
  wideLogDataValid_of_cachedCheck endpoint484PositiveFacts
    endpoint486PositiveFacts.valid leaf6954CoverageChecked

private noncomputable def leaf6954InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629749/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6954InputLogOnePlusV_eq :
    leaf6954InputLogOnePlusV = outerEnclosure 24
      (leaf6954Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6954RoundedFacts : LeafRoundedFacts 8
    leaf6954Certificate.logOnePlusV leaf6954InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6954InputLogOnePlusV_eq }

private noncomputable def leaf6954Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi337InputQChi innerPair755Input
    leaf6954InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6954LowerChecked :
    lowerCheck 24 leaf6954Box leaf6954Inputs = true := by
  rfl'

private theorem leaf6954CoversExact : CoversExact 8
    leaf6954Box leaf6954Certificate leaf6954InnerLog leaf6954Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi337RoundedFacts
    innerPair755RoundedFacts leaf6954RoundedFacts (by rfl)

private theorem leaf6954FlatSound : Sound leaf6954Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6954CertificateValid
    leaf6954InnerLogValid leaf6954CoversExact leaf6954LowerChecked

private noncomputable def leaf6955Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (37/64), chiHi := (75/128) }

private noncomputable def leaf6955Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435857/268435456) }, vSqrt := { lower := (8191/8192), upper := (17178836991/17177449984) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (874573289/536870912) }, upper := { exponent := 1, mantissa := (6773/4096) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi337LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34356286975/34354899968) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf6955InnerLog : WideLogData :=
  innerPair760Data

set_option maxRecDepth 1000000 in
private theorem leaf6955LocalValidity :
    LeafFacts leaf6955Box leaf6955Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6955Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178836991/17177449984) }) = true
      norm_num [leaf6955Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6955CertificateValid :
    WideCertificateValid leaf6955Box leaf6955Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi337ValidityFacts
    leaf6955LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6955CoverageChecked :
    coverageCheck (innerAD leaf6955Box) leaf6955InnerLog = true := by
  rfl'

private theorem leaf6955InnerLogValid :
    leaf6955InnerLog.Valid 8 (innerAD leaf6955Box) :=
  wideLogDataValid_of_cachedCheck endpoint485PositiveFacts
    endpoint486PositiveFacts.valid leaf6955CoverageChecked

private noncomputable def leaf6955InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814879/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6955InputLogOnePlusV_eq :
    leaf6955InputLogOnePlusV = outerEnclosure 24
      (leaf6955Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6955RoundedFacts : LeafRoundedFacts 8
    leaf6955Certificate.logOnePlusV leaf6955InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6955InputLogOnePlusV_eq }

private noncomputable def leaf6955Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi337InputQChi innerPair760Input
    leaf6955InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6955LowerChecked :
    lowerCheck 24 leaf6955Box leaf6955Inputs = true := by
  rfl'

private theorem leaf6955CoversExact : CoversExact 8
    leaf6955Box leaf6955Certificate leaf6955InnerLog leaf6955Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi337RoundedFacts
    innerPair760RoundedFacts leaf6955RoundedFacts (by rfl)

private theorem leaf6955FlatSound : Sound leaf6955Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6955CertificateValid
    leaf6955InnerLogValid leaf6955CoversExact leaf6955LowerChecked

private noncomputable def leaf6956Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (75/128), chiHi := (19/32) }

private noncomputable def leaf6956Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218005/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588708864) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (438908485/268435456) }, upper := { exponent := 1, mantissa := (1709/1024) } }, logOuter := sk159LogOuterCertificate, logK := sk159LogKCertificate, logChi := chi338LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178135551/17177417728) } }, logDArg := sk159LogDArgCertificate }

private noncomputable def leaf6956InnerLog : WideLogData :=
  innerPair839Data

set_option maxRecDepth 1000000 in
private theorem leaf6956LocalValidity :
    LeafFacts leaf6956Box leaf6956Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6956Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588708864) }) = true
      norm_num [leaf6956Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6956CertificateValid :
    WideCertificateValid leaf6956Box leaf6956Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk159ValidityFacts chi338ValidityFacts
    leaf6956LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6956CoverageChecked :
    coverageCheck (innerAD leaf6956Box) leaf6956InnerLog = true := by
  rfl'

private theorem leaf6956InnerLogValid :
    leaf6956InnerLog.Valid 8 (innerAD leaf6956Box) :=
  wideLogDataValid_of_cachedCheck endpoint533PositiveFacts
    endpoint558PositiveFacts.valid leaf6956CoverageChecked

private noncomputable def leaf6956InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814891/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6956InputLogOnePlusV_eq :
    leaf6956InputLogOnePlusV = outerEnclosure 24
      (leaf6956Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6956RoundedFacts : LeafRoundedFacts 8
    leaf6956Certificate.logOnePlusV leaf6956InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6956InputLogOnePlusV_eq }

private noncomputable def leaf6956Inputs : Inputs :=
  inputsOfCaches globalInput sk159RoundedInputs
    chi338InputQChi innerPair839Input
    leaf6956InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6956LowerChecked :
    lowerCheck 24 leaf6956Box leaf6956Inputs = true := by
  rfl'

private theorem leaf6956CoversExact : CoversExact 8
    leaf6956Box leaf6956Certificate leaf6956InnerLog leaf6956Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk159RoundedFacts chi338RoundedFacts
    innerPair839RoundedFacts leaf6956RoundedFacts (by rfl)

private theorem leaf6956FlatSound : Sound leaf6956Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6956CertificateValid
    leaf6956InnerLogValid leaf6956CoversExact leaf6956LowerChecked

private noncomputable def leaf6957Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (37/64), chiHi := (75/128) }

private noncomputable def leaf6957Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435859/268435456) }, vSqrt := { lower := (8191/8192), upper := (17178836991/17177430784) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (879422655/536870912) }, upper := { exponent := 1, mantissa := (13621/8192) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi337LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34356267775/34354861568) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf6957InnerLog : WideLogData :=
  innerPair761Data

set_option maxRecDepth 1000000 in
private theorem leaf6957LocalValidity :
    LeafFacts leaf6957Box leaf6957Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6957Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178836991/17177430784) }) = true
      norm_num [leaf6957Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6957CertificateValid :
    WideCertificateValid leaf6957Box leaf6957Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi337ValidityFacts
    leaf6957LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6957CoverageChecked :
    coverageCheck (innerAD leaf6957Box) leaf6957InnerLog = true := by
  rfl'

private theorem leaf6957InnerLogValid :
    leaf6957InnerLog.Valid 8 (innerAD leaf6957Box) :=
  wideLogDataValid_of_cachedCheck endpoint485PositiveFacts
    endpoint487PositiveFacts.valid leaf6957CoverageChecked

private noncomputable def leaf6957InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629767/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6957InputLogOnePlusV_eq :
    leaf6957InputLogOnePlusV = outerEnclosure 24
      (leaf6957Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6957RoundedFacts : LeafRoundedFacts 8
    leaf6957Certificate.logOnePlusV leaf6957InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6957InputLogOnePlusV_eq }

private noncomputable def leaf6957Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi337InputQChi innerPair761Input
    leaf6957InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6957LowerChecked :
    lowerCheck 24 leaf6957Box leaf6957Inputs = true := by
  rfl'

private theorem leaf6957CoversExact : CoversExact 8
    leaf6957Box leaf6957Certificate leaf6957InnerLog leaf6957Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi337RoundedFacts
    innerPair761RoundedFacts leaf6957RoundedFacts (by rfl)

private theorem leaf6957FlatSound : Sound leaf6957Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6957CertificateValid
    leaf6957InnerLogValid leaf6957CoversExact leaf6957LowerChecked

private noncomputable def leaf6958Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (37/64), chiHi := (75/128) }

private noncomputable def leaf6958Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435861/268435456) }, vSqrt := { lower := (65527/65536), upper := (399507837/399474688) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (884272021/536870912) }, upper := { exponent := 1, mantissa := (107/64) } }, logOuter := sk176LogOuterCertificate, logK := sk176LogKCertificate, logChi := chi337LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (798982525/798949376) } }, logDArg := sk176LogDArgCertificate }

private noncomputable def leaf6958InnerLog : WideLogData :=
  innerPair761Data

set_option maxRecDepth 1000000 in
private theorem leaf6958LocalValidity :
    LeafFacts leaf6958Box leaf6958Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6958Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (399507837/399474688) }) = true
      norm_num [leaf6958Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6958CertificateValid :
    WideCertificateValid leaf6958Box leaf6958Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk176ValidityFacts chi337ValidityFacts
    leaf6958LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6958CoverageChecked :
    coverageCheck (innerAD leaf6958Box) leaf6958InnerLog = true := by
  rfl'

private theorem leaf6958InnerLogValid :
    leaf6958InnerLog.Valid 8 (innerAD leaf6958Box) :=
  wideLogDataValid_of_cachedCheck endpoint485PositiveFacts
    endpoint487PositiveFacts.valid leaf6958CoverageChecked

private noncomputable def leaf6958InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629777/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6958InputLogOnePlusV_eq :
    leaf6958InputLogOnePlusV = outerEnclosure 24
      (leaf6958Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6958RoundedFacts : LeafRoundedFacts 8
    leaf6958Certificate.logOnePlusV leaf6958InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6958InputLogOnePlusV_eq }

private noncomputable def leaf6958Inputs : Inputs :=
  inputsOfCaches globalInput sk176RoundedInputs
    chi337InputQChi innerPair761Input
    leaf6958InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6958LowerChecked :
    lowerCheck 24 leaf6958Box leaf6958Inputs = true := by
  rfl'

private theorem leaf6958CoversExact : CoversExact 8
    leaf6958Box leaf6958Certificate leaf6958InnerLog leaf6958Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk176RoundedFacts chi337RoundedFacts
    innerPair761RoundedFacts leaf6958RoundedFacts (by rfl)

private theorem leaf6958FlatSound : Sound leaf6958Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6958CertificateValid
    leaf6958InnerLogValid leaf6958CoversExact leaf6958LowerChecked

private noncomputable def leaf6959Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (75/128), chiHi := (19/32) }

private noncomputable def leaf6959Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218007/134217728) }, vSqrt := { lower := (65527/65536), upper := (8589426687/8588689408) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (443823383/268435456) }, upper := { exponent := 1, mantissa := (27/16) } }, logOuter := sk160LogOuterCertificate, logK := sk160LogKCertificate, logChi := chi338LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (17178116095/17177378816) } }, logDArg := sk160LogDArgCertificate }

private noncomputable def leaf6959InnerLog : WideLogData :=
  innerPair761Data

set_option maxRecDepth 1000000 in
private theorem leaf6959LocalValidity :
    LeafFacts leaf6959Box leaf6959Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6959Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (8589426687/8588689408) }) = true
      norm_num [leaf6959Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6959CertificateValid :
    WideCertificateValid leaf6959Box leaf6959Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk160ValidityFacts chi338ValidityFacts
    leaf6959LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6959CoverageChecked :
    coverageCheck (innerAD leaf6959Box) leaf6959InnerLog = true := by
  rfl'

private theorem leaf6959InnerLogValid :
    leaf6959InnerLog.Valid 8 (innerAD leaf6959Box) :=
  wideLogDataValid_of_cachedCheck endpoint485PositiveFacts
    endpoint487PositiveFacts.valid leaf6959CoverageChecked

private noncomputable def leaf6959InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629801/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6959InputLogOnePlusV_eq :
    leaf6959InputLogOnePlusV = outerEnclosure 24
      (leaf6959Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6959RoundedFacts : LeafRoundedFacts 8
    leaf6959Certificate.logOnePlusV leaf6959InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6959InputLogOnePlusV_eq }

private noncomputable def leaf6959Inputs : Inputs :=
  inputsOfCaches globalInput sk160RoundedInputs
    chi338InputQChi innerPair761Input
    leaf6959InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6959LowerChecked :
    lowerCheck 24 leaf6959Box leaf6959Inputs = true := by
  rfl'

private theorem leaf6959CoversExact : CoversExact 8
    leaf6959Box leaf6959Certificate leaf6959InnerLog leaf6959Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk160RoundedFacts chi338RoundedFacts
    innerPair761RoundedFacts leaf6959RoundedFacts (by rfl)

private theorem leaf6959FlatSound : Sound leaf6959Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6959CertificateValid
    leaf6959InnerLogValid leaf6959CoversExact leaf6959LowerChecked

private noncomputable def leaf6960Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (19/32), chiHi := (77/128) }

private noncomputable def leaf6960Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218003/134217728) }, vSqrt := { lower := (8191/8192), upper := (2863142229/2862910720) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (433010607/268435456) }, upper := { exponent := 1, mantissa := (6745/4096) } }, logOuter := sk157LogOuterCertificate, logK := sk157LogKCertificate, logChi := chi339LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (5726052949/5725821440) } }, logDArg := sk157LogDArgCertificate }

private noncomputable def leaf6960InnerLog : WideLogData :=
  innerPair755Data

set_option maxRecDepth 1000000 in
private theorem leaf6960LocalValidity :
    LeafFacts leaf6960Box leaf6960Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6960Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (2863142229/2862910720) }) = true
      norm_num [leaf6960Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6960CertificateValid :
    WideCertificateValid leaf6960Box leaf6960Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk157ValidityFacts chi339ValidityFacts
    leaf6960LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6960CoverageChecked :
    coverageCheck (innerAD leaf6960Box) leaf6960InnerLog = true := by
  rfl'

private theorem leaf6960InnerLogValid :
    leaf6960InnerLog.Valid 8 (innerAD leaf6960Box) :=
  wideLogDataValid_of_cachedCheck endpoint484PositiveFacts
    endpoint486PositiveFacts.valid leaf6960CoverageChecked

private noncomputable def leaf6960InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629759/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6960InputLogOnePlusV_eq :
    leaf6960InputLogOnePlusV = outerEnclosure 24
      (leaf6960Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6960RoundedFacts : LeafRoundedFacts 8
    leaf6960Certificate.logOnePlusV leaf6960InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6960InputLogOnePlusV_eq }

private noncomputable def leaf6960Inputs : Inputs :=
  inputsOfCaches globalInput sk157RoundedInputs
    chi339InputQChi innerPair755Input
    leaf6960InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6960LowerChecked :
    lowerCheck 24 leaf6960Box leaf6960Inputs = true := by
  rfl'

private theorem leaf6960CoversExact : CoversExact 8
    leaf6960Box leaf6960Certificate leaf6960InnerLog leaf6960Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk157RoundedFacts chi339RoundedFacts
    innerPair755RoundedFacts leaf6960RoundedFacts (by rfl)

private theorem leaf6960FlatSound : Sound leaf6960Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6960CertificateValid
    leaf6960InnerLogValid leaf6960CoversExact leaf6960LowerChecked

private noncomputable def leaf6961Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (77/128), chiHi := (39/64) }

private noncomputable def leaf6961Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218005/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588716544) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (436942525/268435456) }, upper := { exponent := 1, mantissa := (3403/2048) } }, logOuter := sk157LogOuterCertificate, logK := sk157LogKCertificate, logChi := chi340LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178143231/17177433088) } }, logDArg := sk157LogDArgCertificate }

private noncomputable def leaf6961InnerLog : WideLogData :=
  innerPair764Data

set_option maxRecDepth 1000000 in
private theorem leaf6961LocalValidity :
    LeafFacts leaf6961Box leaf6961Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6961Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588716544) }) = true
      norm_num [leaf6961Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6961CertificateValid :
    WideCertificateValid leaf6961Box leaf6961Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk157ValidityFacts chi340ValidityFacts
    leaf6961LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6961CoverageChecked :
    coverageCheck (innerAD leaf6961Box) leaf6961InnerLog = true := by
  rfl'

private theorem leaf6961InnerLogValid :
    leaf6961InnerLog.Valid 8 (innerAD leaf6961Box) :=
  wideLogDataValid_of_cachedCheck endpoint485PositiveFacts
    endpoint536PositiveFacts.valid leaf6961CoverageChecked

private noncomputable def leaf6961InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814887/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6961InputLogOnePlusV_eq :
    leaf6961InputLogOnePlusV = outerEnclosure 24
      (leaf6961Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6961RoundedFacts : LeafRoundedFacts 8
    leaf6961Certificate.logOnePlusV leaf6961InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6961InputLogOnePlusV_eq }

private noncomputable def leaf6961Inputs : Inputs :=
  inputsOfCaches globalInput sk157RoundedInputs
    chi340InputQChi innerPair764Input
    leaf6961InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6961LowerChecked :
    lowerCheck 24 leaf6961Box leaf6961Inputs = true := by
  rfl'

private theorem leaf6961CoversExact : CoversExact 8
    leaf6961Box leaf6961Certificate leaf6961InnerLog leaf6961Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk157RoundedFacts chi340RoundedFacts
    innerPair764RoundedFacts leaf6961RoundedFacts (by rfl)

private theorem leaf6961FlatSound : Sound leaf6961Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6961CertificateValid
    leaf6961InnerLogValid leaf6961CoversExact leaf6961LowerChecked

private noncomputable def leaf6962Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (19/32), chiHi := (77/128) }

private noncomputable def leaf6962Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218005/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588712448) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (437991037/268435456) }, upper := { exponent := 1, mantissa := (3411/2048) } }, logOuter := sk158LogOuterCertificate, logK := sk158LogKCertificate, logChi := chi339LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178139135/17177424896) } }, logDArg := sk158LogDArgCertificate }

private noncomputable def leaf6962InnerLog : WideLogData :=
  innerPair763Data

set_option maxRecDepth 1000000 in
private theorem leaf6962LocalValidity :
    LeafFacts leaf6962Box leaf6962Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6962Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588712448) }) = true
      norm_num [leaf6962Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6962CertificateValid :
    WideCertificateValid leaf6962Box leaf6962Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk158ValidityFacts chi339ValidityFacts
    leaf6962LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6962CoverageChecked :
    coverageCheck (innerAD leaf6962Box) leaf6962InnerLog = true := by
  rfl'

private theorem leaf6962InnerLogValid :
    leaf6962InnerLog.Valid 8 (innerAD leaf6962Box) :=
  wideLogDataValid_of_cachedCheck endpoint485PositiveFacts
    endpoint495PositiveFacts.valid leaf6962CoverageChecked

private noncomputable def leaf6962InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814889/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6962InputLogOnePlusV_eq :
    leaf6962InputLogOnePlusV = outerEnclosure 24
      (leaf6962Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6962RoundedFacts : LeafRoundedFacts 8
    leaf6962Certificate.logOnePlusV leaf6962InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6962InputLogOnePlusV_eq }

private noncomputable def leaf6962Inputs : Inputs :=
  inputsOfCaches globalInput sk158RoundedInputs
    chi339InputQChi innerPair763Input
    leaf6962InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6962LowerChecked :
    lowerCheck 24 leaf6962Box leaf6962Inputs = true := by
  rfl'

private theorem leaf6962CoversExact : CoversExact 8
    leaf6962Box leaf6962Certificate leaf6962InnerLog leaf6962Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk158RoundedFacts chi339RoundedFacts
    innerPair763RoundedFacts leaf6962RoundedFacts (by rfl)

private theorem leaf6962FlatSound : Sound leaf6962Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6962CertificateValid
    leaf6962InnerLogValid leaf6962CoversExact leaf6962LowerChecked

private noncomputable def leaf6963Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (77/128), chiHi := (39/64) }

private noncomputable def leaf6963Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218007/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588696576) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (441988487/268435456) }, upper := { exponent := 1, mantissa := (1721/1024) } }, logOuter := sk158LogOuterCertificate, logK := sk158LogKCertificate, logChi := chi340LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178123263/17177393152) } }, logDArg := sk158LogDArgCertificate }

private noncomputable def leaf6963InnerLog : WideLogData :=
  innerPair761Data

set_option maxRecDepth 1000000 in
private theorem leaf6963LocalValidity :
    LeafFacts leaf6963Box leaf6963Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6963Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588696576) }) = true
      norm_num [leaf6963Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6963CertificateValid :
    WideCertificateValid leaf6963Box leaf6963Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk158ValidityFacts chi340ValidityFacts
    leaf6963LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6963CoverageChecked :
    coverageCheck (innerAD leaf6963Box) leaf6963InnerLog = true := by
  rfl'

private theorem leaf6963InnerLogValid :
    leaf6963InnerLog.Valid 8 (innerAD leaf6963Box) :=
  wideLogDataValid_of_cachedCheck endpoint485PositiveFacts
    endpoint487PositiveFacts.valid leaf6963CoverageChecked

private noncomputable def leaf6963InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814897/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6963InputLogOnePlusV_eq :
    leaf6963InputLogOnePlusV = outerEnclosure 24
      (leaf6963Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6963RoundedFacts : LeafRoundedFacts 8
    leaf6963Certificate.logOnePlusV leaf6963InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6963InputLogOnePlusV_eq }

private noncomputable def leaf6963Inputs : Inputs :=
  inputsOfCaches globalInput sk158RoundedInputs
    chi340InputQChi innerPair761Input
    leaf6963InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6963LowerChecked :
    lowerCheck 24 leaf6963Box leaf6963Inputs = true := by
  rfl'

private theorem leaf6963CoversExact : CoversExact 8
    leaf6963Box leaf6963Certificate leaf6963InnerLog leaf6963Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk158RoundedFacts chi340RoundedFacts
    innerPair761RoundedFacts leaf6963RoundedFacts (by rfl)

private theorem leaf6963FlatSound : Sound leaf6963Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6963CertificateValid
    leaf6963InnerLogValid leaf6963CoversExact leaf6963LowerChecked

private noncomputable def leaf6964Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (39/64), chiHi := (79/128) }

private noncomputable def leaf6964Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218007/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588700928) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (440874443/268435456) }, upper := { exponent := 1, mantissa := (6867/4096) } }, logOuter := sk157LogOuterCertificate, logK := sk157LogKCertificate, logChi := chi347LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178127615/17177401856) } }, logDArg := sk157LogDArgCertificate }

private noncomputable def leaf6964InnerLog : WideLogData :=
  innerPair761Data

set_option maxRecDepth 1000000 in
private theorem leaf6964LocalValidity :
    LeafFacts leaf6964Box leaf6964Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6964Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588700928) }) = true
      norm_num [leaf6964Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6964CertificateValid :
    WideCertificateValid leaf6964Box leaf6964Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk157ValidityFacts chi347ValidityFacts
    leaf6964LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6964CoverageChecked :
    coverageCheck (innerAD leaf6964Box) leaf6964InnerLog = true := by
  rfl'

private theorem leaf6964InnerLogValid :
    leaf6964InnerLog.Valid 8 (innerAD leaf6964Box) :=
  wideLogDataValid_of_cachedCheck endpoint485PositiveFacts
    endpoint487PositiveFacts.valid leaf6964CoverageChecked

private noncomputable def leaf6964InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814895/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6964InputLogOnePlusV_eq :
    leaf6964InputLogOnePlusV = outerEnclosure 24
      (leaf6964Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6964RoundedFacts : LeafRoundedFacts 8
    leaf6964Certificate.logOnePlusV leaf6964InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6964InputLogOnePlusV_eq }

private noncomputable def leaf6964Inputs : Inputs :=
  inputsOfCaches globalInput sk157RoundedInputs
    chi347InputQChi innerPair761Input
    leaf6964InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6964LowerChecked :
    lowerCheck 24 leaf6964Box leaf6964Inputs = true := by
  rfl'

private theorem leaf6964CoversExact : CoversExact 8
    leaf6964Box leaf6964Certificate leaf6964InnerLog leaf6964Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk157RoundedFacts chi347RoundedFacts
    innerPair761RoundedFacts leaf6964RoundedFacts (by rfl)

private theorem leaf6964FlatSound : Sound leaf6964Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6964CertificateValid
    leaf6964InnerLogValid leaf6964CoversExact leaf6964LowerChecked

private noncomputable def leaf6965Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (79/128), chiHi := (5/8) }

private noncomputable def leaf6965Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218009/134217728) }, vSqrt := { lower := (8191/8192), upper := (954380743/954298368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (444806361/268435456) }, upper := { exponent := 1, mantissa := (433/256) } }, logOuter := sk157LogOuterCertificate, logK := sk157LogKCertificate, logChi := chi348LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (1908679111/1908596736) } }, logDArg := sk157LogDArgCertificate }

private noncomputable def leaf6965InnerLog : WideLogData :=
  innerPair767Data

set_option maxRecDepth 1000000 in
private theorem leaf6965LocalValidity :
    LeafFacts leaf6965Box leaf6965Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6965Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (954380743/954298368) }) = true
      norm_num [leaf6965Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6965CertificateValid :
    WideCertificateValid leaf6965Box leaf6965Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk157ValidityFacts chi348ValidityFacts
    leaf6965LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6965CoverageChecked :
    coverageCheck (innerAD leaf6965Box) leaf6965InnerLog = true := by
  rfl'

private theorem leaf6965InnerLogValid :
    leaf6965InnerLog.Valid 8 (innerAD leaf6965Box) :=
  wideLogDataValid_of_cachedCheck endpoint486PositiveFacts
    endpoint497PositiveFacts.valid leaf6965CoverageChecked

private noncomputable def leaf6965InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629805/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6965InputLogOnePlusV_eq :
    leaf6965InputLogOnePlusV = outerEnclosure 24
      (leaf6965Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6965RoundedFacts : LeafRoundedFacts 8
    leaf6965Certificate.logOnePlusV leaf6965InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6965InputLogOnePlusV_eq }

private noncomputable def leaf6965Inputs : Inputs :=
  inputsOfCaches globalInput sk157RoundedInputs
    chi348InputQChi innerPair767Input
    leaf6965InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6965LowerChecked :
    lowerCheck 24 leaf6965Box leaf6965Inputs = true := by
  rfl'

private theorem leaf6965CoversExact : CoversExact 8
    leaf6965Box leaf6965Certificate leaf6965InnerLog leaf6965Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk157RoundedFacts chi348RoundedFacts
    innerPair767RoundedFacts leaf6965RoundedFacts (by rfl)

private theorem leaf6965FlatSound : Sound leaf6965Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6965CertificateValid
    leaf6965InnerLogValid leaf6965CoversExact leaf6965LowerChecked

private noncomputable def leaf6966Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (39/64), chiHi := (79/128) }

private noncomputable def leaf6966Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218009/134217728) }, vSqrt := { lower := (8191/8192), upper := (954380743/954297856) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (445985937/268435456) }, upper := { exponent := 1, mantissa := (3473/2048) } }, logOuter := sk158LogOuterCertificate, logK := sk158LogKCertificate, logChi := chi347LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (1908678599/1908595712) } }, logDArg := sk158LogDArgCertificate }

private noncomputable def leaf6966InnerLog : WideLogData :=
  innerPair769Data

set_option maxRecDepth 1000000 in
private theorem leaf6966LocalValidity :
    LeafFacts leaf6966Box leaf6966Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6966Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (954380743/954297856) }) = true
      norm_num [leaf6966Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6966CertificateValid :
    WideCertificateValid leaf6966Box leaf6966Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk158ValidityFacts chi347ValidityFacts
    leaf6966LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6966CoverageChecked :
    coverageCheck (innerAD leaf6966Box) leaf6966InnerLog = true := by
  rfl'

private theorem leaf6966InnerLogValid :
    leaf6966InnerLog.Valid 8 (innerAD leaf6966Box) :=
  wideLogDataValid_of_cachedCheck endpoint486PositiveFacts
    endpoint540PositiveFacts.valid leaf6966CoverageChecked

private noncomputable def leaf6966InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629809/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6966InputLogOnePlusV_eq :
    leaf6966InputLogOnePlusV = outerEnclosure 24
      (leaf6966Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6966RoundedFacts : LeafRoundedFacts 8
    leaf6966Certificate.logOnePlusV leaf6966InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6966InputLogOnePlusV_eq }

private noncomputable def leaf6966Inputs : Inputs :=
  inputsOfCaches globalInput sk158RoundedInputs
    chi347InputQChi innerPair769Input
    leaf6966InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6966LowerChecked :
    lowerCheck 24 leaf6966Box leaf6966Inputs = true := by
  rfl'

private theorem leaf6966CoversExact : CoversExact 8
    leaf6966Box leaf6966Certificate leaf6966InnerLog leaf6966Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk158RoundedFacts chi347RoundedFacts
    innerPair769RoundedFacts leaf6966RoundedFacts (by rfl)

private theorem leaf6966FlatSound : Sound leaf6966Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6966CertificateValid
    leaf6966InnerLogValid leaf6966CoversExact leaf6966LowerChecked

private noncomputable def leaf6967Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (79/128), chiHi := (5/8) }

private noncomputable def leaf6967Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218011/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588664832) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (449983387/268435456) }, upper := { exponent := 1, mantissa := (219/128) } }, logOuter := sk158LogOuterCertificate, logK := sk158LogKCertificate, logChi := chi348LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178091519/17177329664) } }, logDArg := sk158LogDArgCertificate }

private noncomputable def leaf6967InnerLog : WideLogData :=
  innerPair765Data

set_option maxRecDepth 1000000 in
private theorem leaf6967LocalValidity :
    LeafFacts leaf6967Box leaf6967Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6967Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588664832) }) = true
      norm_num [leaf6967Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6967CertificateValid :
    WideCertificateValid leaf6967Box leaf6967Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk158ValidityFacts chi348ValidityFacts
    leaf6967LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6967CoverageChecked :
    coverageCheck (innerAD leaf6967Box) leaf6967InnerLog = true := by
  rfl'

private theorem leaf6967InnerLogValid :
    leaf6967InnerLog.Valid 8 (innerAD leaf6967Box) :=
  wideLogDataValid_of_cachedCheck endpoint486PositiveFacts
    endpoint488PositiveFacts.valid leaf6967CoverageChecked

private noncomputable def leaf6967InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629825/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6967InputLogOnePlusV_eq :
    leaf6967InputLogOnePlusV = outerEnclosure 24
      (leaf6967Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6967RoundedFacts : LeafRoundedFacts 8
    leaf6967Certificate.logOnePlusV leaf6967InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6967InputLogOnePlusV_eq }

private noncomputable def leaf6967Inputs : Inputs :=
  inputsOfCaches globalInput sk158RoundedInputs
    chi348InputQChi innerPair765Input
    leaf6967InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6967LowerChecked :
    lowerCheck 24 leaf6967Box leaf6967Inputs = true := by
  rfl'

private theorem leaf6967CoversExact : CoversExact 8
    leaf6967Box leaf6967Certificate leaf6967InnerLog leaf6967Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk158RoundedFacts chi348RoundedFacts
    innerPair765RoundedFacts leaf6967RoundedFacts (by rfl)

private theorem leaf6967FlatSound : Sound leaf6967Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6967CertificateValid
    leaf6967InnerLogValid leaf6967CoversExact leaf6967LowerChecked

private noncomputable def leaf6968Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (19/32), chiHi := (77/128) }

private noncomputable def leaf6968Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218007/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588692736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (442971467/268435456) }, upper := { exponent := 1, mantissa := (6899/4096) } }, logOuter := sk159LogOuterCertificate, logK := sk159LogKCertificate, logChi := chi339LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178119423/17177385472) } }, logDArg := sk159LogDArgCertificate }

private noncomputable def leaf6968InnerLog : WideLogData :=
  innerPair761Data

set_option maxRecDepth 1000000 in
private theorem leaf6968LocalValidity :
    LeafFacts leaf6968Box leaf6968Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6968Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588692736) }) = true
      norm_num [leaf6968Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6968CertificateValid :
    WideCertificateValid leaf6968Box leaf6968Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk159ValidityFacts chi339ValidityFacts
    leaf6968LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6968CoverageChecked :
    coverageCheck (innerAD leaf6968Box) leaf6968InnerLog = true := by
  rfl'

private theorem leaf6968InnerLogValid :
    leaf6968InnerLog.Valid 8 (innerAD leaf6968Box) :=
  wideLogDataValid_of_cachedCheck endpoint485PositiveFacts
    endpoint487PositiveFacts.valid leaf6968CoverageChecked

private noncomputable def leaf6968InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814899/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6968InputLogOnePlusV_eq :
    leaf6968InputLogOnePlusV = outerEnclosure 24
      (leaf6968Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6968RoundedFacts : LeafRoundedFacts 8
    leaf6968Certificate.logOnePlusV leaf6968InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6968InputLogOnePlusV_eq }

private noncomputable def leaf6968Inputs : Inputs :=
  inputsOfCaches globalInput sk159RoundedInputs
    chi339InputQChi innerPair761Input
    leaf6968InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6968LowerChecked :
    lowerCheck 24 leaf6968Box leaf6968Inputs = true := by
  rfl'

private theorem leaf6968CoversExact : CoversExact 8
    leaf6968Box leaf6968Certificate leaf6968InnerLog leaf6968Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk159RoundedFacts chi339RoundedFacts
    innerPair761RoundedFacts leaf6968RoundedFacts (by rfl)

private theorem leaf6968FlatSound : Sound leaf6968Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6968CertificateValid
    leaf6968InnerLogValid leaf6968CoversExact leaf6968LowerChecked

private noncomputable def leaf6969Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (77/128), chiHi := (39/64) }

private noncomputable def leaf6969Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218009/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588676608) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (447034449/268435456) }, upper := { exponent := 1, mantissa := (3481/2048) } }, logOuter := sk159LogOuterCertificate, logK := sk159LogKCertificate, logChi := chi340LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178103295/17177353216) } }, logDArg := sk159LogDArgCertificate }

private noncomputable def leaf6969InnerLog : WideLogData :=
  innerPair842Data

set_option maxRecDepth 1000000 in
private theorem leaf6969LocalValidity :
    LeafFacts leaf6969Box leaf6969Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6969Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588676608) }) = true
      norm_num [leaf6969Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6969CertificateValid :
    WideCertificateValid leaf6969Box leaf6969Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk159ValidityFacts chi340ValidityFacts
    leaf6969LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6969CoverageChecked :
    coverageCheck (innerAD leaf6969Box) leaf6969InnerLog = true := by
  rfl'

private theorem leaf6969InnerLogValid :
    leaf6969InnerLog.Valid 8 (innerAD leaf6969Box) :=
  wideLogDataValid_of_cachedCheck endpoint536PositiveFacts
    endpoint540PositiveFacts.valid leaf6969CoverageChecked

private noncomputable def leaf6969InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629813/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6969InputLogOnePlusV_eq :
    leaf6969InputLogOnePlusV = outerEnclosure 24
      (leaf6969Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6969RoundedFacts : LeafRoundedFacts 8
    leaf6969Certificate.logOnePlusV leaf6969InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6969InputLogOnePlusV_eq }

private noncomputable def leaf6969Inputs : Inputs :=
  inputsOfCaches globalInput sk159RoundedInputs
    chi340InputQChi innerPair842Input
    leaf6969InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6969LowerChecked :
    lowerCheck 24 leaf6969Box leaf6969Inputs = true := by
  rfl'

private theorem leaf6969CoversExact : CoversExact 8
    leaf6969Box leaf6969Certificate leaf6969InnerLog leaf6969Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk159RoundedFacts chi340RoundedFacts
    innerPair842RoundedFacts leaf6969RoundedFacts (by rfl)

private theorem leaf6969FlatSound : Sound leaf6969Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6969CertificateValid
    leaf6969InnerLogValid leaf6969CoversExact leaf6969LowerChecked

private noncomputable def leaf6970Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (19/32), chiHi := (77/128) }

private noncomputable def leaf6970Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218009/134217728) }, vSqrt := { lower := (65527/65536), upper := (2863142229/2862891008) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (447951897/268435456) }, upper := { exponent := 1, mantissa := (109/64) } }, logOuter := sk160LogOuterCertificate, logK := sk160LogKCertificate, logChi := chi339LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (5726033237/5725782016) } }, logDArg := sk160LogDArgCertificate }

private noncomputable def leaf6970InnerLog : WideLogData :=
  innerPair842Data

set_option maxRecDepth 1000000 in
private theorem leaf6970LocalValidity :
    LeafFacts leaf6970Box leaf6970Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6970Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (2863142229/2862891008) }) = true
      norm_num [leaf6970Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6970CertificateValid :
    WideCertificateValid leaf6970Box leaf6970Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk160ValidityFacts chi339ValidityFacts
    leaf6970LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6970CoverageChecked :
    coverageCheck (innerAD leaf6970Box) leaf6970InnerLog = true := by
  rfl'

private theorem leaf6970InnerLogValid :
    leaf6970InnerLog.Valid 8 (innerAD leaf6970Box) :=
  wideLogDataValid_of_cachedCheck endpoint536PositiveFacts
    endpoint540PositiveFacts.valid leaf6970CoverageChecked

private noncomputable def leaf6970InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629817/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6970InputLogOnePlusV_eq :
    leaf6970InputLogOnePlusV = outerEnclosure 24
      (leaf6970Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6970RoundedFacts : LeafRoundedFacts 8
    leaf6970Certificate.logOnePlusV leaf6970InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6970InputLogOnePlusV_eq }

private noncomputable def leaf6970Inputs : Inputs :=
  inputsOfCaches globalInput sk160RoundedInputs
    chi339InputQChi innerPair842Input
    leaf6970InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6970LowerChecked :
    lowerCheck 24 leaf6970Box leaf6970Inputs = true := by
  rfl'

private theorem leaf6970CoversExact : CoversExact 8
    leaf6970Box leaf6970Certificate leaf6970InnerLog leaf6970Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk160RoundedFacts chi339RoundedFacts
    innerPair842RoundedFacts leaf6970RoundedFacts (by rfl)

private theorem leaf6970FlatSound : Sound leaf6970Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6970CertificateValid
    leaf6970InnerLogValid leaf6970CoversExact leaf6970LowerChecked

private noncomputable def leaf6971Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (77/128), chiHi := (39/64) }

private noncomputable def leaf6971Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218011/134217728) }, vSqrt := { lower := (65527/65536), upper := (8589426687/8588656640) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (452080411/268435456) }, upper := { exponent := 1, mantissa := (55/32) } }, logOuter := sk160LogOuterCertificate, logK := sk160LogKCertificate, logChi := chi340LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (17178083327/17177313280) } }, logDArg := sk160LogDArgCertificate }

private noncomputable def leaf6971InnerLog : WideLogData :=
  innerPair765Data

set_option maxRecDepth 1000000 in
private theorem leaf6971LocalValidity :
    LeafFacts leaf6971Box leaf6971Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6971Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (8589426687/8588656640) }) = true
      norm_num [leaf6971Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6971CertificateValid :
    WideCertificateValid leaf6971Box leaf6971Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk160ValidityFacts chi340ValidityFacts
    leaf6971LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6971CoverageChecked :
    coverageCheck (innerAD leaf6971Box) leaf6971InnerLog = true := by
  rfl'

private theorem leaf6971InnerLogValid :
    leaf6971InnerLog.Valid 8 (innerAD leaf6971Box) :=
  wideLogDataValid_of_cachedCheck endpoint486PositiveFacts
    endpoint488PositiveFacts.valid leaf6971CoverageChecked

private noncomputable def leaf6971InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629833/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6971InputLogOnePlusV_eq :
    leaf6971InputLogOnePlusV = outerEnclosure 24
      (leaf6971Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6971RoundedFacts : LeafRoundedFacts 8
    leaf6971Certificate.logOnePlusV leaf6971InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6971InputLogOnePlusV_eq }

private noncomputable def leaf6971Inputs : Inputs :=
  inputsOfCaches globalInput sk160RoundedInputs
    chi340InputQChi innerPair765Input
    leaf6971InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6971LowerChecked :
    lowerCheck 24 leaf6971Box leaf6971Inputs = true := by
  rfl'

private theorem leaf6971CoversExact : CoversExact 8
    leaf6971Box leaf6971Certificate leaf6971InnerLog leaf6971Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk160RoundedFacts chi340RoundedFacts
    innerPair765RoundedFacts leaf6971RoundedFacts (by rfl)

private theorem leaf6971FlatSound : Sound leaf6971Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6971CertificateValid
    leaf6971InnerLogValid leaf6971CoversExact leaf6971LowerChecked

private noncomputable def leaf6972Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (39/64), chiHi := (79/128) }

private noncomputable def leaf6972Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218011/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588660480) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (451097431/268435456) }, upper := { exponent := 1, mantissa := (7025/4096) } }, logOuter := sk159LogOuterCertificate, logK := sk159LogKCertificate, logChi := chi347LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178087167/17177320960) } }, logDArg := sk159LogDArgCertificate }

private noncomputable def leaf6972InnerLog : WideLogData :=
  innerPair765Data

set_option maxRecDepth 1000000 in
private theorem leaf6972LocalValidity :
    LeafFacts leaf6972Box leaf6972Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6972Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588660480) }) = true
      norm_num [leaf6972Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6972CertificateValid :
    WideCertificateValid leaf6972Box leaf6972Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk159ValidityFacts chi347ValidityFacts
    leaf6972LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6972CoverageChecked :
    coverageCheck (innerAD leaf6972Box) leaf6972InnerLog = true := by
  rfl'

private theorem leaf6972InnerLogValid :
    leaf6972InnerLog.Valid 8 (innerAD leaf6972Box) :=
  wideLogDataValid_of_cachedCheck endpoint486PositiveFacts
    endpoint488PositiveFacts.valid leaf6972CoverageChecked

private noncomputable def leaf6972InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629829/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6972InputLogOnePlusV_eq :
    leaf6972InputLogOnePlusV = outerEnclosure 24
      (leaf6972Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6972RoundedFacts : LeafRoundedFacts 8
    leaf6972Certificate.logOnePlusV leaf6972InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6972InputLogOnePlusV_eq }

private noncomputable def leaf6972Inputs : Inputs :=
  inputsOfCaches globalInput sk159RoundedInputs
    chi347InputQChi innerPair765Input
    leaf6972InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6972LowerChecked :
    lowerCheck 24 leaf6972Box leaf6972Inputs = true := by
  rfl'

private theorem leaf6972CoversExact : CoversExact 8
    leaf6972Box leaf6972Certificate leaf6972InnerLog leaf6972Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk159RoundedFacts chi347RoundedFacts
    innerPair765RoundedFacts leaf6972RoundedFacts (by rfl)

private theorem leaf6972FlatSound : Sound leaf6972Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6972CertificateValid
    leaf6972InnerLogValid leaf6972CoversExact leaf6972LowerChecked

private noncomputable def leaf6973Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (79/128), chiHi := (5/8) }

private noncomputable def leaf6973Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218013/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588644352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (455160413/268435456) }, upper := { exponent := 1, mantissa := (443/256) } }, logOuter := sk159LogOuterCertificate, logK := sk159LogKCertificate, logChi := chi348LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178071039/17177288704) } }, logDArg := sk159LogDArgCertificate }

private noncomputable def leaf6973InnerLog : WideLogData :=
  innerPair791Data

set_option maxRecDepth 1000000 in
private theorem leaf6973LocalValidity :
    LeafFacts leaf6973Box leaf6973Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6973Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588644352) }) = true
      norm_num [leaf6973Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6973CertificateValid :
    WideCertificateValid leaf6973Box leaf6973Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk159ValidityFacts chi348ValidityFacts
    leaf6973LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6973CoverageChecked :
    coverageCheck (innerAD leaf6973Box) leaf6973InnerLog = true := by
  rfl'

private theorem leaf6973InnerLogValid :
    leaf6973InnerLog.Valid 8 (innerAD leaf6973Box) :=
  wideLogDataValid_of_cachedCheck endpoint497PositiveFacts
    endpoint542PositiveFacts.valid leaf6973CoverageChecked

private noncomputable def leaf6973InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629845/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6973InputLogOnePlusV_eq :
    leaf6973InputLogOnePlusV = outerEnclosure 24
      (leaf6973Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6973RoundedFacts : LeafRoundedFacts 8
    leaf6973Certificate.logOnePlusV leaf6973InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6973InputLogOnePlusV_eq }

private noncomputable def leaf6973Inputs : Inputs :=
  inputsOfCaches globalInput sk159RoundedInputs
    chi348InputQChi innerPair791Input
    leaf6973InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6973LowerChecked :
    lowerCheck 24 leaf6973Box leaf6973Inputs = true := by
  rfl'

private theorem leaf6973CoversExact : CoversExact 8
    leaf6973Box leaf6973Certificate leaf6973InnerLog leaf6973Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk159RoundedFacts chi348RoundedFacts
    innerPair791RoundedFacts leaf6973RoundedFacts (by rfl)

private theorem leaf6973FlatSound : Sound leaf6973Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6973CertificateValid
    leaf6973InnerLogValid leaf6973CoversExact leaf6973LowerChecked

private noncomputable def leaf6974Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (39/64), chiHi := (79/128) }

private noncomputable def leaf6974Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218013/134217728) }, vSqrt := { lower := (65527/65536), upper := (34357182459/34354561024) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (456208925/268435456) }, upper := { exponent := 1, mantissa := (111/64) } }, logOuter := sk160LogOuterCertificate, logK := sk160LogKCertificate, logChi := chi347LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (68711743483/68709122048) } }, logDArg := sk160LogDArgCertificate }

private noncomputable def leaf6974InnerLog : WideLogData :=
  innerPair791Data

set_option maxRecDepth 1000000 in
private theorem leaf6974LocalValidity :
    LeafFacts leaf6974Box leaf6974Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6974Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (34357182459/34354561024) }) = true
      norm_num [leaf6974Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6974CertificateValid :
    WideCertificateValid leaf6974Box leaf6974Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk160ValidityFacts chi347ValidityFacts
    leaf6974LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6974CoverageChecked :
    coverageCheck (innerAD leaf6974Box) leaf6974InnerLog = true := by
  rfl'

private theorem leaf6974InnerLogValid :
    leaf6974InnerLog.Valid 8 (innerAD leaf6974Box) :=
  wideLogDataValid_of_cachedCheck endpoint497PositiveFacts
    endpoint542PositiveFacts.valid leaf6974CoverageChecked

private noncomputable def leaf6974InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629721/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6974InputLogOnePlusV_eq :
    leaf6974InputLogOnePlusV = outerEnclosure 24
      (leaf6974Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6974RoundedFacts : LeafRoundedFacts 8
    leaf6974Certificate.logOnePlusV leaf6974InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6974InputLogOnePlusV_eq }

private noncomputable def leaf6974Inputs : Inputs :=
  inputsOfCaches globalInput sk160RoundedInputs
    chi347InputQChi innerPair791Input
    leaf6974InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6974LowerChecked :
    lowerCheck 24 leaf6974Box leaf6974Inputs = true := by
  rfl'

private theorem leaf6974CoversExact : CoversExact 8
    leaf6974Box leaf6974Certificate leaf6974InnerLog leaf6974Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk160RoundedFacts chi347RoundedFacts
    innerPair791RoundedFacts leaf6974RoundedFacts (by rfl)

private theorem leaf6974FlatSound : Sound leaf6974Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6974CertificateValid
    leaf6974InnerLogValid leaf6974CoversExact leaf6974LowerChecked

private noncomputable def leaf6975Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (79/128), chiHi := (5/8) }

private noncomputable def leaf6975Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (134218015/134217728) }, vSqrt := { lower := (65527/65536), upper := (11452394153/11451498496) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (460337439/268435456) }, upper := { exponent := 1, mantissa := (7/4) } }, logOuter := sk160LogOuterCertificate, logK := sk160LogKCertificate, logChi := chi348LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (22903892649/22902996992) } }, logDArg := sk160LogDArgCertificate }

private noncomputable def leaf6975InnerLog : WideLogData :=
  innerPair770Data

set_option maxRecDepth 1000000 in
private theorem leaf6975LocalValidity :
    LeafFacts leaf6975Box leaf6975Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6975Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (11452394153/11451498496) }) = true
      norm_num [leaf6975Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6975CertificateValid :
    WideCertificateValid leaf6975Box leaf6975Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk160ValidityFacts chi348ValidityFacts
    leaf6975LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6975CoverageChecked :
    coverageCheck (innerAD leaf6975Box) leaf6975InnerLog = true := by
  rfl'

private theorem leaf6975InnerLogValid :
    leaf6975InnerLog.Valid 8 (innerAD leaf6975Box) :=
  wideLogDataValid_of_cachedCheck endpoint487PositiveFacts
    endpoint489PositiveFacts.valid leaf6975CoverageChecked

private noncomputable def leaf6975InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629737/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6975InputLogOnePlusV_eq :
    leaf6975InputLogOnePlusV = outerEnclosure 24
      (leaf6975Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6975RoundedFacts : LeafRoundedFacts 8
    leaf6975Certificate.logOnePlusV leaf6975InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6975InputLogOnePlusV_eq }

private noncomputable def leaf6975Inputs : Inputs :=
  inputsOfCaches globalInput sk160RoundedInputs
    chi348InputQChi innerPair770Input
    leaf6975InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6975LowerChecked :
    lowerCheck 24 leaf6975Box leaf6975Inputs = true := by
  rfl'

private theorem leaf6975CoversExact : CoversExact 8
    leaf6975Box leaf6975Certificate leaf6975InnerLog leaf6975Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk160RoundedFacts chi348RoundedFacts
    innerPair770RoundedFacts leaf6975RoundedFacts (by rfl)

private theorem leaf6975FlatSound : Sound leaf6975Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6975CertificateValid
    leaf6975InnerLogValid leaf6975CoversExact leaf6975LowerChecked

private noncomputable def component141Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (9/16), chiHi := (73/128) }

set_option maxRecDepth 1000000 in
private theorem component141Node0_sound : Sound component141Node0Box :=
  sound_of_literal_split component141Node0Box leaf6934Box leaf6935Box
    .k (121/32) (by rfl) (by rfl)
    leaf6934FlatSound leaf6935FlatSound

private noncomputable def component141Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (73/128), chiHi := (37/64) }

set_option maxRecDepth 1000000 in
private theorem component141Node1_sound : Sound component141Node1Box :=
  sound_of_literal_split component141Node1Box leaf6936Box leaf6937Box
    .k (121/32) (by rfl) (by rfl)
    leaf6936FlatSound leaf6937FlatSound

private noncomputable def component141Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (9/16), chiHi := (37/64) }

set_option maxRecDepth 1000000 in
private theorem component141Node2_sound : Sound component141Node2Box :=
  sound_of_literal_split component141Node2Box component141Node0Box component141Node1Box
    .chi (73/128) (by rfl) (by rfl)
    component141Node0_sound component141Node1_sound

private noncomputable def component141Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (9/16), chiHi := (73/128) }

set_option maxRecDepth 1000000 in
private theorem component141Node3_sound : Sound component141Node3Box :=
  sound_of_literal_split component141Node3Box leaf6938Box leaf6939Box
    .k (123/32) (by rfl) (by rfl)
    leaf6938FlatSound leaf6939FlatSound

private noncomputable def component141Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (73/128), chiHi := (37/64) }

set_option maxRecDepth 1000000 in
private theorem component141Node4_sound : Sound component141Node4Box :=
  sound_of_literal_split component141Node4Box leaf6940Box leaf6941Box
    .k (123/32) (by rfl) (by rfl)
    leaf6940FlatSound leaf6941FlatSound

private noncomputable def component141Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (9/16), chiHi := (37/64) }

set_option maxRecDepth 1000000 in
private theorem component141Node5_sound : Sound component141Node5Box :=
  sound_of_literal_split component141Node5Box component141Node3Box component141Node4Box
    .chi (73/128) (by rfl) (by rfl)
    component141Node3_sound component141Node4_sound

private noncomputable def component141Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (9/16), chiHi := (37/64) }

set_option maxRecDepth 1000000 in
private theorem component141Node6_sound : Sound component141Node6Box :=
  sound_of_literal_split component141Node6Box component141Node2Box component141Node5Box
    .k (61/16) (by rfl) (by rfl)
    component141Node2_sound component141Node5_sound

private noncomputable def component141Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (37/64), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component141Node7_sound : Sound component141Node7Box :=
  sound_of_literal_split component141Node7Box leaf6942Box leaf6943Box
    .chi (75/128) (by rfl) (by rfl)
    leaf6942FlatSound leaf6943FlatSound

private noncomputable def component141Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (37/64), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component141Node8_sound : Sound component141Node8Box :=
  sound_of_literal_split component141Node8Box leaf6944Box leaf6945Box
    .chi (75/128) (by rfl) (by rfl)
    leaf6944FlatSound leaf6945FlatSound

private noncomputable def component141Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (37/64), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component141Node9_sound : Sound component141Node9Box :=
  sound_of_literal_split component141Node9Box component141Node7Box component141Node8Box
    .k (61/16) (by rfl) (by rfl)
    component141Node7_sound component141Node8_sound

private noncomputable def component141Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (9/16), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component141Node10_sound : Sound component141Node10Box :=
  sound_of_literal_split component141Node10Box component141Node6Box component141Node9Box
    .chi (37/64) (by rfl) (by rfl)
    component141Node6_sound component141Node9_sound

private noncomputable def component141Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (9/16), chiHi := (73/128) }

set_option maxRecDepth 1000000 in
private theorem component141Node11_sound : Sound component141Node11Box :=
  sound_of_literal_split component141Node11Box leaf6946Box leaf6947Box
    .k (125/32) (by rfl) (by rfl)
    leaf6946FlatSound leaf6947FlatSound

private noncomputable def component141Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (73/128), chiHi := (37/64) }

set_option maxRecDepth 1000000 in
private theorem component141Node12_sound : Sound component141Node12Box :=
  sound_of_literal_split component141Node12Box leaf6948Box leaf6949Box
    .k (125/32) (by rfl) (by rfl)
    leaf6948FlatSound leaf6949FlatSound

private noncomputable def component141Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (9/16), chiHi := (37/64) }

set_option maxRecDepth 1000000 in
private theorem component141Node13_sound : Sound component141Node13Box :=
  sound_of_literal_split component141Node13Box component141Node11Box component141Node12Box
    .chi (73/128) (by rfl) (by rfl)
    component141Node11_sound component141Node12_sound

private noncomputable def component141Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (9/16), chiHi := (73/128) }

set_option maxRecDepth 1000000 in
private theorem component141Node14_sound : Sound component141Node14Box :=
  sound_of_literal_split component141Node14Box leaf6950Box leaf6951Box
    .k (127/32) (by rfl) (by rfl)
    leaf6950FlatSound leaf6951FlatSound

private noncomputable def component141Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (73/128), chiHi := (37/64) }

set_option maxRecDepth 1000000 in
private theorem component141Node15_sound : Sound component141Node15Box :=
  sound_of_literal_split component141Node15Box leaf6952Box leaf6953Box
    .k (127/32) (by rfl) (by rfl)
    leaf6952FlatSound leaf6953FlatSound

private noncomputable def component141Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (9/16), chiHi := (37/64) }

set_option maxRecDepth 1000000 in
private theorem component141Node16_sound : Sound component141Node16Box :=
  sound_of_literal_split component141Node16Box component141Node14Box component141Node15Box
    .chi (73/128) (by rfl) (by rfl)
    component141Node14_sound component141Node15_sound

private noncomputable def component141Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (9/16), chiHi := (37/64) }

set_option maxRecDepth 1000000 in
private theorem component141Node17_sound : Sound component141Node17Box :=
  sound_of_literal_split component141Node17Box component141Node13Box component141Node16Box
    .k (63/16) (by rfl) (by rfl)
    component141Node13_sound component141Node16_sound

private noncomputable def component141Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (37/64), chiHi := (75/128) }

set_option maxRecDepth 1000000 in
private theorem component141Node18_sound : Sound component141Node18Box :=
  sound_of_literal_split component141Node18Box leaf6954Box leaf6955Box
    .k (125/32) (by rfl) (by rfl)
    leaf6954FlatSound leaf6955FlatSound

private noncomputable def component141Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (37/64), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component141Node19_sound : Sound component141Node19Box :=
  sound_of_literal_split component141Node19Box component141Node18Box leaf6956Box
    .chi (75/128) (by rfl) (by rfl)
    component141Node18_sound leaf6956FlatSound

private noncomputable def component141Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (37/64), chiHi := (75/128) }

set_option maxRecDepth 1000000 in
private theorem component141Node20_sound : Sound component141Node20Box :=
  sound_of_literal_split component141Node20Box leaf6957Box leaf6958Box
    .k (127/32) (by rfl) (by rfl)
    leaf6957FlatSound leaf6958FlatSound

private noncomputable def component141Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (37/64), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component141Node21_sound : Sound component141Node21Box :=
  sound_of_literal_split component141Node21Box component141Node20Box leaf6959Box
    .chi (75/128) (by rfl) (by rfl)
    component141Node20_sound leaf6959FlatSound

private noncomputable def component141Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (37/64), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component141Node22_sound : Sound component141Node22Box :=
  sound_of_literal_split component141Node22Box component141Node19Box component141Node21Box
    .k (63/16) (by rfl) (by rfl)
    component141Node19_sound component141Node21_sound

private noncomputable def component141Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (9/16), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component141Node23_sound : Sound component141Node23Box :=
  sound_of_literal_split component141Node23Box component141Node17Box component141Node22Box
    .chi (37/64) (by rfl) (by rfl)
    component141Node17_sound component141Node22_sound

private noncomputable def component141Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (4), chiLo := (9/16), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component141Node24_sound : Sound component141Node24Box :=
  sound_of_literal_split component141Node24Box component141Node10Box component141Node23Box
    .k (31/8) (by rfl) (by rfl)
    component141Node10_sound component141Node23_sound

private noncomputable def component141Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (19/32), chiHi := (39/64) }

set_option maxRecDepth 1000000 in
private theorem component141Node25_sound : Sound component141Node25Box :=
  sound_of_literal_split component141Node25Box leaf6960Box leaf6961Box
    .chi (77/128) (by rfl) (by rfl)
    leaf6960FlatSound leaf6961FlatSound

private noncomputable def component141Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (19/32), chiHi := (39/64) }

set_option maxRecDepth 1000000 in
private theorem component141Node26_sound : Sound component141Node26Box :=
  sound_of_literal_split component141Node26Box leaf6962Box leaf6963Box
    .chi (77/128) (by rfl) (by rfl)
    leaf6962FlatSound leaf6963FlatSound

private noncomputable def component141Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (19/32), chiHi := (39/64) }

set_option maxRecDepth 1000000 in
private theorem component141Node27_sound : Sound component141Node27Box :=
  sound_of_literal_split component141Node27Box component141Node25Box component141Node26Box
    .k (61/16) (by rfl) (by rfl)
    component141Node25_sound component141Node26_sound

private noncomputable def component141Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (39/64), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component141Node28_sound : Sound component141Node28Box :=
  sound_of_literal_split component141Node28Box leaf6964Box leaf6965Box
    .chi (79/128) (by rfl) (by rfl)
    leaf6964FlatSound leaf6965FlatSound

private noncomputable def component141Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (39/64), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component141Node29_sound : Sound component141Node29Box :=
  sound_of_literal_split component141Node29Box leaf6966Box leaf6967Box
    .chi (79/128) (by rfl) (by rfl)
    leaf6966FlatSound leaf6967FlatSound

private noncomputable def component141Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (39/64), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component141Node30_sound : Sound component141Node30Box :=
  sound_of_literal_split component141Node30Box component141Node28Box component141Node29Box
    .k (61/16) (by rfl) (by rfl)
    component141Node28_sound component141Node29_sound

private noncomputable def component141Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (19/32), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component141Node31_sound : Sound component141Node31Box :=
  sound_of_literal_split component141Node31Box component141Node27Box component141Node30Box
    .chi (39/64) (by rfl) (by rfl)
    component141Node27_sound component141Node30_sound

private noncomputable def component141Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (19/32), chiHi := (39/64) }

set_option maxRecDepth 1000000 in
private theorem component141Node32_sound : Sound component141Node32Box :=
  sound_of_literal_split component141Node32Box leaf6968Box leaf6969Box
    .chi (77/128) (by rfl) (by rfl)
    leaf6968FlatSound leaf6969FlatSound

private noncomputable def component141Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (19/32), chiHi := (39/64) }

set_option maxRecDepth 1000000 in
private theorem component141Node33_sound : Sound component141Node33Box :=
  sound_of_literal_split component141Node33Box leaf6970Box leaf6971Box
    .chi (77/128) (by rfl) (by rfl)
    leaf6970FlatSound leaf6971FlatSound

private noncomputable def component141Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (19/32), chiHi := (39/64) }

set_option maxRecDepth 1000000 in
private theorem component141Node34_sound : Sound component141Node34Box :=
  sound_of_literal_split component141Node34Box component141Node32Box component141Node33Box
    .k (63/16) (by rfl) (by rfl)
    component141Node32_sound component141Node33_sound

private noncomputable def component141Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (39/64), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component141Node35_sound : Sound component141Node35Box :=
  sound_of_literal_split component141Node35Box leaf6972Box leaf6973Box
    .chi (79/128) (by rfl) (by rfl)
    leaf6972FlatSound leaf6973FlatSound

private noncomputable def component141Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (39/64), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component141Node36_sound : Sound component141Node36Box :=
  sound_of_literal_split component141Node36Box leaf6974Box leaf6975Box
    .chi (79/128) (by rfl) (by rfl)
    leaf6974FlatSound leaf6975FlatSound

private noncomputable def component141Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (39/64), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component141Node37_sound : Sound component141Node37Box :=
  sound_of_literal_split component141Node37Box component141Node35Box component141Node36Box
    .k (63/16) (by rfl) (by rfl)
    component141Node35_sound component141Node36_sound

private noncomputable def component141Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (19/32), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component141Node38_sound : Sound component141Node38Box :=
  sound_of_literal_split component141Node38Box component141Node34Box component141Node37Box
    .chi (39/64) (by rfl) (by rfl)
    component141Node34_sound component141Node37_sound

private noncomputable def component141Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (4), chiLo := (19/32), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component141Node39_sound : Sound component141Node39Box :=
  sound_of_literal_split component141Node39Box component141Node31Box component141Node38Box
    .k (31/8) (by rfl) (by rfl)
    component141Node31_sound component141Node38_sound

noncomputable def component141Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (4), chiLo := (9/16), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
theorem component141_sound : Sound component141Box :=
  sound_of_literal_split component141Box component141Node24Box component141Node39Box
    .chi (19/32) (by rfl) (by rfl)
    component141Node24_sound component141Node39_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
