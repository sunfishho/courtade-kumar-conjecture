import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheSKBatch1

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

private noncomputable def leaf1051Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (81/32), chiLo := (1/8), chiHi := (17/128) }

private noncomputable def leaf1051Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435651/268435456) }, vSqrt := { lower := (32765/32768), upper := (67108928/67107487) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (352283455/268435456) }, upper := { exponent := 0, mantissa := (5473/4096) } }, logOuter := sk99LogOuterCertificate, logK := sk99LogKCertificate, logChi := chi107LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (134216415/134214974) } }, logDArg := sk99LogDArgCertificate }

private noncomputable def leaf1051InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf1051LocalValidity :
    LeafFacts leaf1051Box leaf1051Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1051Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (67108928/67107487) }) = true
      norm_num [leaf1051Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1051CertificateValid :
    WideCertificateValid leaf1051Box leaf1051Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk99ValidityFacts chi107ValidityFacts
    leaf1051LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1051CoverageChecked :
    coverageCheck (innerAD leaf1051Box) leaf1051InnerLog = true := by
  rfl'

private theorem leaf1051InnerLogValid :
    leaf1051InnerLog.Valid 8 (innerAD leaf1051Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf1051CoverageChecked

private noncomputable def leaf1051InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629261/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1051InputLogOnePlusV_eq :
    leaf1051InputLogOnePlusV = outerEnclosure 24
      (leaf1051Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1051RoundedFacts : LeafRoundedFacts 8
    leaf1051Certificate.logOnePlusV leaf1051InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1051InputLogOnePlusV_eq }

private noncomputable def leaf1051Inputs : Inputs :=
  inputsOfCaches globalInput sk99RoundedInputs
    chi107InputQChi innerPair17Input
    leaf1051InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1051LowerChecked :
    lowerCheck 24 leaf1051Box leaf1051Inputs = true := by
  rfl'

private theorem leaf1051CoversExact : CoversExact 8
    leaf1051Box leaf1051Certificate leaf1051InnerLog leaf1051Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk99RoundedFacts chi107RoundedFacts
    innerPair17RoundedFacts leaf1051RoundedFacts (by rfl)

private theorem leaf1051FlatSound : Sound leaf1051Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1051CertificateValid
    leaf1051InnerLogValid leaf1051CoversExact leaf1051LowerChecked

private noncomputable def leaf1052Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (81/32), kHi := (41/16), chiLo := (1/8), chiHi := (17/128) }

private noncomputable def leaf1052Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435653/268435456) }, vSqrt := { lower := (32765/32768), upper := (33554464/33553735) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (353331965/268435456) }, upper := { exponent := 0, mantissa := (2745/2048) } }, logOuter := sk100LogOuterCertificate, logK := sk100LogKCertificate, logChi := chi107LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (67108199/67107470) } }, logDArg := sk100LogDArgCertificate }

private noncomputable def leaf1052InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1052LocalValidity :
    LeafFacts leaf1052Box leaf1052Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1052Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (33554464/33553735) }) = true
      norm_num [leaf1052Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1052CertificateValid :
    WideCertificateValid leaf1052Box leaf1052Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk100ValidityFacts chi107ValidityFacts
    leaf1052LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1052CoverageChecked :
    coverageCheck (innerAD leaf1052Box) leaf1052InnerLog = true := by
  rfl'

private theorem leaf1052InnerLogValid :
    leaf1052InnerLog.Valid 8 (innerAD leaf1052Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1052CoverageChecked

private noncomputable def leaf1052InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629263/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1052InputLogOnePlusV_eq :
    leaf1052InputLogOnePlusV = outerEnclosure 24
      (leaf1052Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1052RoundedFacts : LeafRoundedFacts 8
    leaf1052Certificate.logOnePlusV leaf1052InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1052InputLogOnePlusV_eq }

private noncomputable def leaf1052Inputs : Inputs :=
  inputsOfCaches globalInput sk100RoundedInputs
    chi107InputQChi innerPair21Input
    leaf1052InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1052LowerChecked :
    lowerCheck 24 leaf1052Box leaf1052Inputs = true := by
  rfl'

private theorem leaf1052CoversExact : CoversExact 8
    leaf1052Box leaf1052Certificate leaf1052InnerLog leaf1052Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk100RoundedFacts chi107RoundedFacts
    innerPair21RoundedFacts leaf1052RoundedFacts (by rfl)

private theorem leaf1052FlatSound : Sound leaf1052Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1052CertificateValid
    leaf1052InnerLogValid leaf1052CoversExact leaf1052LowerChecked

private noncomputable def leaf1053Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (81/32), chiLo := (17/128), chiHi := (9/64) }

private noncomputable def leaf1053Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435653/268435456) }, vSqrt := { lower := (32765/32768), upper := (33554464/33553703) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (357526013/268435456) }, upper := { exponent := 0, mantissa := (2777/2048) } }, logOuter := sk99LogOuterCertificate, logK := sk99LogKCertificate, logChi := chi108LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (67108167/67107406) } }, logDArg := sk99LogDArgCertificate }

private noncomputable def leaf1053InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1053LocalValidity :
    LeafFacts leaf1053Box leaf1053Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1053Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (33554464/33553703) }) = true
      norm_num [leaf1053Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1053CertificateValid :
    WideCertificateValid leaf1053Box leaf1053Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk99ValidityFacts chi108ValidityFacts
    leaf1053LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1053CoverageChecked :
    coverageCheck (innerAD leaf1053Box) leaf1053InnerLog = true := by
  rfl'

private theorem leaf1053InnerLogValid :
    leaf1053InnerLog.Valid 8 (innerAD leaf1053Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1053CoverageChecked

private noncomputable def leaf1053InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629271/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1053InputLogOnePlusV_eq :
    leaf1053InputLogOnePlusV = outerEnclosure 24
      (leaf1053Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1053RoundedFacts : LeafRoundedFacts 8
    leaf1053Certificate.logOnePlusV leaf1053InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1053InputLogOnePlusV_eq }

private noncomputable def leaf1053Inputs : Inputs :=
  inputsOfCaches globalInput sk99RoundedInputs
    chi108InputQChi innerPair21Input
    leaf1053InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1053LowerChecked :
    lowerCheck 24 leaf1053Box leaf1053Inputs = true := by
  rfl'

private theorem leaf1053CoversExact : CoversExact 8
    leaf1053Box leaf1053Certificate leaf1053InnerLog leaf1053Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk99RoundedFacts chi108RoundedFacts
    innerPair21RoundedFacts leaf1053RoundedFacts (by rfl)

private theorem leaf1053FlatSound : Sound leaf1053Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1053CertificateValid
    leaf1053InnerLogValid leaf1053CoversExact leaf1053LowerChecked

private noncomputable def leaf1054Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (81/32), kHi := (41/16), chiLo := (17/128), chiHi := (9/64) }

private noncomputable def leaf1054Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435655/268435456) }, vSqrt := { lower := (32765/32768), upper := (16777232/16776847) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (358640055/268435456) }, upper := { exponent := 0, mantissa := (1393/1024) } }, logOuter := sk100LogOuterCertificate, logK := sk100LogKCertificate, logChi := chi108LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (33554079/33553694) } }, logDArg := sk100LogDArgCertificate }

private noncomputable def leaf1054InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1054LocalValidity :
    LeafFacts leaf1054Box leaf1054Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1054Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (16777232/16776847) }) = true
      norm_num [leaf1054Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1054CertificateValid :
    WideCertificateValid leaf1054Box leaf1054Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk100ValidityFacts chi108ValidityFacts
    leaf1054LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1054CoverageChecked :
    coverageCheck (innerAD leaf1054Box) leaf1054InnerLog = true := by
  rfl'

private theorem leaf1054InnerLogValid :
    leaf1054InnerLog.Valid 8 (innerAD leaf1054Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1054CoverageChecked

private noncomputable def leaf1054InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629273/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1054InputLogOnePlusV_eq :
    leaf1054InputLogOnePlusV = outerEnclosure 24
      (leaf1054Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1054RoundedFacts : LeafRoundedFacts 8
    leaf1054Certificate.logOnePlusV leaf1054InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1054InputLogOnePlusV_eq }

private noncomputable def leaf1054Inputs : Inputs :=
  inputsOfCaches globalInput sk100RoundedInputs
    chi108InputQChi innerPair21Input
    leaf1054InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1054LowerChecked :
    lowerCheck 24 leaf1054Box leaf1054Inputs = true := by
  rfl'

private theorem leaf1054CoversExact : CoversExact 8
    leaf1054Box leaf1054Certificate leaf1054InnerLog leaf1054Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk100RoundedFacts chi108RoundedFacts
    innerPair21RoundedFacts leaf1054RoundedFacts (by rfl)

private theorem leaf1054FlatSound : Sound leaf1054Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1054CertificateValid
    leaf1054InnerLogValid leaf1054CoversExact leaf1054LowerChecked

private noncomputable def leaf1055Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (83/32), chiLo := (1/8), chiHi := (17/128) }

private noncomputable def leaf1055Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435655/268435456) }, vSqrt := { lower := (32765/32768), upper := (67108928/67107453) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (354380475/268435456) }, upper := { exponent := 0, mantissa := (5507/4096) } }, logOuter := sk101LogOuterCertificate, logK := sk101LogKCertificate, logChi := chi107LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (134216381/134214906) } }, logDArg := sk101LogDArgCertificate }

private noncomputable def leaf1055InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1055LocalValidity :
    LeafFacts leaf1055Box leaf1055Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1055Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (67108928/67107453) }) = true
      norm_num [leaf1055Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1055CertificateValid :
    WideCertificateValid leaf1055Box leaf1055Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk101ValidityFacts chi107ValidityFacts
    leaf1055LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1055CoverageChecked :
    coverageCheck (innerAD leaf1055Box) leaf1055InnerLog = true := by
  rfl'

private theorem leaf1055InnerLogValid :
    leaf1055InnerLog.Valid 8 (innerAD leaf1055Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1055CoverageChecked

private noncomputable def leaf1055InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629265/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1055InputLogOnePlusV_eq :
    leaf1055InputLogOnePlusV = outerEnclosure 24
      (leaf1055Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1055RoundedFacts : LeafRoundedFacts 8
    leaf1055Certificate.logOnePlusV leaf1055InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1055InputLogOnePlusV_eq }

private noncomputable def leaf1055Inputs : Inputs :=
  inputsOfCaches globalInput sk101RoundedInputs
    chi107InputQChi innerPair21Input
    leaf1055InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1055LowerChecked :
    lowerCheck 24 leaf1055Box leaf1055Inputs = true := by
  rfl'

private theorem leaf1055CoversExact : CoversExact 8
    leaf1055Box leaf1055Certificate leaf1055InnerLog leaf1055Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk101RoundedFacts chi107RoundedFacts
    innerPair21RoundedFacts leaf1055RoundedFacts (by rfl)

private theorem leaf1055FlatSound : Sound leaf1055Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1055CertificateValid
    leaf1055InnerLogValid leaf1055CoversExact leaf1055LowerChecked

private noncomputable def leaf1056Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (83/32), kHi := (21/8), chiLo := (1/8), chiHi := (17/128) }

private noncomputable def leaf1056Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435657/268435456) }, vSqrt := { lower := (32765/32768), upper := (16777232/16776859) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (355428985/268435456) }, upper := { exponent := 0, mantissa := (1381/1024) } }, logOuter := sk102LogOuterCertificate, logK := sk102LogKCertificate, logChi := chi107LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (33554091/33553718) } }, logDArg := sk102LogDArgCertificate }

private noncomputable def leaf1056InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1056LocalValidity :
    LeafFacts leaf1056Box leaf1056Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1056Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (16777232/16776859) }) = true
      norm_num [leaf1056Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1056CertificateValid :
    WideCertificateValid leaf1056Box leaf1056Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk102ValidityFacts chi107ValidityFacts
    leaf1056LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1056CoverageChecked :
    coverageCheck (innerAD leaf1056Box) leaf1056InnerLog = true := by
  rfl'

private theorem leaf1056InnerLogValid :
    leaf1056InnerLog.Valid 8 (innerAD leaf1056Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1056CoverageChecked

private noncomputable def leaf1056InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629267/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1056InputLogOnePlusV_eq :
    leaf1056InputLogOnePlusV = outerEnclosure 24
      (leaf1056Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1056RoundedFacts : LeafRoundedFacts 8
    leaf1056Certificate.logOnePlusV leaf1056InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1056InputLogOnePlusV_eq }

private noncomputable def leaf1056Inputs : Inputs :=
  inputsOfCaches globalInput sk102RoundedInputs
    chi107InputQChi innerPair21Input
    leaf1056InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1056LowerChecked :
    lowerCheck 24 leaf1056Box leaf1056Inputs = true := by
  rfl'

private theorem leaf1056CoversExact : CoversExact 8
    leaf1056Box leaf1056Certificate leaf1056InnerLog leaf1056Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk102RoundedFacts chi107RoundedFacts
    innerPair21RoundedFacts leaf1056RoundedFacts (by rfl)

private theorem leaf1056FlatSound : Sound leaf1056Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1056CertificateValid
    leaf1056InnerLogValid leaf1056CoversExact leaf1056LowerChecked

private noncomputable def leaf1057Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (83/32), chiLo := (17/128), chiHi := (9/64) }

private noncomputable def leaf1057Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435657/268435456) }, vSqrt := { lower := (32765/32768), upper := (33554464/33553685) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (359754097/268435456) }, upper := { exponent := 0, mantissa := (2795/2048) } }, logOuter := sk101LogOuterCertificate, logK := sk101LogKCertificate, logChi := chi108LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (67108149/67107370) } }, logDArg := sk101LogDArgCertificate }

private noncomputable def leaf1057InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1057LocalValidity :
    LeafFacts leaf1057Box leaf1057Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1057Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (33554464/33553685) }) = true
      norm_num [leaf1057Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1057CertificateValid :
    WideCertificateValid leaf1057Box leaf1057Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk101ValidityFacts chi108ValidityFacts
    leaf1057LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1057CoverageChecked :
    coverageCheck (innerAD leaf1057Box) leaf1057InnerLog = true := by
  rfl'

private theorem leaf1057InnerLogValid :
    leaf1057InnerLog.Valid 8 (innerAD leaf1057Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1057CoverageChecked

private noncomputable def leaf1057InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629275/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1057InputLogOnePlusV_eq :
    leaf1057InputLogOnePlusV = outerEnclosure 24
      (leaf1057Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1057RoundedFacts : LeafRoundedFacts 8
    leaf1057Certificate.logOnePlusV leaf1057InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1057InputLogOnePlusV_eq }

private noncomputable def leaf1057Inputs : Inputs :=
  inputsOfCaches globalInput sk101RoundedInputs
    chi108InputQChi innerPair21Input
    leaf1057InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1057LowerChecked :
    lowerCheck 24 leaf1057Box leaf1057Inputs = true := by
  rfl'

private theorem leaf1057CoversExact : CoversExact 8
    leaf1057Box leaf1057Certificate leaf1057InnerLog leaf1057Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk101RoundedFacts chi108RoundedFacts
    innerPair21RoundedFacts leaf1057RoundedFacts (by rfl)

private theorem leaf1057FlatSound : Sound leaf1057Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1057CertificateValid
    leaf1057InnerLogValid leaf1057CoversExact leaf1057LowerChecked

private noncomputable def leaf1058Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (83/32), kHi := (21/8), chiLo := (17/128), chiHi := (9/64) }

private noncomputable def leaf1058Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435659/268435456) }, vSqrt := { lower := (32765/32768), upper := (8388616/8388419) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (360868139/268435456) }, upper := { exponent := 0, mantissa := (701/512) } }, logOuter := sk102LogOuterCertificate, logK := sk102LogKCertificate, logChi := chi108LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (16777035/16776838) } }, logDArg := sk102LogDArgCertificate }

private noncomputable def leaf1058InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1058LocalValidity :
    LeafFacts leaf1058Box leaf1058Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1058Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8388616/8388419) }) = true
      norm_num [leaf1058Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1058CertificateValid :
    WideCertificateValid leaf1058Box leaf1058Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk102ValidityFacts chi108ValidityFacts
    leaf1058LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1058CoverageChecked :
    coverageCheck (innerAD leaf1058Box) leaf1058InnerLog = true := by
  rfl'

private theorem leaf1058InnerLogValid :
    leaf1058InnerLog.Valid 8 (innerAD leaf1058Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1058CoverageChecked

private noncomputable def leaf1058InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814639/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1058InputLogOnePlusV_eq :
    leaf1058InputLogOnePlusV = outerEnclosure 24
      (leaf1058Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1058RoundedFacts : LeafRoundedFacts 8
    leaf1058Certificate.logOnePlusV leaf1058InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1058InputLogOnePlusV_eq }

private noncomputable def leaf1058Inputs : Inputs :=
  inputsOfCaches globalInput sk102RoundedInputs
    chi108InputQChi innerPair21Input
    leaf1058InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1058LowerChecked :
    lowerCheck 24 leaf1058Box leaf1058Inputs = true := by
  rfl'

private theorem leaf1058CoversExact : CoversExact 8
    leaf1058Box leaf1058Certificate leaf1058InnerLog leaf1058Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk102RoundedFacts chi108RoundedFacts
    innerPair21RoundedFacts leaf1058RoundedFacts (by rfl)

private theorem leaf1058FlatSound : Sound leaf1058Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1058CertificateValid
    leaf1058InnerLogValid leaf1058CoversExact leaf1058LowerChecked

private noncomputable def leaf1059Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (81/32), chiLo := (9/64), chiHi := (19/128) }

private noncomputable def leaf1059Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435655/268435456) }, vSqrt := { lower := (32765/32768), upper := (67108928/67107325) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (362768571/268435456) }, upper := { exponent := 0, mantissa := (5635/4096) } }, logOuter := sk99LogOuterCertificate, logK := sk99LogKCertificate, logChi := chi109LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (134216253/134214650) } }, logDArg := sk99LogDArgCertificate }

private noncomputable def leaf1059InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf1059LocalValidity :
    LeafFacts leaf1059Box leaf1059Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1059Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (67108928/67107325) }) = true
      norm_num [leaf1059Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1059CertificateValid :
    WideCertificateValid leaf1059Box leaf1059Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk99ValidityFacts chi109ValidityFacts
    leaf1059LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1059CoverageChecked :
    coverageCheck (innerAD leaf1059Box) leaf1059InnerLog = true := by
  rfl'

private theorem leaf1059InnerLogValid :
    leaf1059InnerLog.Valid 8 (innerAD leaf1059Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf1059CoverageChecked

private noncomputable def leaf1059InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629281/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1059InputLogOnePlusV_eq :
    leaf1059InputLogOnePlusV = outerEnclosure 24
      (leaf1059Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1059RoundedFacts : LeafRoundedFacts 8
    leaf1059Certificate.logOnePlusV leaf1059InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1059InputLogOnePlusV_eq }

private noncomputable def leaf1059Inputs : Inputs :=
  inputsOfCaches globalInput sk99RoundedInputs
    chi109InputQChi innerPair22Input
    leaf1059InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1059LowerChecked :
    lowerCheck 24 leaf1059Box leaf1059Inputs = true := by
  rfl'

private theorem leaf1059CoversExact : CoversExact 8
    leaf1059Box leaf1059Certificate leaf1059InnerLog leaf1059Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk99RoundedFacts chi109RoundedFacts
    innerPair22RoundedFacts leaf1059RoundedFacts (by rfl)

private theorem leaf1059FlatSound : Sound leaf1059Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1059CertificateValid
    leaf1059InnerLogValid leaf1059CoversExact leaf1059LowerChecked

private noncomputable def leaf1060Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (81/32), kHi := (41/16), chiLo := (9/64), chiHi := (19/128) }

private noncomputable def leaf1060Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435657/268435456) }, vSqrt := { lower := (32765/32768), upper := (33554464/33553653) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (363948145/268435456) }, upper := { exponent := 0, mantissa := (2827/2048) } }, logOuter := sk100LogOuterCertificate, logK := sk100LogKCertificate, logChi := chi109LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (67108117/67107306) } }, logDArg := sk100LogDArgCertificate }

private noncomputable def leaf1060InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf1060LocalValidity :
    LeafFacts leaf1060Box leaf1060Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1060Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (33554464/33553653) }) = true
      norm_num [leaf1060Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1060CertificateValid :
    WideCertificateValid leaf1060Box leaf1060Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk100ValidityFacts chi109ValidityFacts
    leaf1060LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1060CoverageChecked :
    coverageCheck (innerAD leaf1060Box) leaf1060InnerLog = true := by
  rfl'

private theorem leaf1060InnerLogValid :
    leaf1060InnerLog.Valid 8 (innerAD leaf1060Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf1060CoverageChecked

private noncomputable def leaf1060InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629283/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1060InputLogOnePlusV_eq :
    leaf1060InputLogOnePlusV = outerEnclosure 24
      (leaf1060Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1060RoundedFacts : LeafRoundedFacts 8
    leaf1060Certificate.logOnePlusV leaf1060InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1060InputLogOnePlusV_eq }

private noncomputable def leaf1060Inputs : Inputs :=
  inputsOfCaches globalInput sk100RoundedInputs
    chi109InputQChi innerPair22Input
    leaf1060InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1060LowerChecked :
    lowerCheck 24 leaf1060Box leaf1060Inputs = true := by
  rfl'

private theorem leaf1060CoversExact : CoversExact 8
    leaf1060Box leaf1060Certificate leaf1060InnerLog leaf1060Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk100RoundedFacts chi109RoundedFacts
    innerPair22RoundedFacts leaf1060RoundedFacts (by rfl)

private theorem leaf1060FlatSound : Sound leaf1060Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1060CertificateValid
    leaf1060InnerLogValid leaf1060CoversExact leaf1060LowerChecked

private noncomputable def leaf1061Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (81/32), chiLo := (19/128), chiHi := (5/32) }

private noncomputable def leaf1061Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435657/268435456) }, vSqrt := { lower := (32765/32768), upper := (16777232/16776811) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (368011129/268435456) }, upper := { exponent := 0, mantissa := (1429/1024) } }, logOuter := sk99LogOuterCertificate, logK := sk99LogKCertificate, logChi := chi110LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (33554043/33553622) } }, logDArg := sk99LogDArgCertificate }

private noncomputable def leaf1061InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf1061LocalValidity :
    LeafFacts leaf1061Box leaf1061Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1061Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (16777232/16776811) }) = true
      norm_num [leaf1061Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1061CertificateValid :
    WideCertificateValid leaf1061Box leaf1061Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk99ValidityFacts chi110ValidityFacts
    leaf1061LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1061CoverageChecked :
    coverageCheck (innerAD leaf1061Box) leaf1061InnerLog = true := by
  rfl'

private theorem leaf1061InnerLogValid :
    leaf1061InnerLog.Valid 8 (innerAD leaf1061Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf1061CoverageChecked

private noncomputable def leaf1061InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629291/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1061InputLogOnePlusV_eq :
    leaf1061InputLogOnePlusV = outerEnclosure 24
      (leaf1061Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1061RoundedFacts : LeafRoundedFacts 8
    leaf1061Certificate.logOnePlusV leaf1061InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1061InputLogOnePlusV_eq }

private noncomputable def leaf1061Inputs : Inputs :=
  inputsOfCaches globalInput sk99RoundedInputs
    chi110InputQChi innerPair22Input
    leaf1061InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1061LowerChecked :
    lowerCheck 24 leaf1061Box leaf1061Inputs = true := by
  rfl'

private theorem leaf1061CoversExact : CoversExact 8
    leaf1061Box leaf1061Certificate leaf1061InnerLog leaf1061Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk99RoundedFacts chi110RoundedFacts
    innerPair22RoundedFacts leaf1061RoundedFacts (by rfl)

private theorem leaf1061FlatSound : Sound leaf1061Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1061CertificateValid
    leaf1061InnerLogValid leaf1061CoversExact leaf1061LowerChecked

private noncomputable def leaf1062Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (81/32), kHi := (41/16), chiLo := (19/128), chiHi := (5/32) }

private noncomputable def leaf1062Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435659/268435456) }, vSqrt := { lower := (32765/32768), upper := (8388616/8388403) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (369256235/268435456) }, upper := { exponent := 0, mantissa := (717/512) } }, logOuter := sk100LogOuterCertificate, logK := sk100LogKCertificate, logChi := chi110LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (16777019/16776806) } }, logDArg := sk100LogDArgCertificate }

private noncomputable def leaf1062InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1062LocalValidity :
    LeafFacts leaf1062Box leaf1062Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1062Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8388616/8388403) }) = true
      norm_num [leaf1062Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1062CertificateValid :
    WideCertificateValid leaf1062Box leaf1062Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk100ValidityFacts chi110ValidityFacts
    leaf1062LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1062CoverageChecked :
    coverageCheck (innerAD leaf1062Box) leaf1062InnerLog = true := by
  rfl'

private theorem leaf1062InnerLogValid :
    leaf1062InnerLog.Valid 8 (innerAD leaf1062Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1062CoverageChecked

private noncomputable def leaf1062InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814647/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1062InputLogOnePlusV_eq :
    leaf1062InputLogOnePlusV = outerEnclosure 24
      (leaf1062Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1062RoundedFacts : LeafRoundedFacts 8
    leaf1062Certificate.logOnePlusV leaf1062InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1062InputLogOnePlusV_eq }

private noncomputable def leaf1062Inputs : Inputs :=
  inputsOfCaches globalInput sk100RoundedInputs
    chi110InputQChi innerPair26Input
    leaf1062InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1062LowerChecked :
    lowerCheck 24 leaf1062Box leaf1062Inputs = true := by
  rfl'

private theorem leaf1062CoversExact : CoversExact 8
    leaf1062Box leaf1062Certificate leaf1062InnerLog leaf1062Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk100RoundedFacts chi110RoundedFacts
    innerPair26RoundedFacts leaf1062RoundedFacts (by rfl)

private theorem leaf1062FlatSound : Sound leaf1062Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1062CertificateValid
    leaf1062InnerLogValid leaf1062CoversExact leaf1062LowerChecked

private noncomputable def leaf1063Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (83/32), chiLo := (9/64), chiHi := (19/128) }

private noncomputable def leaf1063Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435659/268435456) }, vSqrt := { lower := (32765/32768), upper := (67108928/67107287) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (365127719/268435456) }, upper := { exponent := 0, mantissa := (5673/4096) } }, logOuter := sk101LogOuterCertificate, logK := sk101LogKCertificate, logChi := chi109LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (134216215/134214574) } }, logDArg := sk101LogDArgCertificate }

private noncomputable def leaf1063InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf1063LocalValidity :
    LeafFacts leaf1063Box leaf1063Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1063Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (67108928/67107287) }) = true
      norm_num [leaf1063Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1063CertificateValid :
    WideCertificateValid leaf1063Box leaf1063Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk101ValidityFacts chi109ValidityFacts
    leaf1063LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1063CoverageChecked :
    coverageCheck (innerAD leaf1063Box) leaf1063InnerLog = true := by
  rfl'

private theorem leaf1063InnerLogValid :
    leaf1063InnerLog.Valid 8 (innerAD leaf1063Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf1063CoverageChecked

private noncomputable def leaf1063InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814643/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1063InputLogOnePlusV_eq :
    leaf1063InputLogOnePlusV = outerEnclosure 24
      (leaf1063Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1063RoundedFacts : LeafRoundedFacts 8
    leaf1063Certificate.logOnePlusV leaf1063InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1063InputLogOnePlusV_eq }

private noncomputable def leaf1063Inputs : Inputs :=
  inputsOfCaches globalInput sk101RoundedInputs
    chi109InputQChi innerPair22Input
    leaf1063InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1063LowerChecked :
    lowerCheck 24 leaf1063Box leaf1063Inputs = true := by
  rfl'

private theorem leaf1063CoversExact : CoversExact 8
    leaf1063Box leaf1063Certificate leaf1063InnerLog leaf1063Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk101RoundedFacts chi109RoundedFacts
    innerPair22RoundedFacts leaf1063RoundedFacts (by rfl)

private theorem leaf1063FlatSound : Sound leaf1063Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1063CertificateValid
    leaf1063InnerLogValid leaf1063CoversExact leaf1063LowerChecked

private noncomputable def leaf1064Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (83/32), kHi := (21/8), chiLo := (9/64), chiHi := (19/128) }

private noncomputable def leaf1064Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435661/268435456) }, vSqrt := { lower := (32765/32768), upper := (16777232/16776817) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (366307293/268435456) }, upper := { exponent := 0, mantissa := (1423/1024) } }, logOuter := sk102LogOuterCertificate, logK := sk102LogKCertificate, logChi := chi109LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (33554049/33553634) } }, logDArg := sk102LogDArgCertificate }

private noncomputable def leaf1064InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf1064LocalValidity :
    LeafFacts leaf1064Box leaf1064Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1064Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (16777232/16776817) }) = true
      norm_num [leaf1064Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1064CertificateValid :
    WideCertificateValid leaf1064Box leaf1064Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk102ValidityFacts chi109ValidityFacts
    leaf1064LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1064CoverageChecked :
    coverageCheck (innerAD leaf1064Box) leaf1064InnerLog = true := by
  rfl'

private theorem leaf1064InnerLogValid :
    leaf1064InnerLog.Valid 8 (innerAD leaf1064Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf1064CoverageChecked

private noncomputable def leaf1064InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (1453661/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf1064InputLogOnePlusV_eq :
    leaf1064InputLogOnePlusV = outerEnclosure 24
      (leaf1064Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1064RoundedFacts : LeafRoundedFacts 8
    leaf1064Certificate.logOnePlusV leaf1064InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1064InputLogOnePlusV_eq }

private noncomputable def leaf1064Inputs : Inputs :=
  inputsOfCaches globalInput sk102RoundedInputs
    chi109InputQChi innerPair22Input
    leaf1064InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1064LowerChecked :
    lowerCheck 24 leaf1064Box leaf1064Inputs = true := by
  rfl'

private theorem leaf1064CoversExact : CoversExact 8
    leaf1064Box leaf1064Certificate leaf1064InnerLog leaf1064Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk102RoundedFacts chi109RoundedFacts
    innerPair22RoundedFacts leaf1064RoundedFacts (by rfl)

private theorem leaf1064FlatSound : Sound leaf1064Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1064CertificateValid
    leaf1064InnerLogValid leaf1064CoversExact leaf1064LowerChecked

private noncomputable def leaf1065Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (83/32), chiLo := (19/128), chiHi := (5/32) }

private noncomputable def leaf1065Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435661/268435456) }, vSqrt := { lower := (32765/32768), upper := (16777232/16776801) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (370501341/268435456) }, upper := { exponent := 0, mantissa := (1439/1024) } }, logOuter := sk101LogOuterCertificate, logK := sk101LogKCertificate, logChi := chi110LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (33554033/33553602) } }, logDArg := sk101LogDArgCertificate }

private noncomputable def leaf1065InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1065LocalValidity :
    LeafFacts leaf1065Box leaf1065Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1065Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (16777232/16776801) }) = true
      norm_num [leaf1065Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1065CertificateValid :
    WideCertificateValid leaf1065Box leaf1065Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk101ValidityFacts chi110ValidityFacts
    leaf1065LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1065CoverageChecked :
    coverageCheck (innerAD leaf1065Box) leaf1065InnerLog = true := by
  rfl'

private theorem leaf1065InnerLogValid :
    leaf1065InnerLog.Valid 8 (innerAD leaf1065Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1065CoverageChecked

private noncomputable def leaf1065InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (726831/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf1065InputLogOnePlusV_eq :
    leaf1065InputLogOnePlusV = outerEnclosure 24
      (leaf1065Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1065RoundedFacts : LeafRoundedFacts 8
    leaf1065Certificate.logOnePlusV leaf1065InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1065InputLogOnePlusV_eq }

private noncomputable def leaf1065Inputs : Inputs :=
  inputsOfCaches globalInput sk101RoundedInputs
    chi110InputQChi innerPair26Input
    leaf1065InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1065LowerChecked :
    lowerCheck 24 leaf1065Box leaf1065Inputs = true := by
  rfl'

private theorem leaf1065CoversExact : CoversExact 8
    leaf1065Box leaf1065Certificate leaf1065InnerLog leaf1065Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk101RoundedFacts chi110RoundedFacts
    innerPair26RoundedFacts leaf1065RoundedFacts (by rfl)

private theorem leaf1065FlatSound : Sound leaf1065Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1065CertificateValid
    leaf1065InnerLogValid leaf1065CoversExact leaf1065LowerChecked

private noncomputable def leaf1066Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (83/32), kHi := (21/8), chiLo := (19/128), chiHi := (5/32) }

private noncomputable def leaf1066Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435663/268435456) }, vSqrt := { lower := (32765/32768), upper := (4194308/4194199) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (371746447/268435456) }, upper := { exponent := 0, mantissa := (361/256) } }, logOuter := sk102LogOuterCertificate, logK := sk102LogKCertificate, logChi := chi110LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (8388507/8388398) } }, logDArg := sk102LogDArgCertificate }

private noncomputable def leaf1066InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1066LocalValidity :
    LeafFacts leaf1066Box leaf1066Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1066Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4194308/4194199) }) = true
      norm_num [leaf1066Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1066CertificateValid :
    WideCertificateValid leaf1066Box leaf1066Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk102ValidityFacts chi110ValidityFacts
    leaf1066LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1066CoverageChecked :
    coverageCheck (innerAD leaf1066Box) leaf1066InnerLog = true := by
  rfl'

private theorem leaf1066InnerLogValid :
    leaf1066InnerLog.Valid 8 (innerAD leaf1066Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1066CoverageChecked

private noncomputable def leaf1066InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629299/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1066InputLogOnePlusV_eq :
    leaf1066InputLogOnePlusV = outerEnclosure 24
      (leaf1066Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1066RoundedFacts : LeafRoundedFacts 8
    leaf1066Certificate.logOnePlusV leaf1066InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1066InputLogOnePlusV_eq }

private noncomputable def leaf1066Inputs : Inputs :=
  inputsOfCaches globalInput sk102RoundedInputs
    chi110InputQChi innerPair26Input
    leaf1066InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1066LowerChecked :
    lowerCheck 24 leaf1066Box leaf1066Inputs = true := by
  rfl'

private theorem leaf1066CoversExact : CoversExact 8
    leaf1066Box leaf1066Certificate leaf1066InnerLog leaf1066Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk102RoundedFacts chi110RoundedFacts
    innerPair26RoundedFacts leaf1066RoundedFacts (by rfl)

private theorem leaf1066FlatSound : Sound leaf1066Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1066CertificateValid
    leaf1066InnerLogValid leaf1066CoversExact leaf1066LowerChecked

private noncomputable def leaf1067Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (85/32), chiLo := (1/8), chiHi := (17/128) }

private noncomputable def leaf1067Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435659/268435456) }, vSqrt := { lower := (32765/32768), upper := (67108928/67107419) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (356477495/268435456) }, upper := { exponent := 0, mantissa := (5541/4096) } }, logOuter := sk105LogOuterCertificate, logK := sk105LogKCertificate, logChi := chi107LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (134216347/134214838) } }, logDArg := sk105LogDArgCertificate }

private noncomputable def leaf1067InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1067LocalValidity :
    LeafFacts leaf1067Box leaf1067Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1067Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (67108928/67107419) }) = true
      norm_num [leaf1067Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1067CertificateValid :
    WideCertificateValid leaf1067Box leaf1067Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk105ValidityFacts chi107ValidityFacts
    leaf1067LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1067CoverageChecked :
    coverageCheck (innerAD leaf1067Box) leaf1067InnerLog = true := by
  rfl'

private theorem leaf1067InnerLogValid :
    leaf1067InnerLog.Valid 8 (innerAD leaf1067Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1067CoverageChecked

private noncomputable def leaf1067InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629269/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1067InputLogOnePlusV_eq :
    leaf1067InputLogOnePlusV = outerEnclosure 24
      (leaf1067Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1067RoundedFacts : LeafRoundedFacts 8
    leaf1067Certificate.logOnePlusV leaf1067InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1067InputLogOnePlusV_eq }

private noncomputable def leaf1067Inputs : Inputs :=
  inputsOfCaches globalInput sk105RoundedInputs
    chi107InputQChi innerPair21Input
    leaf1067InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1067LowerChecked :
    lowerCheck 24 leaf1067Box leaf1067Inputs = true := by
  rfl'

private theorem leaf1067CoversExact : CoversExact 8
    leaf1067Box leaf1067Certificate leaf1067InnerLog leaf1067Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk105RoundedFacts chi107RoundedFacts
    innerPair21RoundedFacts leaf1067RoundedFacts (by rfl)

private theorem leaf1067FlatSound : Sound leaf1067Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1067CertificateValid
    leaf1067InnerLogValid leaf1067CoversExact leaf1067LowerChecked

private noncomputable def leaf1068Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (85/32), kHi := (43/16), chiLo := (1/8), chiHi := (17/128) }

private noncomputable def leaf1068Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435661/268435456) }, vSqrt := { lower := (32765/32768), upper := (33554464/33553701) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (357526005/268435456) }, upper := { exponent := 0, mantissa := (2779/2048) } }, logOuter := sk106LogOuterCertificate, logK := sk106LogKCertificate, logChi := chi107LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (67108165/67107402) } }, logDArg := sk106LogDArgCertificate }

private noncomputable def leaf1068InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1068LocalValidity :
    LeafFacts leaf1068Box leaf1068Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1068Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (33554464/33553701) }) = true
      norm_num [leaf1068Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1068CertificateValid :
    WideCertificateValid leaf1068Box leaf1068Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk106ValidityFacts chi107ValidityFacts
    leaf1068LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1068CoverageChecked :
    coverageCheck (innerAD leaf1068Box) leaf1068InnerLog = true := by
  rfl'

private theorem leaf1068InnerLogValid :
    leaf1068InnerLog.Valid 8 (innerAD leaf1068Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1068CoverageChecked

private noncomputable def leaf1068InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629271/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1068InputLogOnePlusV_eq :
    leaf1068InputLogOnePlusV = outerEnclosure 24
      (leaf1068Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1068RoundedFacts : LeafRoundedFacts 8
    leaf1068Certificate.logOnePlusV leaf1068InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1068InputLogOnePlusV_eq }

private noncomputable def leaf1068Inputs : Inputs :=
  inputsOfCaches globalInput sk106RoundedInputs
    chi107InputQChi innerPair21Input
    leaf1068InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1068LowerChecked :
    lowerCheck 24 leaf1068Box leaf1068Inputs = true := by
  rfl'

private theorem leaf1068CoversExact : CoversExact 8
    leaf1068Box leaf1068Certificate leaf1068InnerLog leaf1068Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk106RoundedFacts chi107RoundedFacts
    innerPair21RoundedFacts leaf1068RoundedFacts (by rfl)

private theorem leaf1068FlatSound : Sound leaf1068Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1068CertificateValid
    leaf1068InnerLogValid leaf1068CoversExact leaf1068LowerChecked

private noncomputable def leaf1069Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (85/32), chiLo := (17/128), chiHi := (9/64) }

private noncomputable def leaf1069Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435661/268435456) }, vSqrt := { lower := (32765/32768), upper := (33554464/33553667) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (361982181/268435456) }, upper := { exponent := 0, mantissa := (2813/2048) } }, logOuter := sk105LogOuterCertificate, logK := sk105LogKCertificate, logChi := chi108LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (67108131/67107334) } }, logDArg := sk105LogDArgCertificate }

private noncomputable def leaf1069InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1069LocalValidity :
    LeafFacts leaf1069Box leaf1069Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1069Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (33554464/33553667) }) = true
      norm_num [leaf1069Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1069CertificateValid :
    WideCertificateValid leaf1069Box leaf1069Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk105ValidityFacts chi108ValidityFacts
    leaf1069LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1069CoverageChecked :
    coverageCheck (innerAD leaf1069Box) leaf1069InnerLog = true := by
  rfl'

private theorem leaf1069InnerLogValid :
    leaf1069InnerLog.Valid 8 (innerAD leaf1069Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1069CoverageChecked

private noncomputable def leaf1069InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (363415/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf1069InputLogOnePlusV_eq :
    leaf1069InputLogOnePlusV = outerEnclosure 24
      (leaf1069Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1069RoundedFacts : LeafRoundedFacts 8
    leaf1069Certificate.logOnePlusV leaf1069InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1069InputLogOnePlusV_eq }

private noncomputable def leaf1069Inputs : Inputs :=
  inputsOfCaches globalInput sk105RoundedInputs
    chi108InputQChi innerPair21Input
    leaf1069InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1069LowerChecked :
    lowerCheck 24 leaf1069Box leaf1069Inputs = true := by
  rfl'

private theorem leaf1069CoversExact : CoversExact 8
    leaf1069Box leaf1069Certificate leaf1069InnerLog leaf1069Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk105RoundedFacts chi108RoundedFacts
    innerPair21RoundedFacts leaf1069RoundedFacts (by rfl)

private theorem leaf1069FlatSound : Sound leaf1069Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1069CertificateValid
    leaf1069InnerLogValid leaf1069CoversExact leaf1069LowerChecked

private noncomputable def leaf1070Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (85/32), kHi := (43/16), chiLo := (17/128), chiHi := (9/64) }

private noncomputable def leaf1070Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435663/268435456) }, vSqrt := { lower := (32765/32768), upper := (16777232/16776829) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (363096223/268435456) }, upper := { exponent := 0, mantissa := (1411/1024) } }, logOuter := sk106LogOuterCertificate, logK := sk106LogKCertificate, logChi := chi108LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (33554061/33553658) } }, logDArg := sk106LogDArgCertificate }

private noncomputable def leaf1070InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf1070LocalValidity :
    LeafFacts leaf1070Box leaf1070Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1070Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (16777232/16776829) }) = true
      norm_num [leaf1070Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1070CertificateValid :
    WideCertificateValid leaf1070Box leaf1070Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk106ValidityFacts chi108ValidityFacts
    leaf1070LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1070CoverageChecked :
    coverageCheck (innerAD leaf1070Box) leaf1070InnerLog = true := by
  rfl'

private theorem leaf1070InnerLogValid :
    leaf1070InnerLog.Valid 8 (innerAD leaf1070Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf1070CoverageChecked

private noncomputable def leaf1070InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814641/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1070InputLogOnePlusV_eq :
    leaf1070InputLogOnePlusV = outerEnclosure 24
      (leaf1070Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1070RoundedFacts : LeafRoundedFacts 8
    leaf1070Certificate.logOnePlusV leaf1070InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1070InputLogOnePlusV_eq }

private noncomputable def leaf1070Inputs : Inputs :=
  inputsOfCaches globalInput sk106RoundedInputs
    chi108InputQChi innerPair22Input
    leaf1070InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1070LowerChecked :
    lowerCheck 24 leaf1070Box leaf1070Inputs = true := by
  rfl'

private theorem leaf1070CoversExact : CoversExact 8
    leaf1070Box leaf1070Certificate leaf1070InnerLog leaf1070Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk106RoundedFacts chi108RoundedFacts
    innerPair22RoundedFacts leaf1070RoundedFacts (by rfl)

private theorem leaf1070FlatSound : Sound leaf1070Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1070CertificateValid
    leaf1070InnerLogValid leaf1070CoversExact leaf1070LowerChecked

private noncomputable def leaf1071Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (87/32), chiLo := (1/8), chiHi := (17/128) }

private noncomputable def leaf1071Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435663/268435456) }, vSqrt := { lower := (32765/32768), upper := (67108928/67107385) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (358574515/268435456) }, upper := { exponent := 0, mantissa := (5575/4096) } }, logOuter := sk103LogOuterCertificate, logK := sk103LogKCertificate, logChi := chi107LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (134216313/134214770) } }, logDArg := sk103LogDArgCertificate }

private noncomputable def leaf1071InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1071LocalValidity :
    LeafFacts leaf1071Box leaf1071Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1071Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (67108928/67107385) }) = true
      norm_num [leaf1071Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1071CertificateValid :
    WideCertificateValid leaf1071Box leaf1071Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk103ValidityFacts chi107ValidityFacts
    leaf1071LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1071CoverageChecked :
    coverageCheck (innerAD leaf1071Box) leaf1071InnerLog = true := by
  rfl'

private theorem leaf1071InnerLogValid :
    leaf1071InnerLog.Valid 8 (innerAD leaf1071Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1071CoverageChecked

private noncomputable def leaf1071InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814637/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1071InputLogOnePlusV_eq :
    leaf1071InputLogOnePlusV = outerEnclosure 24
      (leaf1071Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1071RoundedFacts : LeafRoundedFacts 8
    leaf1071Certificate.logOnePlusV leaf1071InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1071InputLogOnePlusV_eq }

private noncomputable def leaf1071Inputs : Inputs :=
  inputsOfCaches globalInput sk103RoundedInputs
    chi107InputQChi innerPair21Input
    leaf1071InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1071LowerChecked :
    lowerCheck 24 leaf1071Box leaf1071Inputs = true := by
  rfl'

private theorem leaf1071CoversExact : CoversExact 8
    leaf1071Box leaf1071Certificate leaf1071InnerLog leaf1071Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk103RoundedFacts chi107RoundedFacts
    innerPair21RoundedFacts leaf1071RoundedFacts (by rfl)

private theorem leaf1071FlatSound : Sound leaf1071Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1071CertificateValid
    leaf1071InnerLogValid leaf1071CoversExact leaf1071LowerChecked

private noncomputable def leaf1072Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (87/32), kHi := (11/4), chiLo := (1/8), chiHi := (17/128) }

private noncomputable def leaf1072Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435665/268435456) }, vSqrt := { lower := (32765/32768), upper := (8388616/8388421) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (359623025/268435456) }, upper := { exponent := 0, mantissa := (699/512) } }, logOuter := sk104LogOuterCertificate, logK := sk104LogKCertificate, logChi := chi107LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (16777037/16776842) } }, logDArg := sk104LogDArgCertificate }

private noncomputable def leaf1072InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1072LocalValidity :
    LeafFacts leaf1072Box leaf1072Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1072Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8388616/8388421) }) = true
      norm_num [leaf1072Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1072CertificateValid :
    WideCertificateValid leaf1072Box leaf1072Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk104ValidityFacts chi107ValidityFacts
    leaf1072LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1072CoverageChecked :
    coverageCheck (innerAD leaf1072Box) leaf1072InnerLog = true := by
  rfl'

private theorem leaf1072InnerLogValid :
    leaf1072InnerLog.Valid 8 (innerAD leaf1072Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1072CoverageChecked

private noncomputable def leaf1072InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907319/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1072InputLogOnePlusV_eq :
    leaf1072InputLogOnePlusV = outerEnclosure 24
      (leaf1072Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1072RoundedFacts : LeafRoundedFacts 8
    leaf1072Certificate.logOnePlusV leaf1072InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1072InputLogOnePlusV_eq }

private noncomputable def leaf1072Inputs : Inputs :=
  inputsOfCaches globalInput sk104RoundedInputs
    chi107InputQChi innerPair21Input
    leaf1072InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1072LowerChecked :
    lowerCheck 24 leaf1072Box leaf1072Inputs = true := by
  rfl'

private theorem leaf1072CoversExact : CoversExact 8
    leaf1072Box leaf1072Certificate leaf1072InnerLog leaf1072Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk104RoundedFacts chi107RoundedFacts
    innerPair21RoundedFacts leaf1072RoundedFacts (by rfl)

private theorem leaf1072FlatSound : Sound leaf1072Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1072CertificateValid
    leaf1072InnerLogValid leaf1072CoversExact leaf1072LowerChecked

private noncomputable def leaf1073Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (87/32), chiLo := (17/128), chiHi := (9/64) }

private noncomputable def leaf1073Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435665/268435456) }, vSqrt := { lower := (32765/32768), upper := (33554464/33553649) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (364210265/268435456) }, upper := { exponent := 0, mantissa := (2831/2048) } }, logOuter := sk103LogOuterCertificate, logK := sk103LogKCertificate, logChi := chi108LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (67108113/67107298) } }, logDArg := sk103LogDArgCertificate }

private noncomputable def leaf1073InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf1073LocalValidity :
    LeafFacts leaf1073Box leaf1073Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1073Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (33554464/33553649) }) = true
      norm_num [leaf1073Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1073CertificateValid :
    WideCertificateValid leaf1073Box leaf1073Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk103ValidityFacts chi108ValidityFacts
    leaf1073LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1073CoverageChecked :
    coverageCheck (innerAD leaf1073Box) leaf1073InnerLog = true := by
  rfl'

private theorem leaf1073InnerLogValid :
    leaf1073InnerLog.Valid 8 (innerAD leaf1073Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf1073CoverageChecked

private noncomputable def leaf1073InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907321/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1073InputLogOnePlusV_eq :
    leaf1073InputLogOnePlusV = outerEnclosure 24
      (leaf1073Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1073RoundedFacts : LeafRoundedFacts 8
    leaf1073Certificate.logOnePlusV leaf1073InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1073InputLogOnePlusV_eq }

private noncomputable def leaf1073Inputs : Inputs :=
  inputsOfCaches globalInput sk103RoundedInputs
    chi108InputQChi innerPair22Input
    leaf1073InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1073LowerChecked :
    lowerCheck 24 leaf1073Box leaf1073Inputs = true := by
  rfl'

private theorem leaf1073CoversExact : CoversExact 8
    leaf1073Box leaf1073Certificate leaf1073InnerLog leaf1073Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk103RoundedFacts chi108RoundedFacts
    innerPair22RoundedFacts leaf1073RoundedFacts (by rfl)

private theorem leaf1073FlatSound : Sound leaf1073Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1073CertificateValid
    leaf1073InnerLogValid leaf1073CoversExact leaf1073LowerChecked

private noncomputable def leaf1074Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (87/32), kHi := (11/4), chiLo := (17/128), chiHi := (9/64) }

private noncomputable def leaf1074Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435667/268435456) }, vSqrt := { lower := (32765/32768), upper := (4194308/4194205) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (365324307/268435456) }, upper := { exponent := 0, mantissa := (355/256) } }, logOuter := sk104LogOuterCertificate, logK := sk104LogKCertificate, logChi := chi108LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (8388513/8388410) } }, logDArg := sk104LogDArgCertificate }

private noncomputable def leaf1074InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf1074LocalValidity :
    LeafFacts leaf1074Box leaf1074Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1074Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4194308/4194205) }) = true
      norm_num [leaf1074Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1074CertificateValid :
    WideCertificateValid leaf1074Box leaf1074Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk104ValidityFacts chi108ValidityFacts
    leaf1074LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1074CoverageChecked :
    coverageCheck (innerAD leaf1074Box) leaf1074InnerLog = true := by
  rfl'

private theorem leaf1074InnerLogValid :
    leaf1074InnerLog.Valid 8 (innerAD leaf1074Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf1074CoverageChecked

private noncomputable def leaf1074InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629287/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1074InputLogOnePlusV_eq :
    leaf1074InputLogOnePlusV = outerEnclosure 24
      (leaf1074Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1074RoundedFacts : LeafRoundedFacts 8
    leaf1074Certificate.logOnePlusV leaf1074InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1074InputLogOnePlusV_eq }

private noncomputable def leaf1074Inputs : Inputs :=
  inputsOfCaches globalInput sk104RoundedInputs
    chi108InputQChi innerPair22Input
    leaf1074InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1074LowerChecked :
    lowerCheck 24 leaf1074Box leaf1074Inputs = true := by
  rfl'

private theorem leaf1074CoversExact : CoversExact 8
    leaf1074Box leaf1074Certificate leaf1074InnerLog leaf1074Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk104RoundedFacts chi108RoundedFacts
    innerPair22RoundedFacts leaf1074RoundedFacts (by rfl)

private theorem leaf1074FlatSound : Sound leaf1074Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1074CertificateValid
    leaf1074InnerLogValid leaf1074CoversExact leaf1074LowerChecked

private noncomputable def leaf1075Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (85/32), chiLo := (9/64), chiHi := (19/128) }

private noncomputable def leaf1075Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435663/268435456) }, vSqrt := { lower := (32765/32768), upper := (67108928/67107249) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (367486867/268435456) }, upper := { exponent := 0, mantissa := (5711/4096) } }, logOuter := sk105LogOuterCertificate, logK := sk105LogKCertificate, logChi := chi109LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (134216177/134214498) } }, logDArg := sk105LogDArgCertificate }

private noncomputable def leaf1075InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf1075LocalValidity :
    LeafFacts leaf1075Box leaf1075Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1075Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (67108928/67107249) }) = true
      norm_num [leaf1075Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1075CertificateValid :
    WideCertificateValid leaf1075Box leaf1075Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk105ValidityFacts chi109ValidityFacts
    leaf1075LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1075CoverageChecked :
    coverageCheck (innerAD leaf1075Box) leaf1075InnerLog = true := by
  rfl'

private theorem leaf1075InnerLogValid :
    leaf1075InnerLog.Valid 8 (innerAD leaf1075Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf1075CoverageChecked

private noncomputable def leaf1075InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629291/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1075InputLogOnePlusV_eq :
    leaf1075InputLogOnePlusV = outerEnclosure 24
      (leaf1075Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1075RoundedFacts : LeafRoundedFacts 8
    leaf1075Certificate.logOnePlusV leaf1075InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1075InputLogOnePlusV_eq }

private noncomputable def leaf1075Inputs : Inputs :=
  inputsOfCaches globalInput sk105RoundedInputs
    chi109InputQChi innerPair22Input
    leaf1075InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1075LowerChecked :
    lowerCheck 24 leaf1075Box leaf1075Inputs = true := by
  rfl'

private theorem leaf1075CoversExact : CoversExact 8
    leaf1075Box leaf1075Certificate leaf1075InnerLog leaf1075Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk105RoundedFacts chi109RoundedFacts
    innerPair22RoundedFacts leaf1075RoundedFacts (by rfl)

private theorem leaf1075FlatSound : Sound leaf1075Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1075CertificateValid
    leaf1075InnerLogValid leaf1075CoversExact leaf1075LowerChecked

private noncomputable def leaf1076Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (85/32), kHi := (43/16), chiLo := (9/64), chiHi := (19/128) }

private noncomputable def leaf1076Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435665/268435456) }, vSqrt := { lower := (32765/32768), upper := (33554464/33553615) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (368666441/268435456) }, upper := { exponent := 0, mantissa := (2865/2048) } }, logOuter := sk106LogOuterCertificate, logK := sk106LogKCertificate, logChi := chi109LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (67108079/67107230) } }, logDArg := sk106LogDArgCertificate }

private noncomputable def leaf1076InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf1076LocalValidity :
    LeafFacts leaf1076Box leaf1076Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1076Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (33554464/33553615) }) = true
      norm_num [leaf1076Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1076CertificateValid :
    WideCertificateValid leaf1076Box leaf1076Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk106ValidityFacts chi109ValidityFacts
    leaf1076LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1076CoverageChecked :
    coverageCheck (innerAD leaf1076Box) leaf1076InnerLog = true := by
  rfl'

private theorem leaf1076InnerLogValid :
    leaf1076InnerLog.Valid 8 (innerAD leaf1076Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf1076CoverageChecked

private noncomputable def leaf1076InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629293/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1076InputLogOnePlusV_eq :
    leaf1076InputLogOnePlusV = outerEnclosure 24
      (leaf1076Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1076RoundedFacts : LeafRoundedFacts 8
    leaf1076Certificate.logOnePlusV leaf1076InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1076InputLogOnePlusV_eq }

private noncomputable def leaf1076Inputs : Inputs :=
  inputsOfCaches globalInput sk106RoundedInputs
    chi109InputQChi innerPair22Input
    leaf1076InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1076LowerChecked :
    lowerCheck 24 leaf1076Box leaf1076Inputs = true := by
  rfl'

private theorem leaf1076CoversExact : CoversExact 8
    leaf1076Box leaf1076Certificate leaf1076InnerLog leaf1076Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk106RoundedFacts chi109RoundedFacts
    innerPair22RoundedFacts leaf1076RoundedFacts (by rfl)

private theorem leaf1076FlatSound : Sound leaf1076Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1076CertificateValid
    leaf1076InnerLogValid leaf1076CoversExact leaf1076LowerChecked

private noncomputable def leaf1077Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (85/32), chiLo := (19/128), chiHi := (5/32) }

private noncomputable def leaf1077Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435665/268435456) }, vSqrt := { lower := (32765/32768), upper := (16777232/16776791) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (372991553/268435456) }, upper := { exponent := 0, mantissa := (1449/1024) } }, logOuter := sk105LogOuterCertificate, logK := sk105LogKCertificate, logChi := chi110LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (33554023/33553582) } }, logDArg := sk105LogDArgCertificate }

private noncomputable def leaf1077InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1077LocalValidity :
    LeafFacts leaf1077Box leaf1077Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1077Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (16777232/16776791) }) = true
      norm_num [leaf1077Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1077CertificateValid :
    WideCertificateValid leaf1077Box leaf1077Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk105ValidityFacts chi110ValidityFacts
    leaf1077LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1077CoverageChecked :
    coverageCheck (innerAD leaf1077Box) leaf1077InnerLog = true := by
  rfl'

private theorem leaf1077InnerLogValid :
    leaf1077InnerLog.Valid 8 (innerAD leaf1077Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1077CoverageChecked

private noncomputable def leaf1077InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629301/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1077InputLogOnePlusV_eq :
    leaf1077InputLogOnePlusV = outerEnclosure 24
      (leaf1077Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1077RoundedFacts : LeafRoundedFacts 8
    leaf1077Certificate.logOnePlusV leaf1077InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1077InputLogOnePlusV_eq }

private noncomputable def leaf1077Inputs : Inputs :=
  inputsOfCaches globalInput sk105RoundedInputs
    chi110InputQChi innerPair26Input
    leaf1077InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1077LowerChecked :
    lowerCheck 24 leaf1077Box leaf1077Inputs = true := by
  rfl'

private theorem leaf1077CoversExact : CoversExact 8
    leaf1077Box leaf1077Certificate leaf1077InnerLog leaf1077Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk105RoundedFacts chi110RoundedFacts
    innerPair26RoundedFacts leaf1077RoundedFacts (by rfl)

private theorem leaf1077FlatSound : Sound leaf1077Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1077CertificateValid
    leaf1077InnerLogValid leaf1077CoversExact leaf1077LowerChecked

private noncomputable def leaf1078Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (85/32), kHi := (43/16), chiLo := (19/128), chiHi := (5/32) }

private noncomputable def leaf1078Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435667/268435456) }, vSqrt := { lower := (32765/32768), upper := (8388616/8388393) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (374236659/268435456) }, upper := { exponent := 0, mantissa := (727/512) } }, logOuter := sk106LogOuterCertificate, logK := sk106LogKCertificate, logChi := chi110LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (16777009/16776786) } }, logDArg := sk106LogDArgCertificate }

private noncomputable def leaf1078InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1078LocalValidity :
    LeafFacts leaf1078Box leaf1078Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1078Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8388616/8388393) }) = true
      norm_num [leaf1078Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1078CertificateValid :
    WideCertificateValid leaf1078Box leaf1078Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk106ValidityFacts chi110ValidityFacts
    leaf1078LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1078CoverageChecked :
    coverageCheck (innerAD leaf1078Box) leaf1078InnerLog = true := by
  rfl'

private theorem leaf1078InnerLogValid :
    leaf1078InnerLog.Valid 8 (innerAD leaf1078Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1078CoverageChecked

private noncomputable def leaf1078InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (1453663/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf1078InputLogOnePlusV_eq :
    leaf1078InputLogOnePlusV = outerEnclosure 24
      (leaf1078Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1078RoundedFacts : LeafRoundedFacts 8
    leaf1078Certificate.logOnePlusV leaf1078InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1078InputLogOnePlusV_eq }

private noncomputable def leaf1078Inputs : Inputs :=
  inputsOfCaches globalInput sk106RoundedInputs
    chi110InputQChi innerPair26Input
    leaf1078InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1078LowerChecked :
    lowerCheck 24 leaf1078Box leaf1078Inputs = true := by
  rfl'

private theorem leaf1078CoversExact : CoversExact 8
    leaf1078Box leaf1078Certificate leaf1078InnerLog leaf1078Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk106RoundedFacts chi110RoundedFacts
    innerPair26RoundedFacts leaf1078RoundedFacts (by rfl)

private theorem leaf1078FlatSound : Sound leaf1078Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1078CertificateValid
    leaf1078InnerLogValid leaf1078CoversExact leaf1078LowerChecked

private noncomputable def leaf1079Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (87/32), chiLo := (9/64), chiHi := (19/128) }

private noncomputable def leaf1079Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435667/268435456) }, vSqrt := { lower := (32765/32768), upper := (3947584/3947483) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (369846015/268435456) }, upper := { exponent := 0, mantissa := (5749/4096) } }, logOuter := sk103LogOuterCertificate, logK := sk103LogKCertificate, logChi := chi109LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (7895067/7894966) } }, logDArg := sk103LogDArgCertificate }

private noncomputable def leaf1079InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1079LocalValidity :
    LeafFacts leaf1079Box leaf1079Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1079Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (3947584/3947483) }) = true
      norm_num [leaf1079Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1079CertificateValid :
    WideCertificateValid leaf1079Box leaf1079Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk103ValidityFacts chi109ValidityFacts
    leaf1079LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1079CoverageChecked :
    coverageCheck (innerAD leaf1079Box) leaf1079InnerLog = true := by
  rfl'

private theorem leaf1079InnerLogValid :
    leaf1079InnerLog.Valid 8 (innerAD leaf1079Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1079CoverageChecked

private noncomputable def leaf1079InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629295/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1079InputLogOnePlusV_eq :
    leaf1079InputLogOnePlusV = outerEnclosure 24
      (leaf1079Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1079RoundedFacts : LeafRoundedFacts 8
    leaf1079Certificate.logOnePlusV leaf1079InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1079InputLogOnePlusV_eq }

private noncomputable def leaf1079Inputs : Inputs :=
  inputsOfCaches globalInput sk103RoundedInputs
    chi109InputQChi innerPair26Input
    leaf1079InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1079LowerChecked :
    lowerCheck 24 leaf1079Box leaf1079Inputs = true := by
  rfl'

private theorem leaf1079CoversExact : CoversExact 8
    leaf1079Box leaf1079Certificate leaf1079InnerLog leaf1079Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk103RoundedFacts chi109RoundedFacts
    innerPair26RoundedFacts leaf1079RoundedFacts (by rfl)

private theorem leaf1079FlatSound : Sound leaf1079Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1079CertificateValid
    leaf1079InnerLogValid leaf1079CoversExact leaf1079LowerChecked

private noncomputable def leaf1080Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (87/32), kHi := (11/4), chiLo := (9/64), chiHi := (19/128) }

private noncomputable def leaf1080Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435669/268435456) }, vSqrt := { lower := (32765/32768), upper := (8388616/8388399) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (371025589/268435456) }, upper := { exponent := 0, mantissa := (721/512) } }, logOuter := sk104LogOuterCertificate, logK := sk104LogKCertificate, logChi := chi109LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (16777015/16776798) } }, logDArg := sk104LogDArgCertificate }

private noncomputable def leaf1080InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1080LocalValidity :
    LeafFacts leaf1080Box leaf1080Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1080Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8388616/8388399) }) = true
      norm_num [leaf1080Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1080CertificateValid :
    WideCertificateValid leaf1080Box leaf1080Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk104ValidityFacts chi109ValidityFacts
    leaf1080LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1080CoverageChecked :
    coverageCheck (innerAD leaf1080Box) leaf1080InnerLog = true := by
  rfl'

private theorem leaf1080InnerLogValid :
    leaf1080InnerLog.Valid 8 (innerAD leaf1080Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1080CoverageChecked

private noncomputable def leaf1080InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814649/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1080InputLogOnePlusV_eq :
    leaf1080InputLogOnePlusV = outerEnclosure 24
      (leaf1080Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1080RoundedFacts : LeafRoundedFacts 8
    leaf1080Certificate.logOnePlusV leaf1080InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1080InputLogOnePlusV_eq }

private noncomputable def leaf1080Inputs : Inputs :=
  inputsOfCaches globalInput sk104RoundedInputs
    chi109InputQChi innerPair26Input
    leaf1080InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1080LowerChecked :
    lowerCheck 24 leaf1080Box leaf1080Inputs = true := by
  rfl'

private theorem leaf1080CoversExact : CoversExact 8
    leaf1080Box leaf1080Certificate leaf1080InnerLog leaf1080Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk104RoundedFacts chi109RoundedFacts
    innerPair26RoundedFacts leaf1080RoundedFacts (by rfl)

private theorem leaf1080FlatSound : Sound leaf1080Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1080CertificateValid
    leaf1080InnerLogValid leaf1080CoversExact leaf1080LowerChecked

private noncomputable def leaf1081Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (87/32), chiLo := (19/128), chiHi := (5/32) }

private noncomputable def leaf1081Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435669/268435456) }, vSqrt := { lower := (32765/32768), upper := (16777232/16776781) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (375481765/268435456) }, upper := { exponent := 0, mantissa := (1459/1024) } }, logOuter := sk103LogOuterCertificate, logK := sk103LogKCertificate, logChi := chi110LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (33554013/33553562) } }, logDArg := sk103LogDArgCertificate }

private noncomputable def leaf1081InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1081LocalValidity :
    LeafFacts leaf1081Box leaf1081Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1081Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (16777232/16776781) }) = true
      norm_num [leaf1081Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1081CertificateValid :
    WideCertificateValid leaf1081Box leaf1081Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk103ValidityFacts chi110ValidityFacts
    leaf1081LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1081CoverageChecked :
    coverageCheck (innerAD leaf1081Box) leaf1081InnerLog = true := by
  rfl'

private theorem leaf1081InnerLogValid :
    leaf1081InnerLog.Valid 8 (innerAD leaf1081Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1081CoverageChecked

private noncomputable def leaf1081InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814653/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1081InputLogOnePlusV_eq :
    leaf1081InputLogOnePlusV = outerEnclosure 24
      (leaf1081Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1081RoundedFacts : LeafRoundedFacts 8
    leaf1081Certificate.logOnePlusV leaf1081InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1081InputLogOnePlusV_eq }

private noncomputable def leaf1081Inputs : Inputs :=
  inputsOfCaches globalInput sk103RoundedInputs
    chi110InputQChi innerPair26Input
    leaf1081InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1081LowerChecked :
    lowerCheck 24 leaf1081Box leaf1081Inputs = true := by
  rfl'

private theorem leaf1081CoversExact : CoversExact 8
    leaf1081Box leaf1081Certificate leaf1081InnerLog leaf1081Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk103RoundedFacts chi110RoundedFacts
    innerPair26RoundedFacts leaf1081RoundedFacts (by rfl)

private theorem leaf1081FlatSound : Sound leaf1081Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1081CertificateValid
    leaf1081InnerLogValid leaf1081CoversExact leaf1081LowerChecked

private noncomputable def leaf1082Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (87/32), kHi := (11/4), chiLo := (19/128), chiHi := (5/32) }

private noncomputable def leaf1082Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435671/268435456) }, vSqrt := { lower := (32765/32768), upper := (2097154/2097097) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (376726871/268435456) }, upper := { exponent := 0, mantissa := (183/128) } }, logOuter := sk104LogOuterCertificate, logK := sk104LogKCertificate, logChi := chi110LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (4194251/4194194) } }, logDArg := sk104LogDArgCertificate }

private noncomputable def leaf1082InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1082LocalValidity :
    LeafFacts leaf1082Box leaf1082Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1082Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (2097154/2097097) }) = true
      norm_num [leaf1082Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1082CertificateValid :
    WideCertificateValid leaf1082Box leaf1082Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk104ValidityFacts chi110ValidityFacts
    leaf1082LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1082CoverageChecked :
    coverageCheck (innerAD leaf1082Box) leaf1082InnerLog = true := by
  rfl'

private theorem leaf1082InnerLogValid :
    leaf1082InnerLog.Valid 8 (innerAD leaf1082Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1082CoverageChecked

private noncomputable def leaf1082InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629309/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1082InputLogOnePlusV_eq :
    leaf1082InputLogOnePlusV = outerEnclosure 24
      (leaf1082Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1082RoundedFacts : LeafRoundedFacts 8
    leaf1082Certificate.logOnePlusV leaf1082InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1082InputLogOnePlusV_eq }

private noncomputable def leaf1082Inputs : Inputs :=
  inputsOfCaches globalInput sk104RoundedInputs
    chi110InputQChi innerPair26Input
    leaf1082InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1082LowerChecked :
    lowerCheck 24 leaf1082Box leaf1082Inputs = true := by
  rfl'

private theorem leaf1082CoversExact : CoversExact 8
    leaf1082Box leaf1082Certificate leaf1082InnerLog leaf1082Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk104RoundedFacts chi110RoundedFacts
    innerPair26RoundedFacts leaf1082RoundedFacts (by rfl)

private theorem leaf1082FlatSound : Sound leaf1082Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1082CertificateValid
    leaf1082InnerLogValid leaf1082CoversExact leaf1082LowerChecked

private noncomputable def leaf1083Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (81/32), chiLo := (5/32), chiHi := (21/128) }

private noncomputable def leaf1083Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435659/268435456) }, vSqrt := { lower := (32765/32768), upper := (67108928/67107163) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (373253687/268435456) }, upper := { exponent := 0, mantissa := (5797/4096) } }, logOuter := sk99LogOuterCertificate, logK := sk99LogKCertificate, logChi := chi111LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (134216091/134214326) } }, logDArg := sk99LogDArgCertificate }

private noncomputable def leaf1083InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1083LocalValidity :
    LeafFacts leaf1083Box leaf1083Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1083Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (67108928/67107163) }) = true
      norm_num [leaf1083Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1083CertificateValid :
    WideCertificateValid leaf1083Box leaf1083Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk99ValidityFacts chi111ValidityFacts
    leaf1083LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1083CoverageChecked :
    coverageCheck (innerAD leaf1083Box) leaf1083InnerLog = true := by
  rfl'

private theorem leaf1083InnerLogValid :
    leaf1083InnerLog.Valid 8 (innerAD leaf1083Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1083CoverageChecked

private noncomputable def leaf1083InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629301/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1083InputLogOnePlusV_eq :
    leaf1083InputLogOnePlusV = outerEnclosure 24
      (leaf1083Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1083RoundedFacts : LeafRoundedFacts 8
    leaf1083Certificate.logOnePlusV leaf1083InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1083InputLogOnePlusV_eq }

private noncomputable def leaf1083Inputs : Inputs :=
  inputsOfCaches globalInput sk99RoundedInputs
    chi111InputQChi innerPair26Input
    leaf1083InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1083LowerChecked :
    lowerCheck 24 leaf1083Box leaf1083Inputs = true := by
  rfl'

private theorem leaf1083CoversExact : CoversExact 8
    leaf1083Box leaf1083Certificate leaf1083InnerLog leaf1083Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk99RoundedFacts chi111RoundedFacts
    innerPair26RoundedFacts leaf1083RoundedFacts (by rfl)

private theorem leaf1083FlatSound : Sound leaf1083Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1083CertificateValid
    leaf1083InnerLogValid leaf1083CoversExact leaf1083LowerChecked

private noncomputable def leaf1084Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (81/32), kHi := (41/16), chiLo := (5/32), chiHi := (21/128) }

private noncomputable def leaf1084Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435661/268435456) }, vSqrt := { lower := (32765/32768), upper := (33554464/33553571) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (374564325/268435456) }, upper := { exponent := 0, mantissa := (2909/2048) } }, logOuter := sk100LogOuterCertificate, logK := sk100LogKCertificate, logChi := chi111LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (67108035/67107142) } }, logDArg := sk100LogDArgCertificate }

private noncomputable def leaf1084InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1084LocalValidity :
    LeafFacts leaf1084Box leaf1084Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1084Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (33554464/33553571) }) = true
      norm_num [leaf1084Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1084CertificateValid :
    WideCertificateValid leaf1084Box leaf1084Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk100ValidityFacts chi111ValidityFacts
    leaf1084LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1084CoverageChecked :
    coverageCheck (innerAD leaf1084Box) leaf1084InnerLog = true := by
  rfl'

private theorem leaf1084InnerLogValid :
    leaf1084InnerLog.Valid 8 (innerAD leaf1084Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1084CoverageChecked

private noncomputable def leaf1084InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (1453663/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf1084InputLogOnePlusV_eq :
    leaf1084InputLogOnePlusV = outerEnclosure 24
      (leaf1084Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1084RoundedFacts : LeafRoundedFacts 8
    leaf1084Certificate.logOnePlusV leaf1084InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1084InputLogOnePlusV_eq }

private noncomputable def leaf1084Inputs : Inputs :=
  inputsOfCaches globalInput sk100RoundedInputs
    chi111InputQChi innerPair26Input
    leaf1084InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1084LowerChecked :
    lowerCheck 24 leaf1084Box leaf1084Inputs = true := by
  rfl'

private theorem leaf1084CoversExact : CoversExact 8
    leaf1084Box leaf1084Certificate leaf1084InnerLog leaf1084Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk100RoundedFacts chi111RoundedFacts
    innerPair26RoundedFacts leaf1084RoundedFacts (by rfl)

private theorem leaf1084FlatSound : Sound leaf1084Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1084CertificateValid
    leaf1084InnerLogValid leaf1084CoversExact leaf1084LowerChecked

private noncomputable def leaf1085Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (81/32), chiLo := (21/128), chiHi := (11/64) }

private noncomputable def leaf1085Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435661/268435456) }, vSqrt := { lower := (32765/32768), upper := (33554464/33553541) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (378496245/268435456) }, upper := { exponent := 0, mantissa := (2939/2048) } }, logOuter := sk99LogOuterCertificate, logK := sk99LogKCertificate, logChi := chi112LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (67108005/67107082) } }, logDArg := sk99LogDArgCertificate }

private noncomputable def leaf1085InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1085LocalValidity :
    LeafFacts leaf1085Box leaf1085Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1085Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (33554464/33553541) }) = true
      norm_num [leaf1085Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1085CertificateValid :
    WideCertificateValid leaf1085Box leaf1085Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk99ValidityFacts chi112ValidityFacts
    leaf1085LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1085CoverageChecked :
    coverageCheck (innerAD leaf1085Box) leaf1085InnerLog = true := by
  rfl'

private theorem leaf1085InnerLogValid :
    leaf1085InnerLog.Valid 8 (innerAD leaf1085Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1085CoverageChecked

private noncomputable def leaf1085InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629311/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1085InputLogOnePlusV_eq :
    leaf1085InputLogOnePlusV = outerEnclosure 24
      (leaf1085Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1085RoundedFacts : LeafRoundedFacts 8
    leaf1085Certificate.logOnePlusV leaf1085InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1085InputLogOnePlusV_eq }

private noncomputable def leaf1085Inputs : Inputs :=
  inputsOfCaches globalInput sk99RoundedInputs
    chi112InputQChi innerPair26Input
    leaf1085InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1085LowerChecked :
    lowerCheck 24 leaf1085Box leaf1085Inputs = true := by
  rfl'

private theorem leaf1085CoversExact : CoversExact 8
    leaf1085Box leaf1085Certificate leaf1085InnerLog leaf1085Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk99RoundedFacts chi112RoundedFacts
    innerPair26RoundedFacts leaf1085RoundedFacts (by rfl)

private theorem leaf1085FlatSound : Sound leaf1085Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1085CertificateValid
    leaf1085InnerLogValid leaf1085CoversExact leaf1085LowerChecked

private noncomputable def leaf1086Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (81/32), kHi := (41/16), chiLo := (21/128), chiHi := (11/64) }

private noncomputable def leaf1086Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435663/268435456) }, vSqrt := { lower := (32765/32768), upper := (16777232/16776765) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (379872415/268435456) }, upper := { exponent := 0, mantissa := (1475/1024) } }, logOuter := sk100LogOuterCertificate, logK := sk100LogKCertificate, logChi := chi112LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (33553997/33553530) } }, logDArg := sk100LogDArgCertificate }

private noncomputable def leaf1086InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf1086LocalValidity :
    LeafFacts leaf1086Box leaf1086Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1086Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (16777232/16776765) }) = true
      norm_num [leaf1086Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1086CertificateValid :
    WideCertificateValid leaf1086Box leaf1086Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk100ValidityFacts chi112ValidityFacts
    leaf1086LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1086CoverageChecked :
    coverageCheck (innerAD leaf1086Box) leaf1086InnerLog = true := by
  rfl'

private theorem leaf1086InnerLogValid :
    leaf1086InnerLog.Valid 8 (innerAD leaf1086Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf1086CoverageChecked

private noncomputable def leaf1086InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814657/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1086InputLogOnePlusV_eq :
    leaf1086InputLogOnePlusV = outerEnclosure 24
      (leaf1086Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1086RoundedFacts : LeafRoundedFacts 8
    leaf1086Certificate.logOnePlusV leaf1086InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1086InputLogOnePlusV_eq }

private noncomputable def leaf1086Inputs : Inputs :=
  inputsOfCaches globalInput sk100RoundedInputs
    chi112InputQChi innerPair27Input
    leaf1086InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1086LowerChecked :
    lowerCheck 24 leaf1086Box leaf1086Inputs = true := by
  rfl'

private theorem leaf1086CoversExact : CoversExact 8
    leaf1086Box leaf1086Certificate leaf1086InnerLog leaf1086Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk100RoundedFacts chi112RoundedFacts
    innerPair27RoundedFacts leaf1086RoundedFacts (by rfl)

private theorem leaf1086FlatSound : Sound leaf1086Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1086CertificateValid
    leaf1086InnerLogValid leaf1086CoversExact leaf1086LowerChecked

private noncomputable def leaf1087Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (83/32), chiLo := (5/32), chiHi := (21/128) }

private noncomputable def leaf1087Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435663/268435456) }, vSqrt := { lower := (32765/32768), upper := (67108928/67107121) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (375874963/268435456) }, upper := { exponent := 0, mantissa := (5839/4096) } }, logOuter := sk101LogOuterCertificate, logK := sk101LogKCertificate, logChi := chi111LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (134216049/134214242) } }, logDArg := sk101LogDArgCertificate }

private noncomputable def leaf1087InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1087LocalValidity :
    LeafFacts leaf1087Box leaf1087Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1087Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (67108928/67107121) }) = true
      norm_num [leaf1087Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1087CertificateValid :
    WideCertificateValid leaf1087Box leaf1087Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk101ValidityFacts chi111ValidityFacts
    leaf1087LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1087CoverageChecked :
    coverageCheck (innerAD leaf1087Box) leaf1087InnerLog = true := by
  rfl'

private theorem leaf1087InnerLogValid :
    leaf1087InnerLog.Valid 8 (innerAD leaf1087Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1087CoverageChecked

private noncomputable def leaf1087InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629307/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1087InputLogOnePlusV_eq :
    leaf1087InputLogOnePlusV = outerEnclosure 24
      (leaf1087Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1087RoundedFacts : LeafRoundedFacts 8
    leaf1087Certificate.logOnePlusV leaf1087InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1087InputLogOnePlusV_eq }

private noncomputable def leaf1087Inputs : Inputs :=
  inputsOfCaches globalInput sk101RoundedInputs
    chi111InputQChi innerPair26Input
    leaf1087InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1087LowerChecked :
    lowerCheck 24 leaf1087Box leaf1087Inputs = true := by
  rfl'

private theorem leaf1087CoversExact : CoversExact 8
    leaf1087Box leaf1087Certificate leaf1087InnerLog leaf1087Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk101RoundedFacts chi111RoundedFacts
    innerPair26RoundedFacts leaf1087RoundedFacts (by rfl)

private theorem leaf1087FlatSound : Sound leaf1087Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1087CertificateValid
    leaf1087InnerLogValid leaf1087CoversExact leaf1087LowerChecked

private noncomputable def leaf1088Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (83/32), kHi := (21/8), chiLo := (5/32), chiHi := (21/128) }

private noncomputable def leaf1088Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435665/268435456) }, vSqrt := { lower := (32765/32768), upper := (16777232/16776775) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (377185601/268435456) }, upper := { exponent := 0, mantissa := (1465/1024) } }, logOuter := sk102LogOuterCertificate, logK := sk102LogKCertificate, logChi := chi111LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (33554007/33553550) } }, logDArg := sk102LogDArgCertificate }

private noncomputable def leaf1088InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1088LocalValidity :
    LeafFacts leaf1088Box leaf1088Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1088Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (16777232/16776775) }) = true
      norm_num [leaf1088Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1088CertificateValid :
    WideCertificateValid leaf1088Box leaf1088Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk102ValidityFacts chi111ValidityFacts
    leaf1088LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1088CoverageChecked :
    coverageCheck (innerAD leaf1088Box) leaf1088InnerLog = true := by
  rfl'

private theorem leaf1088InnerLogValid :
    leaf1088InnerLog.Valid 8 (innerAD leaf1088Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1088CoverageChecked

private noncomputable def leaf1088InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629309/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1088InputLogOnePlusV_eq :
    leaf1088InputLogOnePlusV = outerEnclosure 24
      (leaf1088Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1088RoundedFacts : LeafRoundedFacts 8
    leaf1088Certificate.logOnePlusV leaf1088InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1088InputLogOnePlusV_eq }

private noncomputable def leaf1088Inputs : Inputs :=
  inputsOfCaches globalInput sk102RoundedInputs
    chi111InputQChi innerPair26Input
    leaf1088InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1088LowerChecked :
    lowerCheck 24 leaf1088Box leaf1088Inputs = true := by
  rfl'

private theorem leaf1088CoversExact : CoversExact 8
    leaf1088Box leaf1088Certificate leaf1088InnerLog leaf1088Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk102RoundedFacts chi111RoundedFacts
    innerPair26RoundedFacts leaf1088RoundedFacts (by rfl)

private theorem leaf1088FlatSound : Sound leaf1088Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1088CertificateValid
    leaf1088InnerLogValid leaf1088CoversExact leaf1088LowerChecked

private noncomputable def leaf1089Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (83/32), chiLo := (21/128), chiHi := (11/64) }

private noncomputable def leaf1089Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435665/268435456) }, vSqrt := { lower := (32765/32768), upper := (33554464/33553519) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (381248585/268435456) }, upper := { exponent := 0, mantissa := (2961/2048) } }, logOuter := sk101LogOuterCertificate, logK := sk101LogKCertificate, logChi := chi112LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (67107983/67107038) } }, logDArg := sk101LogDArgCertificate }

private noncomputable def leaf1089InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf1089LocalValidity :
    LeafFacts leaf1089Box leaf1089Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1089Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (33554464/33553519) }) = true
      norm_num [leaf1089Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1089CertificateValid :
    WideCertificateValid leaf1089Box leaf1089Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk101ValidityFacts chi112ValidityFacts
    leaf1089LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1089CoverageChecked :
    coverageCheck (innerAD leaf1089Box) leaf1089InnerLog = true := by
  rfl'

private theorem leaf1089InnerLogValid :
    leaf1089InnerLog.Valid 8 (innerAD leaf1089Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf1089CoverageChecked

private noncomputable def leaf1089InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629317/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1089InputLogOnePlusV_eq :
    leaf1089InputLogOnePlusV = outerEnclosure 24
      (leaf1089Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1089RoundedFacts : LeafRoundedFacts 8
    leaf1089Certificate.logOnePlusV leaf1089InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1089InputLogOnePlusV_eq }

private noncomputable def leaf1089Inputs : Inputs :=
  inputsOfCaches globalInput sk101RoundedInputs
    chi112InputQChi innerPair27Input
    leaf1089InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1089LowerChecked :
    lowerCheck 24 leaf1089Box leaf1089Inputs = true := by
  rfl'

private theorem leaf1089CoversExact : CoversExact 8
    leaf1089Box leaf1089Certificate leaf1089InnerLog leaf1089Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk101RoundedFacts chi112RoundedFacts
    innerPair27RoundedFacts leaf1089RoundedFacts (by rfl)

private theorem leaf1089FlatSound : Sound leaf1089Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1089CertificateValid
    leaf1089InnerLogValid leaf1089CoversExact leaf1089LowerChecked

private noncomputable def leaf1090Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (83/32), kHi := (21/8), chiLo := (21/128), chiHi := (11/64) }

private noncomputable def leaf1090Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435667/268435456) }, vSqrt := { lower := (32765/32768), upper := (8388616/8388377) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (382624755/268435456) }, upper := { exponent := 0, mantissa := (743/512) } }, logOuter := sk102LogOuterCertificate, logK := sk102LogKCertificate, logChi := chi112LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (16776993/16776754) } }, logDArg := sk102LogDArgCertificate }

private noncomputable def leaf1090InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf1090LocalValidity :
    LeafFacts leaf1090Box leaf1090Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1090Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8388616/8388377) }) = true
      norm_num [leaf1090Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1090CertificateValid :
    WideCertificateValid leaf1090Box leaf1090Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk102ValidityFacts chi112ValidityFacts
    leaf1090LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1090CoverageChecked :
    coverageCheck (innerAD leaf1090Box) leaf1090InnerLog = true := by
  rfl'

private theorem leaf1090InnerLogValid :
    leaf1090InnerLog.Valid 8 (innerAD leaf1090Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf1090CoverageChecked

private noncomputable def leaf1090InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (1453665/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf1090InputLogOnePlusV_eq :
    leaf1090InputLogOnePlusV = outerEnclosure 24
      (leaf1090Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1090RoundedFacts : LeafRoundedFacts 8
    leaf1090Certificate.logOnePlusV leaf1090InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1090InputLogOnePlusV_eq }

private noncomputable def leaf1090Inputs : Inputs :=
  inputsOfCaches globalInput sk102RoundedInputs
    chi112InputQChi innerPair27Input
    leaf1090InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1090LowerChecked :
    lowerCheck 24 leaf1090Box leaf1090Inputs = true := by
  rfl'

private theorem leaf1090CoversExact : CoversExact 8
    leaf1090Box leaf1090Certificate leaf1090InnerLog leaf1090Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk102RoundedFacts chi112RoundedFacts
    innerPair27RoundedFacts leaf1090RoundedFacts (by rfl)

private theorem leaf1090FlatSound : Sound leaf1090Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1090CertificateValid
    leaf1090InnerLogValid leaf1090CoversExact leaf1090LowerChecked

private noncomputable def leaf1091Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (81/32), chiLo := (11/64), chiHi := (23/128) }

private noncomputable def leaf1091Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435663/268435456) }, vSqrt := { lower := (32765/32768), upper := (67108928/67107001) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (383738803/268435456) }, upper := { exponent := 0, mantissa := (5959/4096) } }, logOuter := sk99LogOuterCertificate, logK := sk99LogKCertificate, logChi := chi113LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (134215929/134214002) } }, logDArg := sk99LogDArgCertificate }

private noncomputable def leaf1091InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf1091LocalValidity :
    LeafFacts leaf1091Box leaf1091Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1091Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (67108928/67107001) }) = true
      norm_num [leaf1091Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1091CertificateValid :
    WideCertificateValid leaf1091Box leaf1091Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk99ValidityFacts chi113ValidityFacts
    leaf1091LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1091CoverageChecked :
    coverageCheck (innerAD leaf1091Box) leaf1091InnerLog = true := by
  rfl'

private theorem leaf1091InnerLogValid :
    leaf1091InnerLog.Valid 8 (innerAD leaf1091Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf1091CoverageChecked

private noncomputable def leaf1091InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814661/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1091InputLogOnePlusV_eq :
    leaf1091InputLogOnePlusV = outerEnclosure 24
      (leaf1091Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1091RoundedFacts : LeafRoundedFacts 8
    leaf1091Certificate.logOnePlusV leaf1091InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1091InputLogOnePlusV_eq }

private noncomputable def leaf1091Inputs : Inputs :=
  inputsOfCaches globalInput sk99RoundedInputs
    chi113InputQChi innerPair27Input
    leaf1091InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1091LowerChecked :
    lowerCheck 24 leaf1091Box leaf1091Inputs = true := by
  rfl'

private theorem leaf1091CoversExact : CoversExact 8
    leaf1091Box leaf1091Certificate leaf1091InnerLog leaf1091Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk99RoundedFacts chi113RoundedFacts
    innerPair27RoundedFacts leaf1091RoundedFacts (by rfl)

private theorem leaf1091FlatSound : Sound leaf1091Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1091CertificateValid
    leaf1091InnerLogValid leaf1091CoversExact leaf1091LowerChecked

private noncomputable def leaf1092Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (81/32), chiLo := (23/128), chiHi := (3/16) }

private noncomputable def leaf1092Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435665/268435456) }, vSqrt := { lower := (32765/32768), upper := (8388616/8388365) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (388981361/268435456) }, upper := { exponent := 0, mantissa := (755/512) } }, logOuter := sk99LogOuterCertificate, logK := sk99LogKCertificate, logChi := chi114LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (16776981/16776730) } }, logDArg := sk99LogDArgCertificate }

private noncomputable def leaf1092InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1092LocalValidity :
    LeafFacts leaf1092Box leaf1092Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1092Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8388616/8388365) }) = true
      norm_num [leaf1092Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1092CertificateValid :
    WideCertificateValid leaf1092Box leaf1092Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk99ValidityFacts chi114ValidityFacts
    leaf1092LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1092CoverageChecked :
    coverageCheck (innerAD leaf1092Box) leaf1092InnerLog = true := by
  rfl'

private theorem leaf1092InnerLogValid :
    leaf1092InnerLog.Valid 8 (innerAD leaf1092Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1092CoverageChecked

private noncomputable def leaf1092InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907333/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1092InputLogOnePlusV_eq :
    leaf1092InputLogOnePlusV = outerEnclosure 24
      (leaf1092Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1092RoundedFacts : LeafRoundedFacts 8
    leaf1092Certificate.logOnePlusV leaf1092InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1092InputLogOnePlusV_eq }

private noncomputable def leaf1092Inputs : Inputs :=
  inputsOfCaches globalInput sk99RoundedInputs
    chi114InputQChi innerPair34Input
    leaf1092InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1092LowerChecked :
    lowerCheck 24 leaf1092Box leaf1092Inputs = true := by
  rfl'

private theorem leaf1092CoversExact : CoversExact 8
    leaf1092Box leaf1092Certificate leaf1092InnerLog leaf1092Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk99RoundedFacts chi114RoundedFacts
    innerPair34RoundedFacts leaf1092RoundedFacts (by rfl)

private theorem leaf1092FlatSound : Sound leaf1092Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1092CertificateValid
    leaf1092InnerLogValid leaf1092CoversExact leaf1092LowerChecked

private noncomputable def leaf1093Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (81/32), kHi := (41/16), chiLo := (11/64), chiHi := (23/128) }

private noncomputable def leaf1093Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435665/268435456) }, vSqrt := { lower := (32765/32768), upper := (33554464/33553489) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (385180505/268435456) }, upper := { exponent := 0, mantissa := (2991/2048) } }, logOuter := sk100LogOuterCertificate, logK := sk100LogKCertificate, logChi := chi113LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (67107953/67106978) } }, logDArg := sk100LogDArgCertificate }

private noncomputable def leaf1093InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf1093LocalValidity :
    LeafFacts leaf1093Box leaf1093Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1093Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (33554464/33553489) }) = true
      norm_num [leaf1093Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1093CertificateValid :
    WideCertificateValid leaf1093Box leaf1093Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk100ValidityFacts chi113ValidityFacts
    leaf1093LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1093CoverageChecked :
    coverageCheck (innerAD leaf1093Box) leaf1093InnerLog = true := by
  rfl'

private theorem leaf1093InnerLogValid :
    leaf1093InnerLog.Valid 8 (innerAD leaf1093Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf1093CoverageChecked

private noncomputable def leaf1093InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907331/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1093InputLogOnePlusV_eq :
    leaf1093InputLogOnePlusV = outerEnclosure 24
      (leaf1093Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1093RoundedFacts : LeafRoundedFacts 8
    leaf1093Certificate.logOnePlusV leaf1093InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1093InputLogOnePlusV_eq }

private noncomputable def leaf1093Inputs : Inputs :=
  inputsOfCaches globalInput sk100RoundedInputs
    chi113InputQChi innerPair27Input
    leaf1093InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1093LowerChecked :
    lowerCheck 24 leaf1093Box leaf1093Inputs = true := by
  rfl'

private theorem leaf1093CoversExact : CoversExact 8
    leaf1093Box leaf1093Certificate leaf1093InnerLog leaf1093Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk100RoundedFacts chi113RoundedFacts
    innerPair27RoundedFacts leaf1093RoundedFacts (by rfl)

private theorem leaf1093FlatSound : Sound leaf1093Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1093CertificateValid
    leaf1093InnerLogValid leaf1093CoversExact leaf1093LowerChecked

private noncomputable def leaf1094Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (81/32), kHi := (41/16), chiLo := (23/128), chiHi := (3/16) }

private noncomputable def leaf1094Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435667/268435456) }, vSqrt := { lower := (32765/32768), upper := (4194308/4194181) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (390488595/268435456) }, upper := { exponent := 0, mantissa := (379/256) } }, logOuter := sk100LogOuterCertificate, logK := sk100LogKCertificate, logChi := chi114LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (8388489/8388362) } }, logDArg := sk100LogDArgCertificate }

private noncomputable def leaf1094InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1094LocalValidity :
    LeafFacts leaf1094Box leaf1094Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1094Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4194308/4194181) }) = true
      norm_num [leaf1094Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1094CertificateValid :
    WideCertificateValid leaf1094Box leaf1094Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk100ValidityFacts chi114ValidityFacts
    leaf1094LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1094CoverageChecked :
    coverageCheck (innerAD leaf1094Box) leaf1094InnerLog = true := by
  rfl'

private theorem leaf1094InnerLogValid :
    leaf1094InnerLog.Valid 8 (innerAD leaf1094Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1094CoverageChecked

private noncomputable def leaf1094InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629335/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1094InputLogOnePlusV_eq :
    leaf1094InputLogOnePlusV = outerEnclosure 24
      (leaf1094Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1094RoundedFacts : LeafRoundedFacts 8
    leaf1094Certificate.logOnePlusV leaf1094InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1094InputLogOnePlusV_eq }

private noncomputable def leaf1094Inputs : Inputs :=
  inputsOfCaches globalInput sk100RoundedInputs
    chi114InputQChi innerPair34Input
    leaf1094InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1094LowerChecked :
    lowerCheck 24 leaf1094Box leaf1094Inputs = true := by
  rfl'

private theorem leaf1094CoversExact : CoversExact 8
    leaf1094Box leaf1094Certificate leaf1094InnerLog leaf1094Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk100RoundedFacts chi114RoundedFacts
    innerPair34RoundedFacts leaf1094RoundedFacts (by rfl)

private theorem leaf1094FlatSound : Sound leaf1094Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1094CertificateValid
    leaf1094InnerLogValid leaf1094CoversExact leaf1094LowerChecked

private noncomputable def leaf1095Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (83/32), chiLo := (11/64), chiHi := (23/128) }

private noncomputable def leaf1095Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435667/268435456) }, vSqrt := { lower := (32765/32768), upper := (67108928/67106955) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (386622207/268435456) }, upper := { exponent := 0, mantissa := (6005/4096) } }, logOuter := sk101LogOuterCertificate, logK := sk101LogKCertificate, logChi := chi113LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (134215883/134213910) } }, logDArg := sk101LogDArgCertificate }

private noncomputable def leaf1095InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1095LocalValidity :
    LeafFacts leaf1095Box leaf1095Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1095Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (67108928/67106955) }) = true
      norm_num [leaf1095Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1095CertificateValid :
    WideCertificateValid leaf1095Box leaf1095Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk101ValidityFacts chi113ValidityFacts
    leaf1095LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1095CoverageChecked :
    coverageCheck (innerAD leaf1095Box) leaf1095InnerLog = true := by
  rfl'

private theorem leaf1095InnerLogValid :
    leaf1095InnerLog.Valid 8 (innerAD leaf1095Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1095CoverageChecked

private noncomputable def leaf1095InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629327/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1095InputLogOnePlusV_eq :
    leaf1095InputLogOnePlusV = outerEnclosure 24
      (leaf1095Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1095RoundedFacts : LeafRoundedFacts 8
    leaf1095Certificate.logOnePlusV leaf1095InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1095InputLogOnePlusV_eq }

private noncomputable def leaf1095Inputs : Inputs :=
  inputsOfCaches globalInput sk101RoundedInputs
    chi113InputQChi innerPair34Input
    leaf1095InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1095LowerChecked :
    lowerCheck 24 leaf1095Box leaf1095Inputs = true := by
  rfl'

private theorem leaf1095CoversExact : CoversExact 8
    leaf1095Box leaf1095Certificate leaf1095InnerLog leaf1095Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk101RoundedFacts chi113RoundedFacts
    innerPair34RoundedFacts leaf1095RoundedFacts (by rfl)

private theorem leaf1095FlatSound : Sound leaf1095Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1095CertificateValid
    leaf1095InnerLogValid leaf1095CoversExact leaf1095LowerChecked

private noncomputable def leaf1096Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (83/32), chiLo := (23/128), chiHi := (3/16) }

private noncomputable def leaf1096Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435669/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68717436928) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (391995829/268435456) }, upper := { exponent := 0, mantissa := (761/512) } }, logOuter := sk101LogOuterCertificate, logK := sk101LogKCertificate, logChi := chi114LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435930623/137434873856) } }, logDArg := sk101LogDArgCertificate }

private noncomputable def leaf1096InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1096LocalValidity :
    LeafFacts leaf1096Box leaf1096Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1096Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68717436928) }) = true
      norm_num [leaf1096Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1096CertificateValid :
    WideCertificateValid leaf1096Box leaf1096Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk101ValidityFacts chi114ValidityFacts
    leaf1096LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1096CoverageChecked :
    coverageCheck (innerAD leaf1096Box) leaf1096InnerLog = true := by
  rfl'

private theorem leaf1096InnerLogValid :
    leaf1096InnerLog.Valid 8 (innerAD leaf1096Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1096CoverageChecked

private noncomputable def leaf1096InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814605/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1096InputLogOnePlusV_eq :
    leaf1096InputLogOnePlusV = outerEnclosure 24
      (leaf1096Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1096RoundedFacts : LeafRoundedFacts 8
    leaf1096Certificate.logOnePlusV leaf1096InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1096InputLogOnePlusV_eq }

private noncomputable def leaf1096Inputs : Inputs :=
  inputsOfCaches globalInput sk101RoundedInputs
    chi114InputQChi innerPair34Input
    leaf1096InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1096LowerChecked :
    lowerCheck 24 leaf1096Box leaf1096Inputs = true := by
  rfl'

private theorem leaf1096CoversExact : CoversExact 8
    leaf1096Box leaf1096Certificate leaf1096InnerLog leaf1096Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk101RoundedFacts chi114RoundedFacts
    innerPair34RoundedFacts leaf1096RoundedFacts (by rfl)

private theorem leaf1096FlatSound : Sound leaf1096Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1096CertificateValid
    leaf1096InnerLogValid leaf1096CoversExact leaf1096LowerChecked

private noncomputable def leaf1097Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (83/32), kHi := (21/8), chiLo := (11/64), chiHi := (23/128) }

private noncomputable def leaf1097Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435669/268435456) }, vSqrt := { lower := (32765/32768), upper := (16777232/16776733) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (388063909/268435456) }, upper := { exponent := 0, mantissa := (1507/1024) } }, logOuter := sk102LogOuterCertificate, logK := sk102LogKCertificate, logChi := chi113LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (33553965/33553466) } }, logDArg := sk102LogDArgCertificate }

private noncomputable def leaf1097InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1097LocalValidity :
    LeafFacts leaf1097Box leaf1097Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1097Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (16777232/16776733) }) = true
      norm_num [leaf1097Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1097CertificateValid :
    WideCertificateValid leaf1097Box leaf1097Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk102ValidityFacts chi113ValidityFacts
    leaf1097LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1097CoverageChecked :
    coverageCheck (innerAD leaf1097Box) leaf1097InnerLog = true := by
  rfl'

private theorem leaf1097InnerLogValid :
    leaf1097InnerLog.Valid 8 (innerAD leaf1097Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1097CoverageChecked

private noncomputable def leaf1097InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814665/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1097InputLogOnePlusV_eq :
    leaf1097InputLogOnePlusV = outerEnclosure 24
      (leaf1097Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1097RoundedFacts : LeafRoundedFacts 8
    leaf1097Certificate.logOnePlusV leaf1097InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1097InputLogOnePlusV_eq }

private noncomputable def leaf1097Inputs : Inputs :=
  inputsOfCaches globalInput sk102RoundedInputs
    chi113InputQChi innerPair34Input
    leaf1097InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1097LowerChecked :
    lowerCheck 24 leaf1097Box leaf1097Inputs = true := by
  rfl'

private theorem leaf1097CoversExact : CoversExact 8
    leaf1097Box leaf1097Certificate leaf1097InnerLog leaf1097Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk102RoundedFacts chi113RoundedFacts
    innerPair34RoundedFacts leaf1097RoundedFacts (by rfl)

private theorem leaf1097FlatSound : Sound leaf1097Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1097CertificateValid
    leaf1097InnerLogValid leaf1097CoversExact leaf1097LowerChecked

private noncomputable def leaf1098Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (83/32), kHi := (21/8), chiLo := (23/128), chiHi := (3/16) }

private noncomputable def leaf1098Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435671/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68717412352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (393503063/268435456) }, upper := { exponent := 0, mantissa := (191/128) } }, logOuter := sk102LogOuterCertificate, logK := sk102LogKCertificate, logChi := chi114LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435906047/137434824704) } }, logDArg := sk102LogDArgCertificate }

private noncomputable def leaf1098InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1098LocalValidity :
    LeafFacts leaf1098Box leaf1098Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1098Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68717412352) }) = true
      norm_num [leaf1098Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1098CertificateValid :
    WideCertificateValid leaf1098Box leaf1098Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk102ValidityFacts chi114ValidityFacts
    leaf1098LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1098CoverageChecked :
    coverageCheck (innerAD leaf1098Box) leaf1098InnerLog = true := by
  rfl'

private theorem leaf1098InnerLogValid :
    leaf1098InnerLog.Valid 8 (innerAD leaf1098Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1098CoverageChecked

private noncomputable def leaf1098InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629213/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1098InputLogOnePlusV_eq :
    leaf1098InputLogOnePlusV = outerEnclosure 24
      (leaf1098Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1098RoundedFacts : LeafRoundedFacts 8
    leaf1098Certificate.logOnePlusV leaf1098InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1098InputLogOnePlusV_eq }

private noncomputable def leaf1098Inputs : Inputs :=
  inputsOfCaches globalInput sk102RoundedInputs
    chi114InputQChi innerPair34Input
    leaf1098InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1098LowerChecked :
    lowerCheck 24 leaf1098Box leaf1098Inputs = true := by
  rfl'

private theorem leaf1098CoversExact : CoversExact 8
    leaf1098Box leaf1098Certificate leaf1098InnerLog leaf1098Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk102RoundedFacts chi114RoundedFacts
    innerPair34RoundedFacts leaf1098RoundedFacts (by rfl)

private theorem leaf1098FlatSound : Sound leaf1098Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1098CertificateValid
    leaf1098InnerLogValid leaf1098CoversExact leaf1098LowerChecked

private noncomputable def leaf1099Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (85/32), chiLo := (5/32), chiHi := (21/128) }

private noncomputable def leaf1099Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435667/268435456) }, vSqrt := { lower := (32765/32768), upper := (67108928/67107079) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (378496239/268435456) }, upper := { exponent := 0, mantissa := (5881/4096) } }, logOuter := sk105LogOuterCertificate, logK := sk105LogKCertificate, logChi := chi111LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (134216007/134214158) } }, logDArg := sk105LogDArgCertificate }

private noncomputable def leaf1099InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1099LocalValidity :
    LeafFacts leaf1099Box leaf1099Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1099Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (67108928/67107079) }) = true
      norm_num [leaf1099Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1099CertificateValid :
    WideCertificateValid leaf1099Box leaf1099Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk105ValidityFacts chi111ValidityFacts
    leaf1099LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1099CoverageChecked :
    coverageCheck (innerAD leaf1099Box) leaf1099InnerLog = true := by
  rfl'

private theorem leaf1099InnerLogValid :
    leaf1099InnerLog.Valid 8 (innerAD leaf1099Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1099CoverageChecked

private noncomputable def leaf1099InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (45427/65536) }

set_option maxRecDepth 1000000 in
private theorem leaf1099InputLogOnePlusV_eq :
    leaf1099InputLogOnePlusV = outerEnclosure 24
      (leaf1099Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1099RoundedFacts : LeafRoundedFacts 8
    leaf1099Certificate.logOnePlusV leaf1099InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1099InputLogOnePlusV_eq }

private noncomputable def leaf1099Inputs : Inputs :=
  inputsOfCaches globalInput sk105RoundedInputs
    chi111InputQChi innerPair26Input
    leaf1099InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1099LowerChecked :
    lowerCheck 24 leaf1099Box leaf1099Inputs = true := by
  rfl'

private theorem leaf1099CoversExact : CoversExact 8
    leaf1099Box leaf1099Certificate leaf1099InnerLog leaf1099Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk105RoundedFacts chi111RoundedFacts
    innerPair26RoundedFacts leaf1099RoundedFacts (by rfl)

private theorem leaf1099FlatSound : Sound leaf1099Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1099CertificateValid
    leaf1099InnerLogValid leaf1099CoversExact leaf1099LowerChecked

private noncomputable def leaf1100Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (85/32), kHi := (43/16), chiLo := (5/32), chiHi := (21/128) }

private noncomputable def leaf1100Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435669/268435456) }, vSqrt := { lower := (32765/32768), upper := (1973792/1973737) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (379806877/268435456) }, upper := { exponent := 0, mantissa := (2951/2048) } }, logOuter := sk106LogOuterCertificate, logK := sk106LogKCertificate, logChi := chi111LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (3947529/3947474) } }, logDArg := sk106LogDArgCertificate }

private noncomputable def leaf1100InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf1100LocalValidity :
    LeafFacts leaf1100Box leaf1100Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1100Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (1973792/1973737) }) = true
      norm_num [leaf1100Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1100CertificateValid :
    WideCertificateValid leaf1100Box leaf1100Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk106ValidityFacts chi111ValidityFacts
    leaf1100LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1100CoverageChecked :
    coverageCheck (innerAD leaf1100Box) leaf1100InnerLog = true := by
  rfl'

private theorem leaf1100InnerLogValid :
    leaf1100InnerLog.Valid 8 (innerAD leaf1100Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf1100CoverageChecked

private noncomputable def leaf1100InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814657/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1100InputLogOnePlusV_eq :
    leaf1100InputLogOnePlusV = outerEnclosure 24
      (leaf1100Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1100RoundedFacts : LeafRoundedFacts 8
    leaf1100Certificate.logOnePlusV leaf1100InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1100InputLogOnePlusV_eq }

private noncomputable def leaf1100Inputs : Inputs :=
  inputsOfCaches globalInput sk106RoundedInputs
    chi111InputQChi innerPair27Input
    leaf1100InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1100LowerChecked :
    lowerCheck 24 leaf1100Box leaf1100Inputs = true := by
  rfl'

private theorem leaf1100CoversExact : CoversExact 8
    leaf1100Box leaf1100Certificate leaf1100InnerLog leaf1100Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk106RoundedFacts chi111RoundedFacts
    innerPair27RoundedFacts leaf1100RoundedFacts (by rfl)

private theorem leaf1100FlatSound : Sound leaf1100Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1100CertificateValid
    leaf1100InnerLogValid leaf1100CoversExact leaf1100LowerChecked

private noncomputable def leaf1101Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (85/32), chiLo := (21/128), chiHi := (11/64) }

private noncomputable def leaf1101Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435669/268435456) }, vSqrt := { lower := (32765/32768), upper := (33554464/33553497) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (384000925/268435456) }, upper := { exponent := 0, mantissa := (2983/2048) } }, logOuter := sk105LogOuterCertificate, logK := sk105LogKCertificate, logChi := chi112LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (67107961/67106994) } }, logDArg := sk105LogDArgCertificate }

private noncomputable def leaf1101InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf1101LocalValidity :
    LeafFacts leaf1101Box leaf1101Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1101Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (33554464/33553497) }) = true
      norm_num [leaf1101Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1101CertificateValid :
    WideCertificateValid leaf1101Box leaf1101Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk105ValidityFacts chi112ValidityFacts
    leaf1101LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1101CoverageChecked :
    coverageCheck (innerAD leaf1101Box) leaf1101InnerLog = true := by
  rfl'

private theorem leaf1101InnerLogValid :
    leaf1101InnerLog.Valid 8 (innerAD leaf1101Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf1101CoverageChecked

private noncomputable def leaf1101InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814661/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1101InputLogOnePlusV_eq :
    leaf1101InputLogOnePlusV = outerEnclosure 24
      (leaf1101Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1101RoundedFacts : LeafRoundedFacts 8
    leaf1101Certificate.logOnePlusV leaf1101InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1101InputLogOnePlusV_eq }

private noncomputable def leaf1101Inputs : Inputs :=
  inputsOfCaches globalInput sk105RoundedInputs
    chi112InputQChi innerPair27Input
    leaf1101InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1101LowerChecked :
    lowerCheck 24 leaf1101Box leaf1101Inputs = true := by
  rfl'

private theorem leaf1101CoversExact : CoversExact 8
    leaf1101Box leaf1101Certificate leaf1101InnerLog leaf1101Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk105RoundedFacts chi112RoundedFacts
    innerPair27RoundedFacts leaf1101RoundedFacts (by rfl)

private theorem leaf1101FlatSound : Sound leaf1101Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1101CertificateValid
    leaf1101InnerLogValid leaf1101CoversExact leaf1101LowerChecked

private noncomputable def leaf1102Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (85/32), kHi := (43/16), chiLo := (21/128), chiHi := (11/64) }

private noncomputable def leaf1102Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435671/268435456) }, vSqrt := { lower := (32765/32768), upper := (16777232/16776743) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (385377095/268435456) }, upper := { exponent := 0, mantissa := (1497/1024) } }, logOuter := sk106LogOuterCertificate, logK := sk106LogKCertificate, logChi := chi112LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (33553975/33553486) } }, logDArg := sk106LogDArgCertificate }

private noncomputable def leaf1102InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf1102LocalValidity :
    LeafFacts leaf1102Box leaf1102Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1102Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (16777232/16776743) }) = true
      norm_num [leaf1102Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1102CertificateValid :
    WideCertificateValid leaf1102Box leaf1102Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk106ValidityFacts chi112ValidityFacts
    leaf1102LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1102CoverageChecked :
    coverageCheck (innerAD leaf1102Box) leaf1102InnerLog = true := by
  rfl'

private theorem leaf1102InnerLogValid :
    leaf1102InnerLog.Valid 8 (innerAD leaf1102Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf1102CoverageChecked

private noncomputable def leaf1102InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629325/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1102InputLogOnePlusV_eq :
    leaf1102InputLogOnePlusV = outerEnclosure 24
      (leaf1102Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1102RoundedFacts : LeafRoundedFacts 8
    leaf1102Certificate.logOnePlusV leaf1102InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1102InputLogOnePlusV_eq }

private noncomputable def leaf1102Inputs : Inputs :=
  inputsOfCaches globalInput sk106RoundedInputs
    chi112InputQChi innerPair27Input
    leaf1102InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1102LowerChecked :
    lowerCheck 24 leaf1102Box leaf1102Inputs = true := by
  rfl'

private theorem leaf1102CoversExact : CoversExact 8
    leaf1102Box leaf1102Certificate leaf1102InnerLog leaf1102Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk106RoundedFacts chi112RoundedFacts
    innerPair27RoundedFacts leaf1102RoundedFacts (by rfl)

private theorem leaf1102FlatSound : Sound leaf1102Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1102CertificateValid
    leaf1102InnerLogValid leaf1102CoversExact leaf1102LowerChecked

private noncomputable def leaf1103Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (87/32), chiLo := (5/32), chiHi := (21/128) }

private noncomputable def leaf1103Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435671/268435456) }, vSqrt := { lower := (32765/32768), upper := (67108928/67107037) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (381117515/268435456) }, upper := { exponent := 0, mantissa := (5923/4096) } }, logOuter := sk103LogOuterCertificate, logK := sk103LogKCertificate, logChi := chi111LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (134215965/134214074) } }, logDArg := sk103LogDArgCertificate }

private noncomputable def leaf1103InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf1103LocalValidity :
    LeafFacts leaf1103Box leaf1103Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1103Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (67108928/67107037) }) = true
      norm_num [leaf1103Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1103CertificateValid :
    WideCertificateValid leaf1103Box leaf1103Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk103ValidityFacts chi111ValidityFacts
    leaf1103LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1103CoverageChecked :
    coverageCheck (innerAD leaf1103Box) leaf1103InnerLog = true := by
  rfl'

private theorem leaf1103InnerLogValid :
    leaf1103InnerLog.Valid 8 (innerAD leaf1103Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf1103CoverageChecked

private noncomputable def leaf1103InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629317/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1103InputLogOnePlusV_eq :
    leaf1103InputLogOnePlusV = outerEnclosure 24
      (leaf1103Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1103RoundedFacts : LeafRoundedFacts 8
    leaf1103Certificate.logOnePlusV leaf1103InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1103InputLogOnePlusV_eq }

private noncomputable def leaf1103Inputs : Inputs :=
  inputsOfCaches globalInput sk103RoundedInputs
    chi111InputQChi innerPair27Input
    leaf1103InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1103LowerChecked :
    lowerCheck 24 leaf1103Box leaf1103Inputs = true := by
  rfl'

private theorem leaf1103CoversExact : CoversExact 8
    leaf1103Box leaf1103Certificate leaf1103InnerLog leaf1103Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk103RoundedFacts chi111RoundedFacts
    innerPair27RoundedFacts leaf1103RoundedFacts (by rfl)

private theorem leaf1103FlatSound : Sound leaf1103Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1103CertificateValid
    leaf1103InnerLogValid leaf1103CoversExact leaf1103LowerChecked

private noncomputable def leaf1104Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (87/32), kHi := (11/4), chiLo := (5/32), chiHi := (21/128) }

private noncomputable def leaf1104Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435673/268435456) }, vSqrt := { lower := (32765/32768), upper := (8388616/8388377) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (382428153/268435456) }, upper := { exponent := 0, mantissa := (743/512) } }, logOuter := sk104LogOuterCertificate, logK := sk104LogKCertificate, logChi := chi111LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (16776993/16776754) } }, logDArg := sk104LogDArgCertificate }

private noncomputable def leaf1104InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf1104LocalValidity :
    LeafFacts leaf1104Box leaf1104Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1104Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8388616/8388377) }) = true
      norm_num [leaf1104Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1104CertificateValid :
    WideCertificateValid leaf1104Box leaf1104Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk104ValidityFacts chi111ValidityFacts
    leaf1104LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1104CoverageChecked :
    coverageCheck (innerAD leaf1104Box) leaf1104InnerLog = true := by
  rfl'

private theorem leaf1104InnerLogValid :
    leaf1104InnerLog.Valid 8 (innerAD leaf1104Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf1104CoverageChecked

private noncomputable def leaf1104InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (1453665/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf1104InputLogOnePlusV_eq :
    leaf1104InputLogOnePlusV = outerEnclosure 24
      (leaf1104Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1104RoundedFacts : LeafRoundedFacts 8
    leaf1104Certificate.logOnePlusV leaf1104InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1104InputLogOnePlusV_eq }

private noncomputable def leaf1104Inputs : Inputs :=
  inputsOfCaches globalInput sk104RoundedInputs
    chi111InputQChi innerPair27Input
    leaf1104InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1104LowerChecked :
    lowerCheck 24 leaf1104Box leaf1104Inputs = true := by
  rfl'

private theorem leaf1104CoversExact : CoversExact 8
    leaf1104Box leaf1104Certificate leaf1104InnerLog leaf1104Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk104RoundedFacts chi111RoundedFacts
    innerPair27RoundedFacts leaf1104RoundedFacts (by rfl)

private theorem leaf1104FlatSound : Sound leaf1104Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1104CertificateValid
    leaf1104InnerLogValid leaf1104CoversExact leaf1104LowerChecked

private noncomputable def leaf1105Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (87/32), chiLo := (21/128), chiHi := (11/64) }

private noncomputable def leaf1105Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435673/268435456) }, vSqrt := { lower := (32765/32768), upper := (33554464/33553475) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (386753265/268435456) }, upper := { exponent := 0, mantissa := (3005/2048) } }, logOuter := sk103LogOuterCertificate, logK := sk103LogKCertificate, logChi := chi112LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (67107939/67106950) } }, logDArg := sk103LogDArgCertificate }

private noncomputable def leaf1105InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1105LocalValidity :
    LeafFacts leaf1105Box leaf1105Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1105Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (33554464/33553475) }) = true
      norm_num [leaf1105Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1105CertificateValid :
    WideCertificateValid leaf1105Box leaf1105Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk103ValidityFacts chi112ValidityFacts
    leaf1105LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1105CoverageChecked :
    coverageCheck (innerAD leaf1105Box) leaf1105InnerLog = true := by
  rfl'

private theorem leaf1105InnerLogValid :
    leaf1105InnerLog.Valid 8 (innerAD leaf1105Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1105CoverageChecked

private noncomputable def leaf1105InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (726833/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf1105InputLogOnePlusV_eq :
    leaf1105InputLogOnePlusV = outerEnclosure 24
      (leaf1105Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1105RoundedFacts : LeafRoundedFacts 8
    leaf1105Certificate.logOnePlusV leaf1105InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1105InputLogOnePlusV_eq }

private noncomputable def leaf1105Inputs : Inputs :=
  inputsOfCaches globalInput sk103RoundedInputs
    chi112InputQChi innerPair34Input
    leaf1105InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1105LowerChecked :
    lowerCheck 24 leaf1105Box leaf1105Inputs = true := by
  rfl'

private theorem leaf1105CoversExact : CoversExact 8
    leaf1105Box leaf1105Certificate leaf1105InnerLog leaf1105Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk103RoundedFacts chi112RoundedFacts
    innerPair34RoundedFacts leaf1105RoundedFacts (by rfl)

private theorem leaf1105FlatSound : Sound leaf1105Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1105CertificateValid
    leaf1105InnerLogValid leaf1105CoversExact leaf1105LowerChecked

private noncomputable def leaf1106Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (87/32), kHi := (11/4), chiLo := (21/128), chiHi := (11/64) }

private noncomputable def leaf1106Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435675/268435456) }, vSqrt := { lower := (32765/32768), upper := (4194308/4194183) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (388129435/268435456) }, upper := { exponent := 0, mantissa := (377/256) } }, logOuter := sk104LogOuterCertificate, logK := sk104LogKCertificate, logChi := chi112LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (8388491/8388366) } }, logDArg := sk104LogDArgCertificate }

private noncomputable def leaf1106InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1106LocalValidity :
    LeafFacts leaf1106Box leaf1106Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1106Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4194308/4194183) }) = true
      norm_num [leaf1106Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1106CertificateValid :
    WideCertificateValid leaf1106Box leaf1106Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk104ValidityFacts chi112ValidityFacts
    leaf1106LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1106CoverageChecked :
    coverageCheck (innerAD leaf1106Box) leaf1106InnerLog = true := by
  rfl'

private theorem leaf1106InnerLogValid :
    leaf1106InnerLog.Valid 8 (innerAD leaf1106Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1106CoverageChecked

private noncomputable def leaf1106InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629331/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1106InputLogOnePlusV_eq :
    leaf1106InputLogOnePlusV = outerEnclosure 24
      (leaf1106Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1106RoundedFacts : LeafRoundedFacts 8
    leaf1106Certificate.logOnePlusV leaf1106InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1106InputLogOnePlusV_eq }

private noncomputable def leaf1106Inputs : Inputs :=
  inputsOfCaches globalInput sk104RoundedInputs
    chi112InputQChi innerPair34Input
    leaf1106InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1106LowerChecked :
    lowerCheck 24 leaf1106Box leaf1106Inputs = true := by
  rfl'

private theorem leaf1106CoversExact : CoversExact 8
    leaf1106Box leaf1106Certificate leaf1106InnerLog leaf1106Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk104RoundedFacts chi112RoundedFacts
    innerPair34RoundedFacts leaf1106RoundedFacts (by rfl)

private theorem leaf1106FlatSound : Sound leaf1106Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1106CertificateValid
    leaf1106InnerLogValid leaf1106CoversExact leaf1106LowerChecked

private noncomputable def leaf1107Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (85/32), chiLo := (11/64), chiHi := (23/128) }

private noncomputable def leaf1107Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435671/268435456) }, vSqrt := { lower := (32765/32768), upper := (67108928/67106909) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (389505611/268435456) }, upper := { exponent := 0, mantissa := (6051/4096) } }, logOuter := sk105LogOuterCertificate, logK := sk105LogKCertificate, logChi := chi113LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (134215837/134213818) } }, logDArg := sk105LogDArgCertificate }

private noncomputable def leaf1107InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1107LocalValidity :
    LeafFacts leaf1107Box leaf1107Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1107Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (67108928/67106909) }) = true
      norm_num [leaf1107Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1107CertificateValid :
    WideCertificateValid leaf1107Box leaf1107Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk105ValidityFacts chi113ValidityFacts
    leaf1107LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1107CoverageChecked :
    coverageCheck (innerAD leaf1107Box) leaf1107InnerLog = true := by
  rfl'

private theorem leaf1107InnerLogValid :
    leaf1107InnerLog.Valid 8 (innerAD leaf1107Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1107CoverageChecked

private noncomputable def leaf1107InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629333/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1107InputLogOnePlusV_eq :
    leaf1107InputLogOnePlusV = outerEnclosure 24
      (leaf1107Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1107RoundedFacts : LeafRoundedFacts 8
    leaf1107Certificate.logOnePlusV leaf1107InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1107InputLogOnePlusV_eq }

private noncomputable def leaf1107Inputs : Inputs :=
  inputsOfCaches globalInput sk105RoundedInputs
    chi113InputQChi innerPair34Input
    leaf1107InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1107LowerChecked :
    lowerCheck 24 leaf1107Box leaf1107Inputs = true := by
  rfl'

private theorem leaf1107CoversExact : CoversExact 8
    leaf1107Box leaf1107Certificate leaf1107InnerLog leaf1107Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk105RoundedFacts chi113RoundedFacts
    innerPair34RoundedFacts leaf1107RoundedFacts (by rfl)

private theorem leaf1107FlatSound : Sound leaf1107Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1107CertificateValid
    leaf1107InnerLogValid leaf1107CoversExact leaf1107LowerChecked

private noncomputable def leaf1108Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (85/32), chiLo := (23/128), chiHi := (3/16) }

private noncomputable def leaf1108Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435673/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68717387776) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (395010297/268435456) }, upper := { exponent := 0, mantissa := (767/512) } }, logOuter := sk105LogOuterCertificate, logK := sk105LogKCertificate, logChi := chi114LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435881471/137434775552) } }, logDArg := sk105LogDArgCertificate }

private noncomputable def leaf1108InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1108LocalValidity :
    LeafFacts leaf1108Box leaf1108Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1108Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68717387776) }) = true
      norm_num [leaf1108Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1108CertificateValid :
    WideCertificateValid leaf1108Box leaf1108Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk105ValidityFacts chi114ValidityFacts
    leaf1108LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1108CoverageChecked :
    coverageCheck (innerAD leaf1108Box) leaf1108InnerLog = true := by
  rfl'

private theorem leaf1108InnerLogValid :
    leaf1108InnerLog.Valid 8 (innerAD leaf1108Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1108CoverageChecked

private noncomputable def leaf1108InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (363413/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf1108InputLogOnePlusV_eq :
    leaf1108InputLogOnePlusV = outerEnclosure 24
      (leaf1108Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1108RoundedFacts : LeafRoundedFacts 8
    leaf1108Certificate.logOnePlusV leaf1108InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1108InputLogOnePlusV_eq }

private noncomputable def leaf1108Inputs : Inputs :=
  inputsOfCaches globalInput sk105RoundedInputs
    chi114InputQChi innerPair34Input
    leaf1108InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1108LowerChecked :
    lowerCheck 24 leaf1108Box leaf1108Inputs = true := by
  rfl'

private theorem leaf1108CoversExact : CoversExact 8
    leaf1108Box leaf1108Certificate leaf1108InnerLog leaf1108Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk105RoundedFacts chi114RoundedFacts
    innerPair34RoundedFacts leaf1108RoundedFacts (by rfl)

private theorem leaf1108FlatSound : Sound leaf1108Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1108CertificateValid
    leaf1108InnerLogValid leaf1108CoversExact leaf1108LowerChecked

private noncomputable def leaf1109Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (85/32), kHi := (43/16), chiLo := (11/64), chiHi := (23/128) }

private noncomputable def leaf1109Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435673/268435456) }, vSqrt := { lower := (32765/32768), upper := (33554464/33553443) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (390947313/268435456) }, upper := { exponent := 0, mantissa := (3037/2048) } }, logOuter := sk106LogOuterCertificate, logK := sk106LogKCertificate, logChi := chi113LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (67107907/67106886) } }, logDArg := sk106LogDArgCertificate }

private noncomputable def leaf1109InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1109LocalValidity :
    LeafFacts leaf1109Box leaf1109Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1109Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (33554464/33553443) }) = true
      norm_num [leaf1109Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1109CertificateValid :
    WideCertificateValid leaf1109Box leaf1109Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk106ValidityFacts chi113ValidityFacts
    leaf1109LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1109CoverageChecked :
    coverageCheck (innerAD leaf1109Box) leaf1109InnerLog = true := by
  rfl'

private theorem leaf1109InnerLogValid :
    leaf1109InnerLog.Valid 8 (innerAD leaf1109Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1109CoverageChecked

private noncomputable def leaf1109InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (1453667/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf1109InputLogOnePlusV_eq :
    leaf1109InputLogOnePlusV = outerEnclosure 24
      (leaf1109Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1109RoundedFacts : LeafRoundedFacts 8
    leaf1109Certificate.logOnePlusV leaf1109InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1109InputLogOnePlusV_eq }

private noncomputable def leaf1109Inputs : Inputs :=
  inputsOfCaches globalInput sk106RoundedInputs
    chi113InputQChi innerPair34Input
    leaf1109InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1109LowerChecked :
    lowerCheck 24 leaf1109Box leaf1109Inputs = true := by
  rfl'

private theorem leaf1109CoversExact : CoversExact 8
    leaf1109Box leaf1109Certificate leaf1109InnerLog leaf1109Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk106RoundedFacts chi113RoundedFacts
    innerPair34RoundedFacts leaf1109RoundedFacts (by rfl)

private theorem leaf1109FlatSound : Sound leaf1109Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1109CertificateValid
    leaf1109InnerLogValid leaf1109CoversExact leaf1109LowerChecked

private noncomputable def leaf1110Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (85/32), kHi := (43/16), chiLo := (23/128), chiHi := (3/16) }

private noncomputable def leaf1110Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435675/268435456) }, vSqrt := { lower := (32765/32768), upper := (13743698739/13743472640) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (396517531/268435456) }, upper := { exponent := 0, mantissa := (385/256) } }, logOuter := sk106LogOuterCertificate, logK := sk106LogKCertificate, logChi := chi114LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (27487171379/27486945280) } }, logDArg := sk106LogDArgCertificate }

private noncomputable def leaf1110InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf1110LocalValidity :
    LeafFacts leaf1110Box leaf1110Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1110Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (13743698739/13743472640) }) = true
      norm_num [leaf1110Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1110CertificateValid :
    WideCertificateValid leaf1110Box leaf1110Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk106ValidityFacts chi114ValidityFacts
    leaf1110LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1110CoverageChecked :
    coverageCheck (innerAD leaf1110Box) leaf1110InnerLog = true := by
  rfl'

private theorem leaf1110InnerLogValid :
    leaf1110InnerLog.Valid 8 (innerAD leaf1110Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf1110CoverageChecked

private noncomputable def leaf1110InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629219/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1110InputLogOnePlusV_eq :
    leaf1110InputLogOnePlusV = outerEnclosure 24
      (leaf1110Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1110RoundedFacts : LeafRoundedFacts 8
    leaf1110Certificate.logOnePlusV leaf1110InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1110InputLogOnePlusV_eq }

private noncomputable def leaf1110Inputs : Inputs :=
  inputsOfCaches globalInput sk106RoundedInputs
    chi114InputQChi innerPair35Input
    leaf1110InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1110LowerChecked :
    lowerCheck 24 leaf1110Box leaf1110Inputs = true := by
  rfl'

private theorem leaf1110CoversExact : CoversExact 8
    leaf1110Box leaf1110Certificate leaf1110InnerLog leaf1110Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk106RoundedFacts chi114RoundedFacts
    innerPair35RoundedFacts leaf1110RoundedFacts (by rfl)

private theorem leaf1110FlatSound : Sound leaf1110Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1110CertificateValid
    leaf1110InnerLogValid leaf1110CoversExact leaf1110LowerChecked

private noncomputable def leaf1111Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (87/32), chiLo := (11/64), chiHi := (23/128) }

private noncomputable def leaf1111Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435675/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68717427712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (392389015/268435456) }, upper := { exponent := 0, mantissa := (6097/4096) } }, logOuter := sk103LogOuterCertificate, logK := sk103LogKCertificate, logChi := chi113LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435921407/137434855424) } }, logDArg := sk103LogDArgCertificate }

private noncomputable def leaf1111InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1111LocalValidity :
    LeafFacts leaf1111Box leaf1111Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1111Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68717427712) }) = true
      norm_num [leaf1111Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1111CertificateValid :
    WideCertificateValid leaf1111Box leaf1111Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk103ValidityFacts chi113ValidityFacts
    leaf1111LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1111CoverageChecked :
    coverageCheck (innerAD leaf1111Box) leaf1111InnerLog = true := by
  rfl'

private theorem leaf1111InnerLogValid :
    leaf1111InnerLog.Valid 8 (innerAD leaf1111Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1111CoverageChecked

private noncomputable def leaf1111InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629211/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1111InputLogOnePlusV_eq :
    leaf1111InputLogOnePlusV = outerEnclosure 24
      (leaf1111Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1111RoundedFacts : LeafRoundedFacts 8
    leaf1111Certificate.logOnePlusV leaf1111InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1111InputLogOnePlusV_eq }

private noncomputable def leaf1111Inputs : Inputs :=
  inputsOfCaches globalInput sk103RoundedInputs
    chi113InputQChi innerPair34Input
    leaf1111InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1111LowerChecked :
    lowerCheck 24 leaf1111Box leaf1111Inputs = true := by
  rfl'

private theorem leaf1111CoversExact : CoversExact 8
    leaf1111Box leaf1111Certificate leaf1111InnerLog leaf1111Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk103RoundedFacts chi113RoundedFacts
    innerPair34RoundedFacts leaf1111RoundedFacts (by rfl)

private theorem leaf1111FlatSound : Sound leaf1111Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1111CertificateValid
    leaf1111InnerLogValid leaf1111CoversExact leaf1111LowerChecked

private noncomputable def leaf1112Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (87/32), kHi := (11/4), chiLo := (11/64), chiHi := (23/128) }

private noncomputable def leaf1112Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435677/268435456) }, vSqrt := { lower := (32765/32768), upper := (13743698739/13743480832) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (393830717/268435456) }, upper := { exponent := 0, mantissa := (765/512) } }, logOuter := sk104LogOuterCertificate, logK := sk104LogKCertificate, logChi := chi113LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (27487179571/27486961664) } }, logDArg := sk104LogDArgCertificate }

private noncomputable def leaf1112InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1112LocalValidity :
    LeafFacts leaf1112Box leaf1112Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1112Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (13743698739/13743480832) }) = true
      norm_num [leaf1112Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1112CertificateValid :
    WideCertificateValid leaf1112Box leaf1112Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk104ValidityFacts chi113ValidityFacts
    leaf1112LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1112CoverageChecked :
    coverageCheck (innerAD leaf1112Box) leaf1112InnerLog = true := by
  rfl'

private theorem leaf1112InnerLogValid :
    leaf1112InnerLog.Valid 8 (innerAD leaf1112Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1112CoverageChecked

private noncomputable def leaf1112InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814607/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1112InputLogOnePlusV_eq :
    leaf1112InputLogOnePlusV = outerEnclosure 24
      (leaf1112Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1112RoundedFacts : LeafRoundedFacts 8
    leaf1112Certificate.logOnePlusV leaf1112InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1112InputLogOnePlusV_eq }

private noncomputable def leaf1112Inputs : Inputs :=
  inputsOfCaches globalInput sk104RoundedInputs
    chi113InputQChi innerPair34Input
    leaf1112InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1112LowerChecked :
    lowerCheck 24 leaf1112Box leaf1112Inputs = true := by
  rfl'

private theorem leaf1112CoversExact : CoversExact 8
    leaf1112Box leaf1112Certificate leaf1112InnerLog leaf1112Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk104RoundedFacts chi113RoundedFacts
    innerPair34RoundedFacts leaf1112RoundedFacts (by rfl)

private theorem leaf1112FlatSound : Sound leaf1112Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1112CertificateValid
    leaf1112InnerLogValid leaf1112CoversExact leaf1112LowerChecked

private noncomputable def leaf1113Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (87/32), chiLo := (23/128), chiHi := (3/16) }

private noncomputable def leaf1113Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435677/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68717338624) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (398024765/268435456) }, upper := { exponent := 0, mantissa := (773/512) } }, logOuter := sk103LogOuterCertificate, logK := sk103LogKCertificate, logChi := chi114LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435832319/137434677248) } }, logDArg := sk103LogDArgCertificate }

private noncomputable def leaf1113InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf1113LocalValidity :
    LeafFacts leaf1113Box leaf1113Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1113Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68717338624) }) = true
      norm_num [leaf1113Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1113CertificateValid :
    WideCertificateValid leaf1113Box leaf1113Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk103ValidityFacts chi114ValidityFacts
    leaf1113LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1113CoverageChecked :
    coverageCheck (innerAD leaf1113Box) leaf1113InnerLog = true := by
  rfl'

private theorem leaf1113InnerLogValid :
    leaf1113InnerLog.Valid 8 (innerAD leaf1113Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf1113CoverageChecked

private noncomputable def leaf1113InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814611/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1113InputLogOnePlusV_eq :
    leaf1113InputLogOnePlusV = outerEnclosure 24
      (leaf1113Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1113RoundedFacts : LeafRoundedFacts 8
    leaf1113Certificate.logOnePlusV leaf1113InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1113InputLogOnePlusV_eq }

private noncomputable def leaf1113Inputs : Inputs :=
  inputsOfCaches globalInput sk103RoundedInputs
    chi114InputQChi innerPair35Input
    leaf1113InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1113LowerChecked :
    lowerCheck 24 leaf1113Box leaf1113Inputs = true := by
  rfl'

private theorem leaf1113CoversExact : CoversExact 8
    leaf1113Box leaf1113Certificate leaf1113InnerLog leaf1113Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk103RoundedFacts chi114RoundedFacts
    innerPair35RoundedFacts leaf1113RoundedFacts (by rfl)

private theorem leaf1113FlatSound : Sound leaf1113Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1113CertificateValid
    leaf1113InnerLogValid leaf1113CoversExact leaf1113LowerChecked

private noncomputable def leaf1114Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (87/32), kHi := (11/4), chiLo := (23/128), chiHi := (3/16) }

private noncomputable def leaf1114Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435679/268435456) }, vSqrt := { lower := (32765/32768), upper := (4042264335/4042194944) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (399531999/268435456) }, upper := { exponent := 0, mantissa := (97/64) } }, logOuter := sk104LogOuterCertificate, logK := sk104LogKCertificate, logChi := chi114LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (8084459279/8084389888) } }, logDArg := sk104LogDArgCertificate }

private noncomputable def leaf1114InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf1114LocalValidity :
    LeafFacts leaf1114Box leaf1114Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1114Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4042264335/4042194944) }) = true
      norm_num [leaf1114Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1114CertificateValid :
    WideCertificateValid leaf1114Box leaf1114Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk104ValidityFacts chi114ValidityFacts
    leaf1114LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1114CoverageChecked :
    coverageCheck (innerAD leaf1114Box) leaf1114InnerLog = true := by
  rfl'

private theorem leaf1114InnerLogValid :
    leaf1114InnerLog.Valid 8 (innerAD leaf1114Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf1114CoverageChecked

private noncomputable def leaf1114InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629225/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1114InputLogOnePlusV_eq :
    leaf1114InputLogOnePlusV = outerEnclosure 24
      (leaf1114Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1114RoundedFacts : LeafRoundedFacts 8
    leaf1114Certificate.logOnePlusV leaf1114InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1114InputLogOnePlusV_eq }

private noncomputable def leaf1114Inputs : Inputs :=
  inputsOfCaches globalInput sk104RoundedInputs
    chi114InputQChi innerPair35Input
    leaf1114InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1114LowerChecked :
    lowerCheck 24 leaf1114Box leaf1114Inputs = true := by
  rfl'

private theorem leaf1114CoversExact : CoversExact 8
    leaf1114Box leaf1114Certificate leaf1114InnerLog leaf1114Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk104RoundedFacts chi114RoundedFacts
    innerPair35RoundedFacts leaf1114RoundedFacts (by rfl)

private theorem leaf1114FlatSound : Sound leaf1114Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1114CertificateValid
    leaf1114InnerLogValid leaf1114CoversExact leaf1114LowerChecked

private noncomputable def component25Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (1/8), chiHi := (17/128) }

set_option maxRecDepth 1000000 in
private theorem component25Node0_sound : Sound component25Node0Box :=
  sound_of_literal_split component25Node0Box leaf1051Box leaf1052Box
    .k (81/32) (by rfl) (by rfl)
    leaf1051FlatSound leaf1052FlatSound

private noncomputable def component25Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (17/128), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component25Node1_sound : Sound component25Node1Box :=
  sound_of_literal_split component25Node1Box leaf1053Box leaf1054Box
    .k (81/32) (by rfl) (by rfl)
    leaf1053FlatSound leaf1054FlatSound

private noncomputable def component25Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (1/8), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component25Node2_sound : Sound component25Node2Box :=
  sound_of_literal_split component25Node2Box component25Node0Box component25Node1Box
    .chi (17/128) (by rfl) (by rfl)
    component25Node0_sound component25Node1_sound

private noncomputable def component25Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (1/8), chiHi := (17/128) }

set_option maxRecDepth 1000000 in
private theorem component25Node3_sound : Sound component25Node3Box :=
  sound_of_literal_split component25Node3Box leaf1055Box leaf1056Box
    .k (83/32) (by rfl) (by rfl)
    leaf1055FlatSound leaf1056FlatSound

private noncomputable def component25Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (17/128), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component25Node4_sound : Sound component25Node4Box :=
  sound_of_literal_split component25Node4Box leaf1057Box leaf1058Box
    .k (83/32) (by rfl) (by rfl)
    leaf1057FlatSound leaf1058FlatSound

private noncomputable def component25Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (1/8), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component25Node5_sound : Sound component25Node5Box :=
  sound_of_literal_split component25Node5Box component25Node3Box component25Node4Box
    .chi (17/128) (by rfl) (by rfl)
    component25Node3_sound component25Node4_sound

private noncomputable def component25Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8), chiLo := (1/8), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component25Node6_sound : Sound component25Node6Box :=
  sound_of_literal_split component25Node6Box component25Node2Box component25Node5Box
    .k (41/16) (by rfl) (by rfl)
    component25Node2_sound component25Node5_sound

private noncomputable def component25Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (9/64), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component25Node7_sound : Sound component25Node7Box :=
  sound_of_literal_split component25Node7Box leaf1059Box leaf1060Box
    .k (81/32) (by rfl) (by rfl)
    leaf1059FlatSound leaf1060FlatSound

private noncomputable def component25Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (19/128), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component25Node8_sound : Sound component25Node8Box :=
  sound_of_literal_split component25Node8Box leaf1061Box leaf1062Box
    .k (81/32) (by rfl) (by rfl)
    leaf1061FlatSound leaf1062FlatSound

private noncomputable def component25Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (9/64), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component25Node9_sound : Sound component25Node9Box :=
  sound_of_literal_split component25Node9Box component25Node7Box component25Node8Box
    .chi (19/128) (by rfl) (by rfl)
    component25Node7_sound component25Node8_sound

private noncomputable def component25Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (9/64), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component25Node10_sound : Sound component25Node10Box :=
  sound_of_literal_split component25Node10Box leaf1063Box leaf1064Box
    .k (83/32) (by rfl) (by rfl)
    leaf1063FlatSound leaf1064FlatSound

private noncomputable def component25Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (19/128), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component25Node11_sound : Sound component25Node11Box :=
  sound_of_literal_split component25Node11Box leaf1065Box leaf1066Box
    .k (83/32) (by rfl) (by rfl)
    leaf1065FlatSound leaf1066FlatSound

private noncomputable def component25Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (9/64), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component25Node12_sound : Sound component25Node12Box :=
  sound_of_literal_split component25Node12Box component25Node10Box component25Node11Box
    .chi (19/128) (by rfl) (by rfl)
    component25Node10_sound component25Node11_sound

private noncomputable def component25Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8), chiLo := (9/64), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component25Node13_sound : Sound component25Node13Box :=
  sound_of_literal_split component25Node13Box component25Node9Box component25Node12Box
    .k (41/16) (by rfl) (by rfl)
    component25Node9_sound component25Node12_sound

private noncomputable def component25Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8), chiLo := (1/8), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component25Node14_sound : Sound component25Node14Box :=
  sound_of_literal_split component25Node14Box component25Node6Box component25Node13Box
    .chi (9/64) (by rfl) (by rfl)
    component25Node6_sound component25Node13_sound

private noncomputable def component25Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (1/8), chiHi := (17/128) }

set_option maxRecDepth 1000000 in
private theorem component25Node15_sound : Sound component25Node15Box :=
  sound_of_literal_split component25Node15Box leaf1067Box leaf1068Box
    .k (85/32) (by rfl) (by rfl)
    leaf1067FlatSound leaf1068FlatSound

private noncomputable def component25Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (17/128), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component25Node16_sound : Sound component25Node16Box :=
  sound_of_literal_split component25Node16Box leaf1069Box leaf1070Box
    .k (85/32) (by rfl) (by rfl)
    leaf1069FlatSound leaf1070FlatSound

private noncomputable def component25Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (1/8), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component25Node17_sound : Sound component25Node17Box :=
  sound_of_literal_split component25Node17Box component25Node15Box component25Node16Box
    .chi (17/128) (by rfl) (by rfl)
    component25Node15_sound component25Node16_sound

private noncomputable def component25Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (1/8), chiHi := (17/128) }

set_option maxRecDepth 1000000 in
private theorem component25Node18_sound : Sound component25Node18Box :=
  sound_of_literal_split component25Node18Box leaf1071Box leaf1072Box
    .k (87/32) (by rfl) (by rfl)
    leaf1071FlatSound leaf1072FlatSound

private noncomputable def component25Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (17/128), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component25Node19_sound : Sound component25Node19Box :=
  sound_of_literal_split component25Node19Box leaf1073Box leaf1074Box
    .k (87/32) (by rfl) (by rfl)
    leaf1073FlatSound leaf1074FlatSound

private noncomputable def component25Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (1/8), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component25Node20_sound : Sound component25Node20Box :=
  sound_of_literal_split component25Node20Box component25Node18Box component25Node19Box
    .chi (17/128) (by rfl) (by rfl)
    component25Node18_sound component25Node19_sound

private noncomputable def component25Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4), chiLo := (1/8), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component25Node21_sound : Sound component25Node21Box :=
  sound_of_literal_split component25Node21Box component25Node17Box component25Node20Box
    .k (43/16) (by rfl) (by rfl)
    component25Node17_sound component25Node20_sound

private noncomputable def component25Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (9/64), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component25Node22_sound : Sound component25Node22Box :=
  sound_of_literal_split component25Node22Box leaf1075Box leaf1076Box
    .k (85/32) (by rfl) (by rfl)
    leaf1075FlatSound leaf1076FlatSound

private noncomputable def component25Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (19/128), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component25Node23_sound : Sound component25Node23Box :=
  sound_of_literal_split component25Node23Box leaf1077Box leaf1078Box
    .k (85/32) (by rfl) (by rfl)
    leaf1077FlatSound leaf1078FlatSound

private noncomputable def component25Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (9/64), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component25Node24_sound : Sound component25Node24Box :=
  sound_of_literal_split component25Node24Box component25Node22Box component25Node23Box
    .chi (19/128) (by rfl) (by rfl)
    component25Node22_sound component25Node23_sound

private noncomputable def component25Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (9/64), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component25Node25_sound : Sound component25Node25Box :=
  sound_of_literal_split component25Node25Box leaf1079Box leaf1080Box
    .k (87/32) (by rfl) (by rfl)
    leaf1079FlatSound leaf1080FlatSound

private noncomputable def component25Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (19/128), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component25Node26_sound : Sound component25Node26Box :=
  sound_of_literal_split component25Node26Box leaf1081Box leaf1082Box
    .k (87/32) (by rfl) (by rfl)
    leaf1081FlatSound leaf1082FlatSound

private noncomputable def component25Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (9/64), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component25Node27_sound : Sound component25Node27Box :=
  sound_of_literal_split component25Node27Box component25Node25Box component25Node26Box
    .chi (19/128) (by rfl) (by rfl)
    component25Node25_sound component25Node26_sound

private noncomputable def component25Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4), chiLo := (9/64), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component25Node28_sound : Sound component25Node28Box :=
  sound_of_literal_split component25Node28Box component25Node24Box component25Node27Box
    .k (43/16) (by rfl) (by rfl)
    component25Node24_sound component25Node27_sound

private noncomputable def component25Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4), chiLo := (1/8), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component25Node29_sound : Sound component25Node29Box :=
  sound_of_literal_split component25Node29Box component25Node21Box component25Node28Box
    .chi (9/64) (by rfl) (by rfl)
    component25Node21_sound component25Node28_sound

private noncomputable def component25Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (11/4), chiLo := (1/8), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component25Node30_sound : Sound component25Node30Box :=
  sound_of_literal_split component25Node30Box component25Node14Box component25Node29Box
    .k (21/8) (by rfl) (by rfl)
    component25Node14_sound component25Node29_sound

private noncomputable def component25Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (5/32), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component25Node31_sound : Sound component25Node31Box :=
  sound_of_literal_split component25Node31Box leaf1083Box leaf1084Box
    .k (81/32) (by rfl) (by rfl)
    leaf1083FlatSound leaf1084FlatSound

private noncomputable def component25Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (21/128), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component25Node32_sound : Sound component25Node32Box :=
  sound_of_literal_split component25Node32Box leaf1085Box leaf1086Box
    .k (81/32) (by rfl) (by rfl)
    leaf1085FlatSound leaf1086FlatSound

private noncomputable def component25Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (5/32), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component25Node33_sound : Sound component25Node33Box :=
  sound_of_literal_split component25Node33Box component25Node31Box component25Node32Box
    .chi (21/128) (by rfl) (by rfl)
    component25Node31_sound component25Node32_sound

private noncomputable def component25Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (5/32), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component25Node34_sound : Sound component25Node34Box :=
  sound_of_literal_split component25Node34Box leaf1087Box leaf1088Box
    .k (83/32) (by rfl) (by rfl)
    leaf1087FlatSound leaf1088FlatSound

private noncomputable def component25Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (21/128), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component25Node35_sound : Sound component25Node35Box :=
  sound_of_literal_split component25Node35Box leaf1089Box leaf1090Box
    .k (83/32) (by rfl) (by rfl)
    leaf1089FlatSound leaf1090FlatSound

private noncomputable def component25Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (5/32), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component25Node36_sound : Sound component25Node36Box :=
  sound_of_literal_split component25Node36Box component25Node34Box component25Node35Box
    .chi (21/128) (by rfl) (by rfl)
    component25Node34_sound component25Node35_sound

private noncomputable def component25Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8), chiLo := (5/32), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component25Node37_sound : Sound component25Node37Box :=
  sound_of_literal_split component25Node37Box component25Node33Box component25Node36Box
    .k (41/16) (by rfl) (by rfl)
    component25Node33_sound component25Node36_sound

private noncomputable def component25Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (81/32), chiLo := (11/64), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component25Node38_sound : Sound component25Node38Box :=
  sound_of_literal_split component25Node38Box leaf1091Box leaf1092Box
    .chi (23/128) (by rfl) (by rfl)
    leaf1091FlatSound leaf1092FlatSound

private noncomputable def component25Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (81/32), kHi := (41/16), chiLo := (11/64), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component25Node39_sound : Sound component25Node39Box :=
  sound_of_literal_split component25Node39Box leaf1093Box leaf1094Box
    .chi (23/128) (by rfl) (by rfl)
    leaf1093FlatSound leaf1094FlatSound

private noncomputable def component25Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (11/64), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component25Node40_sound : Sound component25Node40Box :=
  sound_of_literal_split component25Node40Box component25Node38Box component25Node39Box
    .k (81/32) (by rfl) (by rfl)
    component25Node38_sound component25Node39_sound

private noncomputable def component25Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (83/32), chiLo := (11/64), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component25Node41_sound : Sound component25Node41Box :=
  sound_of_literal_split component25Node41Box leaf1095Box leaf1096Box
    .chi (23/128) (by rfl) (by rfl)
    leaf1095FlatSound leaf1096FlatSound

private noncomputable def component25Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (83/32), kHi := (21/8), chiLo := (11/64), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component25Node42_sound : Sound component25Node42Box :=
  sound_of_literal_split component25Node42Box leaf1097Box leaf1098Box
    .chi (23/128) (by rfl) (by rfl)
    leaf1097FlatSound leaf1098FlatSound

private noncomputable def component25Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (11/64), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component25Node43_sound : Sound component25Node43Box :=
  sound_of_literal_split component25Node43Box component25Node41Box component25Node42Box
    .k (83/32) (by rfl) (by rfl)
    component25Node41_sound component25Node42_sound

private noncomputable def component25Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8), chiLo := (11/64), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component25Node44_sound : Sound component25Node44Box :=
  sound_of_literal_split component25Node44Box component25Node40Box component25Node43Box
    .k (41/16) (by rfl) (by rfl)
    component25Node40_sound component25Node43_sound

private noncomputable def component25Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8), chiLo := (5/32), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component25Node45_sound : Sound component25Node45Box :=
  sound_of_literal_split component25Node45Box component25Node37Box component25Node44Box
    .chi (11/64) (by rfl) (by rfl)
    component25Node37_sound component25Node44_sound

private noncomputable def component25Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (5/32), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component25Node46_sound : Sound component25Node46Box :=
  sound_of_literal_split component25Node46Box leaf1099Box leaf1100Box
    .k (85/32) (by rfl) (by rfl)
    leaf1099FlatSound leaf1100FlatSound

private noncomputable def component25Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (21/128), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component25Node47_sound : Sound component25Node47Box :=
  sound_of_literal_split component25Node47Box leaf1101Box leaf1102Box
    .k (85/32) (by rfl) (by rfl)
    leaf1101FlatSound leaf1102FlatSound

private noncomputable def component25Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (5/32), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component25Node48_sound : Sound component25Node48Box :=
  sound_of_literal_split component25Node48Box component25Node46Box component25Node47Box
    .chi (21/128) (by rfl) (by rfl)
    component25Node46_sound component25Node47_sound

private noncomputable def component25Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (5/32), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component25Node49_sound : Sound component25Node49Box :=
  sound_of_literal_split component25Node49Box leaf1103Box leaf1104Box
    .k (87/32) (by rfl) (by rfl)
    leaf1103FlatSound leaf1104FlatSound

private noncomputable def component25Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (21/128), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component25Node50_sound : Sound component25Node50Box :=
  sound_of_literal_split component25Node50Box leaf1105Box leaf1106Box
    .k (87/32) (by rfl) (by rfl)
    leaf1105FlatSound leaf1106FlatSound

private noncomputable def component25Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (5/32), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component25Node51_sound : Sound component25Node51Box :=
  sound_of_literal_split component25Node51Box component25Node49Box component25Node50Box
    .chi (21/128) (by rfl) (by rfl)
    component25Node49_sound component25Node50_sound

private noncomputable def component25Node52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4), chiLo := (5/32), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component25Node52_sound : Sound component25Node52Box :=
  sound_of_literal_split component25Node52Box component25Node48Box component25Node51Box
    .k (43/16) (by rfl) (by rfl)
    component25Node48_sound component25Node51_sound

private noncomputable def component25Node53Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (85/32), chiLo := (11/64), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component25Node53_sound : Sound component25Node53Box :=
  sound_of_literal_split component25Node53Box leaf1107Box leaf1108Box
    .chi (23/128) (by rfl) (by rfl)
    leaf1107FlatSound leaf1108FlatSound

private noncomputable def component25Node54Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (85/32), kHi := (43/16), chiLo := (11/64), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component25Node54_sound : Sound component25Node54Box :=
  sound_of_literal_split component25Node54Box leaf1109Box leaf1110Box
    .chi (23/128) (by rfl) (by rfl)
    leaf1109FlatSound leaf1110FlatSound

private noncomputable def component25Node55Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (11/64), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component25Node55_sound : Sound component25Node55Box :=
  sound_of_literal_split component25Node55Box component25Node53Box component25Node54Box
    .k (85/32) (by rfl) (by rfl)
    component25Node53_sound component25Node54_sound

private noncomputable def component25Node56Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (11/64), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component25Node56_sound : Sound component25Node56Box :=
  sound_of_literal_split component25Node56Box leaf1111Box leaf1112Box
    .k (87/32) (by rfl) (by rfl)
    leaf1111FlatSound leaf1112FlatSound

private noncomputable def component25Node57Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (23/128), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component25Node57_sound : Sound component25Node57Box :=
  sound_of_literal_split component25Node57Box leaf1113Box leaf1114Box
    .k (87/32) (by rfl) (by rfl)
    leaf1113FlatSound leaf1114FlatSound

private noncomputable def component25Node58Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (11/64), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component25Node58_sound : Sound component25Node58Box :=
  sound_of_literal_split component25Node58Box component25Node56Box component25Node57Box
    .chi (23/128) (by rfl) (by rfl)
    component25Node56_sound component25Node57_sound

private noncomputable def component25Node59Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4), chiLo := (11/64), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component25Node59_sound : Sound component25Node59Box :=
  sound_of_literal_split component25Node59Box component25Node55Box component25Node58Box
    .k (43/16) (by rfl) (by rfl)
    component25Node55_sound component25Node58_sound

private noncomputable def component25Node60Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4), chiLo := (5/32), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component25Node60_sound : Sound component25Node60Box :=
  sound_of_literal_split component25Node60Box component25Node52Box component25Node59Box
    .chi (11/64) (by rfl) (by rfl)
    component25Node52_sound component25Node59_sound

private noncomputable def component25Node61Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (11/4), chiLo := (5/32), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component25Node61_sound : Sound component25Node61Box :=
  sound_of_literal_split component25Node61Box component25Node45Box component25Node60Box
    .k (21/8) (by rfl) (by rfl)
    component25Node45_sound component25Node60_sound

noncomputable def component25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (11/4), chiLo := (1/8), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
theorem component25_sound : Sound component25Box :=
  sound_of_literal_split component25Box component25Node30Box component25Node61Box
    .chi (5/32) (by rfl) (by rfl)
    component25Node30_sound component25Node61_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
