import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheSKBatch0
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

private noncomputable def leaf761Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (1/8), chiHi := (17/128) }

private noncomputable def leaf761Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217827/134217728) }, vSqrt := { lower := (65531/65536), upper := (33554496/33553871) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (167737247/134217728) }, upper := { exponent := 0, mantissa := (2609/2048) } }, logOuter := sk61LogOuterCertificate, logK := sk61LogKCertificate, logChi := chi107LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (67108367/67107742) } }, logDArg := sk61LogDArgCertificate }

private noncomputable def leaf761InnerLog : WideLogData :=
  innerPair13Data

set_option maxRecDepth 1000000 in
private theorem leaf761LocalValidity :
    LeafFacts leaf761Box leaf761Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf761Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (33554496/33553871) }) = true
      norm_num [leaf761Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf761CertificateValid :
    WideCertificateValid leaf761Box leaf761Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk61ValidityFacts chi107ValidityFacts
    leaf761LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf761CoverageChecked :
    coverageCheck (innerAD leaf761Box) leaf761InnerLog = true := by
  rfl'

private theorem leaf761InnerLogValid :
    leaf761InnerLog.Valid 8 (innerAD leaf761Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint6PositiveFacts.valid leaf761CoverageChecked

private noncomputable def leaf761InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629237/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf761InputLogOnePlusV_eq :
    leaf761InputLogOnePlusV = outerEnclosure 24
      (leaf761Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf761RoundedFacts : LeafRoundedFacts 8
    leaf761Certificate.logOnePlusV leaf761InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf761InputLogOnePlusV_eq }

private noncomputable def leaf761Inputs : Inputs :=
  inputsOfCaches globalInput sk61RoundedInputs
    chi107InputQChi innerPair13Input
    leaf761InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf761LowerChecked :
    lowerCheck 24 leaf761Box leaf761Inputs = true := by
  rfl'

private theorem leaf761CoversExact : CoversExact 8
    leaf761Box leaf761Certificate leaf761InnerLog leaf761Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk61RoundedFacts chi107RoundedFacts
    innerPair13RoundedFacts leaf761RoundedFacts (by rfl)

private theorem leaf761FlatSound : Sound leaf761Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf761CertificateValid
    leaf761InnerLogValid leaf761CoversExact leaf761LowerChecked

private noncomputable def leaf762Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (17/128), chiHi := (9/64) }

private noncomputable def leaf762Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217829/134217728) }, vSqrt := { lower := (65531/65536), upper := (16777248/16776919) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (169834269/134217728) }, upper := { exponent := 0, mantissa := (1321/1024) } }, logOuter := sk61LogOuterCertificate, logK := sk61LogKCertificate, logChi := chi108LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (33554167/33553838) } }, logDArg := sk61LogDArgCertificate }

private noncomputable def leaf762InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf762LocalValidity :
    LeafFacts leaf762Box leaf762Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf762Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (16777248/16776919) }) = true
      norm_num [leaf762Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf762CertificateValid :
    WideCertificateValid leaf762Box leaf762Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk61ValidityFacts chi108ValidityFacts
    leaf762LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf762CoverageChecked :
    coverageCheck (innerAD leaf762Box) leaf762InnerLog = true := by
  rfl'

private theorem leaf762InnerLogValid :
    leaf762InnerLog.Valid 8 (innerAD leaf762Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf762CoverageChecked

private noncomputable def leaf762InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629245/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf762InputLogOnePlusV_eq :
    leaf762InputLogOnePlusV = outerEnclosure 24
      (leaf762Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf762RoundedFacts : LeafRoundedFacts 8
    leaf762Certificate.logOnePlusV leaf762InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf762InputLogOnePlusV_eq }

private noncomputable def leaf762Inputs : Inputs :=
  inputsOfCaches globalInput sk61RoundedInputs
    chi108InputQChi innerPair16Input
    leaf762InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf762LowerChecked :
    lowerCheck 24 leaf762Box leaf762Inputs = true := by
  rfl'

private theorem leaf762CoversExact : CoversExact 8
    leaf762Box leaf762Certificate leaf762InnerLog leaf762Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk61RoundedFacts chi108RoundedFacts
    innerPair16RoundedFacts leaf762RoundedFacts (by rfl)

private theorem leaf762FlatSound : Sound leaf762Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf762CertificateValid
    leaf762InnerLogValid leaf762CoversExact leaf762LowerChecked

private noncomputable def leaf763Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (65/32), chiLo := (9/64), chiHi := (5/32) }

private noncomputable def leaf763Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217877/134217728) }, vSqrt := { lower := (65531/65536), upper := (16777232/16776891) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (171931245/134217728) }, upper := { exponent := 0, mantissa := (1349/1024) } }, logOuter := sk71LogOuterCertificate, logK := sk71LogKCertificate, logChi := chi41LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (33554123/33553782) } }, logDArg := sk71LogDArgCertificate }

private noncomputable def leaf763InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf763LocalValidity :
    LeafFacts leaf763Box leaf763Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf763Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (16777232/16776891) }) = true
      norm_num [leaf763Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf763CertificateValid :
    WideCertificateValid leaf763Box leaf763Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk71ValidityFacts chi41ValidityFacts
    leaf763LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf763CoverageChecked :
    coverageCheck (innerAD leaf763Box) leaf763InnerLog = true := by
  rfl'

private theorem leaf763InnerLogValid :
    leaf763InnerLog.Valid 8 (innerAD leaf763Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf763CoverageChecked

private noncomputable def leaf763InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629251/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf763InputLogOnePlusV_eq :
    leaf763InputLogOnePlusV = outerEnclosure 24
      (leaf763Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf763RoundedFacts : LeafRoundedFacts 8
    leaf763Certificate.logOnePlusV leaf763InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf763InputLogOnePlusV_eq }

private noncomputable def leaf763Inputs : Inputs :=
  inputsOfCaches globalInput sk71RoundedInputs
    chi41InputQChi innerPair17Input
    leaf763InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf763LowerChecked :
    lowerCheck 24 leaf763Box leaf763Inputs = true := by
  rfl'

private theorem leaf763CoversExact : CoversExact 8
    leaf763Box leaf763Certificate leaf763InnerLog leaf763Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk71RoundedFacts chi41RoundedFacts
    innerPair17RoundedFacts leaf763RoundedFacts (by rfl)

private theorem leaf763FlatSound : Sound leaf763Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf763CertificateValid
    leaf763InnerLogValid leaf763CoversExact leaf763LowerChecked

private noncomputable def leaf764Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (65/32), kHi := (33/16), chiLo := (9/64), chiHi := (5/32) }

private noncomputable def leaf764Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217879/134217728) }, vSqrt := { lower := (65531/65536), upper := (8388616/8388443) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (172521031/134217728) }, upper := { exponent := 0, mantissa := (677/512) } }, logOuter := sk72LogOuterCertificate, logK := sk72LogKCertificate, logChi := chi41LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (16777059/16776886) } }, logDArg := sk72LogDArgCertificate }

private noncomputable def leaf764InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf764LocalValidity :
    LeafFacts leaf764Box leaf764Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf764Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (8388616/8388443) }) = true
      norm_num [leaf764Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf764CertificateValid :
    WideCertificateValid leaf764Box leaf764Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk72ValidityFacts chi41ValidityFacts
    leaf764LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf764CoverageChecked :
    coverageCheck (innerAD leaf764Box) leaf764InnerLog = true := by
  rfl'

private theorem leaf764InnerLogValid :
    leaf764InnerLog.Valid 8 (innerAD leaf764Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf764CoverageChecked

private noncomputable def leaf764InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814627/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf764InputLogOnePlusV_eq :
    leaf764InputLogOnePlusV = outerEnclosure 24
      (leaf764Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf764RoundedFacts : LeafRoundedFacts 8
    leaf764Certificate.logOnePlusV leaf764InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf764InputLogOnePlusV_eq }

private noncomputable def leaf764Inputs : Inputs :=
  inputsOfCaches globalInput sk72RoundedInputs
    chi41InputQChi innerPair17Input
    leaf764InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf764LowerChecked :
    lowerCheck 24 leaf764Box leaf764Inputs = true := by
  rfl'

private theorem leaf764CoversExact : CoversExact 8
    leaf764Box leaf764Certificate leaf764InnerLog leaf764Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk72RoundedFacts chi41RoundedFacts
    innerPair17RoundedFacts leaf764RoundedFacts (by rfl)

private theorem leaf764FlatSound : Sound leaf764Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf764CertificateValid
    leaf764InnerLogValid leaf764CoversExact leaf764LowerChecked

private noncomputable def leaf765Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (1/8), chiHi := (17/128) }

private noncomputable def leaf765Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217829/134217728) }, vSqrt := { lower := (65531/65536), upper := (5592416/5592309) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (168785757/134217728) }, upper := { exponent := 0, mantissa := (1313/1024) } }, logOuter := sk62LogOuterCertificate, logK := sk62LogKCertificate, logChi := chi107LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (11184725/11184618) } }, logDArg := sk62LogDArgCertificate }

private noncomputable def leaf765InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf765LocalValidity :
    LeafFacts leaf765Box leaf765Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf765Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (5592416/5592309) }) = true
      norm_num [leaf765Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf765CertificateValid :
    WideCertificateValid leaf765Box leaf765Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk62ValidityFacts chi107ValidityFacts
    leaf765LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf765CoverageChecked :
    coverageCheck (innerAD leaf765Box) leaf765InnerLog = true := by
  rfl'

private theorem leaf765InnerLogValid :
    leaf765InnerLog.Valid 8 (innerAD leaf765Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf765CoverageChecked

private noncomputable def leaf765InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629241/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf765InputLogOnePlusV_eq :
    leaf765InputLogOnePlusV = outerEnclosure 24
      (leaf765Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf765RoundedFacts : LeafRoundedFacts 8
    leaf765Certificate.logOnePlusV leaf765InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf765InputLogOnePlusV_eq }

private noncomputable def leaf765Inputs : Inputs :=
  inputsOfCaches globalInput sk62RoundedInputs
    chi107InputQChi innerPair16Input
    leaf765InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf765LowerChecked :
    lowerCheck 24 leaf765Box leaf765Inputs = true := by
  rfl'

private theorem leaf765CoversExact : CoversExact 8
    leaf765Box leaf765Certificate leaf765InnerLog leaf765Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk62RoundedFacts chi107RoundedFacts
    innerPair16RoundedFacts leaf765RoundedFacts (by rfl)

private theorem leaf765FlatSound : Sound leaf765Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf765CertificateValid
    leaf765InnerLogValid leaf765CoversExact leaf765LowerChecked

private noncomputable def leaf766Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (17/128), chiHi := (9/64) }

private noncomputable def leaf766Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217831/134217728) }, vSqrt := { lower := (65531/65536), upper := (8388624/8388455) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (170948311/134217728) }, upper := { exponent := 0, mantissa := (665/512) } }, logOuter := sk62LogOuterCertificate, logK := sk62LogKCertificate, logChi := chi108LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (16777079/16776910) } }, logDArg := sk62LogDArgCertificate }

private noncomputable def leaf766InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf766LocalValidity :
    LeafFacts leaf766Box leaf766Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf766Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (8388624/8388455) }) = true
      norm_num [leaf766Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf766CertificateValid :
    WideCertificateValid leaf766Box leaf766Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk62ValidityFacts chi108ValidityFacts
    leaf766LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf766CoverageChecked :
    coverageCheck (innerAD leaf766Box) leaf766InnerLog = true := by
  rfl'

private theorem leaf766InnerLogValid :
    leaf766InnerLog.Valid 8 (innerAD leaf766Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf766CoverageChecked

private noncomputable def leaf766InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814625/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf766InputLogOnePlusV_eq :
    leaf766InputLogOnePlusV = outerEnclosure 24
      (leaf766Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf766RoundedFacts : LeafRoundedFacts 8
    leaf766Certificate.logOnePlusV leaf766InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf766InputLogOnePlusV_eq }

private noncomputable def leaf766Inputs : Inputs :=
  inputsOfCaches globalInput sk62RoundedInputs
    chi108InputQChi innerPair16Input
    leaf766InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf766LowerChecked :
    lowerCheck 24 leaf766Box leaf766Inputs = true := by
  rfl'

private theorem leaf766CoversExact : CoversExact 8
    leaf766Box leaf766Certificate leaf766InnerLog leaf766Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk62RoundedFacts chi108RoundedFacts
    innerPair16RoundedFacts leaf766RoundedFacts (by rfl)

private theorem leaf766FlatSound : Sound leaf766Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf766CertificateValid
    leaf766InnerLogValid leaf766CoversExact leaf766LowerChecked

private noncomputable def leaf767Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (67/32), chiLo := (9/64), chiHi := (5/32) }

private noncomputable def leaf767Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217881/134217728) }, vSqrt := { lower := (65531/65536), upper := (16777232/16776881) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (173110817/134217728) }, upper := { exponent := 0, mantissa := (1359/1024) } }, logOuter := sk73LogOuterCertificate, logK := sk73LogKCertificate, logChi := chi41LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (33554113/33553762) } }, logDArg := sk73LogDArgCertificate }

private noncomputable def leaf767InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf767LocalValidity :
    LeafFacts leaf767Box leaf767Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf767Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (16777232/16776881) }) = true
      norm_num [leaf767Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf767CertificateValid :
    WideCertificateValid leaf767Box leaf767Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk73ValidityFacts chi41ValidityFacts
    leaf767LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf767CoverageChecked :
    coverageCheck (innerAD leaf767Box) leaf767InnerLog = true := by
  rfl'

private theorem leaf767InnerLogValid :
    leaf767InnerLog.Valid 8 (innerAD leaf767Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf767CoverageChecked

private noncomputable def leaf767InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (1453657/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf767InputLogOnePlusV_eq :
    leaf767InputLogOnePlusV = outerEnclosure 24
      (leaf767Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf767RoundedFacts : LeafRoundedFacts 8
    leaf767Certificate.logOnePlusV leaf767InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf767InputLogOnePlusV_eq }

private noncomputable def leaf767Inputs : Inputs :=
  inputsOfCaches globalInput sk73RoundedInputs
    chi41InputQChi innerPair17Input
    leaf767InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf767LowerChecked :
    lowerCheck 24 leaf767Box leaf767Inputs = true := by
  rfl'

private theorem leaf767CoversExact : CoversExact 8
    leaf767Box leaf767Certificate leaf767InnerLog leaf767Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk73RoundedFacts chi41RoundedFacts
    innerPair17RoundedFacts leaf767RoundedFacts (by rfl)

private theorem leaf767FlatSound : Sound leaf767Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf767CertificateValid
    leaf767InnerLogValid leaf767CoversExact leaf767LowerChecked

private noncomputable def leaf768Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (67/32), kHi := (17/8), chiLo := (9/64), chiHi := (5/32) }

private noncomputable def leaf768Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217883/134217728) }, vSqrt := { lower := (65531/65536), upper := (4194308/4194219) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (173700603/134217728) }, upper := { exponent := 0, mantissa := (341/256) } }, logOuter := sk74LogOuterCertificate, logK := sk74LogKCertificate, logChi := chi41LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (8388527/8388438) } }, logDArg := sk74LogDArgCertificate }

private noncomputable def leaf768InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf768LocalValidity :
    LeafFacts leaf768Box leaf768Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf768Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (4194308/4194219) }) = true
      norm_num [leaf768Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf768CertificateValid :
    WideCertificateValid leaf768Box leaf768Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk74ValidityFacts chi41ValidityFacts
    leaf768LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf768CoverageChecked :
    coverageCheck (innerAD leaf768Box) leaf768InnerLog = true := by
  rfl'

private theorem leaf768InnerLogValid :
    leaf768InnerLog.Valid 8 (innerAD leaf768Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf768CoverageChecked

private noncomputable def leaf768InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629259/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf768InputLogOnePlusV_eq :
    leaf768InputLogOnePlusV = outerEnclosure 24
      (leaf768Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf768RoundedFacts : LeafRoundedFacts 8
    leaf768Certificate.logOnePlusV leaf768InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf768InputLogOnePlusV_eq }

private noncomputable def leaf768Inputs : Inputs :=
  inputsOfCaches globalInput sk74RoundedInputs
    chi41InputQChi innerPair17Input
    leaf768InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf768LowerChecked :
    lowerCheck 24 leaf768Box leaf768Inputs = true := by
  rfl'

private theorem leaf768CoversExact : CoversExact 8
    leaf768Box leaf768Certificate leaf768InnerLog leaf768Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk74RoundedFacts chi41RoundedFacts
    innerPair17RoundedFacts leaf768RoundedFacts (by rfl)

private theorem leaf768FlatSound : Sound leaf768Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf768CertificateValid
    leaf768InnerLogValid leaf768CoversExact leaf768LowerChecked

private noncomputable def leaf769Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (65/32), chiLo := (5/32), chiHi := (11/64) }

private noncomputable def leaf769Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217879/134217728) }, vSqrt := { lower := (65531/65536), upper := (33554464/33553717) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (176125291/134217728) }, upper := { exponent := 0, mantissa := (2763/2048) } }, logOuter := sk71LogOuterCertificate, logK := sk71LogKCertificate, logChi := chi42LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (67108181/67107434) } }, logDArg := sk71LogDArgCertificate }

private noncomputable def leaf769InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf769LocalValidity :
    LeafFacts leaf769Box leaf769Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf769Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (33554464/33553717) }) = true
      norm_num [leaf769Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf769CertificateValid :
    WideCertificateValid leaf769Box leaf769Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk71ValidityFacts chi42ValidityFacts
    leaf769LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf769CoverageChecked :
    coverageCheck (innerAD leaf769Box) leaf769InnerLog = true := by
  rfl'

private theorem leaf769InnerLogValid :
    leaf769InnerLog.Valid 8 (innerAD leaf769Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf769CoverageChecked

private noncomputable def leaf769InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629267/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf769InputLogOnePlusV_eq :
    leaf769InputLogOnePlusV = outerEnclosure 24
      (leaf769Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf769RoundedFacts : LeafRoundedFacts 8
    leaf769Certificate.logOnePlusV leaf769InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf769InputLogOnePlusV_eq }

private noncomputable def leaf769Inputs : Inputs :=
  inputsOfCaches globalInput sk71RoundedInputs
    chi42InputQChi innerPair17Input
    leaf769InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf769LowerChecked :
    lowerCheck 24 leaf769Box leaf769Inputs = true := by
  rfl'

private theorem leaf769CoversExact : CoversExact 8
    leaf769Box leaf769Certificate leaf769InnerLog leaf769Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk71RoundedFacts chi42RoundedFacts
    innerPair17RoundedFacts leaf769RoundedFacts (by rfl)

private theorem leaf769FlatSound : Sound leaf769Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf769CertificateValid
    leaf769InnerLogValid leaf769CoversExact leaf769LowerChecked

private noncomputable def leaf770Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (65/32), kHi := (33/16), chiLo := (5/32), chiHi := (11/64) }

private noncomputable def leaf770Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217881/134217728) }, vSqrt := { lower := (65531/65536), upper := (16777232/16776853) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (176780609/134217728) }, upper := { exponent := 0, mantissa := (1387/1024) } }, logOuter := sk72LogOuterCertificate, logK := sk72LogKCertificate, logChi := chi42LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (33554085/33553706) } }, logDArg := sk72LogDArgCertificate }

private noncomputable def leaf770InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf770LocalValidity :
    LeafFacts leaf770Box leaf770Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf770Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (16777232/16776853) }) = true
      norm_num [leaf770Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf770CertificateValid :
    WideCertificateValid leaf770Box leaf770Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk72ValidityFacts chi42ValidityFacts
    leaf770LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf770CoverageChecked :
    coverageCheck (innerAD leaf770Box) leaf770InnerLog = true := by
  rfl'

private theorem leaf770InnerLogValid :
    leaf770InnerLog.Valid 8 (innerAD leaf770Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf770CoverageChecked

private noncomputable def leaf770InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814635/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf770InputLogOnePlusV_eq :
    leaf770InputLogOnePlusV = outerEnclosure 24
      (leaf770Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf770RoundedFacts : LeafRoundedFacts 8
    leaf770Certificate.logOnePlusV leaf770InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf770InputLogOnePlusV_eq }

private noncomputable def leaf770Inputs : Inputs :=
  inputsOfCaches globalInput sk72RoundedInputs
    chi42InputQChi innerPair21Input
    leaf770InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf770LowerChecked :
    lowerCheck 24 leaf770Box leaf770Inputs = true := by
  rfl'

private theorem leaf770CoversExact : CoversExact 8
    leaf770Box leaf770Certificate leaf770InnerLog leaf770Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk72RoundedFacts chi42RoundedFacts
    innerPair21RoundedFacts leaf770RoundedFacts (by rfl)

private theorem leaf770FlatSound : Sound leaf770Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf770CertificateValid
    leaf770InnerLogValid leaf770CoversExact leaf770LowerChecked

private noncomputable def leaf771Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (65/32), chiLo := (11/64), chiHi := (3/16) }

private noncomputable def leaf771Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217881/134217728) }, vSqrt := { lower := (65531/65536), upper := (8388616/8388413) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (180319337/134217728) }, upper := { exponent := 0, mantissa := (707/512) } }, logOuter := sk71LogOuterCertificate, logK := sk71LogKCertificate, logChi := chi43LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (16777029/16776826) } }, logDArg := sk71LogDArgCertificate }

private noncomputable def leaf771InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf771LocalValidity :
    LeafFacts leaf771Box leaf771Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf771Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (8388616/8388413) }) = true
      norm_num [leaf771Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf771CertificateValid :
    WideCertificateValid leaf771Box leaf771Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk71ValidityFacts chi43ValidityFacts
    leaf771LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf771CoverageChecked :
    coverageCheck (innerAD leaf771Box) leaf771InnerLog = true := by
  rfl'

private theorem leaf771InnerLogValid :
    leaf771InnerLog.Valid 8 (innerAD leaf771Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf771CoverageChecked

private noncomputable def leaf771InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (2907321/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf771InputLogOnePlusV_eq :
    leaf771InputLogOnePlusV = outerEnclosure 24
      (leaf771Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf771RoundedFacts : LeafRoundedFacts 8
    leaf771Certificate.logOnePlusV leaf771InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf771InputLogOnePlusV_eq }

private noncomputable def leaf771Inputs : Inputs :=
  inputsOfCaches globalInput sk71RoundedInputs
    chi43InputQChi innerPair22Input
    leaf771InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf771LowerChecked :
    lowerCheck 24 leaf771Box leaf771Inputs = true := by
  rfl'

private theorem leaf771CoversExact : CoversExact 8
    leaf771Box leaf771Certificate leaf771InnerLog leaf771Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk71RoundedFacts chi43RoundedFacts
    innerPair22RoundedFacts leaf771RoundedFacts (by rfl)

private theorem leaf771FlatSound : Sound leaf771Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf771CertificateValid
    leaf771InnerLogValid leaf771CoversExact leaf771LowerChecked

private noncomputable def leaf772Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (65/32), kHi := (33/16), chiLo := (11/64), chiHi := (3/16) }

private noncomputable def leaf772Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217883/134217728) }, vSqrt := { lower := (65531/65536), upper := (4194308/4194205) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (181040187/134217728) }, upper := { exponent := 0, mantissa := (355/256) } }, logOuter := sk72LogOuterCertificate, logK := sk72LogKCertificate, logChi := chi43LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (8388513/8388410) } }, logDArg := sk72LogDArgCertificate }

private noncomputable def leaf772InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf772LocalValidity :
    LeafFacts leaf772Box leaf772Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf772Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (4194308/4194205) }) = true
      norm_num [leaf772Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf772CertificateValid :
    WideCertificateValid leaf772Box leaf772Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk72ValidityFacts chi43ValidityFacts
    leaf772LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf772CoverageChecked :
    coverageCheck (innerAD leaf772Box) leaf772InnerLog = true := by
  rfl'

private theorem leaf772InnerLogValid :
    leaf772InnerLog.Valid 8 (innerAD leaf772Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf772CoverageChecked

private noncomputable def leaf772InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629287/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf772InputLogOnePlusV_eq :
    leaf772InputLogOnePlusV = outerEnclosure 24
      (leaf772Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf772RoundedFacts : LeafRoundedFacts 8
    leaf772Certificate.logOnePlusV leaf772InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf772InputLogOnePlusV_eq }

private noncomputable def leaf772Inputs : Inputs :=
  inputsOfCaches globalInput sk72RoundedInputs
    chi43InputQChi innerPair22Input
    leaf772InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf772LowerChecked :
    lowerCheck 24 leaf772Box leaf772Inputs = true := by
  rfl'

private theorem leaf772CoversExact : CoversExact 8
    leaf772Box leaf772Certificate leaf772InnerLog leaf772Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk72RoundedFacts chi43RoundedFacts
    innerPair22RoundedFacts leaf772RoundedFacts (by rfl)

private theorem leaf772FlatSound : Sound leaf772Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf772CertificateValid
    leaf772InnerLogValid leaf772CoversExact leaf772LowerChecked

private noncomputable def leaf773Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (67/32), chiLo := (5/32), chiHi := (11/64) }

private noncomputable def leaf773Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217883/134217728) }, vSqrt := { lower := (65531/65536), upper := (33554464/33553695) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (177435927/134217728) }, upper := { exponent := 0, mantissa := (2785/2048) } }, logOuter := sk73LogOuterCertificate, logK := sk73LogKCertificate, logChi := chi42LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (67108159/67107390) } }, logDArg := sk73LogDArgCertificate }

private noncomputable def leaf773InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf773LocalValidity :
    LeafFacts leaf773Box leaf773Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf773Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (33554464/33553695) }) = true
      norm_num [leaf773Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf773CertificateValid :
    WideCertificateValid leaf773Box leaf773Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk73ValidityFacts chi42ValidityFacts
    leaf773LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf773CoverageChecked :
    coverageCheck (innerAD leaf773Box) leaf773InnerLog = true := by
  rfl'

private theorem leaf773InnerLogValid :
    leaf773InnerLog.Valid 8 (innerAD leaf773Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf773CoverageChecked

private noncomputable def leaf773InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629273/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf773InputLogOnePlusV_eq :
    leaf773InputLogOnePlusV = outerEnclosure 24
      (leaf773Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf773RoundedFacts : LeafRoundedFacts 8
    leaf773Certificate.logOnePlusV leaf773InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf773InputLogOnePlusV_eq }

private noncomputable def leaf773Inputs : Inputs :=
  inputsOfCaches globalInput sk73RoundedInputs
    chi42InputQChi innerPair21Input
    leaf773InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf773LowerChecked :
    lowerCheck 24 leaf773Box leaf773Inputs = true := by
  rfl'

private theorem leaf773CoversExact : CoversExact 8
    leaf773Box leaf773Certificate leaf773InnerLog leaf773Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk73RoundedFacts chi42RoundedFacts
    innerPair21RoundedFacts leaf773RoundedFacts (by rfl)

private theorem leaf773FlatSound : Sound leaf773Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf773CertificateValid
    leaf773InnerLogValid leaf773CoversExact leaf773LowerChecked

private noncomputable def leaf774Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (67/32), kHi := (17/8), chiLo := (5/32), chiHi := (11/64) }

private noncomputable def leaf774Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217885/134217728) }, vSqrt := { lower := (65531/65536), upper := (8388616/8388421) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (178091245/134217728) }, upper := { exponent := 0, mantissa := (699/512) } }, logOuter := sk74LogOuterCertificate, logK := sk74LogKCertificate, logChi := chi42LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (16777037/16776842) } }, logDArg := sk74LogDArgCertificate }

private noncomputable def leaf774InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf774LocalValidity :
    LeafFacts leaf774Box leaf774Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf774Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (8388616/8388421) }) = true
      norm_num [leaf774Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf774CertificateValid :
    WideCertificateValid leaf774Box leaf774Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk74ValidityFacts chi42ValidityFacts
    leaf774LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf774CoverageChecked :
    coverageCheck (innerAD leaf774Box) leaf774InnerLog = true := by
  rfl'

private theorem leaf774InnerLogValid :
    leaf774InnerLog.Valid 8 (innerAD leaf774Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf774CoverageChecked

private noncomputable def leaf774InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (2907319/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf774InputLogOnePlusV_eq :
    leaf774InputLogOnePlusV = outerEnclosure 24
      (leaf774Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf774RoundedFacts : LeafRoundedFacts 8
    leaf774Certificate.logOnePlusV leaf774InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf774InputLogOnePlusV_eq }

private noncomputable def leaf774Inputs : Inputs :=
  inputsOfCaches globalInput sk74RoundedInputs
    chi42InputQChi innerPair21Input
    leaf774InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf774LowerChecked :
    lowerCheck 24 leaf774Box leaf774Inputs = true := by
  rfl'

private theorem leaf774CoversExact : CoversExact 8
    leaf774Box leaf774Certificate leaf774InnerLog leaf774Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk74RoundedFacts chi42RoundedFacts
    innerPair21RoundedFacts leaf774RoundedFacts (by rfl)

private theorem leaf774FlatSound : Sound leaf774Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf774CertificateValid
    leaf774InnerLogValid leaf774CoversExact leaf774LowerChecked

private noncomputable def leaf775Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (67/32), chiLo := (11/64), chiHi := (3/16) }

private noncomputable def leaf775Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217885/134217728) }, vSqrt := { lower := (65531/65536), upper := (8388616/8388407) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (181761037/134217728) }, upper := { exponent := 0, mantissa := (713/512) } }, logOuter := sk73LogOuterCertificate, logK := sk73LogKCertificate, logChi := chi43LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (16777023/16776814) } }, logDArg := sk73LogDArgCertificate }

private noncomputable def leaf775InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf775LocalValidity :
    LeafFacts leaf775Box leaf775Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf775Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (8388616/8388407) }) = true
      norm_num [leaf775Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf775CertificateValid :
    WideCertificateValid leaf775Box leaf775Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk73ValidityFacts chi43ValidityFacts
    leaf775LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf775CoverageChecked :
    coverageCheck (innerAD leaf775Box) leaf775InnerLog = true := by
  rfl'

private theorem leaf775InnerLogValid :
    leaf775InnerLog.Valid 8 (innerAD leaf775Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf775CoverageChecked

private noncomputable def leaf775InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814645/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf775InputLogOnePlusV_eq :
    leaf775InputLogOnePlusV = outerEnclosure 24
      (leaf775Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf775RoundedFacts : LeafRoundedFacts 8
    leaf775Certificate.logOnePlusV leaf775InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf775InputLogOnePlusV_eq }

private noncomputable def leaf775Inputs : Inputs :=
  inputsOfCaches globalInput sk73RoundedInputs
    chi43InputQChi innerPair22Input
    leaf775InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf775LowerChecked :
    lowerCheck 24 leaf775Box leaf775Inputs = true := by
  rfl'

private theorem leaf775CoversExact : CoversExact 8
    leaf775Box leaf775Certificate leaf775InnerLog leaf775Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk73RoundedFacts chi43RoundedFacts
    innerPair22RoundedFacts leaf775RoundedFacts (by rfl)

private theorem leaf775FlatSound : Sound leaf775Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf775CertificateValid
    leaf775InnerLogValid leaf775CoversExact leaf775LowerChecked

private noncomputable def leaf776Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (67/32), kHi := (17/8), chiLo := (11/64), chiHi := (3/16) }

private noncomputable def leaf776Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217887/134217728) }, vSqrt := { lower := (65531/65536), upper := (2097154/2097101) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (182481887/134217728) }, upper := { exponent := 0, mantissa := (179/128) } }, logOuter := sk74LogOuterCertificate, logK := sk74LogKCertificate, logChi := chi43LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (4194255/4194202) } }, logDArg := sk74LogDArgCertificate }

private noncomputable def leaf776InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf776LocalValidity :
    LeafFacts leaf776Box leaf776Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf776Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (2097154/2097101) }) = true
      norm_num [leaf776Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf776CertificateValid :
    WideCertificateValid leaf776Box leaf776Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk74ValidityFacts chi43ValidityFacts
    leaf776LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf776CoverageChecked :
    coverageCheck (innerAD leaf776Box) leaf776InnerLog = true := by
  rfl'

private theorem leaf776InnerLogValid :
    leaf776InnerLog.Valid 8 (innerAD leaf776Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf776CoverageChecked

private noncomputable def leaf776InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629293/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf776InputLogOnePlusV_eq :
    leaf776InputLogOnePlusV = outerEnclosure 24
      (leaf776Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf776RoundedFacts : LeafRoundedFacts 8
    leaf776Certificate.logOnePlusV leaf776InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf776InputLogOnePlusV_eq }

private noncomputable def leaf776Inputs : Inputs :=
  inputsOfCaches globalInput sk74RoundedInputs
    chi43InputQChi innerPair22Input
    leaf776InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf776LowerChecked :
    lowerCheck 24 leaf776Box leaf776Inputs = true := by
  rfl'

private theorem leaf776CoversExact : CoversExact 8
    leaf776Box leaf776Certificate leaf776InnerLog leaf776Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk74RoundedFacts chi43RoundedFacts
    innerPair22RoundedFacts leaf776RoundedFacts (by rfl)

private theorem leaf776FlatSound : Sound leaf776Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf776CertificateValid
    leaf776InnerLogValid leaf776CoversExact leaf776LowerChecked

private noncomputable def leaf777Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (1/8), chiHi := (17/128) }

private noncomputable def leaf777Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217831/134217728) }, vSqrt := { lower := (65531/65536), upper := (33554496/33553837) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (169834267/134217728) }, upper := { exponent := 0, mantissa := (2643/2048) } }, logOuter := sk63LogOuterCertificate, logK := sk63LogKCertificate, logChi := chi107LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (67108333/67107674) } }, logDArg := sk63LogDArgCertificate }

private noncomputable def leaf777InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf777LocalValidity :
    LeafFacts leaf777Box leaf777Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf777Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (33554496/33553837) }) = true
      norm_num [leaf777Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf777CertificateValid :
    WideCertificateValid leaf777Box leaf777Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk63ValidityFacts chi107ValidityFacts
    leaf777LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf777CoverageChecked :
    coverageCheck (innerAD leaf777Box) leaf777InnerLog = true := by
  rfl'

private theorem leaf777InnerLogValid :
    leaf777InnerLog.Valid 8 (innerAD leaf777Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf777CoverageChecked

private noncomputable def leaf777InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629245/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf777InputLogOnePlusV_eq :
    leaf777InputLogOnePlusV = outerEnclosure 24
      (leaf777Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf777RoundedFacts : LeafRoundedFacts 8
    leaf777Certificate.logOnePlusV leaf777InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf777InputLogOnePlusV_eq }

private noncomputable def leaf777Inputs : Inputs :=
  inputsOfCaches globalInput sk63RoundedInputs
    chi107InputQChi innerPair16Input
    leaf777InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf777LowerChecked :
    lowerCheck 24 leaf777Box leaf777Inputs = true := by
  rfl'

private theorem leaf777CoversExact : CoversExact 8
    leaf777Box leaf777Certificate leaf777InnerLog leaf777Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk63RoundedFacts chi107RoundedFacts
    innerPair16RoundedFacts leaf777RoundedFacts (by rfl)

private theorem leaf777FlatSound : Sound leaf777Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf777CertificateValid
    leaf777InnerLogValid leaf777CoversExact leaf777LowerChecked

private noncomputable def leaf778Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (17/128), chiHi := (9/64) }

private noncomputable def leaf778Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217833/134217728) }, vSqrt := { lower := (65531/65536), upper := (16777248/16776901) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (172062353/134217728) }, upper := { exponent := 0, mantissa := (1339/1024) } }, logOuter := sk63LogOuterCertificate, logK := sk63LogKCertificate, logChi := chi108LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (33554149/33553802) } }, logDArg := sk63LogDArgCertificate }

private noncomputable def leaf778InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf778LocalValidity :
    LeafFacts leaf778Box leaf778Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf778Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (16777248/16776901) }) = true
      norm_num [leaf778Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf778CertificateValid :
    WideCertificateValid leaf778Box leaf778Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk63ValidityFacts chi108ValidityFacts
    leaf778LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf778CoverageChecked :
    coverageCheck (innerAD leaf778Box) leaf778InnerLog = true := by
  rfl'

private theorem leaf778InnerLogValid :
    leaf778InnerLog.Valid 8 (innerAD leaf778Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf778CoverageChecked

private noncomputable def leaf778InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814627/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf778InputLogOnePlusV_eq :
    leaf778InputLogOnePlusV = outerEnclosure 24
      (leaf778Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf778RoundedFacts : LeafRoundedFacts 8
    leaf778Certificate.logOnePlusV leaf778InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf778InputLogOnePlusV_eq }

private noncomputable def leaf778Inputs : Inputs :=
  inputsOfCaches globalInput sk63RoundedInputs
    chi108InputQChi innerPair16Input
    leaf778InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf778LowerChecked :
    lowerCheck 24 leaf778Box leaf778Inputs = true := by
  rfl'

private theorem leaf778CoversExact : CoversExact 8
    leaf778Box leaf778Certificate leaf778InnerLog leaf778Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk63RoundedFacts chi108RoundedFacts
    innerPair16RoundedFacts leaf778RoundedFacts (by rfl)

private theorem leaf778FlatSound : Sound leaf778Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf778CertificateValid
    leaf778InnerLogValid leaf778CoversExact leaf778LowerChecked

private noncomputable def leaf779Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (1/8), chiHi := (17/128) }

private noncomputable def leaf779Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217833/134217728) }, vSqrt := { lower := (65531/65536), upper := (8388624/8388455) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (170882777/134217728) }, upper := { exponent := 0, mantissa := (665/512) } }, logOuter := sk64LogOuterCertificate, logK := sk64LogKCertificate, logChi := chi107LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (16777079/16776910) } }, logDArg := sk64LogDArgCertificate }

private noncomputable def leaf779InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf779LocalValidity :
    LeafFacts leaf779Box leaf779Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf779Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (8388624/8388455) }) = true
      norm_num [leaf779Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf779CertificateValid :
    WideCertificateValid leaf779Box leaf779Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk64ValidityFacts chi107ValidityFacts
    leaf779LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf779CoverageChecked :
    coverageCheck (innerAD leaf779Box) leaf779InnerLog = true := by
  rfl'

private theorem leaf779InnerLogValid :
    leaf779InnerLog.Valid 8 (innerAD leaf779Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf779CoverageChecked

private noncomputable def leaf779InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814625/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf779InputLogOnePlusV_eq :
    leaf779InputLogOnePlusV = outerEnclosure 24
      (leaf779Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf779RoundedFacts : LeafRoundedFacts 8
    leaf779Certificate.logOnePlusV leaf779InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf779InputLogOnePlusV_eq }

private noncomputable def leaf779Inputs : Inputs :=
  inputsOfCaches globalInput sk64RoundedInputs
    chi107InputQChi innerPair16Input
    leaf779InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf779LowerChecked :
    lowerCheck 24 leaf779Box leaf779Inputs = true := by
  rfl'

private theorem leaf779CoversExact : CoversExact 8
    leaf779Box leaf779Certificate leaf779InnerLog leaf779Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk64RoundedFacts chi107RoundedFacts
    innerPair16RoundedFacts leaf779RoundedFacts (by rfl)

private theorem leaf779FlatSound : Sound leaf779Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf779CertificateValid
    leaf779InnerLogValid leaf779CoversExact leaf779LowerChecked

private noncomputable def leaf780Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (17/128), chiHi := (9/64) }

private noncomputable def leaf780Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217835/134217728) }, vSqrt := { lower := (65531/65536), upper := (4194312/4194223) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (173176395/134217728) }, upper := { exponent := 0, mantissa := (337/256) } }, logOuter := sk64LogOuterCertificate, logK := sk64LogKCertificate, logChi := chi108LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (8388535/8388446) } }, logDArg := sk64LogDArgCertificate }

private noncomputable def leaf780InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf780LocalValidity :
    LeafFacts leaf780Box leaf780Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf780Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (4194312/4194223) }) = true
      norm_num [leaf780Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf780CertificateValid :
    WideCertificateValid leaf780Box leaf780Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk64ValidityFacts chi108ValidityFacts
    leaf780LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf780CoverageChecked :
    coverageCheck (innerAD leaf780Box) leaf780InnerLog = true := by
  rfl'

private theorem leaf780InnerLogValid :
    leaf780InnerLog.Valid 8 (innerAD leaf780Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf780CoverageChecked

private noncomputable def leaf780InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629259/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf780InputLogOnePlusV_eq :
    leaf780InputLogOnePlusV = outerEnclosure 24
      (leaf780Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf780RoundedFacts : LeafRoundedFacts 8
    leaf780Certificate.logOnePlusV leaf780InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf780InputLogOnePlusV_eq }

private noncomputable def leaf780Inputs : Inputs :=
  inputsOfCaches globalInput sk64RoundedInputs
    chi108InputQChi innerPair17Input
    leaf780InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf780LowerChecked :
    lowerCheck 24 leaf780Box leaf780Inputs = true := by
  rfl'

private theorem leaf780CoversExact : CoversExact 8
    leaf780Box leaf780Certificate leaf780InnerLog leaf780Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk64RoundedFacts chi108RoundedFacts
    innerPair17RoundedFacts leaf780RoundedFacts (by rfl)

private theorem leaf780FlatSound : Sound leaf780Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf780CertificateValid
    leaf780InnerLogValid leaf780CoversExact leaf780LowerChecked

private noncomputable def leaf781Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (9/64), chiHi := (19/128) }

private noncomputable def leaf781Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217835/134217728) }, vSqrt := { lower := (65531/65536), upper := (11184832/11184589) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (174290439/134217728) }, upper := { exponent := 0, mantissa := (2713/2048) } }, logOuter := sk63LogOuterCertificate, logK := sk63LogKCertificate, logChi := chi109LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (22369421/22369178) } }, logDArg := sk63LogDArgCertificate }

private noncomputable def leaf781InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf781LocalValidity :
    LeafFacts leaf781Box leaf781Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf781Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (11184832/11184589) }) = true
      norm_num [leaf781Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf781CertificateValid :
    WideCertificateValid leaf781Box leaf781Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk63ValidityFacts chi109ValidityFacts
    leaf781LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf781CoverageChecked :
    coverageCheck (innerAD leaf781Box) leaf781InnerLog = true := by
  rfl'

private theorem leaf781InnerLogValid :
    leaf781InnerLog.Valid 8 (innerAD leaf781Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf781CoverageChecked

private noncomputable def leaf781InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629263/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf781InputLogOnePlusV_eq :
    leaf781InputLogOnePlusV = outerEnclosure 24
      (leaf781Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf781RoundedFacts : LeafRoundedFacts 8
    leaf781Certificate.logOnePlusV leaf781InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf781InputLogOnePlusV_eq }

private noncomputable def leaf781Inputs : Inputs :=
  inputsOfCaches globalInput sk63RoundedInputs
    chi109InputQChi innerPair17Input
    leaf781InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf781LowerChecked :
    lowerCheck 24 leaf781Box leaf781Inputs = true := by
  rfl'

private theorem leaf781CoversExact : CoversExact 8
    leaf781Box leaf781Certificate leaf781InnerLog leaf781Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk63RoundedFacts chi109RoundedFacts
    innerPair17RoundedFacts leaf781RoundedFacts (by rfl)

private theorem leaf781FlatSound : Sound leaf781Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf781CertificateValid
    leaf781InnerLogValid leaf781CoversExact leaf781LowerChecked

private noncomputable def leaf782Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (19/128), chiHi := (5/32) }

private noncomputable def leaf782Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217837/134217728) }, vSqrt := { lower := (65531/65536), upper := (8388624/8388433) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (176518525/134217728) }, upper := { exponent := 0, mantissa := (687/512) } }, logOuter := sk63LogOuterCertificate, logK := sk63LogKCertificate, logChi := chi110LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (16777057/16776866) } }, logDArg := sk63LogDArgCertificate }

private noncomputable def leaf782InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf782LocalValidity :
    LeafFacts leaf782Box leaf782Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf782Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (8388624/8388433) }) = true
      norm_num [leaf782Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf782CertificateValid :
    WideCertificateValid leaf782Box leaf782Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk63ValidityFacts chi110ValidityFacts
    leaf782LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf782CoverageChecked :
    coverageCheck (innerAD leaf782Box) leaf782InnerLog = true := by
  rfl'

private theorem leaf782InnerLogValid :
    leaf782InnerLog.Valid 8 (innerAD leaf782Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf782CoverageChecked

private noncomputable def leaf782InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (1453659/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf782InputLogOnePlusV_eq :
    leaf782InputLogOnePlusV = outerEnclosure 24
      (leaf782Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf782RoundedFacts : LeafRoundedFacts 8
    leaf782Certificate.logOnePlusV leaf782InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf782InputLogOnePlusV_eq }

private noncomputable def leaf782Inputs : Inputs :=
  inputsOfCaches globalInput sk63RoundedInputs
    chi110InputQChi innerPair21Input
    leaf782InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf782LowerChecked :
    lowerCheck 24 leaf782Box leaf782Inputs = true := by
  rfl'

private theorem leaf782CoversExact : CoversExact 8
    leaf782Box leaf782Certificate leaf782InnerLog leaf782Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk63RoundedFacts chi110RoundedFacts
    innerPair21RoundedFacts leaf782RoundedFacts (by rfl)

private theorem leaf782FlatSound : Sound leaf782Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf782CertificateValid
    leaf782InnerLogValid leaf782CoversExact leaf782LowerChecked

private noncomputable def leaf783Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (9/64), chiHi := (19/128) }

private noncomputable def leaf783Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217837/134217728) }, vSqrt := { lower := (65531/65536), upper := (8388624/8388437) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (175470013/134217728) }, upper := { exponent := 0, mantissa := (683/512) } }, logOuter := sk64LogOuterCertificate, logK := sk64LogKCertificate, logChi := chi109LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (16777061/16776874) } }, logDArg := sk64LogDArgCertificate }

private noncomputable def leaf783InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf783LocalValidity :
    LeafFacts leaf783Box leaf783Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf783Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (8388624/8388437) }) = true
      norm_num [leaf783Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf783CertificateValid :
    WideCertificateValid leaf783Box leaf783Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk64ValidityFacts chi109ValidityFacts
    leaf783LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf783CoverageChecked :
    coverageCheck (innerAD leaf783Box) leaf783InnerLog = true := by
  rfl'

private theorem leaf783InnerLogValid :
    leaf783InnerLog.Valid 8 (innerAD leaf783Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf783CoverageChecked

private noncomputable def leaf783InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (2907317/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf783InputLogOnePlusV_eq :
    leaf783InputLogOnePlusV = outerEnclosure 24
      (leaf783Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf783RoundedFacts : LeafRoundedFacts 8
    leaf783Certificate.logOnePlusV leaf783InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf783InputLogOnePlusV_eq }

private noncomputable def leaf783Inputs : Inputs :=
  inputsOfCaches globalInput sk64RoundedInputs
    chi109InputQChi innerPair17Input
    leaf783InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf783LowerChecked :
    lowerCheck 24 leaf783Box leaf783Inputs = true := by
  rfl'

private theorem leaf783CoversExact : CoversExact 8
    leaf783Box leaf783Certificate leaf783InnerLog leaf783Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk64RoundedFacts chi109RoundedFacts
    innerPair17RoundedFacts leaf783RoundedFacts (by rfl)

private theorem leaf783FlatSound : Sound leaf783Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf783CertificateValid
    leaf783InnerLogValid leaf783CoversExact leaf783LowerChecked

private noncomputable def leaf784Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (19/128), chiHi := (5/32) }

private noncomputable def leaf784Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217839/134217728) }, vSqrt := { lower := (65531/65536), upper := (2097156/2097107) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (177763631/134217728) }, upper := { exponent := 0, mantissa := (173/128) } }, logOuter := sk64LogOuterCertificate, logK := sk64LogKCertificate, logChi := chi110LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (4194263/4194214) } }, logDArg := sk64LogDArgCertificate }

private noncomputable def leaf784InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf784LocalValidity :
    LeafFacts leaf784Box leaf784Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf784Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (2097156/2097107) }) = true
      norm_num [leaf784Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf784CertificateValid :
    WideCertificateValid leaf784Box leaf784Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk64ValidityFacts chi110ValidityFacts
    leaf784LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf784CoverageChecked :
    coverageCheck (innerAD leaf784Box) leaf784InnerLog = true := by
  rfl'

private theorem leaf784InnerLogValid :
    leaf784InnerLog.Valid 8 (innerAD leaf784Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf784CoverageChecked

private noncomputable def leaf784InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629277/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf784InputLogOnePlusV_eq :
    leaf784InputLogOnePlusV = outerEnclosure 24
      (leaf784Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf784RoundedFacts : LeafRoundedFacts 8
    leaf784Certificate.logOnePlusV leaf784InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf784InputLogOnePlusV_eq }

private noncomputable def leaf784Inputs : Inputs :=
  inputsOfCaches globalInput sk64RoundedInputs
    chi110InputQChi innerPair21Input
    leaf784InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf784LowerChecked :
    lowerCheck 24 leaf784Box leaf784Inputs = true := by
  rfl'

private theorem leaf784CoversExact : CoversExact 8
    leaf784Box leaf784Certificate leaf784InnerLog leaf784Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk64RoundedFacts chi110RoundedFacts
    innerPair21RoundedFacts leaf784RoundedFacts (by rfl)

private theorem leaf784FlatSound : Sound leaf784Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf784CertificateValid
    leaf784InnerLogValid leaf784CoversExact leaf784LowerChecked

private noncomputable def leaf785Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (69/32), chiLo := (5/32), chiHi := (11/64) }

private noncomputable def leaf785Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217887/134217728) }, vSqrt := { lower := (65531/65536), upper := (33554464/33553673) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (178746563/134217728) }, upper := { exponent := 0, mantissa := (2807/2048) } }, logOuter := sk75LogOuterCertificate, logK := sk75LogKCertificate, logChi := chi42LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (67108137/67107346) } }, logDArg := sk75LogDArgCertificate }

private noncomputable def leaf785InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf785LocalValidity :
    LeafFacts leaf785Box leaf785Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf785Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (33554464/33553673) }) = true
      norm_num [leaf785Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf785CertificateValid :
    WideCertificateValid leaf785Box leaf785Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk75ValidityFacts chi42ValidityFacts
    leaf785LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf785CoverageChecked :
    coverageCheck (innerAD leaf785Box) leaf785InnerLog = true := by
  rfl'

private theorem leaf785InnerLogValid :
    leaf785InnerLog.Valid 8 (innerAD leaf785Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf785CoverageChecked

private noncomputable def leaf785InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814639/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf785InputLogOnePlusV_eq :
    leaf785InputLogOnePlusV = outerEnclosure 24
      (leaf785Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf785RoundedFacts : LeafRoundedFacts 8
    leaf785Certificate.logOnePlusV leaf785InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf785InputLogOnePlusV_eq }

private noncomputable def leaf785Inputs : Inputs :=
  inputsOfCaches globalInput sk75RoundedInputs
    chi42InputQChi innerPair21Input
    leaf785InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf785LowerChecked :
    lowerCheck 24 leaf785Box leaf785Inputs = true := by
  rfl'

private theorem leaf785CoversExact : CoversExact 8
    leaf785Box leaf785Certificate leaf785InnerLog leaf785Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk75RoundedFacts chi42RoundedFacts
    innerPair21RoundedFacts leaf785RoundedFacts (by rfl)

private theorem leaf785FlatSound : Sound leaf785Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf785CertificateValid
    leaf785InnerLogValid leaf785CoversExact leaf785LowerChecked

private noncomputable def leaf786Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (69/32), kHi := (35/16), chiLo := (5/32), chiHi := (11/64) }

private noncomputable def leaf786Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217889/134217728) }, vSqrt := { lower := (65531/65536), upper := (16777232/16776831) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (179401881/134217728) }, upper := { exponent := 0, mantissa := (1409/1024) } }, logOuter := sk76LogOuterCertificate, logK := sk76LogKCertificate, logChi := chi42LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (33554063/33553662) } }, logDArg := sk76LogDArgCertificate }

private noncomputable def leaf786InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf786LocalValidity :
    LeafFacts leaf786Box leaf786Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf786Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (16777232/16776831) }) = true
      norm_num [leaf786Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf786CertificateValid :
    WideCertificateValid leaf786Box leaf786Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk76ValidityFacts chi42ValidityFacts
    leaf786LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf786CoverageChecked :
    coverageCheck (innerAD leaf786Box) leaf786InnerLog = true := by
  rfl'

private theorem leaf786InnerLogValid :
    leaf786InnerLog.Valid 8 (innerAD leaf786Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf786CoverageChecked

private noncomputable def leaf786InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629281/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf786InputLogOnePlusV_eq :
    leaf786InputLogOnePlusV = outerEnclosure 24
      (leaf786Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf786RoundedFacts : LeafRoundedFacts 8
    leaf786Certificate.logOnePlusV leaf786InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf786InputLogOnePlusV_eq }

private noncomputable def leaf786Inputs : Inputs :=
  inputsOfCaches globalInput sk76RoundedInputs
    chi42InputQChi innerPair22Input
    leaf786InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf786LowerChecked :
    lowerCheck 24 leaf786Box leaf786Inputs = true := by
  rfl'

private theorem leaf786CoversExact : CoversExact 8
    leaf786Box leaf786Certificate leaf786InnerLog leaf786Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk76RoundedFacts chi42RoundedFacts
    innerPair22RoundedFacts leaf786RoundedFacts (by rfl)

private theorem leaf786FlatSound : Sound leaf786Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf786CertificateValid
    leaf786InnerLogValid leaf786CoversExact leaf786LowerChecked

private noncomputable def leaf787Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (69/32), chiLo := (11/64), chiHi := (3/16) }

private noncomputable def leaf787Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217889/134217728) }, vSqrt := { lower := (65531/65536), upper := (8388616/8388401) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (183202737/134217728) }, upper := { exponent := 0, mantissa := (719/512) } }, logOuter := sk75LogOuterCertificate, logK := sk75LogKCertificate, logChi := chi43LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (16777017/16776802) } }, logDArg := sk75LogDArgCertificate }

private noncomputable def leaf787InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf787LocalValidity :
    LeafFacts leaf787Box leaf787Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf787Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (8388616/8388401) }) = true
      norm_num [leaf787Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf787CertificateValid :
    WideCertificateValid leaf787Box leaf787Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk75ValidityFacts chi43ValidityFacts
    leaf787LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf787CoverageChecked :
    coverageCheck (innerAD leaf787Box) leaf787InnerLog = true := by
  rfl'

private theorem leaf787InnerLogValid :
    leaf787InnerLog.Valid 8 (innerAD leaf787Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf787CoverageChecked

private noncomputable def leaf787InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (726831/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf787InputLogOnePlusV_eq :
    leaf787InputLogOnePlusV = outerEnclosure 24
      (leaf787Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf787RoundedFacts : LeafRoundedFacts 8
    leaf787Certificate.logOnePlusV leaf787InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf787InputLogOnePlusV_eq }

private noncomputable def leaf787Inputs : Inputs :=
  inputsOfCaches globalInput sk75RoundedInputs
    chi43InputQChi innerPair22Input
    leaf787InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf787LowerChecked :
    lowerCheck 24 leaf787Box leaf787Inputs = true := by
  rfl'

private theorem leaf787CoversExact : CoversExact 8
    leaf787Box leaf787Certificate leaf787InnerLog leaf787Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk75RoundedFacts chi43RoundedFacts
    innerPair22RoundedFacts leaf787RoundedFacts (by rfl)

private theorem leaf787FlatSound : Sound leaf787Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf787CertificateValid
    leaf787InnerLogValid leaf787CoversExact leaf787LowerChecked

private noncomputable def leaf788Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (69/32), kHi := (35/16), chiLo := (11/64), chiHi := (3/16) }

private noncomputable def leaf788Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217891/134217728) }, vSqrt := { lower := (65531/65536), upper := (4194308/4194199) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (183923587/134217728) }, upper := { exponent := 0, mantissa := (361/256) } }, logOuter := sk76LogOuterCertificate, logK := sk76LogKCertificate, logChi := chi43LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (8388507/8388398) } }, logDArg := sk76LogDArgCertificate }

private noncomputable def leaf788InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf788LocalValidity :
    LeafFacts leaf788Box leaf788Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf788Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (4194308/4194199) }) = true
      norm_num [leaf788Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf788CertificateValid :
    WideCertificateValid leaf788Box leaf788Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk76ValidityFacts chi43ValidityFacts
    leaf788LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf788CoverageChecked :
    coverageCheck (innerAD leaf788Box) leaf788InnerLog = true := by
  rfl'

private theorem leaf788InnerLogValid :
    leaf788InnerLog.Valid 8 (innerAD leaf788Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf788CoverageChecked

private noncomputable def leaf788InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629299/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf788InputLogOnePlusV_eq :
    leaf788InputLogOnePlusV = outerEnclosure 24
      (leaf788Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf788RoundedFacts : LeafRoundedFacts 8
    leaf788Certificate.logOnePlusV leaf788InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf788InputLogOnePlusV_eq }

private noncomputable def leaf788Inputs : Inputs :=
  inputsOfCaches globalInput sk76RoundedInputs
    chi43InputQChi innerPair22Input
    leaf788InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf788LowerChecked :
    lowerCheck 24 leaf788Box leaf788Inputs = true := by
  rfl'

private theorem leaf788CoversExact : CoversExact 8
    leaf788Box leaf788Certificate leaf788InnerLog leaf788Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk76RoundedFacts chi43RoundedFacts
    innerPair22RoundedFacts leaf788RoundedFacts (by rfl)

private theorem leaf788FlatSound : Sound leaf788Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf788CertificateValid
    leaf788InnerLogValid leaf788CoversExact leaf788LowerChecked

private noncomputable def leaf789Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (71/32), chiLo := (5/32), chiHi := (11/64) }

private noncomputable def leaf789Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217891/134217728) }, vSqrt := { lower := (65531/65536), upper := (33554464/33553651) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (180057199/134217728) }, upper := { exponent := 0, mantissa := (2829/2048) } }, logOuter := sk77LogOuterCertificate, logK := sk77LogKCertificate, logChi := chi42LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (67108115/67107302) } }, logDArg := sk77LogDArgCertificate }

private noncomputable def leaf789InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf789LocalValidity :
    LeafFacts leaf789Box leaf789Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf789Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (33554464/33553651) }) = true
      norm_num [leaf789Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf789CertificateValid :
    WideCertificateValid leaf789Box leaf789Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk77ValidityFacts chi42ValidityFacts
    leaf789LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf789CoverageChecked :
    coverageCheck (innerAD leaf789Box) leaf789InnerLog = true := by
  rfl'

private theorem leaf789InnerLogValid :
    leaf789InnerLog.Valid 8 (innerAD leaf789Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf789CoverageChecked

private noncomputable def leaf789InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (2907321/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf789InputLogOnePlusV_eq :
    leaf789InputLogOnePlusV = outerEnclosure 24
      (leaf789Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf789RoundedFacts : LeafRoundedFacts 8
    leaf789Certificate.logOnePlusV leaf789InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf789InputLogOnePlusV_eq }

private noncomputable def leaf789Inputs : Inputs :=
  inputsOfCaches globalInput sk77RoundedInputs
    chi42InputQChi innerPair22Input
    leaf789InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf789LowerChecked :
    lowerCheck 24 leaf789Box leaf789Inputs = true := by
  rfl'

private theorem leaf789CoversExact : CoversExact 8
    leaf789Box leaf789Certificate leaf789InnerLog leaf789Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk77RoundedFacts chi42RoundedFacts
    innerPair22RoundedFacts leaf789RoundedFacts (by rfl)

private theorem leaf789FlatSound : Sound leaf789Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf789CertificateValid
    leaf789InnerLogValid leaf789CoversExact leaf789LowerChecked

private noncomputable def leaf790Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (71/32), kHi := (9/4), chiLo := (5/32), chiHi := (11/64) }

private noncomputable def leaf790Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217893/134217728) }, vSqrt := { lower := (65531/65536), upper := (4194308/4194205) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (180712517/134217728) }, upper := { exponent := 0, mantissa := (355/256) } }, logOuter := sk78LogOuterCertificate, logK := sk78LogKCertificate, logChi := chi42LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (8388513/8388410) } }, logDArg := sk78LogDArgCertificate }

private noncomputable def leaf790InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf790LocalValidity :
    LeafFacts leaf790Box leaf790Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf790Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (4194308/4194205) }) = true
      norm_num [leaf790Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf790CertificateValid :
    WideCertificateValid leaf790Box leaf790Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk78ValidityFacts chi42ValidityFacts
    leaf790LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf790CoverageChecked :
    coverageCheck (innerAD leaf790Box) leaf790InnerLog = true := by
  rfl'

private theorem leaf790InnerLogValid :
    leaf790InnerLog.Valid 8 (innerAD leaf790Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf790CoverageChecked

private noncomputable def leaf790InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629287/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf790InputLogOnePlusV_eq :
    leaf790InputLogOnePlusV = outerEnclosure 24
      (leaf790Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf790RoundedFacts : LeafRoundedFacts 8
    leaf790Certificate.logOnePlusV leaf790InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf790InputLogOnePlusV_eq }

private noncomputable def leaf790Inputs : Inputs :=
  inputsOfCaches globalInput sk78RoundedInputs
    chi42InputQChi innerPair22Input
    leaf790InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf790LowerChecked :
    lowerCheck 24 leaf790Box leaf790Inputs = true := by
  rfl'

private theorem leaf790CoversExact : CoversExact 8
    leaf790Box leaf790Certificate leaf790InnerLog leaf790Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk78RoundedFacts chi42RoundedFacts
    innerPair22RoundedFacts leaf790RoundedFacts (by rfl)

private theorem leaf790FlatSound : Sound leaf790Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf790CertificateValid
    leaf790InnerLogValid leaf790CoversExact leaf790LowerChecked

private noncomputable def leaf791Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (71/32), chiLo := (11/64), chiHi := (3/16) }

private noncomputable def leaf791Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217893/134217728) }, vSqrt := { lower := (65531/65536), upper := (493448/493435) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (184644437/134217728) }, upper := { exponent := 0, mantissa := (725/512) } }, logOuter := sk77LogOuterCertificate, logK := sk77LogKCertificate, logChi := chi43LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (986883/986870) } }, logDArg := sk77LogDArgCertificate }

private noncomputable def leaf791InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf791LocalValidity :
    LeafFacts leaf791Box leaf791Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf791Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (493448/493435) }) = true
      norm_num [leaf791Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf791CertificateValid :
    WideCertificateValid leaf791Box leaf791Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk77ValidityFacts chi43ValidityFacts
    leaf791LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf791CoverageChecked :
    coverageCheck (innerAD leaf791Box) leaf791InnerLog = true := by
  rfl'

private theorem leaf791InnerLogValid :
    leaf791InnerLog.Valid 8 (innerAD leaf791Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf791CoverageChecked

private noncomputable def leaf791InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814651/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf791InputLogOnePlusV_eq :
    leaf791InputLogOnePlusV = outerEnclosure 24
      (leaf791Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf791RoundedFacts : LeafRoundedFacts 8
    leaf791Certificate.logOnePlusV leaf791InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf791InputLogOnePlusV_eq }

private noncomputable def leaf791Inputs : Inputs :=
  inputsOfCaches globalInput sk77RoundedInputs
    chi43InputQChi innerPair26Input
    leaf791InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf791LowerChecked :
    lowerCheck 24 leaf791Box leaf791Inputs = true := by
  rfl'

private theorem leaf791CoversExact : CoversExact 8
    leaf791Box leaf791Certificate leaf791InnerLog leaf791Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk77RoundedFacts chi43RoundedFacts
    innerPair26RoundedFacts leaf791RoundedFacts (by rfl)

private theorem leaf791FlatSound : Sound leaf791Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf791CertificateValid
    leaf791InnerLogValid leaf791CoversExact leaf791LowerChecked

private noncomputable def leaf792Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (71/32), kHi := (9/4), chiLo := (11/64), chiHi := (3/16) }

private noncomputable def leaf792Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217895/134217728) }, vSqrt := { lower := (65531/65536), upper := (1048577/1048549) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (185365287/134217728) }, upper := { exponent := 0, mantissa := (91/64) } }, logOuter := sk78LogOuterCertificate, logK := sk78LogKCertificate, logChi := chi43LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (1048563/1048549) } }, logDArg := sk78LogDArgCertificate }

private noncomputable def leaf792InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf792LocalValidity :
    LeafFacts leaf792Box leaf792Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf792Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (1048577/1048549) }) = true
      norm_num [leaf792Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf792CertificateValid :
    WideCertificateValid leaf792Box leaf792Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk78ValidityFacts chi43ValidityFacts
    leaf792LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf792CoverageChecked :
    coverageCheck (innerAD leaf792Box) leaf792InnerLog = true := by
  rfl'

private theorem leaf792InnerLogValid :
    leaf792InnerLog.Valid 8 (innerAD leaf792Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf792CoverageChecked

private noncomputable def leaf792InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629305/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf792InputLogOnePlusV_eq :
    leaf792InputLogOnePlusV = outerEnclosure 24
      (leaf792Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf792RoundedFacts : LeafRoundedFacts 8
    leaf792Certificate.logOnePlusV leaf792InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf792InputLogOnePlusV_eq }

private noncomputable def leaf792Inputs : Inputs :=
  inputsOfCaches globalInput sk78RoundedInputs
    chi43InputQChi innerPair26Input
    leaf792InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf792LowerChecked :
    lowerCheck 24 leaf792Box leaf792Inputs = true := by
  rfl'

private theorem leaf792CoversExact : CoversExact 8
    leaf792Box leaf792Certificate leaf792InnerLog leaf792Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk78RoundedFacts chi43RoundedFacts
    innerPair26RoundedFacts leaf792RoundedFacts (by rfl)

private theorem leaf792FlatSound : Sound leaf792Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf792CertificateValid
    leaf792InnerLogValid leaf792CoversExact leaf792LowerChecked

private noncomputable def leaf793Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (65/32), chiLo := (3/16), chiHi := (13/64) }

private noncomputable def leaf793Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217883/134217728) }, vSqrt := { lower := (65531/65536), upper := (33554464/33553587) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (184513383/134217728) }, upper := { exponent := 0, mantissa := (2893/2048) } }, logOuter := sk71LogOuterCertificate, logK := sk71LogKCertificate, logChi := chi34LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (67108051/67107174) } }, logDArg := sk71LogDArgCertificate }

private noncomputable def leaf793InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf793LocalValidity :
    LeafFacts leaf793Box leaf793Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf793Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (33554464/33553587) }) = true
      norm_num [leaf793Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf793CertificateValid :
    WideCertificateValid leaf793Box leaf793Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk71ValidityFacts chi34ValidityFacts
    leaf793LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf793CoverageChecked :
    coverageCheck (innerAD leaf793Box) leaf793InnerLog = true := by
  rfl'

private theorem leaf793InnerLogValid :
    leaf793InnerLog.Valid 8 (innerAD leaf793Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf793CoverageChecked

private noncomputable def leaf793InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (2907325/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf793InputLogOnePlusV_eq :
    leaf793InputLogOnePlusV = outerEnclosure 24
      (leaf793Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf793RoundedFacts : LeafRoundedFacts 8
    leaf793Certificate.logOnePlusV leaf793InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf793InputLogOnePlusV_eq }

private noncomputable def leaf793Inputs : Inputs :=
  inputsOfCaches globalInput sk71RoundedInputs
    chi34InputQChi innerPair22Input
    leaf793InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf793LowerChecked :
    lowerCheck 24 leaf793Box leaf793Inputs = true := by
  rfl'

private theorem leaf793CoversExact : CoversExact 8
    leaf793Box leaf793Certificate leaf793InnerLog leaf793Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk71RoundedFacts chi34RoundedFacts
    innerPair22RoundedFacts leaf793RoundedFacts (by rfl)

private theorem leaf793FlatSound : Sound leaf793Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf793CertificateValid
    leaf793InnerLogValid leaf793CoversExact leaf793LowerChecked

private noncomputable def leaf794Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (65/32), kHi := (33/16), chiLo := (3/16), chiHi := (13/64) }

private noncomputable def leaf794Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217885/134217728) }, vSqrt := { lower := (65531/65536), upper := (16777232/16776787) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (185299765/134217728) }, upper := { exponent := 0, mantissa := (1453/1024) } }, logOuter := sk72LogOuterCertificate, logK := sk72LogKCertificate, logChi := chi34LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (33554019/33553574) } }, logDArg := sk72LogDArgCertificate }

private noncomputable def leaf794InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf794LocalValidity :
    LeafFacts leaf794Box leaf794Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf794Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (16777232/16776787) }) = true
      norm_num [leaf794Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf794CertificateValid :
    WideCertificateValid leaf794Box leaf794Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk72ValidityFacts chi34ValidityFacts
    leaf794LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf794CoverageChecked :
    coverageCheck (innerAD leaf794Box) leaf794InnerLog = true := by
  rfl'

private theorem leaf794InnerLogValid :
    leaf794InnerLog.Valid 8 (innerAD leaf794Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf794CoverageChecked

private noncomputable def leaf794InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629303/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf794InputLogOnePlusV_eq :
    leaf794InputLogOnePlusV = outerEnclosure 24
      (leaf794Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf794RoundedFacts : LeafRoundedFacts 8
    leaf794Certificate.logOnePlusV leaf794InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf794InputLogOnePlusV_eq }

private noncomputable def leaf794Inputs : Inputs :=
  inputsOfCaches globalInput sk72RoundedInputs
    chi34InputQChi innerPair26Input
    leaf794InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf794LowerChecked :
    lowerCheck 24 leaf794Box leaf794Inputs = true := by
  rfl'

private theorem leaf794CoversExact : CoversExact 8
    leaf794Box leaf794Certificate leaf794InnerLog leaf794Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk72RoundedFacts chi34RoundedFacts
    innerPair26RoundedFacts leaf794RoundedFacts (by rfl)

private theorem leaf794FlatSound : Sound leaf794Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf794CertificateValid
    leaf794InnerLogValid leaf794CoversExact leaf794LowerChecked

private noncomputable def leaf795Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (65/32), chiLo := (13/64), chiHi := (7/32) }

private noncomputable def leaf795Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217885/134217728) }, vSqrt := { lower := (65531/65536), upper := (16777232/16776761) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (188707429/134217728) }, upper := { exponent := 0, mantissa := (1479/1024) } }, logOuter := sk71LogOuterCertificate, logK := sk71LogKCertificate, logChi := chi35LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (33553993/33553522) } }, logDArg := sk71LogDArgCertificate }

private noncomputable def leaf795InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf795LocalValidity :
    LeafFacts leaf795Box leaf795Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf795Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (16777232/16776761) }) = true
      norm_num [leaf795Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf795CertificateValid :
    WideCertificateValid leaf795Box leaf795Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk71ValidityFacts chi35ValidityFacts
    leaf795LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf795CoverageChecked :
    coverageCheck (innerAD leaf795Box) leaf795InnerLog = true := by
  rfl'

private theorem leaf795InnerLogValid :
    leaf795InnerLog.Valid 8 (innerAD leaf795Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf795CoverageChecked

private noncomputable def leaf795InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (2907329/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf795InputLogOnePlusV_eq :
    leaf795InputLogOnePlusV = outerEnclosure 24
      (leaf795Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf795RoundedFacts : LeafRoundedFacts 8
    leaf795Certificate.logOnePlusV leaf795InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf795InputLogOnePlusV_eq }

private noncomputable def leaf795Inputs : Inputs :=
  inputsOfCaches globalInput sk71RoundedInputs
    chi35InputQChi innerPair27Input
    leaf795InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf795LowerChecked :
    lowerCheck 24 leaf795Box leaf795Inputs = true := by
  rfl'

private theorem leaf795CoversExact : CoversExact 8
    leaf795Box leaf795Certificate leaf795InnerLog leaf795Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk71RoundedFacts chi35RoundedFacts
    innerPair27RoundedFacts leaf795RoundedFacts (by rfl)

private theorem leaf795FlatSound : Sound leaf795Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf795CertificateValid
    leaf795InnerLogValid leaf795CoversExact leaf795LowerChecked

private noncomputable def leaf796Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (65/32), kHi := (33/16), chiLo := (13/64), chiHi := (7/32) }

private noncomputable def leaf796Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217887/134217728) }, vSqrt := { lower := (65531/65536), upper := (8388616/8388377) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (189559343/134217728) }, upper := { exponent := 0, mantissa := (743/512) } }, logOuter := sk72LogOuterCertificate, logK := sk72LogKCertificate, logChi := chi35LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (16776993/16776754) } }, logDArg := sk72LogDArgCertificate }

private noncomputable def leaf796InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf796LocalValidity :
    LeafFacts leaf796Box leaf796Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf796Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (8388616/8388377) }) = true
      norm_num [leaf796Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf796CertificateValid :
    WideCertificateValid leaf796Box leaf796Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk72ValidityFacts chi35ValidityFacts
    leaf796LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf796CoverageChecked :
    coverageCheck (innerAD leaf796Box) leaf796InnerLog = true := by
  rfl'

private theorem leaf796InnerLogValid :
    leaf796InnerLog.Valid 8 (innerAD leaf796Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf796CoverageChecked

private noncomputable def leaf796InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (1453665/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf796InputLogOnePlusV_eq :
    leaf796InputLogOnePlusV = outerEnclosure 24
      (leaf796Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf796RoundedFacts : LeafRoundedFacts 8
    leaf796Certificate.logOnePlusV leaf796InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf796InputLogOnePlusV_eq }

private noncomputable def leaf796Inputs : Inputs :=
  inputsOfCaches globalInput sk72RoundedInputs
    chi35InputQChi innerPair27Input
    leaf796InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf796LowerChecked :
    lowerCheck 24 leaf796Box leaf796Inputs = true := by
  rfl'

private theorem leaf796CoversExact : CoversExact 8
    leaf796Box leaf796Certificate leaf796InnerLog leaf796Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk72RoundedFacts chi35RoundedFacts
    innerPair27RoundedFacts leaf796RoundedFacts (by rfl)

private theorem leaf796FlatSound : Sound leaf796Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf796CertificateValid
    leaf796InnerLogValid leaf796CoversExact leaf796LowerChecked

private noncomputable def leaf797Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (67/32), chiLo := (3/16), chiHi := (13/64) }

private noncomputable def leaf797Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217887/134217728) }, vSqrt := { lower := (65531/65536), upper := (33554464/33553561) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (186086147/134217728) }, upper := { exponent := 0, mantissa := (2919/2048) } }, logOuter := sk73LogOuterCertificate, logK := sk73LogKCertificate, logChi := chi34LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (67108025/67107122) } }, logDArg := sk73LogDArgCertificate }

private noncomputable def leaf797InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf797LocalValidity :
    LeafFacts leaf797Box leaf797Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf797Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (33554464/33553561) }) = true
      norm_num [leaf797Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf797CertificateValid :
    WideCertificateValid leaf797Box leaf797Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk73ValidityFacts chi34ValidityFacts
    leaf797LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf797CoverageChecked :
    coverageCheck (innerAD leaf797Box) leaf797InnerLog = true := by
  rfl'

private theorem leaf797InnerLogValid :
    leaf797InnerLog.Valid 8 (innerAD leaf797Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf797CoverageChecked

private noncomputable def leaf797InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814653/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf797InputLogOnePlusV_eq :
    leaf797InputLogOnePlusV = outerEnclosure 24
      (leaf797Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf797RoundedFacts : LeafRoundedFacts 8
    leaf797Certificate.logOnePlusV leaf797InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf797InputLogOnePlusV_eq }

private noncomputable def leaf797Inputs : Inputs :=
  inputsOfCaches globalInput sk73RoundedInputs
    chi34InputQChi innerPair26Input
    leaf797InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf797LowerChecked :
    lowerCheck 24 leaf797Box leaf797Inputs = true := by
  rfl'

private theorem leaf797CoversExact : CoversExact 8
    leaf797Box leaf797Certificate leaf797InnerLog leaf797Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk73RoundedFacts chi34RoundedFacts
    innerPair26RoundedFacts leaf797RoundedFacts (by rfl)

private theorem leaf797FlatSound : Sound leaf797Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf797CertificateValid
    leaf797InnerLogValid leaf797CoversExact leaf797LowerChecked

private noncomputable def leaf798Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (67/32), kHi := (17/8), chiLo := (3/16), chiHi := (13/64) }

private noncomputable def leaf798Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217889/134217728) }, vSqrt := { lower := (65531/65536), upper := (8388616/8388387) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (186872529/134217728) }, upper := { exponent := 0, mantissa := (733/512) } }, logOuter := sk74LogOuterCertificate, logK := sk74LogKCertificate, logChi := chi34LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (16777003/16776774) } }, logDArg := sk74LogDArgCertificate }

private noncomputable def leaf798InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf798LocalValidity :
    LeafFacts leaf798Box leaf798Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf798Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (8388616/8388387) }) = true
      norm_num [leaf798Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf798CertificateValid :
    WideCertificateValid leaf798Box leaf798Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk74ValidityFacts chi34ValidityFacts
    leaf798LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf798CoverageChecked :
    coverageCheck (innerAD leaf798Box) leaf798InnerLog = true := by
  rfl'

private theorem leaf798InnerLogValid :
    leaf798InnerLog.Valid 8 (innerAD leaf798Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf798CoverageChecked

private noncomputable def leaf798InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814655/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf798InputLogOnePlusV_eq :
    leaf798InputLogOnePlusV = outerEnclosure 24
      (leaf798Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf798RoundedFacts : LeafRoundedFacts 8
    leaf798Certificate.logOnePlusV leaf798InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf798InputLogOnePlusV_eq }

private noncomputable def leaf798Inputs : Inputs :=
  inputsOfCaches globalInput sk74RoundedInputs
    chi34InputQChi innerPair26Input
    leaf798InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf798LowerChecked :
    lowerCheck 24 leaf798Box leaf798Inputs = true := by
  rfl'

private theorem leaf798CoversExact : CoversExact 8
    leaf798Box leaf798Certificate leaf798InnerLog leaf798Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk74RoundedFacts chi34RoundedFacts
    innerPair26RoundedFacts leaf798RoundedFacts (by rfl)

private theorem leaf798FlatSound : Sound leaf798Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf798CertificateValid
    leaf798InnerLogValid leaf798CoversExact leaf798LowerChecked

private noncomputable def leaf799Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (67/32), chiLo := (13/64), chiHi := (7/32) }

private noncomputable def leaf799Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217889/134217728) }, vSqrt := { lower := (65531/65536), upper := (16777232/16776747) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (190411257/134217728) }, upper := { exponent := 0, mantissa := (1493/1024) } }, logOuter := sk73LogOuterCertificate, logK := sk73LogKCertificate, logChi := chi35LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (33553979/33553494) } }, logDArg := sk73LogDArgCertificate }

private noncomputable def leaf799InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf799LocalValidity :
    LeafFacts leaf799Box leaf799Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf799Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (16777232/16776747) }) = true
      norm_num [leaf799Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf799CertificateValid :
    WideCertificateValid leaf799Box leaf799Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk73ValidityFacts chi35ValidityFacts
    leaf799LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf799CoverageChecked :
    coverageCheck (innerAD leaf799Box) leaf799InnerLog = true := by
  rfl'

private theorem leaf799InnerLogValid :
    leaf799InnerLog.Valid 8 (innerAD leaf799Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf799CoverageChecked

private noncomputable def leaf799InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629323/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf799InputLogOnePlusV_eq :
    leaf799InputLogOnePlusV = outerEnclosure 24
      (leaf799Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf799RoundedFacts : LeafRoundedFacts 8
    leaf799Certificate.logOnePlusV leaf799InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf799InputLogOnePlusV_eq }

private noncomputable def leaf799Inputs : Inputs :=
  inputsOfCaches globalInput sk73RoundedInputs
    chi35InputQChi innerPair27Input
    leaf799InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf799LowerChecked :
    lowerCheck 24 leaf799Box leaf799Inputs = true := by
  rfl'

private theorem leaf799CoversExact : CoversExact 8
    leaf799Box leaf799Certificate leaf799InnerLog leaf799Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk73RoundedFacts chi35RoundedFacts
    innerPair27RoundedFacts leaf799RoundedFacts (by rfl)

private theorem leaf799FlatSound : Sound leaf799Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf799CertificateValid
    leaf799InnerLogValid leaf799CoversExact leaf799LowerChecked

private noncomputable def leaf800Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (67/32), kHi := (17/8), chiLo := (13/64), chiHi := (7/32) }

private noncomputable def leaf800Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217891/134217728) }, vSqrt := { lower := (65531/65536), upper := (4194308/4194185) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (191263171/134217728) }, upper := { exponent := 0, mantissa := (375/256) } }, logOuter := sk74LogOuterCertificate, logK := sk74LogKCertificate, logChi := chi35LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (8388493/8388370) } }, logDArg := sk74LogDArgCertificate }

private noncomputable def leaf800InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf800LocalValidity :
    LeafFacts leaf800Box leaf800Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf800Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (4194308/4194185) }) = true
      norm_num [leaf800Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf800CertificateValid :
    WideCertificateValid leaf800Box leaf800Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk74ValidityFacts chi35ValidityFacts
    leaf800LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf800CoverageChecked :
    coverageCheck (innerAD leaf800Box) leaf800InnerLog = true := by
  rfl'

private theorem leaf800InnerLogValid :
    leaf800InnerLog.Valid 8 (innerAD leaf800Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf800CoverageChecked

private noncomputable def leaf800InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629327/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf800InputLogOnePlusV_eq :
    leaf800InputLogOnePlusV = outerEnclosure 24
      (leaf800Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf800RoundedFacts : LeafRoundedFacts 8
    leaf800Certificate.logOnePlusV leaf800InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf800InputLogOnePlusV_eq }

private noncomputable def leaf800Inputs : Inputs :=
  inputsOfCaches globalInput sk74RoundedInputs
    chi35InputQChi innerPair27Input
    leaf800InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf800LowerChecked :
    lowerCheck 24 leaf800Box leaf800Inputs = true := by
  rfl'

private theorem leaf800CoversExact : CoversExact 8
    leaf800Box leaf800Certificate leaf800InnerLog leaf800Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk74RoundedFacts chi35RoundedFacts
    innerPair27RoundedFacts leaf800RoundedFacts (by rfl)

private theorem leaf800FlatSound : Sound leaf800Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf800CertificateValid
    leaf800InnerLogValid leaf800CoversExact leaf800LowerChecked

private noncomputable def leaf801Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (65/32), chiLo := (7/32), chiHi := (15/64) }

private noncomputable def leaf801Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217887/134217728) }, vSqrt := { lower := (65531/65536), upper := (33554464/33553457) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (192901475/134217728) }, upper := { exponent := 0, mantissa := (3023/2048) } }, logOuter := sk71LogOuterCertificate, logK := sk71LogKCertificate, logChi := chi44LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (67107921/67106914) } }, logDArg := sk71LogDArgCertificate }

private noncomputable def leaf801InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf801LocalValidity :
    LeafFacts leaf801Box leaf801Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf801Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (33554464/33553457) }) = true
      norm_num [leaf801Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf801CertificateValid :
    WideCertificateValid leaf801Box leaf801Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk71ValidityFacts chi44ValidityFacts
    leaf801LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf801CoverageChecked :
    coverageCheck (innerAD leaf801Box) leaf801InnerLog = true := by
  rfl'

private theorem leaf801InnerLogValid :
    leaf801InnerLog.Valid 8 (innerAD leaf801Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf801CoverageChecked

private noncomputable def leaf801InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (2907333/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf801InputLogOnePlusV_eq :
    leaf801InputLogOnePlusV = outerEnclosure 24
      (leaf801Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf801RoundedFacts : LeafRoundedFacts 8
    leaf801Certificate.logOnePlusV leaf801InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf801InputLogOnePlusV_eq }

private noncomputable def leaf801Inputs : Inputs :=
  inputsOfCaches globalInput sk71RoundedInputs
    chi44InputQChi innerPair27Input
    leaf801InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf801LowerChecked :
    lowerCheck 24 leaf801Box leaf801Inputs = true := by
  rfl'

private theorem leaf801CoversExact : CoversExact 8
    leaf801Box leaf801Certificate leaf801InnerLog leaf801Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk71RoundedFacts chi44RoundedFacts
    innerPair27RoundedFacts leaf801RoundedFacts (by rfl)

private theorem leaf801FlatSound : Sound leaf801Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf801CertificateValid
    leaf801InnerLogValid leaf801CoversExact leaf801LowerChecked

private noncomputable def leaf802Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (65/32), kHi := (33/16), chiLo := (7/32), chiHi := (15/64) }

private noncomputable def leaf802Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217889/134217728) }, vSqrt := { lower := (65531/65536), upper := (16777232/16776721) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (193818921/134217728) }, upper := { exponent := 0, mantissa := (1519/1024) } }, logOuter := sk72LogOuterCertificate, logK := sk72LogKCertificate, logChi := chi44LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (33553953/33553442) } }, logDArg := sk72LogDArgCertificate }

private noncomputable def leaf802InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf802LocalValidity :
    LeafFacts leaf802Box leaf802Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf802Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (16777232/16776721) }) = true
      norm_num [leaf802Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf802CertificateValid :
    WideCertificateValid leaf802Box leaf802Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk72ValidityFacts chi44ValidityFacts
    leaf802LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf802CoverageChecked :
    coverageCheck (innerAD leaf802Box) leaf802InnerLog = true := by
  rfl'

private theorem leaf802InnerLogValid :
    leaf802InnerLog.Valid 8 (innerAD leaf802Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf802CoverageChecked

private noncomputable def leaf802InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (1453667/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf802InputLogOnePlusV_eq :
    leaf802InputLogOnePlusV = outerEnclosure 24
      (leaf802Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf802RoundedFacts : LeafRoundedFacts 8
    leaf802Certificate.logOnePlusV leaf802InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf802InputLogOnePlusV_eq }

private noncomputable def leaf802Inputs : Inputs :=
  inputsOfCaches globalInput sk72RoundedInputs
    chi44InputQChi innerPair34Input
    leaf802InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf802LowerChecked :
    lowerCheck 24 leaf802Box leaf802Inputs = true := by
  rfl'

private theorem leaf802CoversExact : CoversExact 8
    leaf802Box leaf802Certificate leaf802InnerLog leaf802Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk72RoundedFacts chi44RoundedFacts
    innerPair34RoundedFacts leaf802RoundedFacts (by rfl)

private theorem leaf802FlatSound : Sound leaf802Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf802CertificateValid
    leaf802InnerLogValid leaf802CoversExact leaf802LowerChecked

private noncomputable def leaf803Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (65/32), chiLo := (15/64), chiHi := (1/4) }

private noncomputable def leaf803Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217889/134217728) }, vSqrt := { lower := (65531/65536), upper := (22906164565/22905782272) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (197095521/134217728) }, upper := { exponent := 0, mantissa := (193/128) } }, logOuter := sk71LogOuterCertificate, logK := sk71LogKCertificate, logChi := chi45LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (45811946837/45811564544) } }, logDArg := sk71LogDArgCertificate }

private noncomputable def leaf803InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf803LocalValidity :
    LeafFacts leaf803Box leaf803Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf803Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (22906164565/22905782272) }) = true
      norm_num [leaf803Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf803CertificateValid :
    WideCertificateValid leaf803Box leaf803Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk71ValidityFacts chi45ValidityFacts
    leaf803LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf803CoverageChecked :
    coverageCheck (innerAD leaf803Box) leaf803InnerLog = true := by
  rfl'

private theorem leaf803InnerLogValid :
    leaf803InnerLog.Valid 8 (innerAD leaf803Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf803CoverageChecked

private noncomputable def leaf803InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629221/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf803InputLogOnePlusV_eq :
    leaf803InputLogOnePlusV = outerEnclosure 24
      (leaf803Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf803RoundedFacts : LeafRoundedFacts 8
    leaf803Certificate.logOnePlusV leaf803InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf803InputLogOnePlusV_eq }

private noncomputable def leaf803Inputs : Inputs :=
  inputsOfCaches globalInput sk71RoundedInputs
    chi45InputQChi innerPair35Input
    leaf803InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf803LowerChecked :
    lowerCheck 24 leaf803Box leaf803Inputs = true := by
  rfl'

private theorem leaf803CoversExact : CoversExact 8
    leaf803Box leaf803Certificate leaf803InnerLog leaf803Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk71RoundedFacts chi45RoundedFacts
    innerPair35RoundedFacts leaf803RoundedFacts (by rfl)

private theorem leaf803FlatSound : Sound leaf803Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf803CertificateValid
    leaf803InnerLogValid leaf803CoversExact leaf803LowerChecked

private noncomputable def leaf804Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (65/32), kHi := (33/16), chiLo := (15/64), chiHi := (1/4) }

private noncomputable def leaf804Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217891/134217728) }, vSqrt := { lower := (65531/65536), upper := (4042264335/4042194944) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (198078499/134217728) }, upper := { exponent := 0, mantissa := (97/64) } }, logOuter := sk72LogOuterCertificate, logK := sk72LogKCertificate, logChi := chi45LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (8084459279/8084389888) } }, logDArg := sk72LogDArgCertificate }

private noncomputable def leaf804InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf804LocalValidity :
    LeafFacts leaf804Box leaf804Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf804Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (4042264335/4042194944) }) = true
      norm_num [leaf804Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf804CertificateValid :
    WideCertificateValid leaf804Box leaf804Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk72ValidityFacts chi45ValidityFacts
    leaf804LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf804CoverageChecked :
    coverageCheck (innerAD leaf804Box) leaf804InnerLog = true := by
  rfl'

private theorem leaf804InnerLogValid :
    leaf804InnerLog.Valid 8 (innerAD leaf804Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf804CoverageChecked

private noncomputable def leaf804InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629225/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf804InputLogOnePlusV_eq :
    leaf804InputLogOnePlusV = outerEnclosure 24
      (leaf804Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf804RoundedFacts : LeafRoundedFacts 8
    leaf804Certificate.logOnePlusV leaf804InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf804InputLogOnePlusV_eq }

private noncomputable def leaf804Inputs : Inputs :=
  inputsOfCaches globalInput sk72RoundedInputs
    chi45InputQChi innerPair35Input
    leaf804InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf804LowerChecked :
    lowerCheck 24 leaf804Box leaf804Inputs = true := by
  rfl'

private theorem leaf804CoversExact : CoversExact 8
    leaf804Box leaf804Certificate leaf804InnerLog leaf804Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk72RoundedFacts chi45RoundedFacts
    innerPair35RoundedFacts leaf804RoundedFacts (by rfl)

private theorem leaf804FlatSound : Sound leaf804Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf804CertificateValid
    leaf804InnerLogValid leaf804CoversExact leaf804LowerChecked

private noncomputable def leaf805Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (67/32), chiLo := (7/32), chiHi := (15/64) }

private noncomputable def leaf805Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217891/134217728) }, vSqrt := { lower := (65531/65536), upper := (4042264335/4042201088) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (194736367/134217728) }, upper := { exponent := 0, mantissa := (3053/2048) } }, logOuter := sk73LogOuterCertificate, logK := sk73LogKCertificate, logChi := chi44LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (8084465423/8084402176) } }, logDArg := sk73LogDArgCertificate }

private noncomputable def leaf805InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf805LocalValidity :
    LeafFacts leaf805Box leaf805Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf805Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (4042264335/4042201088) }) = true
      norm_num [leaf805Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf805CertificateValid :
    WideCertificateValid leaf805Box leaf805Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk73ValidityFacts chi44ValidityFacts
    leaf805LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf805CoverageChecked :
    coverageCheck (innerAD leaf805Box) leaf805InnerLog = true := by
  rfl'

private theorem leaf805InnerLogValid :
    leaf805InnerLog.Valid 8 (innerAD leaf805Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf805CoverageChecked

private noncomputable def leaf805InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (2907303/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf805InputLogOnePlusV_eq :
    leaf805InputLogOnePlusV = outerEnclosure 24
      (leaf805Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf805RoundedFacts : LeafRoundedFacts 8
    leaf805Certificate.logOnePlusV leaf805InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf805InputLogOnePlusV_eq }

private noncomputable def leaf805Inputs : Inputs :=
  inputsOfCaches globalInput sk73RoundedInputs
    chi44InputQChi innerPair34Input
    leaf805InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf805LowerChecked :
    lowerCheck 24 leaf805Box leaf805Inputs = true := by
  rfl'

private theorem leaf805CoversExact : CoversExact 8
    leaf805Box leaf805Certificate leaf805InnerLog leaf805Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk73RoundedFacts chi44RoundedFacts
    innerPair34RoundedFacts leaf805RoundedFacts (by rfl)

private theorem leaf805FlatSound : Sound leaf805Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf805CertificateValid
    leaf805InnerLogValid leaf805CoversExact leaf805LowerChecked

private noncomputable def leaf806Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (67/32), kHi := (17/8), chiLo := (7/32), chiHi := (15/64) }

private noncomputable def leaf806Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217893/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68717387776) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (195653813/134217728) }, upper := { exponent := 0, mantissa := (767/512) } }, logOuter := sk74LogOuterCertificate, logK := sk74LogKCertificate, logChi := chi44LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435881471/137434775552) } }, logDArg := sk74LogDArgCertificate }

private noncomputable def leaf806InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf806LocalValidity :
    LeafFacts leaf806Box leaf806Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf806Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68717387776) }) = true
      norm_num [leaf806Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf806CertificateValid :
    WideCertificateValid leaf806Box leaf806Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk74ValidityFacts chi44ValidityFacts
    leaf806LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf806CoverageChecked :
    coverageCheck (innerAD leaf806Box) leaf806InnerLog = true := by
  rfl'

private theorem leaf806InnerLogValid :
    leaf806InnerLog.Valid 8 (innerAD leaf806Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf806CoverageChecked

private noncomputable def leaf806InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (363413/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf806InputLogOnePlusV_eq :
    leaf806InputLogOnePlusV = outerEnclosure 24
      (leaf806Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf806RoundedFacts : LeafRoundedFacts 8
    leaf806Certificate.logOnePlusV leaf806InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf806InputLogOnePlusV_eq }

private noncomputable def leaf806Inputs : Inputs :=
  inputsOfCaches globalInput sk74RoundedInputs
    chi44InputQChi innerPair34Input
    leaf806InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf806LowerChecked :
    lowerCheck 24 leaf806Box leaf806Inputs = true := by
  rfl'

private theorem leaf806CoversExact : CoversExact 8
    leaf806Box leaf806Certificate leaf806InnerLog leaf806Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk74RoundedFacts chi44RoundedFacts
    innerPair34RoundedFacts leaf806RoundedFacts (by rfl)

private theorem leaf806FlatSound : Sound leaf806Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf806CertificateValid
    leaf806InnerLogValid leaf806CoversExact leaf806LowerChecked

private noncomputable def leaf807Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (67/32), chiLo := (15/64), chiHi := (1/4) }

private noncomputable def leaf807Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217893/134217728) }, vSqrt := { lower := (65531/65536), upper := (13743698739/13743456256) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (199061477/134217728) }, upper := { exponent := 0, mantissa := (195/128) } }, logOuter := sk73LogOuterCertificate, logK := sk73LogKCertificate, logChi := chi45LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (27487154995/27486912512) } }, logDArg := sk73LogDArgCertificate }

private noncomputable def leaf807InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf807LocalValidity :
    LeafFacts leaf807Box leaf807Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf807Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (13743698739/13743456256) }) = true
      norm_num [leaf807Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf807CertificateValid :
    WideCertificateValid leaf807Box leaf807Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk73ValidityFacts chi45ValidityFacts
    leaf807LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf807CoverageChecked :
    coverageCheck (innerAD leaf807Box) leaf807InnerLog = true := by
  rfl'

private theorem leaf807InnerLogValid :
    leaf807InnerLog.Valid 8 (innerAD leaf807Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf807CoverageChecked

private noncomputable def leaf807InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629229/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf807InputLogOnePlusV_eq :
    leaf807InputLogOnePlusV = outerEnclosure 24
      (leaf807Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf807RoundedFacts : LeafRoundedFacts 8
    leaf807Certificate.logOnePlusV leaf807InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf807InputLogOnePlusV_eq }

private noncomputable def leaf807Inputs : Inputs :=
  inputsOfCaches globalInput sk73RoundedInputs
    chi45InputQChi innerPair35Input
    leaf807InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf807LowerChecked :
    lowerCheck 24 leaf807Box leaf807Inputs = true := by
  rfl'

private theorem leaf807CoversExact : CoversExact 8
    leaf807Box leaf807Certificate leaf807InnerLog leaf807Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk73RoundedFacts chi45RoundedFacts
    innerPair35RoundedFacts leaf807RoundedFacts (by rfl)

private theorem leaf807FlatSound : Sound leaf807Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf807CertificateValid
    leaf807InnerLogValid leaf807CoversExact leaf807LowerChecked

private noncomputable def leaf808Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (67/32), kHi := (17/8), chiLo := (15/64), chiHi := (1/4) }

private noncomputable def leaf808Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217895/134217728) }, vSqrt := { lower := (65531/65536), upper := (22906164565/22905749504) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (200044455/134217728) }, upper := { exponent := 0, mantissa := (49/32) } }, logOuter := sk74LogOuterCertificate, logK := sk74LogKCertificate, logChi := chi45LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (45811914069/45811499008) } }, logDArg := sk74LogDArgCertificate }

private noncomputable def leaf808InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf808LocalValidity :
    LeafFacts leaf808Box leaf808Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf808Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (22906164565/22905749504) }) = true
      norm_num [leaf808Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf808CertificateValid :
    WideCertificateValid leaf808Box leaf808Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk74ValidityFacts chi45ValidityFacts
    leaf808LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf808CoverageChecked :
    coverageCheck (innerAD leaf808Box) leaf808InnerLog = true := by
  rfl'

private theorem leaf808InnerLogValid :
    leaf808InnerLog.Valid 8 (innerAD leaf808Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf808CoverageChecked

private noncomputable def leaf808InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629233/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf808InputLogOnePlusV_eq :
    leaf808InputLogOnePlusV = outerEnclosure 24
      (leaf808Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf808RoundedFacts : LeafRoundedFacts 8
    leaf808Certificate.logOnePlusV leaf808InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf808InputLogOnePlusV_eq }

private noncomputable def leaf808Inputs : Inputs :=
  inputsOfCaches globalInput sk74RoundedInputs
    chi45InputQChi innerPair35Input
    leaf808InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf808LowerChecked :
    lowerCheck 24 leaf808Box leaf808Inputs = true := by
  rfl'

private theorem leaf808CoversExact : CoversExact 8
    leaf808Box leaf808Certificate leaf808InnerLog leaf808Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk74RoundedFacts chi45RoundedFacts
    innerPair35RoundedFacts leaf808RoundedFacts (by rfl)

private theorem leaf808FlatSound : Sound leaf808Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf808CertificateValid
    leaf808InnerLogValid leaf808CoversExact leaf808LowerChecked

private noncomputable def leaf809Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (69/32), chiLo := (3/16), chiHi := (13/64) }

private noncomputable def leaf809Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217891/134217728) }, vSqrt := { lower := (65531/65536), upper := (33554464/33553535) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (187658911/134217728) }, upper := { exponent := 0, mantissa := (2945/2048) } }, logOuter := sk75LogOuterCertificate, logK := sk75LogKCertificate, logChi := chi34LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (67107999/67107070) } }, logDArg := sk75LogDArgCertificate }

private noncomputable def leaf809InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf809LocalValidity :
    LeafFacts leaf809Box leaf809Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf809Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (33554464/33553535) }) = true
      norm_num [leaf809Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf809CertificateValid :
    WideCertificateValid leaf809Box leaf809Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk75ValidityFacts chi34ValidityFacts
    leaf809LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf809CoverageChecked :
    coverageCheck (innerAD leaf809Box) leaf809InnerLog = true := by
  rfl'

private theorem leaf809InnerLogValid :
    leaf809InnerLog.Valid 8 (innerAD leaf809Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf809CoverageChecked

private noncomputable def leaf809InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629313/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf809InputLogOnePlusV_eq :
    leaf809InputLogOnePlusV = outerEnclosure 24
      (leaf809Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf809RoundedFacts : LeafRoundedFacts 8
    leaf809Certificate.logOnePlusV leaf809InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf809InputLogOnePlusV_eq }

private noncomputable def leaf809Inputs : Inputs :=
  inputsOfCaches globalInput sk75RoundedInputs
    chi34InputQChi innerPair27Input
    leaf809InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf809LowerChecked :
    lowerCheck 24 leaf809Box leaf809Inputs = true := by
  rfl'

private theorem leaf809CoversExact : CoversExact 8
    leaf809Box leaf809Certificate leaf809InnerLog leaf809Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk75RoundedFacts chi34RoundedFacts
    innerPair27RoundedFacts leaf809RoundedFacts (by rfl)

private theorem leaf809FlatSound : Sound leaf809Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf809CertificateValid
    leaf809InnerLogValid leaf809CoversExact leaf809LowerChecked

private noncomputable def leaf810Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (69/32), kHi := (35/16), chiLo := (3/16), chiHi := (13/64) }

private noncomputable def leaf810Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217893/134217728) }, vSqrt := { lower := (65531/65536), upper := (16777232/16776761) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (188445293/134217728) }, upper := { exponent := 0, mantissa := (1479/1024) } }, logOuter := sk76LogOuterCertificate, logK := sk76LogKCertificate, logChi := chi34LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (33553993/33553522) } }, logDArg := sk76LogDArgCertificate }

private noncomputable def leaf810InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf810LocalValidity :
    LeafFacts leaf810Box leaf810Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf810Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (16777232/16776761) }) = true
      norm_num [leaf810Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf810CertificateValid :
    WideCertificateValid leaf810Box leaf810Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk76ValidityFacts chi34ValidityFacts
    leaf810LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf810CoverageChecked :
    coverageCheck (innerAD leaf810Box) leaf810InnerLog = true := by
  rfl'

private theorem leaf810InnerLogValid :
    leaf810InnerLog.Valid 8 (innerAD leaf810Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf810CoverageChecked

private noncomputable def leaf810InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (2907329/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf810InputLogOnePlusV_eq :
    leaf810InputLogOnePlusV = outerEnclosure 24
      (leaf810Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf810RoundedFacts : LeafRoundedFacts 8
    leaf810Certificate.logOnePlusV leaf810InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf810InputLogOnePlusV_eq }

private noncomputable def leaf810Inputs : Inputs :=
  inputsOfCaches globalInput sk76RoundedInputs
    chi34InputQChi innerPair27Input
    leaf810InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf810LowerChecked :
    lowerCheck 24 leaf810Box leaf810Inputs = true := by
  rfl'

private theorem leaf810CoversExact : CoversExact 8
    leaf810Box leaf810Certificate leaf810InnerLog leaf810Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk76RoundedFacts chi34RoundedFacts
    innerPair27RoundedFacts leaf810RoundedFacts (by rfl)

private theorem leaf810FlatSound : Sound leaf810Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf810CertificateValid
    leaf810InnerLogValid leaf810CoversExact leaf810LowerChecked

private noncomputable def leaf811Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (69/32), chiLo := (13/64), chiHi := (7/32) }

private noncomputable def leaf811Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217893/134217728) }, vSqrt := { lower := (65531/65536), upper := (16777232/16776733) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (192115085/134217728) }, upper := { exponent := 0, mantissa := (1507/1024) } }, logOuter := sk75LogOuterCertificate, logK := sk75LogKCertificate, logChi := chi35LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (33553965/33553466) } }, logDArg := sk75LogDArgCertificate }

private noncomputable def leaf811InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf811LocalValidity :
    LeafFacts leaf811Box leaf811Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf811Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (16777232/16776733) }) = true
      norm_num [leaf811Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf811CertificateValid :
    WideCertificateValid leaf811Box leaf811Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk75ValidityFacts chi35ValidityFacts
    leaf811LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf811CoverageChecked :
    coverageCheck (innerAD leaf811Box) leaf811InnerLog = true := by
  rfl'

private theorem leaf811InnerLogValid :
    leaf811InnerLog.Valid 8 (innerAD leaf811Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf811CoverageChecked

private noncomputable def leaf811InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814665/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf811InputLogOnePlusV_eq :
    leaf811InputLogOnePlusV = outerEnclosure 24
      (leaf811Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf811RoundedFacts : LeafRoundedFacts 8
    leaf811Certificate.logOnePlusV leaf811InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf811InputLogOnePlusV_eq }

private noncomputable def leaf811Inputs : Inputs :=
  inputsOfCaches globalInput sk75RoundedInputs
    chi35InputQChi innerPair27Input
    leaf811InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf811LowerChecked :
    lowerCheck 24 leaf811Box leaf811Inputs = true := by
  rfl'

private theorem leaf811CoversExact : CoversExact 8
    leaf811Box leaf811Certificate leaf811InnerLog leaf811Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk75RoundedFacts chi35RoundedFacts
    innerPair27RoundedFacts leaf811RoundedFacts (by rfl)

private theorem leaf811FlatSound : Sound leaf811Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf811CertificateValid
    leaf811InnerLogValid leaf811CoversExact leaf811LowerChecked

private noncomputable def leaf812Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (69/32), kHi := (35/16), chiLo := (13/64), chiHi := (7/32) }

private noncomputable def leaf812Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217895/134217728) }, vSqrt := { lower := (65531/65536), upper := (8388616/8388363) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (192966999/134217728) }, upper := { exponent := 0, mantissa := (757/512) } }, logOuter := sk76LogOuterCertificate, logK := sk76LogKCertificate, logChi := chi35LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (16776979/16776726) } }, logDArg := sk76LogDArgCertificate }

private noncomputable def leaf812InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf812LocalValidity :
    LeafFacts leaf812Box leaf812Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf812Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (8388616/8388363) }) = true
      norm_num [leaf812Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf812CertificateValid :
    WideCertificateValid leaf812Box leaf812Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk76ValidityFacts chi35ValidityFacts
    leaf812LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf812CoverageChecked :
    coverageCheck (innerAD leaf812Box) leaf812InnerLog = true := by
  rfl'

private theorem leaf812InnerLogValid :
    leaf812InnerLog.Valid 8 (innerAD leaf812Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf812CoverageChecked

private noncomputable def leaf812InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814667/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf812InputLogOnePlusV_eq :
    leaf812InputLogOnePlusV = outerEnclosure 24
      (leaf812Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf812RoundedFacts : LeafRoundedFacts 8
    leaf812Certificate.logOnePlusV leaf812InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf812InputLogOnePlusV_eq }

private noncomputable def leaf812Inputs : Inputs :=
  inputsOfCaches globalInput sk76RoundedInputs
    chi35InputQChi innerPair34Input
    leaf812InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf812LowerChecked :
    lowerCheck 24 leaf812Box leaf812Inputs = true := by
  rfl'

private theorem leaf812CoversExact : CoversExact 8
    leaf812Box leaf812Certificate leaf812InnerLog leaf812Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk76RoundedFacts chi35RoundedFacts
    innerPair34RoundedFacts leaf812RoundedFacts (by rfl)

private theorem leaf812FlatSound : Sound leaf812Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf812CertificateValid
    leaf812InnerLogValid leaf812CoversExact leaf812LowerChecked

private noncomputable def leaf813Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (71/32), chiLo := (3/16), chiHi := (13/64) }

private noncomputable def leaf813Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217895/134217728) }, vSqrt := { lower := (65531/65536), upper := (33554464/33553509) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (189231675/134217728) }, upper := { exponent := 0, mantissa := (2971/2048) } }, logOuter := sk77LogOuterCertificate, logK := sk77LogKCertificate, logChi := chi34LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (67107973/67107018) } }, logDArg := sk77LogDArgCertificate }

private noncomputable def leaf813InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf813LocalValidity :
    LeafFacts leaf813Box leaf813Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf813Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (33554464/33553509) }) = true
      norm_num [leaf813Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf813CertificateValid :
    WideCertificateValid leaf813Box leaf813Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk77ValidityFacts chi34ValidityFacts
    leaf813LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf813CoverageChecked :
    coverageCheck (innerAD leaf813Box) leaf813InnerLog = true := by
  rfl'

private theorem leaf813InnerLogValid :
    leaf813InnerLog.Valid 8 (innerAD leaf813Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf813CoverageChecked

private noncomputable def leaf813InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629319/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf813InputLogOnePlusV_eq :
    leaf813InputLogOnePlusV = outerEnclosure 24
      (leaf813Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf813RoundedFacts : LeafRoundedFacts 8
    leaf813Certificate.logOnePlusV leaf813InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf813InputLogOnePlusV_eq }

private noncomputable def leaf813Inputs : Inputs :=
  inputsOfCaches globalInput sk77RoundedInputs
    chi34InputQChi innerPair27Input
    leaf813InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf813LowerChecked :
    lowerCheck 24 leaf813Box leaf813Inputs = true := by
  rfl'

private theorem leaf813CoversExact : CoversExact 8
    leaf813Box leaf813Certificate leaf813InnerLog leaf813Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk77RoundedFacts chi34RoundedFacts
    innerPair27RoundedFacts leaf813RoundedFacts (by rfl)

private theorem leaf813FlatSound : Sound leaf813Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf813CertificateValid
    leaf813InnerLogValid leaf813CoversExact leaf813LowerChecked

private noncomputable def leaf814Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (71/32), kHi := (9/4), chiLo := (3/16), chiHi := (13/64) }

private noncomputable def leaf814Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217897/134217728) }, vSqrt := { lower := (65531/65536), upper := (4194308/4194187) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (190018057/134217728) }, upper := { exponent := 0, mantissa := (373/256) } }, logOuter := sk78LogOuterCertificate, logK := sk78LogKCertificate, logChi := chi34LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (8388495/8388374) } }, logDArg := sk78LogDArgCertificate }

private noncomputable def leaf814InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf814LocalValidity :
    LeafFacts leaf814Box leaf814Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf814Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (4194308/4194187) }) = true
      norm_num [leaf814Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf814CertificateValid :
    WideCertificateValid leaf814Box leaf814Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk78ValidityFacts chi34ValidityFacts
    leaf814LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf814CoverageChecked :
    coverageCheck (innerAD leaf814Box) leaf814InnerLog = true := by
  rfl'

private theorem leaf814InnerLogValid :
    leaf814InnerLog.Valid 8 (innerAD leaf814Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf814CoverageChecked

private noncomputable def leaf814InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629323/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf814InputLogOnePlusV_eq :
    leaf814InputLogOnePlusV = outerEnclosure 24
      (leaf814Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf814RoundedFacts : LeafRoundedFacts 8
    leaf814Certificate.logOnePlusV leaf814InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf814InputLogOnePlusV_eq }

private noncomputable def leaf814Inputs : Inputs :=
  inputsOfCaches globalInput sk78RoundedInputs
    chi34InputQChi innerPair27Input
    leaf814InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf814LowerChecked :
    lowerCheck 24 leaf814Box leaf814Inputs = true := by
  rfl'

private theorem leaf814CoversExact : CoversExact 8
    leaf814Box leaf814Certificate leaf814InnerLog leaf814Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk78RoundedFacts chi34RoundedFacts
    innerPair27RoundedFacts leaf814RoundedFacts (by rfl)

private theorem leaf814FlatSound : Sound leaf814Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf814CertificateValid
    leaf814InnerLogValid leaf814CoversExact leaf814LowerChecked

private noncomputable def leaf815Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (71/32), chiLo := (13/64), chiHi := (7/32) }

private noncomputable def leaf815Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217897/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68717441024) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (193818913/134217728) }, upper := { exponent := 0, mantissa := (1521/1024) } }, logOuter := sk77LogOuterCertificate, logK := sk77LogKCertificate, logChi := chi35LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435934719/137434882048) } }, logDArg := sk77LogDArgCertificate }

private noncomputable def leaf815InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf815LocalValidity :
    LeafFacts leaf815Box leaf815Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf815Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68717441024) }) = true
      norm_num [leaf815Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf815CertificateValid :
    WideCertificateValid leaf815Box leaf815Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk77ValidityFacts chi35ValidityFacts
    leaf815LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf815CoverageChecked :
    coverageCheck (innerAD leaf815Box) leaf815InnerLog = true := by
  rfl'

private theorem leaf815InnerLogValid :
    leaf815InnerLog.Valid 8 (innerAD leaf815Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf815CoverageChecked

private noncomputable def leaf815InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629209/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf815InputLogOnePlusV_eq :
    leaf815InputLogOnePlusV = outerEnclosure 24
      (leaf815Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf815RoundedFacts : LeafRoundedFacts 8
    leaf815Certificate.logOnePlusV leaf815InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf815InputLogOnePlusV_eq }

private noncomputable def leaf815Inputs : Inputs :=
  inputsOfCaches globalInput sk77RoundedInputs
    chi35InputQChi innerPair34Input
    leaf815InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf815LowerChecked :
    lowerCheck 24 leaf815Box leaf815Inputs = true := by
  rfl'

private theorem leaf815CoversExact : CoversExact 8
    leaf815Box leaf815Certificate leaf815InnerLog leaf815Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk77RoundedFacts chi35RoundedFacts
    innerPair34RoundedFacts leaf815RoundedFacts (by rfl)

private theorem leaf815FlatSound : Sound leaf815Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf815CertificateValid
    leaf815InnerLogValid leaf815CoversExact leaf815LowerChecked

private noncomputable def leaf816Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (71/32), kHi := (9/4), chiLo := (13/64), chiHi := (7/32) }

private noncomputable def leaf816Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217899/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68717412352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (194670827/134217728) }, upper := { exponent := 0, mantissa := (191/128) } }, logOuter := sk78LogOuterCertificate, logK := sk78LogKCertificate, logChi := chi35LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435906047/137434824704) } }, logDArg := sk78LogDArgCertificate }

private noncomputable def leaf816InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf816LocalValidity :
    LeafFacts leaf816Box leaf816Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf816Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68717412352) }) = true
      norm_num [leaf816Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf816CertificateValid :
    WideCertificateValid leaf816Box leaf816Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk78ValidityFacts chi35ValidityFacts
    leaf816LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf816CoverageChecked :
    coverageCheck (innerAD leaf816Box) leaf816InnerLog = true := by
  rfl'

private theorem leaf816InnerLogValid :
    leaf816InnerLog.Valid 8 (innerAD leaf816Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf816CoverageChecked

private noncomputable def leaf816InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629213/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf816InputLogOnePlusV_eq :
    leaf816InputLogOnePlusV = outerEnclosure 24
      (leaf816Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf816RoundedFacts : LeafRoundedFacts 8
    leaf816Certificate.logOnePlusV leaf816InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf816InputLogOnePlusV_eq }

private noncomputable def leaf816Inputs : Inputs :=
  inputsOfCaches globalInput sk78RoundedInputs
    chi35InputQChi innerPair34Input
    leaf816InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf816LowerChecked :
    lowerCheck 24 leaf816Box leaf816Inputs = true := by
  rfl'

private theorem leaf816CoversExact : CoversExact 8
    leaf816Box leaf816Certificate leaf816InnerLog leaf816Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk78RoundedFacts chi35RoundedFacts
    innerPair34RoundedFacts leaf816RoundedFacts (by rfl)

private theorem leaf816FlatSound : Sound leaf816Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf816CertificateValid
    leaf816InnerLogValid leaf816CoversExact leaf816LowerChecked

private noncomputable def leaf817Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (69/32), chiLo := (7/32), chiHi := (15/64) }

private noncomputable def leaf817Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217895/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68717357056) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (196571259/134217728) }, upper := { exponent := 0, mantissa := (3083/2048) } }, logOuter := sk75LogOuterCertificate, logK := sk75LogKCertificate, logChi := chi44LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435850751/137434714112) } }, logDArg := sk75LogDArgCertificate }

private noncomputable def leaf817InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf817LocalValidity :
    LeafFacts leaf817Box leaf817Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf817Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68717357056) }) = true
      norm_num [leaf817Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf817CertificateValid :
    WideCertificateValid leaf817Box leaf817Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk75ValidityFacts chi44ValidityFacts
    leaf817LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf817CoverageChecked :
    coverageCheck (innerAD leaf817Box) leaf817InnerLog = true := by
  rfl'

private theorem leaf817InnerLogValid :
    leaf817InnerLog.Valid 8 (innerAD leaf817Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf817CoverageChecked

private noncomputable def leaf817InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629219/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf817InputLogOnePlusV_eq :
    leaf817InputLogOnePlusV = outerEnclosure 24
      (leaf817Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf817RoundedFacts : LeafRoundedFacts 8
    leaf817Certificate.logOnePlusV leaf817InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf817InputLogOnePlusV_eq }

private noncomputable def leaf817Inputs : Inputs :=
  inputsOfCaches globalInput sk75RoundedInputs
    chi44InputQChi innerPair35Input
    leaf817InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf817LowerChecked :
    lowerCheck 24 leaf817Box leaf817Inputs = true := by
  rfl'

private theorem leaf817CoversExact : CoversExact 8
    leaf817Box leaf817Certificate leaf817InnerLog leaf817Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk75RoundedFacts chi44RoundedFacts
    innerPair35RoundedFacts leaf817RoundedFacts (by rfl)

private theorem leaf817FlatSound : Sound leaf817Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf817CertificateValid
    leaf817InnerLogValid leaf817CoversExact leaf817LowerChecked

private noncomputable def leaf818Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (69/32), kHi := (35/16), chiLo := (7/32), chiHi := (15/64) }

private noncomputable def leaf818Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217897/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68717326336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (197488705/134217728) }, upper := { exponent := 0, mantissa := (1549/1024) } }, logOuter := sk76LogOuterCertificate, logK := sk76LogKCertificate, logChi := chi44LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435820031/137434652672) } }, logDArg := sk76LogDArgCertificate }

private noncomputable def leaf818InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf818LocalValidity :
    LeafFacts leaf818Box leaf818Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf818Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68717326336) }) = true
      norm_num [leaf818Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf818CertificateValid :
    WideCertificateValid leaf818Box leaf818Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk76ValidityFacts chi44ValidityFacts
    leaf818LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf818CoverageChecked :
    coverageCheck (innerAD leaf818Box) leaf818InnerLog = true := by
  rfl'

private theorem leaf818InnerLogValid :
    leaf818InnerLog.Valid 8 (innerAD leaf818Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf818CoverageChecked

private noncomputable def leaf818InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629223/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf818InputLogOnePlusV_eq :
    leaf818InputLogOnePlusV = outerEnclosure 24
      (leaf818Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf818RoundedFacts : LeafRoundedFacts 8
    leaf818Certificate.logOnePlusV leaf818InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf818InputLogOnePlusV_eq }

private noncomputable def leaf818Inputs : Inputs :=
  inputsOfCaches globalInput sk76RoundedInputs
    chi44InputQChi innerPair35Input
    leaf818InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf818LowerChecked :
    lowerCheck 24 leaf818Box leaf818Inputs = true := by
  rfl'

private theorem leaf818CoversExact : CoversExact 8
    leaf818Box leaf818Certificate leaf818InnerLog leaf818Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk76RoundedFacts chi44RoundedFacts
    innerPair35RoundedFacts leaf818RoundedFacts (by rfl)

private theorem leaf818FlatSound : Sound leaf818Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf818CertificateValid
    leaf818InnerLogValid leaf818CoversExact leaf818LowerChecked

private noncomputable def leaf819Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (69/32), chiLo := (15/64), chiHi := (1/4) }

private noncomputable def leaf819Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217897/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68717215744) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (201027433/134217728) }, upper := { exponent := 0, mantissa := (197/128) } }, logOuter := sk75LogOuterCertificate, logK := sk75LogKCertificate, logChi := chi45LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435709439/137434431488) } }, logDArg := sk75LogDArgCertificate }

private noncomputable def leaf819InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf819LocalValidity :
    LeafFacts leaf819Box leaf819Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf819Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68717215744) }) = true
      norm_num [leaf819Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf819CertificateValid :
    WideCertificateValid leaf819Box leaf819Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk75ValidityFacts chi45ValidityFacts
    leaf819LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf819CoverageChecked :
    coverageCheck (innerAD leaf819Box) leaf819InnerLog = true := by
  rfl'

private theorem leaf819InnerLogValid :
    leaf819InnerLog.Valid 8 (innerAD leaf819Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf819CoverageChecked

private noncomputable def leaf819InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629237/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf819InputLogOnePlusV_eq :
    leaf819InputLogOnePlusV = outerEnclosure 24
      (leaf819Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf819RoundedFacts : LeafRoundedFacts 8
    leaf819Certificate.logOnePlusV leaf819InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf819InputLogOnePlusV_eq }

private noncomputable def leaf819Inputs : Inputs :=
  inputsOfCaches globalInput sk75RoundedInputs
    chi45InputQChi innerPair35Input
    leaf819InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf819LowerChecked :
    lowerCheck 24 leaf819Box leaf819Inputs = true := by
  rfl'

private theorem leaf819CoversExact : CoversExact 8
    leaf819Box leaf819Certificate leaf819InnerLog leaf819Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk75RoundedFacts chi45RoundedFacts
    innerPair35RoundedFacts leaf819RoundedFacts (by rfl)

private theorem leaf819FlatSound : Sound leaf819Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf819CertificateValid
    leaf819InnerLogValid leaf819CoversExact leaf819LowerChecked

private noncomputable def leaf820Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (69/32), kHi := (35/16), chiLo := (15/64), chiHi := (1/4) }

private noncomputable def leaf820Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217899/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68717182976) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (202010411/134217728) }, upper := { exponent := 0, mantissa := (99/64) } }, logOuter := sk76LogOuterCertificate, logK := sk76LogKCertificate, logChi := chi45LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435676671/137434365952) } }, logDArg := sk76LogDArgCertificate }

private noncomputable def leaf820InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf820LocalValidity :
    LeafFacts leaf820Box leaf820Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf820Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68717182976) }) = true
      norm_num [leaf820Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf820CertificateValid :
    WideCertificateValid leaf820Box leaf820Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk76ValidityFacts chi45ValidityFacts
    leaf820LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf820CoverageChecked :
    coverageCheck (innerAD leaf820Box) leaf820InnerLog = true := by
  rfl'

private theorem leaf820InnerLogValid :
    leaf820InnerLog.Valid 8 (innerAD leaf820Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf820CoverageChecked

private noncomputable def leaf820InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629241/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf820InputLogOnePlusV_eq :
    leaf820InputLogOnePlusV = outerEnclosure 24
      (leaf820Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf820RoundedFacts : LeafRoundedFacts 8
    leaf820Certificate.logOnePlusV leaf820InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf820InputLogOnePlusV_eq }

private noncomputable def leaf820Inputs : Inputs :=
  inputsOfCaches globalInput sk76RoundedInputs
    chi45InputQChi innerPair40Input
    leaf820InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf820LowerChecked :
    lowerCheck 24 leaf820Box leaf820Inputs = true := by
  rfl'

private theorem leaf820CoversExact : CoversExact 8
    leaf820Box leaf820Certificate leaf820InnerLog leaf820Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk76RoundedFacts chi45RoundedFacts
    innerPair40RoundedFacts leaf820RoundedFacts (by rfl)

private theorem leaf820FlatSound : Sound leaf820Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf820CertificateValid
    leaf820InnerLogValid leaf820CoversExact leaf820LowerChecked

private noncomputable def leaf821Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (71/32), chiLo := (7/32), chiHi := (15/64) }

private noncomputable def leaf821Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217899/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68717295616) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (198406151/134217728) }, upper := { exponent := 0, mantissa := (3113/2048) } }, logOuter := sk77LogOuterCertificate, logK := sk77LogKCertificate, logChi := chi44LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435789311/137434591232) } }, logDArg := sk77LogDArgCertificate }

private noncomputable def leaf821InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf821LocalValidity :
    LeafFacts leaf821Box leaf821Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf821Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68717295616) }) = true
      norm_num [leaf821Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf821CertificateValid :
    WideCertificateValid leaf821Box leaf821Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk77ValidityFacts chi44ValidityFacts
    leaf821LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf821CoverageChecked :
    coverageCheck (innerAD leaf821Box) leaf821InnerLog = true := by
  rfl'

private theorem leaf821InnerLogValid :
    leaf821InnerLog.Valid 8 (innerAD leaf821Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf821CoverageChecked

private noncomputable def leaf821InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629227/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf821InputLogOnePlusV_eq :
    leaf821InputLogOnePlusV = outerEnclosure 24
      (leaf821Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf821RoundedFacts : LeafRoundedFacts 8
    leaf821Certificate.logOnePlusV leaf821InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf821InputLogOnePlusV_eq }

private noncomputable def leaf821Inputs : Inputs :=
  inputsOfCaches globalInput sk77RoundedInputs
    chi44InputQChi innerPair35Input
    leaf821InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf821LowerChecked :
    lowerCheck 24 leaf821Box leaf821Inputs = true := by
  rfl'

private theorem leaf821CoversExact : CoversExact 8
    leaf821Box leaf821Certificate leaf821InnerLog leaf821Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk77RoundedFacts chi44RoundedFacts
    innerPair35RoundedFacts leaf821RoundedFacts (by rfl)

private theorem leaf821FlatSound : Sound leaf821Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf821CertificateValid
    leaf821InnerLogValid leaf821CoversExact leaf821LowerChecked

private noncomputable def leaf822Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (71/32), kHi := (9/4), chiLo := (7/32), chiHi := (15/64) }

private noncomputable def leaf822Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217901/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68717264896) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (199323597/134217728) }, upper := { exponent := 0, mantissa := (391/256) } }, logOuter := sk78LogOuterCertificate, logK := sk78LogKCertificate, logChi := chi44LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435758591/137434529792) } }, logDArg := sk78LogDArgCertificate }

private noncomputable def leaf822InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf822LocalValidity :
    LeafFacts leaf822Box leaf822Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf822Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68717264896) }) = true
      norm_num [leaf822Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf822CertificateValid :
    WideCertificateValid leaf822Box leaf822Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk78ValidityFacts chi44ValidityFacts
    leaf822LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf822CoverageChecked :
    coverageCheck (innerAD leaf822Box) leaf822InnerLog = true := by
  rfl'

private theorem leaf822InnerLogValid :
    leaf822InnerLog.Valid 8 (innerAD leaf822Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf822CoverageChecked

private noncomputable def leaf822InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629231/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf822InputLogOnePlusV_eq :
    leaf822InputLogOnePlusV = outerEnclosure 24
      (leaf822Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf822RoundedFacts : LeafRoundedFacts 8
    leaf822Certificate.logOnePlusV leaf822InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf822InputLogOnePlusV_eq }

private noncomputable def leaf822Inputs : Inputs :=
  inputsOfCaches globalInput sk78RoundedInputs
    chi44InputQChi innerPair35Input
    leaf822InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf822LowerChecked :
    lowerCheck 24 leaf822Box leaf822Inputs = true := by
  rfl'

private theorem leaf822CoversExact : CoversExact 8
    leaf822Box leaf822Certificate leaf822InnerLog leaf822Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk78RoundedFacts chi44RoundedFacts
    innerPair35RoundedFacts leaf822RoundedFacts (by rfl)

private theorem leaf822FlatSound : Sound leaf822Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf822CertificateValid
    leaf822InnerLogValid leaf822CoversExact leaf822LowerChecked

private noncomputable def leaf823Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (71/32), chiLo := (15/64), chiHi := (1/4) }

private noncomputable def leaf823Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217901/134217728) }, vSqrt := { lower := (65531/65536), upper := (22906164565/22905716736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (202993389/134217728) }, upper := { exponent := 0, mantissa := (199/128) } }, logOuter := sk77LogOuterCertificate, logK := sk77LogKCertificate, logChi := chi45LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (45811881301/45811433472) } }, logDArg := sk77LogDArgCertificate }

private noncomputable def leaf823InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf823LocalValidity :
    LeafFacts leaf823Box leaf823Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf823Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (22906164565/22905716736) }) = true
      norm_num [leaf823Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf823CertificateValid :
    WideCertificateValid leaf823Box leaf823Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk77ValidityFacts chi45ValidityFacts
    leaf823LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf823CoverageChecked :
    coverageCheck (innerAD leaf823Box) leaf823InnerLog = true := by
  rfl'

private theorem leaf823InnerLogValid :
    leaf823InnerLog.Valid 8 (innerAD leaf823Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf823CoverageChecked

private noncomputable def leaf823InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629245/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf823InputLogOnePlusV_eq :
    leaf823InputLogOnePlusV = outerEnclosure 24
      (leaf823Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf823RoundedFacts : LeafRoundedFacts 8
    leaf823Certificate.logOnePlusV leaf823InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf823InputLogOnePlusV_eq }

private noncomputable def leaf823Inputs : Inputs :=
  inputsOfCaches globalInput sk77RoundedInputs
    chi45InputQChi innerPair40Input
    leaf823InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf823LowerChecked :
    lowerCheck 24 leaf823Box leaf823Inputs = true := by
  rfl'

private theorem leaf823CoversExact : CoversExact 8
    leaf823Box leaf823Certificate leaf823InnerLog leaf823Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk77RoundedFacts chi45RoundedFacts
    innerPair40RoundedFacts leaf823RoundedFacts (by rfl)

private theorem leaf823FlatSound : Sound leaf823Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf823CertificateValid
    leaf823InnerLogValid leaf823CoversExact leaf823LowerChecked

private noncomputable def leaf824Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (71/32), kHi := (9/4), chiLo := (15/64), chiHi := (1/4) }

private noncomputable def leaf824Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217903/134217728) }, vSqrt := { lower := (65531/65536), upper := (13743698739/13743423488) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (203976367/134217728) }, upper := { exponent := 0, mantissa := (25/16) } }, logOuter := sk78LogOuterCertificate, logK := sk78LogKCertificate, logChi := chi45LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (27487122227/27486846976) } }, logDArg := sk78LogDArgCertificate }

private noncomputable def leaf824InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf824LocalValidity :
    LeafFacts leaf824Box leaf824Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf824Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (13743698739/13743423488) }) = true
      norm_num [leaf824Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf824CertificateValid :
    WideCertificateValid leaf824Box leaf824Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk78ValidityFacts chi45ValidityFacts
    leaf824LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf824CoverageChecked :
    coverageCheck (innerAD leaf824Box) leaf824InnerLog = true := by
  rfl'

private theorem leaf824InnerLogValid :
    leaf824InnerLog.Valid 8 (innerAD leaf824Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf824CoverageChecked

private noncomputable def leaf824InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629249/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf824InputLogOnePlusV_eq :
    leaf824InputLogOnePlusV = outerEnclosure 24
      (leaf824Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf824RoundedFacts : LeafRoundedFacts 8
    leaf824Certificate.logOnePlusV leaf824InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf824InputLogOnePlusV_eq }

private noncomputable def leaf824Inputs : Inputs :=
  inputsOfCaches globalInput sk78RoundedInputs
    chi45InputQChi innerPair40Input
    leaf824InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf824LowerChecked :
    lowerCheck 24 leaf824Box leaf824Inputs = true := by
  rfl'

private theorem leaf824CoversExact : CoversExact 8
    leaf824Box leaf824Certificate leaf824InnerLog leaf824Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk78RoundedFacts chi45RoundedFacts
    innerPair40RoundedFacts leaf824RoundedFacts (by rfl)

private theorem leaf824FlatSound : Sound leaf824Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf824CertificateValid
    leaf824InnerLogValid leaf824CoversExact leaf824LowerChecked

private noncomputable def component19Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (1/8), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component19Node0_sound : Sound component19Node0Box :=
  sound_of_literal_split component19Node0Box leaf761Box leaf762Box
    .chi (17/128) (by rfl) (by rfl)
    leaf761FlatSound leaf762FlatSound

private noncomputable def component19Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (9/64), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component19Node1_sound : Sound component19Node1Box :=
  sound_of_literal_split component19Node1Box leaf763Box leaf764Box
    .k (65/32) (by rfl) (by rfl)
    leaf763FlatSound leaf764FlatSound

private noncomputable def component19Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (1/8), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component19Node2_sound : Sound component19Node2Box :=
  sound_of_literal_split component19Node2Box component19Node0Box component19Node1Box
    .chi (9/64) (by rfl) (by rfl)
    component19Node0_sound component19Node1_sound

private noncomputable def component19Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (1/8), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component19Node3_sound : Sound component19Node3Box :=
  sound_of_literal_split component19Node3Box leaf765Box leaf766Box
    .chi (17/128) (by rfl) (by rfl)
    leaf765FlatSound leaf766FlatSound

private noncomputable def component19Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (9/64), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component19Node4_sound : Sound component19Node4Box :=
  sound_of_literal_split component19Node4Box leaf767Box leaf768Box
    .k (67/32) (by rfl) (by rfl)
    leaf767FlatSound leaf768FlatSound

private noncomputable def component19Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (1/8), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component19Node5_sound : Sound component19Node5Box :=
  sound_of_literal_split component19Node5Box component19Node3Box component19Node4Box
    .chi (9/64) (by rfl) (by rfl)
    component19Node3_sound component19Node4_sound

private noncomputable def component19Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (17/8), chiLo := (1/8), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component19Node6_sound : Sound component19Node6Box :=
  sound_of_literal_split component19Node6Box component19Node2Box component19Node5Box
    .k (33/16) (by rfl) (by rfl)
    component19Node2_sound component19Node5_sound

private noncomputable def component19Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (5/32), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component19Node7_sound : Sound component19Node7Box :=
  sound_of_literal_split component19Node7Box leaf769Box leaf770Box
    .k (65/32) (by rfl) (by rfl)
    leaf769FlatSound leaf770FlatSound

private noncomputable def component19Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (11/64), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component19Node8_sound : Sound component19Node8Box :=
  sound_of_literal_split component19Node8Box leaf771Box leaf772Box
    .k (65/32) (by rfl) (by rfl)
    leaf771FlatSound leaf772FlatSound

private noncomputable def component19Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (5/32), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component19Node9_sound : Sound component19Node9Box :=
  sound_of_literal_split component19Node9Box component19Node7Box component19Node8Box
    .chi (11/64) (by rfl) (by rfl)
    component19Node7_sound component19Node8_sound

private noncomputable def component19Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (5/32), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component19Node10_sound : Sound component19Node10Box :=
  sound_of_literal_split component19Node10Box leaf773Box leaf774Box
    .k (67/32) (by rfl) (by rfl)
    leaf773FlatSound leaf774FlatSound

private noncomputable def component19Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (11/64), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component19Node11_sound : Sound component19Node11Box :=
  sound_of_literal_split component19Node11Box leaf775Box leaf776Box
    .k (67/32) (by rfl) (by rfl)
    leaf775FlatSound leaf776FlatSound

private noncomputable def component19Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (5/32), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component19Node12_sound : Sound component19Node12Box :=
  sound_of_literal_split component19Node12Box component19Node10Box component19Node11Box
    .chi (11/64) (by rfl) (by rfl)
    component19Node10_sound component19Node11_sound

private noncomputable def component19Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (17/8), chiLo := (5/32), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component19Node13_sound : Sound component19Node13Box :=
  sound_of_literal_split component19Node13Box component19Node9Box component19Node12Box
    .k (33/16) (by rfl) (by rfl)
    component19Node9_sound component19Node12_sound

private noncomputable def component19Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (17/8), chiLo := (1/8), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component19Node14_sound : Sound component19Node14Box :=
  sound_of_literal_split component19Node14Box component19Node6Box component19Node13Box
    .chi (5/32) (by rfl) (by rfl)
    component19Node6_sound component19Node13_sound

private noncomputable def component19Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (1/8), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component19Node15_sound : Sound component19Node15Box :=
  sound_of_literal_split component19Node15Box leaf777Box leaf778Box
    .chi (17/128) (by rfl) (by rfl)
    leaf777FlatSound leaf778FlatSound

private noncomputable def component19Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (1/8), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component19Node16_sound : Sound component19Node16Box :=
  sound_of_literal_split component19Node16Box leaf779Box leaf780Box
    .chi (17/128) (by rfl) (by rfl)
    leaf779FlatSound leaf780FlatSound

private noncomputable def component19Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (9/4), chiLo := (1/8), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component19Node17_sound : Sound component19Node17Box :=
  sound_of_literal_split component19Node17Box component19Node15Box component19Node16Box
    .k (35/16) (by rfl) (by rfl)
    component19Node15_sound component19Node16_sound

private noncomputable def component19Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (9/64), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component19Node18_sound : Sound component19Node18Box :=
  sound_of_literal_split component19Node18Box leaf781Box leaf782Box
    .chi (19/128) (by rfl) (by rfl)
    leaf781FlatSound leaf782FlatSound

private noncomputable def component19Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (9/64), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component19Node19_sound : Sound component19Node19Box :=
  sound_of_literal_split component19Node19Box leaf783Box leaf784Box
    .chi (19/128) (by rfl) (by rfl)
    leaf783FlatSound leaf784FlatSound

private noncomputable def component19Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (9/4), chiLo := (9/64), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component19Node20_sound : Sound component19Node20Box :=
  sound_of_literal_split component19Node20Box component19Node18Box component19Node19Box
    .k (35/16) (by rfl) (by rfl)
    component19Node18_sound component19Node19_sound

private noncomputable def component19Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (9/4), chiLo := (1/8), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component19Node21_sound : Sound component19Node21Box :=
  sound_of_literal_split component19Node21Box component19Node17Box component19Node20Box
    .chi (9/64) (by rfl) (by rfl)
    component19Node17_sound component19Node20_sound

private noncomputable def component19Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (5/32), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component19Node22_sound : Sound component19Node22Box :=
  sound_of_literal_split component19Node22Box leaf785Box leaf786Box
    .k (69/32) (by rfl) (by rfl)
    leaf785FlatSound leaf786FlatSound

private noncomputable def component19Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (11/64), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component19Node23_sound : Sound component19Node23Box :=
  sound_of_literal_split component19Node23Box leaf787Box leaf788Box
    .k (69/32) (by rfl) (by rfl)
    leaf787FlatSound leaf788FlatSound

private noncomputable def component19Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (5/32), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component19Node24_sound : Sound component19Node24Box :=
  sound_of_literal_split component19Node24Box component19Node22Box component19Node23Box
    .chi (11/64) (by rfl) (by rfl)
    component19Node22_sound component19Node23_sound

private noncomputable def component19Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (5/32), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component19Node25_sound : Sound component19Node25Box :=
  sound_of_literal_split component19Node25Box leaf789Box leaf790Box
    .k (71/32) (by rfl) (by rfl)
    leaf789FlatSound leaf790FlatSound

private noncomputable def component19Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (11/64), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component19Node26_sound : Sound component19Node26Box :=
  sound_of_literal_split component19Node26Box leaf791Box leaf792Box
    .k (71/32) (by rfl) (by rfl)
    leaf791FlatSound leaf792FlatSound

private noncomputable def component19Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (5/32), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component19Node27_sound : Sound component19Node27Box :=
  sound_of_literal_split component19Node27Box component19Node25Box component19Node26Box
    .chi (11/64) (by rfl) (by rfl)
    component19Node25_sound component19Node26_sound

private noncomputable def component19Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (9/4), chiLo := (5/32), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component19Node28_sound : Sound component19Node28Box :=
  sound_of_literal_split component19Node28Box component19Node24Box component19Node27Box
    .k (35/16) (by rfl) (by rfl)
    component19Node24_sound component19Node27_sound

private noncomputable def component19Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (9/4), chiLo := (1/8), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component19Node29_sound : Sound component19Node29Box :=
  sound_of_literal_split component19Node29Box component19Node21Box component19Node28Box
    .chi (5/32) (by rfl) (by rfl)
    component19Node21_sound component19Node28_sound

private noncomputable def component19Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (9/4), chiLo := (1/8), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component19Node30_sound : Sound component19Node30Box :=
  sound_of_literal_split component19Node30Box component19Node14Box component19Node29Box
    .k (17/8) (by rfl) (by rfl)
    component19Node14_sound component19Node29_sound

private noncomputable def component19Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (3/16), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component19Node31_sound : Sound component19Node31Box :=
  sound_of_literal_split component19Node31Box leaf793Box leaf794Box
    .k (65/32) (by rfl) (by rfl)
    leaf793FlatSound leaf794FlatSound

private noncomputable def component19Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component19Node32_sound : Sound component19Node32Box :=
  sound_of_literal_split component19Node32Box leaf795Box leaf796Box
    .k (65/32) (by rfl) (by rfl)
    leaf795FlatSound leaf796FlatSound

private noncomputable def component19Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (3/16), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component19Node33_sound : Sound component19Node33Box :=
  sound_of_literal_split component19Node33Box component19Node31Box component19Node32Box
    .chi (13/64) (by rfl) (by rfl)
    component19Node31_sound component19Node32_sound

private noncomputable def component19Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (3/16), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component19Node34_sound : Sound component19Node34Box :=
  sound_of_literal_split component19Node34Box leaf797Box leaf798Box
    .k (67/32) (by rfl) (by rfl)
    leaf797FlatSound leaf798FlatSound

private noncomputable def component19Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component19Node35_sound : Sound component19Node35Box :=
  sound_of_literal_split component19Node35Box leaf799Box leaf800Box
    .k (67/32) (by rfl) (by rfl)
    leaf799FlatSound leaf800FlatSound

private noncomputable def component19Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (3/16), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component19Node36_sound : Sound component19Node36Box :=
  sound_of_literal_split component19Node36Box component19Node34Box component19Node35Box
    .chi (13/64) (by rfl) (by rfl)
    component19Node34_sound component19Node35_sound

private noncomputable def component19Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (17/8), chiLo := (3/16), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component19Node37_sound : Sound component19Node37Box :=
  sound_of_literal_split component19Node37Box component19Node33Box component19Node36Box
    .k (33/16) (by rfl) (by rfl)
    component19Node33_sound component19Node36_sound

private noncomputable def component19Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component19Node38_sound : Sound component19Node38Box :=
  sound_of_literal_split component19Node38Box leaf801Box leaf802Box
    .k (65/32) (by rfl) (by rfl)
    leaf801FlatSound leaf802FlatSound

private noncomputable def component19Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component19Node39_sound : Sound component19Node39Box :=
  sound_of_literal_split component19Node39Box leaf803Box leaf804Box
    .k (65/32) (by rfl) (by rfl)
    leaf803FlatSound leaf804FlatSound

private noncomputable def component19Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (7/32), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component19Node40_sound : Sound component19Node40Box :=
  sound_of_literal_split component19Node40Box component19Node38Box component19Node39Box
    .chi (15/64) (by rfl) (by rfl)
    component19Node38_sound component19Node39_sound

private noncomputable def component19Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component19Node41_sound : Sound component19Node41Box :=
  sound_of_literal_split component19Node41Box leaf805Box leaf806Box
    .k (67/32) (by rfl) (by rfl)
    leaf805FlatSound leaf806FlatSound

private noncomputable def component19Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component19Node42_sound : Sound component19Node42Box :=
  sound_of_literal_split component19Node42Box leaf807Box leaf808Box
    .k (67/32) (by rfl) (by rfl)
    leaf807FlatSound leaf808FlatSound

private noncomputable def component19Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (7/32), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component19Node43_sound : Sound component19Node43Box :=
  sound_of_literal_split component19Node43Box component19Node41Box component19Node42Box
    .chi (15/64) (by rfl) (by rfl)
    component19Node41_sound component19Node42_sound

private noncomputable def component19Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (17/8), chiLo := (7/32), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component19Node44_sound : Sound component19Node44Box :=
  sound_of_literal_split component19Node44Box component19Node40Box component19Node43Box
    .k (33/16) (by rfl) (by rfl)
    component19Node40_sound component19Node43_sound

private noncomputable def component19Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (17/8), chiLo := (3/16), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component19Node45_sound : Sound component19Node45Box :=
  sound_of_literal_split component19Node45Box component19Node37Box component19Node44Box
    .chi (7/32) (by rfl) (by rfl)
    component19Node37_sound component19Node44_sound

private noncomputable def component19Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (3/16), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component19Node46_sound : Sound component19Node46Box :=
  sound_of_literal_split component19Node46Box leaf809Box leaf810Box
    .k (69/32) (by rfl) (by rfl)
    leaf809FlatSound leaf810FlatSound

private noncomputable def component19Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component19Node47_sound : Sound component19Node47Box :=
  sound_of_literal_split component19Node47Box leaf811Box leaf812Box
    .k (69/32) (by rfl) (by rfl)
    leaf811FlatSound leaf812FlatSound

private noncomputable def component19Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (3/16), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component19Node48_sound : Sound component19Node48Box :=
  sound_of_literal_split component19Node48Box component19Node46Box component19Node47Box
    .chi (13/64) (by rfl) (by rfl)
    component19Node46_sound component19Node47_sound

private noncomputable def component19Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (3/16), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component19Node49_sound : Sound component19Node49Box :=
  sound_of_literal_split component19Node49Box leaf813Box leaf814Box
    .k (71/32) (by rfl) (by rfl)
    leaf813FlatSound leaf814FlatSound

private noncomputable def component19Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component19Node50_sound : Sound component19Node50Box :=
  sound_of_literal_split component19Node50Box leaf815Box leaf816Box
    .k (71/32) (by rfl) (by rfl)
    leaf815FlatSound leaf816FlatSound

private noncomputable def component19Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (3/16), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component19Node51_sound : Sound component19Node51Box :=
  sound_of_literal_split component19Node51Box component19Node49Box component19Node50Box
    .chi (13/64) (by rfl) (by rfl)
    component19Node49_sound component19Node50_sound

private noncomputable def component19Node52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (9/4), chiLo := (3/16), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component19Node52_sound : Sound component19Node52Box :=
  sound_of_literal_split component19Node52Box component19Node48Box component19Node51Box
    .k (35/16) (by rfl) (by rfl)
    component19Node48_sound component19Node51_sound

private noncomputable def component19Node53Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component19Node53_sound : Sound component19Node53Box :=
  sound_of_literal_split component19Node53Box leaf817Box leaf818Box
    .k (69/32) (by rfl) (by rfl)
    leaf817FlatSound leaf818FlatSound

private noncomputable def component19Node54Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component19Node54_sound : Sound component19Node54Box :=
  sound_of_literal_split component19Node54Box leaf819Box leaf820Box
    .k (69/32) (by rfl) (by rfl)
    leaf819FlatSound leaf820FlatSound

private noncomputable def component19Node55Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (7/32), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component19Node55_sound : Sound component19Node55Box :=
  sound_of_literal_split component19Node55Box component19Node53Box component19Node54Box
    .chi (15/64) (by rfl) (by rfl)
    component19Node53_sound component19Node54_sound

private noncomputable def component19Node56Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component19Node56_sound : Sound component19Node56Box :=
  sound_of_literal_split component19Node56Box leaf821Box leaf822Box
    .k (71/32) (by rfl) (by rfl)
    leaf821FlatSound leaf822FlatSound

private noncomputable def component19Node57Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component19Node57_sound : Sound component19Node57Box :=
  sound_of_literal_split component19Node57Box leaf823Box leaf824Box
    .k (71/32) (by rfl) (by rfl)
    leaf823FlatSound leaf824FlatSound

private noncomputable def component19Node58Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (7/32), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component19Node58_sound : Sound component19Node58Box :=
  sound_of_literal_split component19Node58Box component19Node56Box component19Node57Box
    .chi (15/64) (by rfl) (by rfl)
    component19Node56_sound component19Node57_sound

private noncomputable def component19Node59Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (9/4), chiLo := (7/32), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component19Node59_sound : Sound component19Node59Box :=
  sound_of_literal_split component19Node59Box component19Node55Box component19Node58Box
    .k (35/16) (by rfl) (by rfl)
    component19Node55_sound component19Node58_sound

private noncomputable def component19Node60Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (9/4), chiLo := (3/16), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component19Node60_sound : Sound component19Node60Box :=
  sound_of_literal_split component19Node60Box component19Node52Box component19Node59Box
    .chi (7/32) (by rfl) (by rfl)
    component19Node52_sound component19Node59_sound

private noncomputable def component19Node61Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (9/4), chiLo := (3/16), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component19Node61_sound : Sound component19Node61Box :=
  sound_of_literal_split component19Node61Box component19Node45Box component19Node60Box
    .k (17/8) (by rfl) (by rfl)
    component19Node45_sound component19Node60_sound

noncomputable def component19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (9/4), chiLo := (1/8), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
theorem component19_sound : Sound component19Box :=
  sound_of_literal_split component19Box component19Node30Box component19Node61Box
    .chi (3/16) (by rfl) (by rfl)
    component19Node30_sound component19Node61_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
